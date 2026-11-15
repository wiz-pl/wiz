#!/usr/bin/env python3
"""Signed build statements, the build manifest and TPM 2.0 quotes for Wiz artifacts.

One flow, one manifest: `wiz build --attest FILE` writes an in-toto Statement v1
whose predicate is the `wiz-build-manifest/v1` body (`Wiz/Attest.lean`).  This
module signs that exact statement as a DSSE envelope with an offline Ed25519 key
(`ssh-keygen -Y sign`), binds its digest to a TPM 2.0 quote, and verifies the
whole bundle.  There is no second manifest format: the manifest is the predicate,
and the statement digest is SHA-256 of the DSSE payload.

This module is deliberately standalone and uses only the Python 3 standard
library plus OpenSSH's `ssh-keygen` (already needed for SSH).  It defines:

* `wiz-attest sign --attest STATEMENT` -- sign the payload as a DSSE envelope,
  also writing a detached `.sig`;
* `wiz-attest quote --attest ENVELOPE` -- quote PCRs with
  `extraData = H("wiz-quote-v1" || nonce || statement_digest)`;
* `wiz-attest attest SRC` -- the convenience producer: run
  `wiz build SRC --attest` (or take `--statement`), sign, then quote;
* `wiz-attest keygen|ak-info`;
* `wiz-verify --attest ENVELOPE`, which checks the DSSE payloadType, signature
  over PAE, key fingerprint allowlist, statement/manifest/artifact binding, the
  quote `extraData`, an expected PCR policy and, when `tpm2-tools` is installed,
  the quote signature and PCR digest via `tpm2_checkquote` (TPM cryptography is
  not reimplemented here).  With `--snp-report`/`--snp-policy` it also verifies
  an AMD SEV-SNP attestation report and its VCEK/VLEK -> ASK -> ARK chain
  (`snp.py`), binding `REPORT_DATA = H("wiz-snp-v1" || nonce || statement_digest)`.

The formats and the trust model are documented in `docs/attestation.md`.
Exit codes are the same for all CLIs:

  0  everything ran and passed (verifier: a real signature check ran)
  1  verification or production failed
  2  usage error
  3  incomplete: a required tool is missing, `--skip-crypto` was used, or a
     required signature/nonce/pin was not supplied

The producer uses only transient TPM objects (no persistent handle, no NV
write); the AK private blob is discarded after the quote.  No private key or
nonce is ever written into the manifest.
"""

from __future__ import annotations

import argparse
import base64
import copy
import datetime
import hashlib
import json
import os
import re
import secrets
import shutil
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Sequence

import snp as wiz_snp

SCHEMA = "wiz-build-manifest/v1"
POLICY_SCHEMA = "wiz-pcr-policy/v1"
RESULT_SCHEMA = "wiz-attestation-result/v1"

# DSSE / in-toto statement signing.  The signature is an OpenSSH SSHSIG made by
# `ssh-keygen -Y sign` with an offline Ed25519 key; the payload is the canonical
# in-toto statement, and the signature is over the DSSE PAE, not the payload
# alone.  The statement's predicate is the one manifest body `wiz build --attest`
# emits (Wiz/Attest.lean); there is no second manifest format.
DSSE_PAYLOAD_TYPE = "application/vnd.in-toto+json"
STATEMENT_TYPE = "https://in-toto.io/Statement/v1"
PREDICATE_TYPE = "https://wiz-lang.org/attestation/wiz-build/v1"
DSSE_NAMESPACE = "wiz-attest-dsse"
DSSE_KEY_IDENTITY = "wiz-attest"
ENVELOPE_NAME = "manifest.intoto.json"
DETACHED_SUFFIX = ".sig"
SIGSTORE_BUNDLE_SUFFIX = ".cosign.bundle"
KEY_SCHEMA = "wiz-attest-key/v1"
SIGN_RESULT_SCHEMA = "wiz-attest-sign-result/v1"
BUILD_TYPE = "https://wiz-lang.org/buildtypes/wiz-build/v1"
QUOTE_LABEL = b"wiz-quote-v1"

BANK = "sha256"
DIGEST_SIZE = hashlib.sha256().digest_size
MAX_PCR = 23

ATTEST_MAGIC = 0xFF544347  # TPM_GENERATED_VALUE
ATTEST_QUOTE = 0x8018  # TPM_ST_ATTEST_QUOTE
ALG_SHA256 = 0x000B

EXIT_OK = 0
EXIT_FAIL = 1
EXIT_USAGE = 2
EXIT_INCOMPLETE = 3

_HEX64 = re.compile(r"^[0-9a-f]{64}$")
_HEX = re.compile(r"^(?:[0-9a-fA-F]{2})+$")


class AttestError(Exception):
    """A failure that the CLI reports as a verification/production error."""

    exit_code = EXIT_FAIL


class UsageError(AttestError):
    exit_code = EXIT_USAGE


class IncompleteError(AttestError):
    exit_code = EXIT_INCOMPLETE


class SchemaError(AttestError):
    exit_code = EXIT_FAIL


# --------------------------------------------------------------------------
# Canonical JSON and digests


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON number {value!r}")


def _unique_object(pairs: Sequence[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError(f"duplicate JSON key {key!r}")
        obj[key] = value
    return obj


def canonical_bytes(obj: Any) -> bytes:
    """The one serialization of a manifest: sorted keys, no whitespace, UTF-8.

    A manifest file is exactly these bytes (no trailing newline).  The SHA-256
    of the file is therefore unambiguous, which is what `extraData` binds.
    """
    return json.dumps(
        obj,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def load_json_strict(data: bytes) -> Any:
    """Parse UTF-8 JSON, rejecting duplicates, NaN/Infinity and trailing data."""
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise SchemaError(f"not UTF-8: {exc}") from None
    try:
        return json.loads(
            text,
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except (ValueError, json.JSONDecodeError) as exc:
        raise SchemaError(f"invalid JSON: {exc}") from None


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# --------------------------------------------------------------------------
# The one manifest (the predicate of the statement `wiz build --attest` writes)
#
# Wiz/Attest.lean emits this body.  It is signed as-is (the DSSE payload is the
# in-toto Statement, whose predicate is this object), so the signer and the
# verifier never assemble a second manifest from the filesystem.


_MANIFEST_KEYS = {
    "schema",
    "buildType",
    "format",
    "builder",
    "target",
    "source",
    "inputsRoot",
    "inputs",
    "headers",
    "toolchain",
    "flags",
    "artifacts",
    "environment",
    "prev",
    "valid_until",
}
_MANIFEST_REQUIRED = {
    "schema", "buildType", "format", "builder", "target", "source",
    "inputsRoot", "inputs", "toolchain", "flags", "artifacts", "environment",
}
_INPUT_ROLES = {"source", "module", "link-c"}
_ARTIFACT_ROLES = {"output", "byproduct"}


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise SchemaError(message)


def _expect_hex64(value: Any, what: str) -> None:
    _expect(isinstance(value, str) and _HEX64.match(value) is not None,
            f"{what} must be 64 lowercase hex characters")


def _expect_keys(obj: Any, allowed: set[str], required: set[str], what: str) -> None:
    _expect(isinstance(obj, dict), f"{what} must be an object")
    unknown = set(obj) - allowed
    missing = required - set(obj)
    _expect(not unknown, f"unknown {what} fields: {', '.join(sorted(unknown))}")
    _expect(not missing, f"missing {what} fields: {', '.join(sorted(missing))}")


def _normalize_relative(path: Any, what: str) -> str:
    """Validate a manifest-relative path and return it with `/` separators."""
    _expect(isinstance(path, str) and path != "", f"{what} must be a non-empty string")
    _expect("\\" not in path, f"{what} must use '/' separators: {path!r}")
    _expect(not path.startswith("/"), f"{what} must be relative: {path!r}")
    parts = path.split("/")
    _expect(all(part not in ("", ".", "..") for part in parts),
            f"{what} must not contain empty, '.' or '..' components: {path!r}")
    return path


def _validate_tool(value: Any, what: str) -> None:
    _expect_keys(value, {"path", "sha256", "version"}, {"path", "sha256"}, what)
    _expect(isinstance(value["path"], str) and value["path"] != "",
            f"{what}.path must be a non-empty string")
    _expect_hex64(value["sha256"], f"{what}.sha256")
    if "version" in value:
        _expect(isinstance(value["version"], str), f"{what}.version must be a string")


def _validate_flag_value(value: Any, where: str) -> None:
    if isinstance(value, (str, bool)) or _is_int(value):
        return
    if isinstance(value, list):
        _expect(all(isinstance(v, str) for v in value),
                f"{where} must be a string or an array of strings")
        return
    raise SchemaError(f"{where} must be a string, integer, boolean or array of strings")


def input_sort_key(item: dict[str, Any]) -> tuple[str, str, str]:
    return (item["role"], item.get("name", ""), item.get("path", ""))


def inputs_root(items: Sequence[dict[str, Any]]) -> str:
    """The manifest root: SHA-256 of the canonical input lines.

    Mirrors `Wiz.Attest.inputsRoot` byte for byte: role, name and path
    tab-separated, one line per input, under a `wiz-inputs-v1` label.
    """
    lines = "".join(
        f"{item['role']}\t{item.get('name', '')}\t{item.get('path', '')}\t"
        f"{item['sha256']}\n"
        for item in items
    )
    return sha256_bytes(("wiz-inputs-v1\n" + lines).encode("utf-8"))


def validate_manifest(obj: Any) -> None:
    """Raise SchemaError unless `obj` is the `SCHEMA` manifest body.

    This is the **one** manifest: the predicate of the in-toto Statement that
    `wiz build --attest` emits.  `wiz-attest sign` signs it, `wiz-verify`
    checks the signed body, the artifacts and (optionally) the quote.
    """
    _expect_keys(obj, _MANIFEST_KEYS, _MANIFEST_REQUIRED, "manifest")
    _expect(obj["schema"] == SCHEMA, f"schema must be {SCHEMA!r}")
    _expect(obj["buildType"] == BUILD_TYPE, f"buildType must be {BUILD_TYPE!r}")
    _expect(_is_int(obj["format"]) and obj["format"] == 1,
            "format must be the integer 1")

    builder = obj["builder"]
    _expect_keys(builder, {"kind", "version"}, {"kind"}, "builder")
    _expect(builder["kind"] == "wiz-build",
            "builder.kind must be \"wiz-build\" (the TPM quote is not the builder)")
    if "version" in builder:
        _expect(isinstance(builder["version"], str) and builder["version"],
                "builder.version must be a non-empty string")

    target = obj["target"]
    _expect(isinstance(target, str) and 0 < len(target) <= 128
            and all(32 <= ord(c) < 127 for c in target),
            "target must be a non-empty printable string (a target triple)")

    source = obj["source"]
    _expect_keys(source, {"file", "sha256", "git"}, {"file", "sha256"}, "source")
    _expect(isinstance(source["file"], str) and source["file"] != "",
            "source.file must be a non-empty string")
    _expect_hex64(source["sha256"], "source.sha256")
    if "git" in source:
        git = source["git"]
        _expect_keys(git, {"commit", "dirty"}, {"commit", "dirty"}, "source.git")
        _expect(isinstance(git["commit"], str)
                and re.fullmatch(r"[0-9a-f]{7,64}", git["commit"]) is not None,
                "source.git.commit must be 7-64 lowercase hex characters")
        _expect(isinstance(git["dirty"], bool), "source.git.dirty must be a boolean")

    inputs = obj["inputs"]
    _expect(isinstance(inputs, list) and inputs, "inputs must be a non-empty array")
    seen: set[tuple[str, str, str]] = set()
    for i, item in enumerate(inputs):
        where = f"inputs[{i}]"
        _expect_keys(item, {"role", "name", "path", "sha256"},
                     {"role", "sha256"}, where)
        _expect(item["role"] in _INPUT_ROLES,
                f"{where}.role must be one of {', '.join(sorted(_INPUT_ROLES))}")
        _expect_hex64(item["sha256"], f"{where}.sha256")
        if item["role"] == "module":
            _expect(isinstance(item.get("name"), str) and item["name"] != "",
                    f"{where}.name must name the imported module")
        else:
            _normalize_relative(item.get("path"), f"{where}.path")
        key = input_sort_key(item)
        _expect(key not in seen, f"inputs contains {key} twice")
        seen.add(key)
    _expect(inputs == sorted(inputs, key=input_sort_key),
            "inputs must be sorted by role, name and path")

    root = obj["inputsRoot"]
    _expect(isinstance(root, str) and root.startswith("sha256:")
            and _HEX64.match(root[7:]) is not None,
            "inputsRoot must be \"sha256:\" + 64 lowercase hex characters")
    _expect(root == "sha256:" + inputs_root(inputs),
            "inputsRoot does not match the canonical input lines")

    if "headers" in obj:
        headers = obj["headers"]
        _expect(isinstance(headers, list)
                and all(isinstance(h, str) and h for h in headers),
                "headers must be an array of non-empty strings")
        _expect(headers == sorted(set(headers)), "headers must be sorted and unique")

    toolchain = obj["toolchain"]
    _expect_keys(toolchain, {"wiz", "cc", "llc"}, {"wiz"}, "toolchain")
    _expect_keys(toolchain["wiz"], {"version", "sha256", "revision"},
                 {"version", "sha256"}, "toolchain.wiz")
    _expect(isinstance(toolchain["wiz"]["version"], str)
            and toolchain["wiz"]["version"] != "",
            "toolchain.wiz.version must be a non-empty string")
    _expect_hex64(toolchain["wiz"]["sha256"], "toolchain.wiz.sha256")
    if "revision" in toolchain["wiz"]:
        _expect(isinstance(toolchain["wiz"]["revision"], str),
                "toolchain.wiz.revision must be a string")
    for name in ("cc", "llc"):
        if name in toolchain:
            _validate_tool(toolchain[name], f"toolchain.{name}")

    flags = obj["flags"]
    _expect(isinstance(flags, dict) and flags, "flags must be a non-empty object")
    for key, value in flags.items():
        _validate_flag_value(value, f"flags.{key}")

    artifacts = obj["artifacts"]
    _expect(isinstance(artifacts, list) and artifacts,
            "artifacts must be a non-empty array")
    paths: list[str] = []
    outputs = 0
    for i, art in enumerate(artifacts):
        where = f"artifacts[{i}]"
        _expect_keys(art, {"path", "role", "kind", "size", "sha256"},
                     {"path", "role", "size", "sha256"}, where)
        path = _normalize_relative(art["path"], f"{where}.path")
        _expect(art["role"] in _ARTIFACT_ROLES,
                f"{where}.role must be output or byproduct")
        if art["role"] == "output":
            outputs += 1
        if "kind" in art:
            _expect(isinstance(art["kind"], str), f"{where}.kind must be a string")
        _expect(_is_int(art["size"]) and art["size"] >= 0,
                f"{where}.size must be a non-negative integer")
        _expect_hex64(art["sha256"], f"{where}.sha256")
        paths.append(path)
    _expect(outputs == 1, "artifacts must contain exactly one output")
    _expect(paths == sorted(paths), "artifacts must be sorted by path")
    _expect(len(paths) == len(set(paths)), "artifact paths must be unique")

    environment = obj["environment"]
    _expect(isinstance(environment, dict) and environment,
            "environment must be a non-empty object")
    for key, value in environment.items():
        _expect(isinstance(value, str), f"environment.{key} must be a string")

    if "prev" in obj:
        _expect(isinstance(obj["prev"], str)
                and _HEX64.match(obj["prev"].lower()) is not None,
                "prev must be 64 hex characters")
    if "valid_until" in obj:
        _expect(isinstance(obj["valid_until"], str),
                "valid_until must be a string")
        _iso_utc(obj["valid_until"], "valid_until")


def validate_policy(obj: Any) -> dict[str, Any]:
    """Raise SchemaError unless `obj` is a valid PCR policy; return it normalized."""
    _expect(isinstance(obj, dict), "policy must be a JSON object")
    unknown = set(obj) - {"schema", "bank", "pcr", "ak_sha256",
                          "ak_spki_sha256", "ak_name", "valid_until"}
    missing = {"schema", "bank", "pcr"} - set(obj)
    _expect(not unknown, f"unknown policy fields: {', '.join(sorted(unknown))}")
    _expect(not missing, f"missing policy fields: {', '.join(sorted(missing))}")
    _expect(obj["schema"] == POLICY_SCHEMA, f"policy schema must be {POLICY_SCHEMA!r}")
    _expect(obj["bank"] == BANK, f"policy bank must be {BANK!r}")
    pcrs = obj["pcr"]
    _expect(isinstance(pcrs, dict) and pcrs, "policy pcr must be a non-empty object")
    normalized: dict[int, str] = {}
    for key, value in pcrs.items():
        _expect(re.fullmatch(r"(?:[0-9]|[12][0-9])", str(key)) is not None
                and 0 <= int(key) <= MAX_PCR,
                f"policy PCR index must be 0..{MAX_PCR}: {key!r}")
        _expect(isinstance(value, str) and _HEX64.match(value.lower()) is not None,
                f"policy PCR {key} must be 64 hex characters")
        normalized[int(key)] = value.lower()
    result: dict[str, Any] = {"bank": BANK, "pcr": normalized}
    if "ak_sha256" in obj:
        _expect(isinstance(obj["ak_sha256"], str)
                and _HEX64.match(obj["ak_sha256"].lower()) is not None,
                "policy ak_sha256 must be 64 hex characters")
        result["ak_sha256"] = obj["ak_sha256"].lower()
    if "ak_spki_sha256" in obj:
        _expect(isinstance(obj["ak_spki_sha256"], str)
                and _HEX64.match(obj["ak_spki_sha256"].lower()) is not None,
                "policy ak_spki_sha256 must be 64 hex characters")
        result["ak_spki_sha256"] = obj["ak_spki_sha256"].lower()
    if "ak_name" in obj:
        _expect(isinstance(obj["ak_name"], str)
                and re.fullmatch(r"[0-9a-fA-F]{68}", obj["ak_name"]) is not None
                and obj["ak_name"].lower().startswith("000b"),
                "policy ak_name must be a sha256 TPM Name (000b + 64 hex)")
        result["ak_name"] = obj["ak_name"].lower()
    if "valid_until" in obj:
        _expect(isinstance(obj["valid_until"], str),
                "policy valid_until must be a string")
        try:
            _iso_utc(obj["valid_until"], "policy valid_until")
        except UsageError as exc:
            raise SchemaError(str(exc)) from None
        result["valid_until"] = obj["valid_until"].strip()
    return result


def subject_of(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    """The statement subject: one entry per artifact, in manifest order."""
    return [
        {"name": art["path"], "digest": {"sha256": art["sha256"]}}
        for art in manifest["artifacts"]
    ]


def validate_statement(statement: Any) -> dict[str, Any]:
    """Check a statement against its predicate and return the manifest.

    The subject is derived from the manifest artifacts, so a statement whose
    predicate was rewritten cannot disagree with what the signature covers.
    """
    _expect(isinstance(statement, dict), "statement must be a JSON object")
    _expect_keys(statement, {"_type", "subject", "predicateType", "predicate"},
                 {"_type", "subject", "predicateType", "predicate"}, "statement")
    _expect(statement["_type"] == STATEMENT_TYPE,
            f"_type must be {STATEMENT_TYPE!r}")
    _expect(statement["predicateType"] == PREDICATE_TYPE,
            f"predicateType must be {PREDICATE_TYPE!r}")
    manifest = statement["predicate"]
    validate_manifest(manifest)
    _expect(statement["subject"] == subject_of(manifest),
            "subject does not match the manifest artifacts")
    return manifest


def load_statement(path: Path) -> tuple[dict[str, Any], bytes, dict[str, Any] | None]:
    """Read a DSSE envelope or a bare statement.

    Returns (statement, payload bytes, envelope or None).  The payload is the
    byte string a signature covers (DSSE PAE) and whose SHA-256 the TPM quote
    and SNP report bind.  Nothing is canonicalised here: the signer writes one
    canonical payload, and verification hashes what is on disk.
    """
    raw = _read_bytes(path, "statement")
    parsed = load_json_strict(raw)
    if not isinstance(parsed, dict):
        raise SchemaError("statement file must be a JSON object")
    if "payloadType" not in parsed:
        return parsed, raw, None
    _expect_keys(parsed, {"payloadType", "payload", "signatures"},
                 {"payloadType", "payload", "signatures"}, "DSSE envelope")
    # The payloadType is checked by verify_signature (a wrong one is a reportable
    # failure, not an unreadable file); the payload is what the signature covers.
    payload = _unb64(parsed["payload"], "DSSE payload")
    try:
        statement = load_json_strict(payload)
    except SchemaError as exc:
        raise SchemaError(f"DSSE payload is not JSON: {exc}") from None
    if not isinstance(statement, dict):
        raise SchemaError("DSSE payload is not a JSON object")
    _expect(canonical_bytes(statement) == payload,
            "DSSE payload is not canonical JSON (sorted keys, no whitespace); "
            "regenerate it with `wiz build --attest` or `wiz-attest sign`")
    return statement, payload, parsed


def quote_extra_data(nonce: bytes, statement_digest: str) -> str:
    """The TPM quote's ``extraData``: H("wiz-quote-v1" || nonce || digest).

    Freshness lives here, not in the manifest, so the manifest/statement is a
    stable function of the inputs and two builders can compare digests.  The
    digest is SHA-256 of the canonical in-toto statement payload, not just the
    manifest, so substituting a subject or predicateType also fails.
    """
    if len(nonce) < 16 or len(nonce) > 64:
        raise UsageError("nonce must be 16..64 bytes")
    if _HEX64.match(statement_digest) is None:
        raise UsageError("statement digest must be 64 lowercase hex characters")
    return sha256_bytes(QUOTE_LABEL + nonce + bytes.fromhex(statement_digest))


# --------------------------------------------------------------------------
# TPMS_ATTEST parsing (format parsing only: no cryptography)


@dataclass
class QuoteAttest:
    extra_data: str
    qualified_signer: str
    pcr_bank: str
    pcr_indices: list[int]
    pcr_digest: str
    clock: int
    reset_count: int
    restart_count: int
    safe: int
    firmware_version: str


class _Reader:
    def __init__(self, data: bytes) -> None:
        self.data = data
        self.pos = 0

    def take(self, n: int, what: str) -> bytes:
        if self.pos + n > len(self.data):
            raise SchemaError(f"quote.msg truncated reading {what}")
        chunk = self.data[self.pos:self.pos + n]
        self.pos += n
        return chunk

    def u8(self, what: str) -> int:
        return self.take(1, what)[0]

    def u16(self, what: str) -> int:
        return struct.unpack(">H", self.take(2, what))[0]

    def u32(self, what: str) -> int:
        return struct.unpack(">I", self.take(4, what))[0]

    def u64(self, what: str) -> int:
        return struct.unpack(">Q", self.take(8, what))[0]

    def tpm2b(self, what: str) -> bytes:
        size = self.u16(f"{what} size")
        return self.take(size, what)

    def done(self) -> bool:
        return self.pos == len(self.data)


def _pcr_selection_mask(mask: bytes) -> list[int]:
    indices: list[int] = []
    for byte_index, byte in enumerate(mask):
        for bit in range(8):
            if byte & (1 << bit):
                indices.append(byte_index * 8 + bit)
    return indices


def parse_quote(data: bytes) -> QuoteAttest:
    """Parse a TPM2B_ATTEST/TPMS_ATTEST produced by `tpm2_quote -m`."""
    r = _Reader(data)
    magic = r.u32("magic")
    stype = r.u16("type")
    if magic != ATTEST_MAGIC:
        raise SchemaError(f"quote.msg magic is {magic:#010x}, expected {ATTEST_MAGIC:#010x}")
    if stype != ATTEST_QUOTE:
        raise SchemaError(f"quote.msg type is {stype:#06x}, expected {ATTEST_QUOTE:#06x}")
    qualified_signer = r.tpm2b("qualifiedSigner")
    extra_data = r.tpm2b("extraData")
    clock = r.u64("clockInfo.clock")
    reset_count = r.u32("clockInfo.resetCount")
    restart_count = r.u32("clockInfo.restartCount")
    safe = r.u8("clockInfo.safe")
    firmware = r.take(8, "firmwareVersion")
    count = r.u32("pcrSelect.count")
    if count != 1:
        raise SchemaError(f"quote.msg selects {count} PCR banks; only one sha256 bank is supported")
    alg = r.u16("pcrSelect.hash")
    if alg != ALG_SHA256:
        raise SchemaError(f"quote.msg PCR bank algorithm is {alg:#06x}, expected sha256")
    size_of_select = r.u8("pcrSelect.sizeofSelect")
    if size_of_select < 1 or size_of_select > 4:
        raise SchemaError(f"quote.msg sizeofSelect is {size_of_select}")
    indices = _pcr_selection_mask(r.take(size_of_select, "pcrSelect.pcrSelect"))
    if not indices:
        raise SchemaError("quote.msg selects no PCRs")
    if indices[-1] > MAX_PCR:
        raise SchemaError(f"quote.msg selects PCR {indices[-1]} beyond the supported 0..{MAX_PCR}")
    pcr_digest = r.tpm2b("pcrDigest")
    if len(pcr_digest) != DIGEST_SIZE:
        raise SchemaError(f"quote.msg pcrDigest is {len(pcr_digest)} bytes, expected {DIGEST_SIZE}")
    if not r.done():
        raise SchemaError(f"quote.msg has {len(data) - r.pos} trailing bytes")
    return QuoteAttest(
        extra_data=extra_data.hex(),
        qualified_signer=qualified_signer.hex(),
        pcr_bank=BANK,
        pcr_indices=indices,
        pcr_digest=pcr_digest.hex(),
        clock=clock,
        reset_count=reset_count,
        restart_count=restart_count,
        safe=safe,
        firmware_version=firmware.hex(),
    )


def parse_pcr_values(data: bytes, indices: Sequence[int]) -> dict[int, str]:
    """Parse `tpm2_quote -o ... -F values`: concatenated 32-byte PCR values."""
    expected = DIGEST_SIZE * len(indices)
    if len(data) != expected:
        raise SchemaError(
            f"quote.pcr is {len(data)} bytes; with {len(indices)} selected PCRs "
            f"the `-F values` format must be {expected} bytes"
        )
    return {
        index: data[i * DIGEST_SIZE:(i + 1) * DIGEST_SIZE].hex()
        for i, index in enumerate(indices)
    }


# --------------------------------------------------------------------------
# AK identity: TPM Name and DER SubjectPublicKeyInfo
#
# `ak.pub` from `tpm2_create -u` is a TPM2B_PUBLIC, not a PEM file.  Pinning
# its file hash (the deprecated `ak_sha256`) is not a stable identity: the same
# key can be re-marshalled, and it says nothing about the TPM Name the quote
# actually signs.  The policy pins `ak_spki_sha256` (DER SPKI, the encoding
# OpenSSL/cosign tooling uses) and `ak_name` (nameAlg || H(publicArea), compared
# with the quote's qualifiedSigner).

RSA_OID = bytes.fromhex("2a864886f70d010101")  # 1.2.840.113549.1.1.1


@dataclass
class AkInfo:
    file_sha256: str
    public_area: bytes
    name_alg: int
    name: str
    spki_sha256: str
    key_type: str


def _der_len(length: int) -> bytes:
    if length < 0x80:
        return bytes([length])
    raw = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(raw)]) + raw


def _der(tag: int, content: bytes) -> bytes:
    return bytes([tag]) + _der_len(len(content)) + content


def _der_uint(value: int) -> bytes:
    if value < 0:
        raise ValueError("negative DER integer")
    raw = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    if raw[0] & 0x80:
        raw = b"\x00" + raw
    return _der(0x02, raw)


def _der_bit_string(content: bytes) -> bytes:
    return _der(0x03, b"\x00" + content)


def rsa_spki(modulus: bytes, exponent: int) -> bytes:
    """DER SubjectPublicKeyInfo for an RSA public key (RFC 5280/3279)."""
    modulus = modulus.lstrip(b"\x00") or b"\x00"
    rsa_public_key = _der(0x30, _der_uint(int.from_bytes(modulus, "big"))
                          + _der_uint(exponent or 65537))
    algorithm = _der(0x30, _der(0x06, RSA_OID) + _der(0x05, b""))
    return _der(0x30, algorithm + _der_bit_string(rsa_public_key))


def _parse_tpmt_public(public_area: bytes) -> tuple[int, int, bytes, int, bytes]:
    """Return (type, nameAlg, publicArea, exponent, modulus) for an RSA key."""
    r = _Reader(public_area)
    key_type = r.u16("TPMT_PUBLIC.type")
    name_alg = r.u16("TPMT_PUBLIC.nameAlg")
    r.u32("TPMT_PUBLIC.objectAttributes")
    r.tpm2b("TPMT_PUBLIC.authPolicy")
    if key_type == 0x0001:  # TPM_ALG_RSA
        symmetric = r.u16("RSA symmetric.algorithm")
        if symmetric != 0x0010:  # TPM_ALG_NULL
            r.u16("RSA symmetric.keyBits")
            r.u16("RSA symmetric.mode")
        scheme = r.u16("RSA scheme.scheme")
        if scheme != 0x0010:
            r.u16("RSA scheme.hashAlg")
        r.u16("RSA keyBits")
        exponent = r.u32("RSA exponent")
        modulus = r.tpm2b("RSA unique")
        key_type_name = "rsa"
    else:
        raise SchemaError(
            f"ak.pub key type is {key_type:#06x}; only RSA AKs are supported"
        )
    if not r.done():
        raise SchemaError(f"ak.pub public area has {len(public_area) - r.pos} trailing bytes")
    return key_type, name_alg, public_area, exponent, modulus


def ak_info(path: Path) -> AkInfo:
    """Parse a TPM2B_PUBLIC AK file into its TPM Name and DER SPKI digest."""
    raw = _read_bytes(path, "AK public key")
    if len(raw) < 2:
        raise SchemaError("ak.pub is shorter than a TPM2B_PUBLIC size field")
    size = struct.unpack(">H", raw[:2])[0]
    if size != len(raw) - 2:
        raise SchemaError(
            f"ak.pub TPM2B_PUBLIC size is {size}, file has {len(raw) - 2} bytes"
        )
    public_area = raw[2:]
    _, name_alg, public_area, exponent, modulus = _parse_tpmt_public(public_area)
    if name_alg != ALG_SHA256:
        raise SchemaError(f"ak.pub nameAlg is {name_alg:#06x}; only sha256 is supported")
    name = struct.pack(">H", name_alg).hex() + sha256_bytes(public_area)
    return AkInfo(
        file_sha256=sha256_bytes(raw),
        public_area=public_area,
        name_alg=name_alg,
        name=name,
        spki_sha256=sha256_bytes(rsa_spki(modulus, exponent)),
        key_type="rsa",
    )


# --------------------------------------------------------------------------
# DSSE envelope, in-toto Statement and offline Ed25519 signing


@dataclass
class PublicKey:
    source: str
    key_type: str
    blob: bytes
    fingerprint: str


def _b64(data: bytes) -> str:
    return base64.b64encode(data).decode("ascii")


def _unb64(text: str, what: str) -> bytes:
    if not isinstance(text, str) or not text:
        raise SchemaError(f"{what} must be a non-empty base64 string")
    try:
        return base64.b64decode(text.encode("ascii"), validate=True)
    except (ValueError, UnicodeEncodeError) as exc:
        raise SchemaError(f"{what} is not valid base64: {exc}") from None


def dsse_pae(payload_type: str, payload: bytes) -> bytes:
    """DSSE Pre-Authentication Encoding: DSSEv1 <len> <type> <len> <payload>."""
    type_bytes = payload_type.encode("utf-8")
    return (b"DSSEv1 " + str(len(type_bytes)).encode("ascii") + b" "
            + type_bytes + b" " + str(len(payload)).encode("ascii") + b" "
            + payload)


def normalize_fingerprint(value: str) -> str:
    text = value.strip()
    if text.lower().startswith("sha256:"):
        text = text[7:]
    text = text.rstrip("=")
    if _HEX64.match(text.lower()):
        return text.lower()
    if re.fullmatch(r"[A-Za-z0-9+/]{43}", text):
        return "SHA256:" + text
    raise UsageError(
        "fingerprints must be SHA256:<base64> (OpenSSH) or 64 hex characters"
    )


def fingerprint_matches(expected: str, key: PublicKey) -> bool:
    normalized = normalize_fingerprint(expected)
    if _HEX64.match(normalized):
        return normalized == sha256_bytes(key.blob)
    return normalized[7:] == key.fingerprint[7:]


def _key_from_line(line: str, source: str) -> PublicKey:
    tokens = line.split()
    for index, token in enumerate(tokens):
        if token in ("ssh-ed25519", "ssh-rsa", "ecdsa-sha2-nistp256",
                     "sk-ssh-ed25519@openssh.com"):
            if index + 1 >= len(tokens):
                raise SchemaError(f"{source}: key type {token!r} has no base64 key")
            key_type, encoded = token, tokens[index + 1]
            break
    else:
        raise SchemaError(f"{source}: no SSH public key found")
    if key_type != "ssh-ed25519":
        raise SchemaError(f"{source}: only Ed25519 keys are supported, got {key_type}")
    try:
        blob = base64.b64decode(encoded.encode("ascii"), validate=True)
    except (ValueError, UnicodeEncodeError) as exc:
        raise SchemaError(f"{source}: invalid base64 key: {exc}") from None
    fingerprint = "SHA256:" + _b64(hashlib.sha256(blob).digest()).rstrip("=")
    return PublicKey(source=source, key_type=key_type, blob=blob,
                     fingerprint=fingerprint)


def parse_public_key(path: Path, *, ssh_keygen: str | None = None) -> PublicKey:
    if not path.is_file():
        raise UsageError(f"public key does not exist: {path}")
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise UsageError(f"cannot read public key {path}: {exc}") from None
    if "PRIVATE KEY" in text:
        # A private key is accepted as a convenience; only its derived public
        # half is ever parsed or printed, never the private bytes.
        tool = ssh_keygen or shutil.which("ssh-keygen")
        if not tool:
            raise IncompleteError("ssh-keygen is required to read a private key")
        proc = subprocess.run([tool, "-y", "-f", str(path)],
                              capture_output=True, text=True, timeout=60)
        if proc.returncode != 0:
            raise UsageError(
                f"cannot derive a public key from {path}: {_tail(proc.stderr)}"
            )
        text = proc.stdout
    for line in text.splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            return _key_from_line(line, str(path))
    raise UsageError(f"public key file is empty: {path}")


def load_allowed_signers(path: Path) -> list[PublicKey]:
    if not path.is_file():
        raise UsageError(f"allowed_signers file does not exist: {path}")
    keys: list[PublicKey] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        raise UsageError(f"cannot read allowed_signers {path}: {exc}") from None
    for number, line in enumerate(lines, 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        keys.append(_key_from_line(stripped, f"{path}:{number}"))
    if not keys:
        raise UsageError(f"allowed_signers file has no keys: {path}")
    return keys


def find_ssh_keygen(explicit: str | None = None) -> str:
    found = explicit or shutil.which("ssh-keygen")
    if not found:
        raise IncompleteError("ssh-keygen not found; install OpenSSH >= 8.8")
    return found


def generate_key(key_path: Path, *, comment: str, force: bool = False,
                 ssh_keygen: str | None = None) -> dict[str, Any]:
    if key_path.exists() and not force:
        raise UsageError(f"key already exists: {key_path} (pass --force to replace)")
    key_path.parent.mkdir(parents=True, exist_ok=True)
    tool = find_ssh_keygen(ssh_keygen)
    cmd = [tool, "-q", "-t", "ed25519", "-N", "", "-C", comment,
           "-f", str(key_path)]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    if proc.returncode != 0:
        raise AttestError(f"ssh-keygen key generation failed: {_tail(proc.stderr)}")
    try:
        os.chmod(key_path, 0o600)
    except OSError:
        pass
    pub_path = Path(str(key_path) + ".pub")
    public = parse_public_key(pub_path, ssh_keygen=tool)
    return {
        "schema": KEY_SCHEMA,
        "key": str(key_path),
        "public_key": str(pub_path),
        "key_type": public.key_type,
        "fingerprint": public.fingerprint,
        "comment": comment,
    }


def sign_pae(key_path: Path, pae: bytes, *, ssh_keygen: str | None = None,
             namespace: str = DSSE_NAMESPACE) -> bytes:
    if not key_path.is_file():
        raise UsageError(f"private key does not exist: {key_path}")
    tool = find_ssh_keygen(ssh_keygen)
    with tempfile.TemporaryDirectory(prefix="wiz-dsse-sign-") as tmp:
        message = Path(tmp) / "pae"
        message.write_bytes(pae)
        cmd = [tool, "-Y", "sign", "-f", str(key_path), "-n", namespace,
               str(message)]
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        if proc.returncode != 0:
            raise AttestError(
                f"ssh-keygen -Y sign failed (exit {proc.returncode}): "
                f"{_tail(proc.stderr or proc.stdout)}"
            )
        signature_path = Path(str(message) + ".sig")
        if not signature_path.is_file():
            raise AttestError("ssh-keygen -Y sign did not write a signature file")
        signature = signature_path.read_bytes()
    if not signature.startswith(b"-----BEGIN SSH SIGNATURE-----"):
        raise AttestError("ssh-keygen wrote an unexpected signature format")
    return signature


def verify_pae(key: PublicKey, signature: bytes, pae: bytes, *,
               ssh_keygen: str | None = None,
               namespace: str = DSSE_NAMESPACE) -> tuple[bool, str]:
    """Verify an SSHSIG over PAE with one Ed25519 key; no network involved."""
    tool = find_ssh_keygen(ssh_keygen)
    with tempfile.TemporaryDirectory(prefix="wiz-dsse-verify-") as tmp:
        allowed = Path(tmp) / "allowed_signers"
        allowed.write_text(
            f"{DSSE_KEY_IDENTITY} namespaces=\"{namespace}\" {key.key_type} "
            f"{_b64(key.blob)}\n",
            encoding="utf-8",
        )
        signature_path = Path(tmp) / "signature"
        signature_path.write_bytes(signature)
        cmd = [tool, "-Y", "verify", "-f", str(allowed),
               "-I", DSSE_KEY_IDENTITY, "-n", namespace,
               "-s", str(signature_path)]
        proc = subprocess.run(cmd, input=pae, capture_output=True, timeout=120)
    if proc.returncode == 0:
        return True, ""
    detail = _tail((proc.stderr or b"").decode("utf-8", "replace")
                   + "\n" + (proc.stdout or b"").decode("utf-8", "replace"))
    return False, detail


def _iso_utc(value: str, what: str) -> str:
    text = value.strip()
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", text):
        raise UsageError(f"{what} must be an RFC 3339 UTC timestamp ending in Z")
    try:
        datetime.datetime.strptime(text, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError as exc:
        raise UsageError(f"{what} is not a valid timestamp: {exc}") from None
    return text


def _valid_until_expired(value: str, *, now: datetime.datetime | None = None) -> bool:
    when = datetime.datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(
        tzinfo=datetime.timezone.utc)
    current = now or datetime.datetime.now(datetime.timezone.utc)
    if current.tzinfo is None:
        current = current.replace(tzinfo=datetime.timezone.utc)
    return current > when


def apply_statement_options(statement: dict[str, Any], payload: bytes, *,
                            prev: str | None = None,
                            valid_until: str | None = None) -> bytes:
    """Add signing-time policy fields, or keep the payload byte-for-byte.

    `wiz build --attest` produces a payload that is a pure function of the
    inputs.  `--prev` and `--valid-until` are choices of the signer, so they are
    applied here, to the statement, and the payload is re-serialised canonically
    (which `wiz build` already emits).  With neither option the original bytes
    are signed: what the build wrote is what the signature covers.
    """
    if prev is None and valid_until is None:
        return payload
    if prev is not None:
        prev = normalize_hex(prev, "--prev")
        if len(prev) != 64:
            raise UsageError("--prev must be 64 hex characters")
    if valid_until is not None:
        valid_until = _iso_utc(valid_until, "--valid-until")
    changed = copy.deepcopy(statement)
    predicate = changed["predicate"]
    if prev is not None:
        predicate["prev"] = prev
    if valid_until is not None:
        predicate["valid_until"] = valid_until
    validate_statement(changed)
    return canonical_bytes(changed)


def statement_digest_of_payload(payload: bytes) -> str:
    return sha256_bytes(payload)


def _write_canonical(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_bytes(obj))


def _sigstore_bundle(envelope_path: Path, bundle_path: Path, *,
                     upload: bool, cosign_bin: str | None = None) -> None:
    """Opt-in Sigstore/Rekor path; never called unless --sigstore is given."""
    cosign = cosign_bin or shutil.which("cosign")
    if not cosign:
        raise IncompleteError(
            "cosign not found; install cosign or omit --sigstore "
            "(the offline DSSE signature does not need it)"
        )
    cmd = [cosign, "sign-blob", "--yes", "--bundle", str(bundle_path)]
    if not upload:
        # Local bundle only: no network and no Rekor entry by default.
        cmd.append("--tlog-upload=false")
    cmd.append(str(envelope_path))
    _run(cmd, what="cosign sign-blob", timeout=300)


def sign_statement(statement_path: Path, key_path: Path, *,
                   out: Path | None = None,
                   detached: Path | None = None,
                   prev: str | None = None,
                   valid_until: str | None = None,
                   sigstore: bool = False,
                   sigstore_upload: bool = False,
                   cosign_bin: str | None = None,
                   ssh_keygen: str | None = None) -> dict[str, Any]:
    """Sign the statement from `wiz build --attest` as a DSSE envelope."""
    statement, payload, _ = load_statement(statement_path)
    validate_statement(statement)
    if canonical_bytes(statement) != payload:
        raise SchemaError(
            "statement payload is not canonical JSON (sorted keys, no whitespace); "
            "regenerate it with wiz build --attest"
        )
    payload = apply_statement_options(statement, payload, prev=prev,
                                      valid_until=valid_until)
    payload_digest = statement_digest_of_payload(payload)
    public = parse_public_key(key_path, ssh_keygen=ssh_keygen)
    signature = sign_pae(key_path, dsse_pae(DSSE_PAYLOAD_TYPE, payload),
                         ssh_keygen=ssh_keygen)
    envelope = {
        "payloadType": DSSE_PAYLOAD_TYPE,
        "payload": _b64(payload),
        "signatures": [{"keyid": public.fingerprint, "sig": _b64(signature)}],
    }
    envelope_path = Path(out) if out else statement_path.parent / ENVELOPE_NAME
    detached_path = (Path(detached) if detached
                     else Path(str(envelope_path) + DETACHED_SUFFIX))
    _write_canonical(envelope_path, envelope)
    detached_path.parent.mkdir(parents=True, exist_ok=True)
    detached_path.write_bytes(signature)
    result: dict[str, Any] = {
        "schema": SIGN_RESULT_SCHEMA,
        "statement": str(statement_path),
        "statement_sha256": payload_digest,
        "envelope": str(envelope_path),
        "detached_signature": str(detached_path),
        "payload_type": DSSE_PAYLOAD_TYPE,
        "keyid": public.fingerprint,
        "signed": True,
        "sigstore": None,
    }
    if prev is not None:
        result["prev"] = prev.lower()
    if valid_until is not None:
        result["valid_until"] = valid_until
    if sigstore or sigstore_upload:
        bundle = Path(str(envelope_path) + SIGSTORE_BUNDLE_SUFFIX)
        _sigstore_bundle(envelope_path, bundle, upload=sigstore_upload,
                         cosign_bin=cosign_bin)
        result["sigstore"] = {
            "bundle": str(bundle),
            "uploaded": bool(sigstore_upload),
        }
    return result


def _statement_failure(result: "VerifyResult", detail: str) -> None:
    result.add("dsse_statement", "fail", detail)


def verify_statement_payload(payload: bytes, statement: dict[str, Any],
                             result: "VerifyResult", *,
                             expect_prev: str | None = None,
                             now: datetime.datetime | None = None) -> None:
    """Check that the payload is the statement the manifest says it is."""
    try:
        parsed = load_json_strict(payload)
    except SchemaError as exc:
        _statement_failure(result, f"signed payload is not JSON: {exc}")
        return
    if canonical_bytes(parsed) != payload:
        _statement_failure(
            result,
            "signed payload is not canonical JSON (sorted keys, no whitespace); "
            "regenerate it with `wiz build --attest` or `wiz-attest sign`",
        )
        return
    if parsed != statement:
        _statement_failure(result, "signed payload differs from the parsed statement")
        return
    try:
        validate_statement(parsed)
    except SchemaError as exc:
        _statement_failure(result, str(exc))
        return
    predicate = parsed["predicate"]
    failures: list[str] = []
    if predicate["schema"] != SCHEMA:
        failures.append(f"predicate.schema is {predicate['schema']!r}")
    if predicate["buildType"] != BUILD_TYPE:
        failures.append(f"predicate.buildType is {predicate['buildType']!r}")
    if predicate["builder"]["kind"] != "wiz-build":
        failures.append("predicate.builder.kind is not wiz-build")
    if parsed["subject"] != subject_of(predicate):
        failures.append("statement subject does not match the manifest artifacts")
    if predicate["inputsRoot"] != "sha256:" + inputs_root(predicate["inputs"]):
        failures.append("inputsRoot does not match the canonical input lines")
    if "prev" in predicate:
        prev = predicate["prev"]
        if not isinstance(prev, str) or _HEX64.match(prev.lower()) is None:
            failures.append("predicate.prev must be 64 hex characters")
        elif expect_prev is None:
            result.add("dsse_prev", "skip",
                       f"statement chains to {prev.lower()}; pass --expect-prev "
                       "to pin the previous root")
        elif prev.lower() == expect_prev.lower():
            result.add("dsse_prev", "pass", prev.lower())
        else:
            result.add("dsse_prev", "fail",
                       f"statement prev is {prev.lower()}, expected {expect_prev.lower()}")
    else:
        result.add("dsse_prev", "pass", "no previous root (first statement)")
    if "valid_until" in predicate:
        until = predicate["valid_until"]
        if not isinstance(until, str):
            result.add("dsse_valid_until", "fail",
                       "predicate.valid_until must be a string")
        else:
            try:
                _iso_utc(until, "predicate.valid_until")
            except UsageError as exc:
                result.add("dsse_valid_until", "fail", str(exc))
            else:
                if _valid_until_expired(until, now=now):
                    result.add("dsse_valid_until", "fail",
                               f"statement expired at {until}")
                else:
                    result.add("dsse_valid_until", "pass", until)
    else:
        result.add("dsse_valid_until", "pass",
                   "no expiry in statement (use --valid-until for releases)")
        result.warnings.append(
            "statement has no valid_until; an old signed statement verifies "
            "forever unless a policy or log limits it"
        )
    if failures:
        _statement_failure(result, "; ".join(failures))
    else:
        result.add("dsse_statement", "pass",
                   "statement matches its manifest, artifacts and build parameters")


def verify_signature(args: argparse.Namespace, result: "VerifyResult",
                     statement: dict[str, Any], payload: bytes,
                     envelope: dict[str, Any] | None) -> None:
    """Verify the DSSE envelope, key allowlist and statement binding."""
    allow_unsigned = bool(getattr(args, "allow_unsigned", False))
    require_signature = bool(getattr(args, "require_signature", False))
    attest_path = Path(args.attest)
    if envelope is None:
        result.signed = False
        if allow_unsigned:
            result.add("signature_policy", "pass",
                       "unsigned statement accepted explicitly (--allow-unsigned)")
            result.warnings.append(
                "no DSSE signature was checked; --allow-unsigned is for local checks"
            )
        else:
            result.add("signature_policy", "fail",
                       "statement is unsigned; run wiz-attest sign or pass "
                       "--allow-unsigned for an explicit unsigned check"
                       + (" (--require-signature)" if require_signature else ""))
        verify_statement_payload(payload, statement, result,
                                 expect_prev=getattr(args, "expect_prev", None),
                                 now=getattr(args, "now", None))
        return

    result.add("dsse_envelope", "pass", str(attest_path))
    payload_type = envelope.get("payloadType")
    if payload_type == DSSE_PAYLOAD_TYPE:
        result.add("dsse_payload_type", "pass", payload_type)
    else:
        result.add("dsse_payload_type", "fail",
                   f"payloadType is {payload_type!r}, expected {DSSE_PAYLOAD_TYPE!r}")
    result.statement_sha256 = sha256_bytes(payload)
    pae = dsse_pae(DSSE_PAYLOAD_TYPE, payload)

    keys: list[PublicKey] = []
    key_problem: str | None = None
    for item in getattr(args, "public_key", []) or []:
        try:
            keys.append(parse_public_key(Path(item),
                                         ssh_keygen=getattr(args, "ssh_keygen", None)))
        except AttestError as exc:
            key_problem = str(exc)
    for item in getattr(args, "allowed_signers", []) or []:
        try:
            keys.extend(load_allowed_signers(Path(item)))
        except AttestError as exc:
            key_problem = str(exc)
    deduped: dict[str, PublicKey] = {}
    for key in keys:
        deduped.setdefault(key.fingerprint, key)
    keys = list(deduped.values())
    fingerprints = [normalize_fingerprint(value)
                    for value in getattr(args, "key_fingerprint", []) or []]
    if fingerprints:
        keys = [key for key in keys
                if any(fingerprint_matches(fp, key) for fp in fingerprints)]
        if not keys and key_problem is None:
            key_problem = ("none of the provided public keys match "
                           "--key-fingerprint")
    if not keys:
        result.signed = True
        result.add("dsse_key", "fail",
                   key_problem or "no --public-key or --allowed-signers given; "
                                  "the signing key is not pinned")
        verify_statement_payload(payload, statement, result,
                                 expect_prev=getattr(args, "expect_prev", None),
                                 now=getattr(args, "now", None))
        return

    signatures = envelope.get("signatures")
    accepted: PublicKey | None = None
    rejected_keyid: str | None = None
    if not isinstance(signatures, list) or not signatures:
        if allow_unsigned:
            result.add("dsse_signature", "skip",
                       "envelope has no signatures; accepted by --allow-unsigned")
            result.warnings.append("signed envelope has no signatures")
        else:
            result.add("dsse_signature", "fail",
                       "DSSE envelope has no signatures; pass --allow-unsigned "
                       "only for local unsigned checks")
        result.signed = False
    else:
        for entry in signatures:
            if (not isinstance(entry, dict)
                    or set(entry) != {"keyid", "sig"}
                    or not isinstance(entry.get("keyid"), str)
                    or not entry["keyid"]):
                result.add("dsse_signature", "fail",
                           "each signature needs exactly a non-empty keyid and sig")
                break
            try:
                signature = _unb64(entry["sig"], "signature")
            except SchemaError as exc:
                result.add("dsse_signature", "fail", str(exc))
                break
            for key in keys:
                ok, _ = verify_pae(key, signature, pae,
                                   ssh_keygen=getattr(args, "ssh_keygen", None))
                if not ok:
                    continue
                if entry["keyid"] != key.fingerprint:
                    rejected_keyid = entry["keyid"]
                    continue
                accepted = key
                break
            if accepted is not None:
                break
        if accepted is not None:
            result.add("dsse_signature", "pass",
                       f"SSHSIG over DSSE PAE verifies under {accepted.fingerprint}")
            result.add("dsse_key", "pass", accepted.fingerprint)
            result.signed = True
            result.keyid = accepted.fingerprint
        else:
            result.signed = True
            if rejected_keyid is not None:
                result.add("dsse_key", "fail",
                           f"envelope keyid {rejected_keyid} does not match the "
                           "fingerprint of the key that signed")
            else:
                result.add("dsse_key", "fail",
                           "signature does not verify under any allowlisted key")
            result.add("dsse_signature", "fail",
                       "no signature verifies over the DSSE PAE")

    detached_arg = getattr(args, "detached_signature", None)
    if detached_arg:
        detached_path = Path(detached_arg)
        try:
            detached_sig = _read_bytes(detached_path, "detached signature")
        except AttestError as exc:
            result.add("dsse_detached_signature", "fail", str(exc))
        else:
            detached_ok = any(
                verify_pae(key, detached_sig, pae,
                           ssh_keygen=getattr(args, "ssh_keygen", None))[0]
                for key in keys
            )
            if detached_ok:
                result.add("dsse_detached_signature", "pass", str(detached_path))
            else:
                result.add("dsse_detached_signature", "fail",
                           "detached SSHSIG over the DSSE PAE does not verify "
                           "under an allowlisted key")

    verify_statement_payload(payload, statement, result,
                             expect_prev=getattr(args, "expect_prev", None),
                             now=getattr(args, "now", None))


# --------------------------------------------------------------------------
# Verifier


@dataclass
class Check:
    name: str
    status: str = "pass"  # pass | fail | skip
    detail: str = ""


@dataclass
class VerifyResult:
    checks: list[Check] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    manifest_sha256: str | None = None
    quote: QuoteAttest | None = None
    signed: bool | None = None
    statement_sha256: str | None = None
    keyid: str | None = None
    snp: dict[str, Any] | None = None

    def add(self, name: str, status: str, detail: str = "") -> None:
        self.checks.append(Check(name, status, detail))
        if status == "fail":
            self.errors.append(f"{name}: {detail}" if detail else name)
        elif status == "skip":
            self.warnings.append(f"{name} skipped: {detail}" if detail else f"{name} skipped")

    def failed(self) -> bool:
        return any(c.status == "fail" for c in self.checks)

    def incomplete(self) -> bool:
        return any(c.status == "skip" for c in self.checks)

    def status(self) -> str:
        if self.failed():
            return "failed"
        if self.incomplete():
            return "partial"
        return "verified"

    def exit_code(self) -> int:
        if self.failed():
            return EXIT_FAIL
        if self.incomplete():
            return EXIT_INCOMPLETE
        return EXIT_OK


def _read_bytes(path: Path, what: str) -> bytes:
    try:
        return path.read_bytes()
    except OSError as exc:
        raise AttestError(f"cannot read {what} at {path}: {exc.strerror}") from None


def normalize_hex(value: str, what: str) -> str:
    text = value.strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    if not text or not _HEX.match(text):
        raise UsageError(f"{what} must be an even-length hex string")
    return text


def find_checkquote(explicit: str | None, tpm2_bin: str | None) -> str | None:
    if explicit:
        return explicit
    if tpm2_bin:
        candidate = Path(tpm2_bin) / "tpm2_checkquote"
        if candidate.is_file():
            return str(candidate)
    return shutil.which("tpm2_checkquote")


def _tail(text: str, lines: int = 4) -> str:
    kept = [line for line in text.strip().splitlines() if line.strip()]
    return " | ".join(kept[-lines:])


def verify(args: argparse.Namespace) -> VerifyResult:
    result = VerifyResult()
    attest_path = Path(args.attest)
    attest_dir = attest_path.parent

    # 1. The statement (DSSE envelope or bare), its schema and its manifest.
    # Nothing below is trustworthy if this fails, so schema failure stops the run.
    try:
        statement, payload, envelope = load_statement(attest_path)
        parsed = validate_statement(statement)
        if canonical_bytes(statement) != payload:
            raise SchemaError(
                "statement payload is not canonical JSON (sorted keys, no "
                "whitespace); regenerate it with wiz build --attest"
            )
    except AttestError as exc:
        result.add("manifest_schema", "fail", str(exc))
        return result

    manifest_digest = sha256_bytes(canonical_bytes(parsed))
    result.manifest_sha256 = manifest_digest
    result.statement_sha256 = sha256_bytes(payload)
    result.add("manifest_schema", "pass",
               f"{SCHEMA}, canonical predicate, {len(parsed['artifacts'])} artifact(s)")
    result.add("manifest_digest", "pass", manifest_digest)
    result.add("statement_digest", "pass", result.statement_sha256)

    if args.expect_digest:
        expected = normalize_hex(args.expect_digest, "--expect-digest")
        if expected == manifest_digest:
            result.add("manifest_pin", "pass", "manifest digest matches --expect-digest")
        else:
            result.add("manifest_pin", "fail",
                       f"manifest is {manifest_digest}, expected {expected}")

    # 2. Every artifact's size and digest.
    artifacts_dir = Path(args.artifacts_dir) if args.artifacts_dir else attest_dir
    try:
        artifacts_root = artifacts_dir.resolve()
    except OSError as exc:
        result.add("artifacts", "fail", f"cannot resolve --artifacts-dir: {exc}")
        artifacts_root = attest_dir.resolve()
    artifact_failures = 0
    for art in parsed["artifacts"]:
        rel = art["path"]
        try:
            target = (artifacts_root / rel).resolve()
            if target != artifacts_root and artifacts_root not in target.parents:
                raise AttestError(f"artifact path escapes the artifacts directory: {rel}")
            if not target.is_file():
                raise AttestError(f"artifact is missing: {rel}")
            size = target.stat().st_size
            if size != art["size"]:
                raise AttestError(f"size is {size}, manifest says {art['size']}")
            digest = sha256_file(target)
            if digest != art["sha256"]:
                raise AttestError(f"sha256 is {digest}, manifest says {art['sha256']}")
        except (AttestError, OSError) as exc:
            artifact_failures += 1
            result.add(f"artifact:{rel}", "fail", str(exc))
        else:
            result.add(f"artifact:{rel}", "pass",
                       f"{art['size']} bytes, sha256 {art['sha256']}")
    if artifact_failures:
        result.add("artifacts", "fail", f"{artifact_failures} artifact(s) failed")
    else:
        result.add("artifacts", "pass", f"{len(parsed['artifacts'])} artifact(s) match")

    # 3. Quote message: shape and extraData binding.
    quote_path = Path(args.quote) if args.quote else attest_dir / "quote.msg"
    sig_path = Path(args.signature) if args.signature else attest_dir / "quote.sig"
    pcr_path = Path(args.pcr) if args.pcr else attest_dir / "quote.pcr"
    ak_path = Path(args.ak) if args.ak else attest_dir / "ak.pub"

    quote: QuoteAttest | None = None
    pcr_values: dict[int, str] = {}
    try:
        quote = parse_quote(_read_bytes(quote_path, "quote message"))
        result.quote = quote
    except AttestError as exc:
        result.add("quote_message", "fail", str(exc))
    else:
        result.add("quote_message", "pass",
                   f"TPMS_ATTEST quote over {len(quote.pcr_indices)} PCRs")
        result.add("quote_pcr_selection", "pass",
                   f"sha256:{','.join(map(str, quote.pcr_indices))}")

    # 4. PCR values against the expected policy.
    policy: dict[str, Any] | None = None
    try:
        policy_obj = load_json_strict(_read_bytes(Path(args.policy), "policy"))
        policy = validate_policy(policy_obj)
        result.add("policy_schema", "pass",
                   f"{POLICY_SCHEMA}, {len(policy['pcr'])} PCR(s)")
    except AttestError as exc:
        result.add("policy_schema", "fail", str(exc))

    if quote is not None:
        try:
            pcr_values = parse_pcr_values(_read_bytes(pcr_path, "PCR values"),
                                          quote.pcr_indices)
            result.add("pcr_values", "pass",
                       f"{len(pcr_values)} value(s), `-F values` format")
        except AttestError as exc:
            result.add("pcr_values", "fail", str(exc))
    else:
        result.add("pcr_values", "fail", "no parsed quote to interpret quote.pcr")

    if policy is not None and quote is not None and pcr_values:
        failures = 0
        for index, expected in sorted(policy["pcr"].items()):
            if index not in pcr_values:
                failures += 1
                result.add(f"pcr_policy:{index}", "fail",
                           f"policy PCR {index} is not covered by the quote")
            elif pcr_values[index] != expected:
                failures += 1
                result.add(f"pcr_policy:{index}", "fail",
                           f"value is {pcr_values[index]}, policy says {expected}")
            else:
                result.add(f"pcr_policy:{index}", "pass", expected)
        if failures == 0:
            result.add("pcr_policy", "pass",
                       f"{len(policy['pcr'])} pinned PCR(s) match")

    # 5. AK pin.  Prefer the DER SPKI digest and the TPM Name (which the quote
    # signs as qualifiedSigner); the legacy ak_sha256 is the TPM2B_PUBLIC file
    # hash and is kept only for older policies.
    pin_conflict = False

    def _pin(option: str, policy_key: str) -> str | None:
        nonlocal pin_conflict
        cli = getattr(args, option, None)
        cli = cli.lower() if cli else None
        from_policy = policy.get(policy_key) if policy is not None else None
        if cli and from_policy and cli != from_policy:
            pin_conflict = True
            result.add("ak_pin", "fail",
                       f"--{option.replace('_', '-')} {cli} conflicts with policy "
                       f"{from_policy}")
        return cli or from_policy

    expected_spki = _pin("ak_spki_sha256", "ak_spki_sha256")
    expected_name = _pin("ak_name", "ak_name")
    expected_ak_file = _pin("ak_sha256", "ak_sha256")
    ak_parsed: AkInfo | None = None
    try:
        ak_parsed = ak_info(ak_path)
    except AttestError as exc:
        if expected_spki or expected_name:
            result.add("ak_pin", "fail", f"cannot parse {ak_path}: {exc}")
    if ak_parsed is not None:
        if quote is not None and quote.qualified_signer != ak_parsed.name:
            result.add("ak_name", "fail",
                       f"quote qualifiedSigner is {quote.qualified_signer}, "
                       f"ak.pub Name is {ak_parsed.name}")
        elif quote is not None:
            result.add("ak_name", "pass", ak_parsed.name)
        if expected_name:
            if ak_parsed.name == expected_name:
                result.add("ak_name_pin", "pass", expected_name)
            else:
                result.add("ak_name_pin", "fail",
                           f"ak.pub Name is {ak_parsed.name}, expected {expected_name}")
        if expected_spki:
            if ak_parsed.spki_sha256 == expected_spki:
                result.add("ak_spki_pin", "pass", expected_spki)
            else:
                result.add("ak_spki_pin", "fail",
                           f"ak.pub DER SPKI is {ak_parsed.spki_sha256}, "
                           f"expected {expected_spki}")
    if expected_ak_file:
        try:
            actual_ak = sha256_file(ak_path)
        except OSError as exc:
            result.add("ak_pin", "fail", f"cannot read {ak_path}: {exc.strerror}")
        else:
            if actual_ak == expected_ak_file:
                result.add("ak_pin", "pass", actual_ak)
            else:
                result.add("ak_pin", "fail",
                           f"AK file is {actual_ak}, expected {expected_ak_file}")
    elif not expected_spki and not expected_name and not pin_conflict:
        result.add("ak_pin", "skip",
                   "no --ak-spki-sha256/--ak-name (or legacy --ak-sha256) and no "
                   "policy pin: the AK identity is not pinned")
    if policy is not None and "valid_until" in policy:
        if _valid_until_expired(policy["valid_until"],
                                now=getattr(args, "now", None)):
            result.add("policy_valid_until", "fail",
                       f"policy expired at {policy['valid_until']}")
        else:
            result.add("policy_valid_until", "pass", policy["valid_until"])

    # 6. DSSE signature, key allowlist and statement/manifest binding.  This
    # runs before the quote check because the quote binds statement_digest.
    verify_signature(args, result, statement, payload, envelope)
    expected_statement = getattr(args, "expect_statement_digest", None)
    if expected_statement:
        if result.statement_sha256 is None:
            result.add("statement_pin", "fail",
                       "cannot pin the statement: no statement payload")
        elif result.statement_sha256 == expected_statement:
            result.add("statement_pin", "pass", expected_statement)
        else:
            result.add("statement_pin", "fail",
                       f"statement is {result.statement_sha256}, expected "
                       f"{expected_statement}")

    # 7. Freshness and quote extraData:
    #    H("wiz-quote-v1" || nonce || statement_digest).
    nonce_hex = getattr(args, "nonce", None) or getattr(args, "challenge", None)
    nonce: bytes | None = None
    if nonce_hex:
        nonce_hex = normalize_hex(nonce_hex, "--nonce")
        if not 16 <= len(nonce_hex) // 2 <= 64:
            result.add("nonce", "fail", "nonce must be 16..64 bytes")
        else:
            nonce = bytes.fromhex(nonce_hex)
            result.add("nonce", "pass", nonce_hex)
    elif getattr(args, "require_nonce", False) or getattr(args, "require_challenge", False):
        result.add("nonce", "fail",
                   "no verifier-supplied nonce; a quote can be replayed")
    else:
        sidecar = attest_dir / "quote.nonce"
        if sidecar.is_file():
            try:
                sidecar_hex = normalize_hex(sidecar.read_text(encoding="utf-8"),
                                            "quote.nonce")
                nonce = bytes.fromhex(sidecar_hex)
            except (AttestError, OSError, ValueError):
                nonce = None
            if nonce is not None:
                result.add("nonce", "skip",
                           f"read {sidecar.name}; the verifier did not supply it, "
                           "so replay protection is not established")
                result.warnings.append(
                    "nonce came from the bundle (quote.nonce), not from the verifier; "
                    "pass --nonce from your own channel for freshness"
                )
        if nonce is None:
            result.add("nonce", "skip",
                       "no --nonce and no quote.nonce; freshness is not checked")

    # The statement digest is what both the TPM quote and an SNP report bind.
    # It is SHA-256 of the payload (the signed bytes, or the bare statement's
    # bytes when --allow-unsigned is explicit).
    statement_digest = result.statement_sha256

    if quote is not None:
        if nonce is None:
            if quote.extra_data == manifest_digest:
                result.add("quote_extra_data", "skip",
                           "extraData is the deprecated sha256(manifest); pass "
                           "--nonce to check H(label||nonce||statement_digest)")
            else:
                result.add("quote_extra_data", "skip",
                           "cannot recompute extraData without a nonce")
        else:
            expected_extra = quote_extra_data(nonce, statement_digest)
            if quote.extra_data == expected_extra:
                result.add("quote_extra_data", "pass",
                           "extraData = H(wiz-quote-v1||nonce||statement_digest)")
            elif quote.extra_data == manifest_digest:
                result.add("quote_extra_data", "fail",
                           "extraData is the deprecated sha256(manifest); the quote "
                           "does not bind the statement or the nonce")
            else:
                result.add("quote_extra_data", "fail",
                           f"extraData is {quote.extra_data}, expected "
                           f"{expected_extra}")

    # 7b. AMD SEV-SNP evidence (E2).  This is an independent verifier for the
    # raw report: a guest's own attestation.json is evidence, never a result.
    snp_report = getattr(args, "snp_report", None)
    snp_certs = getattr(args, "snp_certs", None)
    snp_policy = getattr(args, "snp_policy", None)
    snp_measurement = getattr(args, "snp_measurement", None)
    snp_product = getattr(args, "snp_product", None)
    snp_requested = bool(snp_report or snp_certs or snp_policy or snp_measurement
                         or snp_product or getattr(args, "require_snp", False))
    if snp_report:
        try:
            snp_result = wiz_snp.verify_report(
                report_path=Path(snp_report),
                certs_path=Path(snp_certs) if snp_certs else None,
                policy_path=Path(snp_policy) if snp_policy else None,
                statement_digest=statement_digest,
                nonce=nonce,
                measurement_pin=snp_measurement,
                product_pin=snp_product,
                ark_paths=getattr(args, "ark", None) or [],
                openssl=getattr(args, "openssl", None),
                now=getattr(args, "now", None),
            )
        except (wiz_snp.SnpError, OSError) as exc:
            result.add("snp_report", "fail", str(exc))
        else:
            for check in snp_result.checks:
                result.add(check.name, check.status, check.detail)
            result.snp = snp_result.info
    elif snp_requested:
        if getattr(args, "allow_machine_only", False):
            result.add("snp_report", "skip",
                       "--allow-machine-only: E1-only result; no E2 evidence")
        else:
            result.add("snp_report", "fail",
                       "E2 evidence is required (--snp-policy/--snp-measurement/"
                       "--require-snp) but --snp-report is missing; pass "
                       "--allow-machine-only for an explicit E1-only result")
    elif getattr(args, "allow_machine_only", False):
        result.add("snp_report", "skip", "--allow-machine-only: E1-only result")

    # 8. Signature and PCR digest: tpm2_checkquote, never reimplemented here.
    if args.skip_crypto:
        result.add("tpm_quote_signature", "skip", "--skip-crypto")
        result.add("pcr_digest", "skip", "--skip-crypto")
    else:
        checkquote = find_checkquote(args.tpm2_checkquote, args.tpm2_bin)
        if not checkquote:
            result.add("tpm_quote_signature", "skip",
                       "tpm2_checkquote not found (install tpm2-tools or pass "
                       "--tpm2-checkquote; --skip-crypto allows manifest-only checks)")
            result.add("pcr_digest", "skip", "tpm2_checkquote not found")
        elif quote is None or not pcr_values:
            result.add("tpm_quote_signature", "fail",
                       "cannot check the signature without quote.msg and quote.pcr")
            result.add("pcr_digest", "fail", "cannot check the PCR digest")
        else:
            pcr_list = f"sha256:{','.join(map(str, quote.pcr_indices))}"
            cmd = [
                checkquote,
                "-u", str(ak_path),
                "-m", str(quote_path),
                "-s", str(sig_path),
                "-f", str(pcr_path),
                "-F", "values",
                "-l", pcr_list,
                "-g", "sha256",
                "-q", quote.extra_data,
            ]
            try:
                proc = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            except (OSError, subprocess.TimeoutExpired) as exc:
                result.add("tpm_quote_signature", "skip",
                           f"tpm2_checkquote could not run: {exc}")
                result.add("pcr_digest", "skip", "tpm2_checkquote could not run")
            else:
                if proc.returncode == 0:
                    result.add("tpm_quote_signature", "pass",
                               "AK signature verifies under ak.pub")
                    result.add("pcr_digest", "pass",
                               f"recomputed digest of {len(quote.pcr_indices)} PCR(s) "
                               "matches TPMS_ATTEST")
                else:
                    detail = _tail(proc.stderr or proc.stdout)
                    result.add("tpm_quote_signature", "fail",
                               f"tpm2_checkquote exited {proc.returncode}: {detail}")
                    result.add("pcr_digest", "fail",
                               "not established because tpm2_checkquote failed")

    return result


def result_json(result: VerifyResult) -> dict[str, Any]:
    status = result.status()
    payload: dict[str, Any] = {
        "schema": RESULT_SCHEMA,
        "ok": not result.failed(),
        "verified": status == "verified",
        "status": status,
        "exit_code": result.exit_code(),
        "manifest_sha256": result.manifest_sha256,
        "statement_sha256": result.statement_sha256,
        "signed": result.signed,
        "signature_keyid": result.keyid,
        "checks": [
            {"name": c.name, "status": c.status, "detail": c.detail}
            for c in result.checks
        ],
        "errors": result.errors,
        "warnings": result.warnings,
        "snp": result.snp,
    }
    if result.quote is not None:
        payload["quote"] = {
            "extra_data": result.quote.extra_data,
            "qualified_signer": result.quote.qualified_signer,
            "pcr_bank": result.quote.pcr_bank,
            "pcr_indices": result.quote.pcr_indices,
            "pcr_digest": result.quote.pcr_digest,
            "firmware_version": result.quote.firmware_version,
        }
    return payload


def print_result(result: VerifyResult, as_json: bool) -> None:
    if as_json:
        json.dump(result_json(result), sys.stdout, sort_keys=True, indent=2)
        sys.stdout.write("\n")
        return
    for check in result.checks:
        mark = {"pass": "ok  ", "fail": "FAIL", "skip": "skip"}[check.status]
        detail = f" - {check.detail}" if check.detail else ""
        print(f"{mark} {check.name}{detail}")
    print(f"status: {result.status()}")
    for warning in result.warnings:
        print(f"warning: {warning}", file=sys.stderr)


# --------------------------------------------------------------------------
# Producer


def _run(cmd: Sequence[str], *, what: str, env: dict[str, str] | None = None,
         cwd: str | None = None, timeout: int = 900) -> subprocess.CompletedProcess[str]:
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, env=env,
                              cwd=cwd, timeout=timeout)
    except FileNotFoundError:
        raise IncompleteError(f"{what}: command not found: {cmd[0]}") from None
    except subprocess.TimeoutExpired:
        raise AttestError(f"{what}: timed out after {timeout}s") from None
    if proc.returncode != 0:
        detail = _tail((proc.stderr or "") + "\n" + (proc.stdout or ""))
        raise AttestError(f"{what} failed (exit {proc.returncode}): {detail}")
    return proc


def _parse_pcr_list(text: str) -> list[int]:
    """Parse `sha256:0,1,4,7` (only one sha256 bank in v1)."""
    if ":" not in text:
        raise UsageError("--pcr-list must look like sha256:0,1,4,7")
    bank, rest = text.split(":", 1)
    if bank != BANK:
        raise UsageError(f"--pcr-list bank must be {BANK!r}")
    indices: list[int] = []
    for part in rest.split(","):
        part = part.strip()
        if not part:
            continue
        if not part.isdigit():
            raise UsageError(f"--pcr-list index is not a number: {part!r}")
        index = int(part)
        if not 0 <= index <= MAX_PCR:
            raise UsageError(f"--pcr-list index {index} is outside 0..{MAX_PCR}")
        indices.append(index)
    if not indices:
        raise UsageError("--pcr-list selects no PCRs")
    if indices != sorted(set(indices)):
        raise UsageError("--pcr-list indices must be sorted and unique")
    return indices


def _resolve_executable(value: str, what: str) -> Path:
    path = Path(value)
    if path.is_file():
        return path
    found = shutil.which(value)
    if found:
        return Path(found)
    raise UsageError(f"{what} not found: {value}")


def _tpm_cmd(tools: dict[str, str], name: str, sudo: bool) -> list[str]:
    prefix = ["sudo", "-n"] if sudo else []
    return prefix + [tools[name]]


def _quote(out: Path, indices: Sequence[int], *,
           extra_data: bytes, tpm2_bin: str | None, sudo: bool) -> None:
    names = ["tpm2_createprimary", "tpm2_create", "tpm2_load", "tpm2_quote",
             "tpm2_checkquote", "tpm2_flushcontext"]
    tools: dict[str, str] = {}
    for name in names:
        found = None
        if tpm2_bin:
            candidate = Path(tpm2_bin) / name
            if candidate.is_file():
                found = str(candidate)
        found = found or shutil.which(name)
        if not found:
            raise IncompleteError(
                f"{name} not found; install tpm2-tools or pass --tpm2-bin"
            )
        tools[name] = found

    if len(extra_data) != DIGEST_SIZE:
        raise UsageError("quote extraData must be a 32-byte SHA-256 digest")
    digest = extra_data.hex()
    pcr_list = f"sha256:{','.join(map(str, indices))}"
    use_sudo = sudo and hasattr(os, "geteuid") and os.geteuid() != 0
    with tempfile.TemporaryDirectory(prefix=".tpm-", dir=out) as tmp:
        tmpdir = Path(tmp)
        primary = tmpdir / "primary.ctx"
        ak_pub = tmpdir / "ak.pub"
        ak_priv = tmpdir / "ak.priv"
        ak_ctx = tmpdir / "ak.ctx"
        msg = tmpdir / "quote.msg"
        sig = tmpdir / "quote.sig"
        pcr = tmpdir / "quote.pcr"
        run = lambda name, *args, what: _run(  # noqa: E731
            _tpm_cmd(tools, name, use_sudo) + list(args), what=what, timeout=300
        )
        try:
            run("tpm2_createprimary", "-C", "o", "-g", "sha256", "-G", "rsa",
                "-c", str(primary), what="tpm2_createprimary")
            run("tpm2_create", "-C", str(primary),
                "-G", "rsa2048:rsassa-sha256:null",
                "-u", str(ak_pub), "-r", str(ak_priv),
                "-a", "restricted|sign|fixedtpm|fixedparent|sensitivedataorigin|"
                      "userwithauth|adminwithpolicy|noda",
                what="tpm2_create (AK)")
            run("tpm2_load", "-C", str(primary), "-u", str(ak_pub),
                "-r", str(ak_priv), "-c", str(ak_ctx), what="tpm2_load (AK)")
            run("tpm2_quote", "-c", str(ak_ctx), "-l", pcr_list,
                "-q", digest, "-m", str(msg), "-s", str(sig),
                "-o", str(pcr), "-g", "sha256", "-F", "values",
                what="tpm2_quote")
            run("tpm2_checkquote", "-u", str(ak_pub), "-m", str(msg),
                "-s", str(sig), "-f", str(pcr), "-F", "values",
                "-l", pcr_list, "-g", "sha256", "-q", digest,
                what="tpm2_checkquote")
            for name, source in (("ak.pub", ak_pub),
                                 ("quote.msg", msg),
                                 ("quote.sig", sig),
                                 ("quote.pcr", pcr)):
                os.replace(source, out / name)
            if use_sudo:
                # The TPM commands ran as root and leave 0600 files; make the
                # public quote artifacts readable by the invoking user.
                chmod = shutil.which("chmod") or "chmod"
                for name in ("ak.pub", "quote.msg", "quote.sig", "quote.pcr"):
                    subprocess.run(["sudo", "-n", chmod, "0644", str(out / name)],
                                   capture_output=True, timeout=30)
        finally:
            for ctx in (ak_ctx, primary):
                if ctx.exists():
                    try:
                        subprocess.run(_tpm_cmd(tools, "tpm2_flushcontext", use_sudo)
                                       + [str(ctx)], capture_output=True, timeout=30)
                    except (OSError, subprocess.TimeoutExpired):
                        pass


def attest(args: argparse.Namespace) -> dict[str, Any]:
    """The convenience producer: obtain the statement, sign it, quote it."""
    if args.source and args.statement:
        raise UsageError("give either SOURCE or --statement, not both")
    if not args.source and not args.statement:
        raise UsageError("give a SOURCE to build, or --statement FILE from "
                         "`wiz build --attest`")
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    if args.source:
        source = Path(args.source)
        if not source.is_file():
            raise UsageError(f"source file does not exist: {source}")
        wiz = _resolve_executable(args.wiz or "wiz", "wiz executable")
        name = args.output_name or source.stem
        target_path = out / name
        statement_path = out / (name + ".attest.json")
        _run([str(wiz), *args.wiz_flag, "build", str(source),
              "-o", str(target_path), "--attest", str(statement_path)],
             what="wiz build --attest")
    else:
        statement_path = Path(args.statement)
        if not statement_path.is_file():
            raise UsageError(f"statement does not exist: {statement_path}")

    statement, payload, envelope = load_statement(statement_path)
    manifest = validate_statement(statement)
    statement_digest = sha256_bytes(payload)

    summary: dict[str, Any] = {
        "schema": "wiz-attest-result/v1",
        "statement": str(statement_path),
        "statement_sha256": statement_digest,
        "artifacts": [a["path"] for a in manifest["artifacts"]],
        "quoted": False,
        "signed": False,
    }

    signed_info: dict[str, Any] | None = None
    if envelope is not None and envelope.get("signatures"):
        # Already signed (e.g. `wiz-attest sign` ran first): do not re-sign the
        # same payload, just bind it to the quote.
        signatures = envelope["signatures"]
        summary.update({
            "signed": True,
            "envelope": str(statement_path),
            "keyid": signatures[0].get("keyid") if signatures else None,
        })
        signed_info = {"statement_sha256": statement_digest}
    else:
        if not args.sign_key:
            raise UsageError(
                "a TPM quote must bind a signed statement; pass --sign-key "
                "(generate one with `wiz-attest keygen --key <path>`)"
            )
        envelope_path = (Path(args.envelope) if args.envelope
                         else out / "attestation.json")
        signed_info = sign_statement(
            statement_path, Path(args.sign_key),
            out=envelope_path,
            detached=(Path(args.detached_signature)
                      if args.detached_signature else None),
            prev=args.prev,
            valid_until=args.valid_until,
            sigstore=args.sigstore,
            sigstore_upload=args.sigstore_upload,
            cosign_bin=args.cosign_bin,
            ssh_keygen=args.ssh_keygen,
        )
        summary.update({
            "signed": True,
            "envelope": signed_info["envelope"],
            "detached_signature": signed_info["detached_signature"],
            "statement_sha256": signed_info["statement_sha256"],
            "keyid": signed_info["keyid"],
        })
        if signed_info.get("sigstore"):
            summary["sigstore"] = signed_info["sigstore"]

    nonce_hex = getattr(args, "nonce", None) or getattr(args, "challenge", None)
    nonce_file = (getattr(args, "nonce_file", None)
                  or getattr(args, "challenge_file", None))
    if nonce_file:
        nonce_hex = _read_bytes(Path(nonce_file), "nonce file").hex()
    nonce: bytes | None = None
    if nonce_hex is not None:
        nonce_hex = normalize_hex(nonce_hex, "--nonce")
        if not 16 <= len(nonce_hex) // 2 <= 64:
            raise UsageError("--nonce must be 16..64 bytes of hex")
        nonce = bytes.fromhex(nonce_hex)

    summary["pcr_indices"] = list(args.pcr_list)
    if args.no_quote:
        return summary
    if signed_info is None:
        raise UsageError("a TPM quote must bind a signed statement; pass --sign-key")
    if nonce is None:
        nonce = secrets.token_bytes(32)
        summary["nonce_generated"] = True
    (out / "quote.nonce").write_text(nonce.hex() + "\n", encoding="utf-8")
    summary["nonce"] = nonce.hex()
    extra_data = bytes.fromhex(
        quote_extra_data(nonce, signed_info["statement_sha256"]))
    _quote(out, args.pcr_list, extra_data=extra_data,
           tpm2_bin=args.tpm2_bin, sudo=args.sudo)
    summary["quoted"] = True
    summary["quote_files"] = ["quote.msg", "quote.sig", "quote.pcr", "ak.pub",
                              "quote.nonce"]
    try:
        info = ak_info(out / "ak.pub")
    except AttestError:
        pass
    else:
        summary["ak"] = {
            "name": info.name,
            "spki_sha256": info.spki_sha256,
            "file_sha256": info.file_sha256,
        }
    return summary


def quote(args: argparse.Namespace) -> dict[str, Any]:
    """E1: bind a signed statement to a TPM 2.0 quote over selected PCRs."""
    statement_path = Path(args.attest)
    if not statement_path.is_file():
        raise UsageError(f"statement does not exist: {statement_path}")
    out = Path(args.out) if args.out else statement_path.parent
    out.mkdir(parents=True, exist_ok=True)
    statement, payload, envelope = load_statement(statement_path)
    validate_statement(statement)
    if envelope is None or not envelope.get("signatures"):
        if not args.allow_unsigned:
            raise UsageError(
                "quote binds a signed statement; sign it with wiz-attest sign or "
                "pass --allow-unsigned for a local unsigned quote"
            )
    nonce: bytes | None = None
    nonce_hex = args.nonce
    if args.nonce_file:
        nonce_hex = _read_bytes(Path(args.nonce_file), "nonce file").hex()
    if nonce_hex is not None:
        nonce_hex = normalize_hex(nonce_hex, "--nonce")
        if not 16 <= len(nonce_hex) // 2 <= 64:
            raise UsageError("--nonce must be 16..64 bytes of hex")
        nonce = bytes.fromhex(nonce_hex)
    generated = False
    if nonce is None:
        nonce = secrets.token_bytes(32)
        generated = True
    statement_digest = sha256_bytes(payload)
    (out / "quote.nonce").write_text(nonce.hex() + "\n", encoding="utf-8")
    extra_data = bytes.fromhex(quote_extra_data(nonce, statement_digest))
    _quote(out, args.pcr_list, extra_data=extra_data,
           tpm2_bin=args.tpm2_bin, sudo=args.sudo)
    summary: dict[str, Any] = {
        "schema": "wiz-attest-quote-result/v1",
        "statement": str(statement_path),
        "statement_sha256": statement_digest,
        "nonce": nonce.hex(),
        "nonce_generated": generated,
        "pcr_indices": list(args.pcr_list),
        "quote_files": ["quote.msg", "quote.sig", "quote.pcr", "ak.pub",
                        "quote.nonce"],
        "quoted": True,
    }
    try:
        info = ak_info(out / "ak.pub")
    except AttestError:
        pass
    else:
        summary["ak"] = {
            "name": info.name,
            "spki_sha256": info.spki_sha256,
            "file_sha256": info.file_sha256,
        }
    return summary


# --------------------------------------------------------------------------
# CLIs


def _keygen_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wiz-attest keygen",
        description="Generate an offline Ed25519 signing key (OpenSSH format).",
    )
    p.add_argument("--key", required=True, help="private key path (created)")
    p.add_argument("--comment", default="wiz-attest offline signing key")
    p.add_argument("--force", action="store_true", help="replace an existing key")
    p.add_argument("--ssh-keygen", help="ssh-keygen executable")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    return p


def main_keygen(argv: Sequence[str]) -> int:
    parser = _keygen_parser()
    try:
        args = parser.parse_args(list(argv))
    except SystemExit as exc:
        return int(exc.code)
    try:
        info = generate_key(Path(args.key), comment=args.comment,
                            force=args.force, ssh_keygen=args.ssh_keygen)
    except AttestError as exc:
        print(f"wiz-attest keygen: {exc}", file=sys.stderr)
        return exc.exit_code
    if args.json:
        json.dump(info, sys.stdout, sort_keys=True, indent=2)
        sys.stdout.write("\n")
    else:
        print(f"key: {info['key']}")
        print(f"public key: {info['public_key']}")
        print(f"fingerprint: {info['fingerprint']}")
    return EXIT_OK


def _sign_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wiz-attest sign",
        description="Sign the statement from `wiz build --attest` as a DSSE "
                    "envelope with an offline Ed25519 key.",
    )
    p.add_argument("--attest", required=True,
                   help="statement or DSSE envelope from wiz build --attest")
    p.add_argument("--key", required=True, help="Ed25519 private key")
    p.add_argument("--out", help="DSSE envelope path")
    p.add_argument("--detached-signature", help="detached SSHSIG path")
    p.add_argument("--prev", help="previous statement digest (64 hex) for chaining")
    p.add_argument("--valid-until", help="RFC 3339 UTC expiry for the statement")
    p.add_argument("--sigstore", action="store_true",
                   help="also write a local cosign bundle (no upload)")
    p.add_argument("--sigstore-upload", action="store_true",
                   help="also upload the cosign bundle to Rekor (needs network)")
    p.add_argument("--cosign-bin", help="cosign executable for --sigstore")
    p.add_argument("--ssh-keygen", help="ssh-keygen executable")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    return p


def main_sign(argv: Sequence[str]) -> int:
    parser = _sign_parser()
    try:
        args = parser.parse_args(list(argv))
    except SystemExit as exc:
        return int(exc.code)
    try:
        info = sign_statement(
            Path(args.attest), Path(args.key),
            out=Path(args.out) if args.out else None,
            detached=(Path(args.detached_signature)
                      if args.detached_signature else None),
            prev=args.prev,
            valid_until=args.valid_until,
            sigstore=args.sigstore,
            sigstore_upload=args.sigstore_upload,
            cosign_bin=args.cosign_bin,
            ssh_keygen=args.ssh_keygen,
        )
    except AttestError as exc:
        print(f"wiz-attest sign: {exc}", file=sys.stderr)
        return exc.exit_code
    except OSError as exc:
        print(f"wiz-attest sign: {exc}", file=sys.stderr)
        return EXIT_FAIL
    if args.json:
        json.dump(info, sys.stdout, sort_keys=True, indent=2)
        sys.stdout.write("\n")
    else:
        print(f"envelope: {info['envelope']}")
        print(f"detached signature: {info['detached_signature']}")
        print(f"statement sha256: {info['statement_sha256']}")
        print(f"keyid: {info['keyid']}")
        if info.get("sigstore"):
            print(f"sigstore bundle: {info['sigstore']['bundle']}"
                  f" (uploaded: {info['sigstore']['uploaded']})")
    return EXIT_OK


def _ak_info_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wiz-attest ak-info",
        description="Print an AK's TPM Name and DER SPKI digest for a policy pin.",
    )
    p.add_argument("--ak", default="ak.pub", help="TPM2B_PUBLIC ak.pub file")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    return p


def main_ak_info(argv: Sequence[str]) -> int:
    parser = _ak_info_parser()
    try:
        args = parser.parse_args(list(argv))
    except SystemExit as exc:
        return int(exc.code)
    try:
        info = ak_info(Path(args.ak))
    except AttestError as exc:
        print(f"wiz-attest ak-info: {exc}", file=sys.stderr)
        return exc.exit_code
    payload = {
        "ak": args.ak,
        "key_type": info.key_type,
        "name": info.name,
        "spki_sha256": info.spki_sha256,
        "file_sha256": info.file_sha256,
    }
    if args.json:
        json.dump(payload, sys.stdout, sort_keys=True, indent=2)
        sys.stdout.write("\n")
    else:
        for key, value in payload.items():
            print(f"{key}: {value}")
    return EXIT_OK


def _attest_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wiz-attest",
        description="Build with `wiz build --attest` (or take --statement), sign "
                    "that statement with an offline Ed25519 key, and bind its "
                    "digest to a TPM 2.0 quote over selected PCRs.",
    )
    p.add_argument("source", nargs="?", help="Wiz source file to build")
    p.add_argument("--statement",
                   help="an existing statement/envelope from `wiz build --attest` "
                        "(instead of building a SOURCE)")
    p.add_argument("--out", default=".", help="output directory (default: .)")
    p.add_argument("--output-name", help="executable name for a built SOURCE")
    p.add_argument("--nonce", help="verifier-supplied hex nonce (16..64 bytes)")
    p.add_argument("--nonce-file", help="read the nonce bytes from a file")
    p.add_argument("--challenge", help=argparse.SUPPRESS)  # deprecated alias
    p.add_argument("--challenge-file", help=argparse.SUPPRESS)
    p.add_argument("--sign-key", help="offline Ed25519 private key used to sign "
                                      "the statement")
    p.add_argument("--envelope", help="signed DSSE envelope path (default: "
                                      "OUT/attestation.json)")
    p.add_argument("--detached-signature",
                   help="detached SSHSIG path (default: <envelope>.sig)")
    p.add_argument("--prev", help="previous statement digest (64 hex) for chaining")
    p.add_argument("--valid-until", help="RFC 3339 UTC expiry for the statement")
    p.add_argument("--sigstore", action="store_true",
                   help="also write a local cosign bundle (no upload)")
    p.add_argument("--sigstore-upload", action="store_true",
                   help="also upload the cosign bundle to Rekor (needs network)")
    p.add_argument("--cosign-bin", help="cosign executable for --sigstore")
    p.add_argument("--ssh-keygen", help="ssh-keygen executable")
    p.add_argument("--pcr-list", default="sha256:0,1,4,7,11,12,14",
                   help="PCRs to quote (default: sha256:0,1,4,7,11,12,14)")
    p.add_argument("--wiz", help="wiz executable (default: wiz on PATH)")
    p.add_argument("--wiz-flag", action="append", default=[],
                   help="extra flag passed to wiz before `build` (repeatable)")
    p.add_argument("--no-quote", action="store_true",
                   help="sign only (no TPM needed): the E1 quote is a separate step")
    p.add_argument("--tpm2-bin", help="directory containing tpm2-tools")
    p.add_argument("--sudo", action="store_true",
                   help="run tpm2 commands through `sudo -n` (device nodes are often root-only)")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    return p


def _quote_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wiz-attest quote",
        description="Bind a signed build statement to a TPM 2.0 quote "
                    "(E1): extraData = H(\"wiz-quote-v1\" || nonce || statement_digest).",
    )
    p.add_argument("--attest", required=True,
                   help="signed DSSE envelope (or statement with --allow-unsigned)")
    p.add_argument("--out", help="where to write quote.* and ak.pub (default: "
                                 "next to --attest)")
    p.add_argument("--pcr-list", default="sha256:0,1,4,7,11,12,14",
                   help="PCRs to quote (default: sha256:0,1,4,7,11,12,14)")
    p.add_argument("--nonce", help="verifier-supplied hex nonce (16..64 bytes)")
    p.add_argument("--nonce-file", help="read the nonce bytes from a file")
    p.add_argument("--allow-unsigned", action="store_true",
                   help="quote an unsigned statement (local check only)")
    p.add_argument("--tpm2-bin", help="directory containing tpm2-tools")
    p.add_argument("--sudo", action="store_true",
                   help="run tpm2 commands through `sudo -n`")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    return p


def main_attest(argv: Sequence[str]) -> int:
    if argv and argv[0] == "keygen":
        return main_keygen(argv[1:])
    if argv and argv[0] == "sign":
        return main_sign(argv[1:])
    if argv and argv[0] == "quote":
        return main_quote(argv[1:])
    if argv and argv[0] == "ak-info":
        return main_ak_info(argv[1:])
    parser = _attest_parser()
    try:
        args = parser.parse_args(list(argv))
        args.pcr_list = _parse_pcr_list(args.pcr_list)
    except UsageError as exc:
        parser.error(str(exc))
    try:
        summary = attest(args)
    except AttestError as exc:
        print(f"wiz-attest: {exc}", file=sys.stderr)
        return exc.exit_code
    except OSError as exc:
        print(f"wiz-attest: {exc}", file=sys.stderr)
        return EXIT_FAIL
    if args.json:
        json.dump(summary, sys.stdout, sort_keys=True, indent=2)
        sys.stdout.write("\n")
    else:
        print(f"statement: {summary['statement']}")
        print(f"statement sha256: {summary['statement_sha256']}")
        print(f"artifacts: {', '.join(summary['artifacts'])}")
        if summary.get("signed"):
            print(f"envelope: {summary['envelope']}")
            if summary.get("detached_signature"):
                print(f"detached signature: {summary['detached_signature']}")
            print(f"keyid: {summary['keyid']}")
        else:
            print("statement: unsigned")
        if summary.get("quoted"):
            print(f"PCRs: sha256:{','.join(map(str, summary['pcr_indices']))}")
            print("quote: quote.msg, quote.sig, quote.pcr, ak.pub, quote.nonce")
            if summary.get("ak"):
                print(f"AK name: {summary['ak']['name']}")
                print(f"AK SPKI sha256: {summary['ak']['spki_sha256']}")
        else:
            print("quote: not requested (--no-quote)")
    return EXIT_OK


def main_quote(argv: Sequence[str]) -> int:
    parser = _quote_parser()
    try:
        args = parser.parse_args(list(argv))
        args.pcr_list = _parse_pcr_list(args.pcr_list)
    except UsageError as exc:
        parser.error(str(exc))
    try:
        info = quote(args)
    except AttestError as exc:
        print(f"wiz-attest quote: {exc}", file=sys.stderr)
        return exc.exit_code
    except OSError as exc:
        print(f"wiz-attest quote: {exc}", file=sys.stderr)
        return EXIT_FAIL
    if args.json:
        json.dump(info, sys.stdout, sort_keys=True, indent=2)
        sys.stdout.write("\n")
    else:
        print(f"statement: {info['statement']}")
        print(f"statement sha256: {info['statement_sha256']}")
        print(f"nonce: {info['nonce']}"
              f"{' (generated)' if info['nonce_generated'] else ''}")
        print(f"PCRs: sha256:{','.join(map(str, info['pcr_indices']))}")
        print("quote: quote.msg, quote.sig, quote.pcr, ak.pub, quote.nonce")
        if info.get("ak"):
            print(f"AK name: {info['ak']['name']}")
            print(f"AK SPKI sha256: {info['ak']['spki_sha256']}")
    return EXIT_OK


def _verify_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wiz-verify",
        description="Verify a DSSE-signed build statement (whose predicate is the "
                    "wiz build manifest), a TPM 2.0 quote, an expected PCR policy and "
                    "the artifact bytes.  With --snp-* it also verifies AMD SEV-SNP "
                    "evidence (E2).",
    )
    p.add_argument("--attest", required=True,
                   help="signed DSSE envelope (or unsigned statement with "
                        "--allow-unsigned) from `wiz build --attest` / wiz-attest")
    p.add_argument("--detached-signature", help="detached SSHSIG over the DSSE PAE")
    p.add_argument("--public-key", action="append", default=[],
                   help="trusted Ed25519 public key (repeatable)")
    p.add_argument("--allowed-signers", action="append", default=[],
                   help="OpenSSH allowed_signers file (repeatable)")
    p.add_argument("--key-fingerprint", action="append", default=[],
                   help="allowlisted SHA256 fingerprint (repeatable)")
    p.add_argument("--require-signature", action="store_true",
                   help="fail unless a signed DSSE envelope verifies")
    p.add_argument("--allow-unsigned", action="store_true",
                   help="explicitly accept an unsigned manifest (never with "
                        "--require-signature)")
    p.add_argument("--ssh-keygen", help="ssh-keygen executable")
    p.add_argument("--quote", help="quote.msg (default: next to the manifest)")
    p.add_argument("--signature", help="quote.sig (default: next to the manifest)")
    p.add_argument("--pcr", help="quote.pcr (default: next to the manifest)")
    p.add_argument("--ak", help="ak.pub (default: next to the manifest)")
    p.add_argument("--policy", required=True,
                   help="expected PCR policy JSON (PCR index -> sha256 value)")
    p.add_argument("--artifacts-dir", help="where artifact paths are resolved "
                                           "(default: the statement's directory)")
    p.add_argument("--nonce", help="verifier-supplied hex nonce (16..64 bytes)")
    p.add_argument("--nonce-file", help="read the verifier nonce from a file")
    p.add_argument("--challenge", help=argparse.SUPPRESS)  # deprecated alias
    p.add_argument("--require-nonce", action="store_true",
                   help="fail unless the verifier supplies the nonce")
    p.add_argument("--require-challenge", action="store_true", help=argparse.SUPPRESS)
    p.add_argument("--expect-digest", help="pin the expected manifest SHA-256")
    p.add_argument("--expect-statement-digest", help="pin the expected statement SHA-256")
    p.add_argument("--expect-prev", help="pin the previous statement digest")
    p.add_argument("--ak-spki-sha256", help="pin the AK DER SPKI SHA-256")
    p.add_argument("--ak-name", help="pin the AK TPM Name (000b + 64 hex)")
    p.add_argument("--ak-sha256", help="legacy pin: SHA-256 of the ak.pub file bytes")
    p.add_argument("--now", help=argparse.SUPPRESS)  # test clock for expiry
    p.add_argument("--snp-report",
                   help="raw AMD SEV-SNP ATTESTATION_REPORT (1184 bytes); an ABI "
                        "certificate table may be appended")
    p.add_argument("--snp-certs",
                   help="SEV-SNP certificate evidence: a directory of PEM files, a "
                        "PEM bundle, or an ABI certificate table (default: the table "
                        "appended to --snp-report)")
    p.add_argument("--snp-policy",
                   help="wiz-snp-policy/v1 JSON: measurement, TCB floor, policy bits")
    p.add_argument("--snp-measurement",
                   help="pin the 48-byte SNP launch measurement (96 hex)")
    p.add_argument("--snp-product", choices=("Milan", "Genoa", "Turin"),
                   help="require this AMD SEV-SNP product family")
    p.add_argument("--ark", action="append", default=[],
                   help="override the embedded AMD KDS trust root with a PEM file "
                        "(repeatable; for tests or private deployments)")
    p.add_argument("--openssl", help="openssl executable (default: PATH or "
                                     "WIZ_ATTEST_OPENSSL)")
    p.add_argument("--require-snp", action="store_true",
                   help="fail unless SEV-SNP evidence is verified (E2)")
    p.add_argument("--allow-machine-only", action="store_true",
                   help="explicitly allow an E1-only result when E2 evidence is "
                        "absent; invalid evidence is never accepted")
    p.add_argument("--tpm2-checkquote", help="path to tpm2_checkquote")
    p.add_argument("--tpm2-bin", help="directory containing tpm2-tools")
    p.add_argument("--skip-crypto", action="store_true",
                   help="do the manifest/digest/policy checks only (partial result)")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    return p


def main_verify(argv: Sequence[str]) -> int:
    parser = _verify_parser()
    try:
        args = parser.parse_args(list(argv))
        if not Path(args.attest).is_file():
            raise UsageError(f"statement does not exist: {args.attest}")
        if not Path(args.policy).is_file():
            raise UsageError(f"policy file does not exist: {args.policy}")
        if args.require_signature and args.allow_unsigned:
            raise UsageError("--require-signature and --allow-unsigned conflict")
        if args.require_snp and args.allow_machine_only:
            raise UsageError("--require-snp and --allow-machine-only conflict")
        for option, label in (("snp_report", "SNP report"),
                              ("snp_policy", "SNP policy"),
                              ("snp_certs", "SNP certificate evidence")):
            value = getattr(args, option)
            if value and not Path(value).exists():
                raise UsageError(f"{label} does not exist: {value}")
        for value in args.ark:
            if not Path(value).is_file():
                raise UsageError(f"--ark is not a file: {value}")
        if args.nonce_file:
            try:
                args.nonce = Path(args.nonce_file).read_bytes().hex()
            except OSError as exc:
                raise UsageError(
                    f"cannot read --nonce-file {args.nonce_file}: {exc}") from None
        if not args.nonce and args.challenge:
            args.nonce = args.challenge
        if args.require_challenge:
            args.require_nonce = True
        for option in ("nonce", "expect_digest", "expect_statement_digest",
                       "expect_prev", "ak_sha256", "ak_spki_sha256"):
            value = getattr(args, option)
            if value:
                value = normalize_hex(value, "--" + option.replace("_", "-"))
                if option == "nonce":
                    if not 16 <= len(value) // 2 <= 64:
                        raise UsageError("--nonce must be 16..64 bytes")
                elif len(value) != 64:
                    raise UsageError(
                        f"--{option.replace('_', '-')} must be 64 hex characters")
                setattr(args, option, value)
        if args.ak_name:
            name = normalize_hex(args.ak_name, "--ak-name")
            if len(name) != 68 or not name.startswith("000b"):
                raise UsageError("--ak-name must be a sha256 TPM Name "
                                 "(000b + 64 hex characters)")
            args.ak_name = name
        if args.snp_measurement:
            measurement = normalize_hex(args.snp_measurement, "--snp-measurement")
            if len(measurement) != 96:
                raise UsageError("--snp-measurement must be 96 hex characters "
                                 "(48 bytes)")
            args.snp_measurement = measurement
        args.key_fingerprint = [normalize_fingerprint(value)
                                for value in args.key_fingerprint]
        if args.now:
            try:
                args.now = datetime.datetime.strptime(
                    args.now, "%Y-%m-%dT%H:%M:%SZ").replace(
                        tzinfo=datetime.timezone.utc)
            except ValueError as exc:
                raise UsageError(f"--now is not an RFC 3339 UTC timestamp: {exc}") from None
    except UsageError as exc:
        parser.error(str(exc))
    try:
        result = verify(args)
    except AttestError as exc:
        print(f"wiz-verify: {exc}", file=sys.stderr)
        return exc.exit_code
    except OSError as exc:
        print(f"wiz-verify: {exc}", file=sys.stderr)
        return EXIT_FAIL
    print_result(result, args.json)
    return result.exit_code()


def main(argv: Sequence[str]) -> int:
    """`python3 wiz_attest.py attest|verify ...` (for tests and development)."""
    if not argv or argv[0] in ("-h", "--help"):
        print("usage: wiz_attest.py {attest,verify,keygen,sign,quote,ak-info} [options]",
              file=sys.stderr)
        return EXIT_USAGE
    if argv[0] == "attest":
        return main_attest(argv[1:])
    if argv[0] == "verify":
        return main_verify(argv[1:])
    print(f"unknown command {argv[0]!r}", file=sys.stderr)
    return EXIT_USAGE


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
