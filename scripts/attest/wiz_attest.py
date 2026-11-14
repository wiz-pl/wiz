#!/usr/bin/env python3
"""Signed build statements, manifests and TPM 2.0 quotes for Wiz artifacts.

This module is deliberately standalone and uses only the Python 3 standard
library plus OpenSSH's `ssh-keygen` (already needed for SSH).  It defines:

* a canonical, challenge-free build-manifest format (`SCHEMA`);
* an in-toto Statement v1 wrapping that manifest, signed as a DSSE envelope
  with an offline Ed25519 key (`ssh-keygen -Y sign`); the DSSE PAE is the
  signed byte string, and detached `.sig` files are also written;
* `wiz-attest keygen|sign|ak-info` and the producer CLI, which emits
  `manifest.json`, `manifest.intoto.json`, `manifest.intoto.json.sig`,
  `quote.msg`, `quote.sig`, `quote.pcr`, `quote.nonce` and `ak.pub`;
* `wiz-verify`, which checks the DSSE payloadType, signature over PAE, key
  fingerprint allowlist, statement/artifact/manifest binding, the quote
  `extraData = H("wiz-quote-v1" || nonce || statement_digest)`, an expected PCR
  policy and, when `tpm2-tools` is installed, the quote signature and PCR
  digest via `tpm2_checkquote` (TPM cryptography is not reimplemented here).

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
import datetime
import hashlib
import json
import os
import platform
import re
import secrets
import shutil
import struct
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Sequence

SCHEMA = "wiz-build-manifest/v1"
POLICY_SCHEMA = "wiz-pcr-policy/v1"
RESULT_SCHEMA = "wiz-attestation-result/v1"

# DSSE / in-toto statement signing.  The signature is an OpenSSH SSHSIG made by
# `ssh-keygen -Y sign` with an offline Ed25519 key; the payload is the canonical
# in-toto statement, and the signature is over the DSSE PAE, not the payload
# alone.
DSSE_PAYLOAD_TYPE = "application/vnd.in-toto+json"
STATEMENT_TYPE = "https://in-toto.io/Statement/v1"
PREDICATE_TYPE = "https://wiz-lang.dev/attestation/build-manifest/v1"
DSSE_NAMESPACE = "wiz-attest-dsse"
DSSE_KEY_IDENTITY = "wiz-attest"
ENVELOPE_NAME = "manifest.intoto.json"
DETACHED_SUFFIX = ".sig"
SIGSTORE_BUNDLE_SUFFIX = ".cosign.bundle"
KEY_SCHEMA = "wiz-attest-key/v1"
SIGN_RESULT_SCHEMA = "wiz-attest-sign-result/v1"
BUILD_TYPE = "https://wiz-lang.dev/buildtypes/wiz-build/v1"
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
_VERSION_LINE = re.compile(r"^wiz\s+(\S+)(?:\s+\(([^)]+)\))?\s*$")


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


def canonical_digest(obj: Any) -> str:
    return sha256_bytes(canonical_bytes(obj))


# --------------------------------------------------------------------------
# Source tree digest


def _normalize_root(path: str) -> str:
    """Like `_normalize_relative`, but accept a leading `./` for a CLI path."""
    while path.startswith("./"):
        path = path[2:]
    return _normalize_relative(path, "tree root")


def tree_entries(roots: Iterable[str]) -> list[tuple[str, str]]:
    """(virtual path, sha256) for every regular file under the given roots.

    Roots are relative directory names ("lib", "runtime").  Files are keyed by
    `root/relative/path` with `/` separators, so the digest does not depend on
    the order the roots are passed in or on where the checkout lives.  Symlinks
    and other non-regular files are rejected: a manifest must not silently
    include bytes from outside the named tree.
    """
    entries: list[tuple[str, str]] = []
    seen: set[str] = set()
    for root in roots:
        normalized = _normalize_root(root)
        base = Path(normalized)
        if not base.is_dir():
            raise UsageError(f"tree root is not a directory: {root}")
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames.sort()
            for name in sorted(filenames):
                path = Path(dirpath) / name
                if not path.is_file() or path.is_symlink():
                    raise AttestError(f"not a regular file in the source tree: {path}")
                rel = path.relative_to(base).as_posix()
                virtual = f"{normalized.rstrip('/')}/{rel}" if normalized not in (".", "") else rel
                if virtual in seen:
                    raise UsageError(f"source tree contains {virtual} twice")
                seen.add(virtual)
                entries.append((virtual, sha256_file(path)))
    entries.sort(key=lambda item: item[0].encode("utf-8"))
    return entries


def tree_digest(roots: Iterable[str]) -> tuple[str, list[str], int]:
    """Return (digest, roots, file count) for a source tree.

    The digest is SHA-256 over the concatenation of `"<sha256>  <path>\\n"` for
    every file, sorted by path (the `sha256sum` shape).  It is a plain Merkle
    substitute, not a standard format; the manifest says which roots it covers.
    """
    roots = sorted({_normalize_root(r) for r in roots})
    entries = tree_entries(roots)
    text = "".join(f"{digest}  {path}\n" for path, digest in entries)
    return sha256_bytes(text.encode("utf-8")), roots, len(entries)


# --------------------------------------------------------------------------
# Manifest schema


_MANIFEST_KEYS = {
    "schema",
    "artifacts",
    "wiz",
    "source",
    "target",
    "pcr",
    "builder",
}


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise SchemaError(message)


def _normalize_relative(path: str, what: str) -> str:
    """Validate a manifest-relative path and return it with `/` separators."""
    _expect(isinstance(path, str) and path != "", f"{what} must be a non-empty string")
    _expect("\\" not in path, f"{what} must use '/' separators: {path!r}")
    _expect(not path.startswith("/"), f"{what} must be relative: {path!r}")
    parts = path.split("/")
    _expect(all(part not in ("", ".", "..") for part in parts),
            f"{what} must not contain empty, '.' or '..' components: {path!r}")
    return path


def validate_manifest(obj: Any) -> None:
    """Raise SchemaError unless `obj` is a valid `SCHEMA` manifest."""
    _expect(isinstance(obj, dict), "manifest must be a JSON object")
    keys = set(obj)
    unknown = keys - _MANIFEST_KEYS
    missing = {"schema", "artifacts", "wiz", "source", "target", "pcr", "builder"} - keys
    _expect(not unknown, f"unknown manifest fields: {', '.join(sorted(unknown))}")
    _expect(not missing, f"missing manifest fields: {', '.join(sorted(missing))}")
    _expect(obj["schema"] == SCHEMA, f"schema must be {SCHEMA!r}")

    artifacts = obj["artifacts"]
    _expect(isinstance(artifacts, list) and artifacts, "artifacts must be a non-empty array")
    paths: list[str] = []
    for i, art in enumerate(artifacts):
        _expect(isinstance(art, dict) and set(art) == {"path", "size", "sha256"},
                f"artifacts[{i}] must have exactly path, size, sha256")
        path = _normalize_relative(art["path"], f"artifacts[{i}].path")
        _expect(_is_int(art["size"]) and art["size"] >= 0,
                f"artifacts[{i}].size must be a non-negative integer")
        _expect(isinstance(art["sha256"], str) and _HEX64.match(art["sha256"]) is not None,
                f"artifacts[{i}].sha256 must be 64 lowercase hex characters")
        paths.append(path)
    _expect(paths == sorted(paths), "artifacts must be sorted by path")
    _expect(len(paths) == len(set(paths)), "artifact paths must be unique")

    wiz = obj["wiz"]
    _expect(isinstance(wiz, dict), "wiz must be an object")
    unknown = set(wiz) - {"version", "commit", "binary_sha256"}
    _expect(not unknown, f"unknown wiz fields: {', '.join(sorted(unknown))}")
    _expect(isinstance(wiz.get("version"), str) and 0 < len(wiz["version"]) <= 128,
            "wiz.version must be a non-empty string")
    if "commit" in wiz:
        _expect(re.fullmatch(r"[0-9a-f]{7,64}", wiz["commit"]) is not None,
                "wiz.commit must be 7-64 lowercase hex characters")
    if "binary_sha256" in wiz:
        _expect(isinstance(wiz["binary_sha256"], str)
                and _HEX64.match(wiz["binary_sha256"]) is not None,
                "wiz.binary_sha256 must be 64 lowercase hex characters")

    source = obj["source"]
    _expect(isinstance(source, dict), "source must be an object")
    _expect(set(source) == {"entry", "sha256", "tree_sha256", "tree_roots"},
            "source must have exactly entry, sha256, tree_sha256, tree_roots")
    _normalize_relative(source["entry"], "source.entry")
    _expect(isinstance(source["sha256"], str) and _HEX64.match(source["sha256"]) is not None,
            "source.sha256 must be 64 lowercase hex characters")
    _expect(isinstance(source["tree_sha256"], str)
            and _HEX64.match(source["tree_sha256"]) is not None,
            "source.tree_sha256 must be 64 lowercase hex characters")
    roots = source["tree_roots"]
    _expect(isinstance(roots, list), "source.tree_roots must be an array")
    normalized_roots = [_normalize_relative(r, "source.tree_roots[]") for r in roots]
    _expect(normalized_roots == sorted(normalized_roots), "source.tree_roots must be sorted")
    _expect(len(normalized_roots) == len(set(normalized_roots)),
            "source.tree_roots must be unique")

    target = obj["target"]
    _expect(isinstance(target, str) and 0 < len(target) <= 128
            and all(32 <= ord(c) < 127 for c in target),
            "target must be a non-empty printable string (a target triple)")

    pcr = obj["pcr"]
    _expect(isinstance(pcr, dict) and set(pcr) == {"bank", "indices"},
            "pcr must have exactly bank and indices")
    _expect(pcr["bank"] == BANK, f"pcr.bank must be {BANK!r}")
    indices = pcr["indices"]
    _expect(isinstance(indices, list) and indices, "pcr.indices must be a non-empty array")
    _expect(all(_is_int(i) and 0 <= i <= MAX_PCR for i in indices),
            f"pcr.indices must be integers 0..{MAX_PCR}")
    _expect(indices == sorted(indices), "pcr.indices must be sorted")
    _expect(len(indices) == len(set(indices)), "pcr.indices must be unique")

    builder = obj["builder"]
    _expect(builder == {"kind": "tpm2-quote"},
            "builder must be {\"kind\": \"tpm2-quote\"}")


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


def build_manifest(
    *,
    artifacts: Sequence[dict[str, Any]],
    wiz_version: str,
    wiz_commit: str | None,
    wiz_binary_sha256: str | None,
    source_entry: str,
    source_sha256: str,
    tree_sha256: str,
    tree_roots: Sequence[str],
    target: str,
    pcr_indices: Sequence[int],
) -> dict[str, Any]:
    """Assemble a manifest object (validated before it is returned)."""
    wiz: dict[str, Any] = {"version": wiz_version}
    if wiz_commit:
        wiz["commit"] = wiz_commit
    if wiz_binary_sha256:
        wiz["binary_sha256"] = wiz_binary_sha256
    manifest: dict[str, Any] = {
        "schema": SCHEMA,
        "artifacts": sorted(artifacts, key=lambda a: a["path"]),
        "wiz": wiz,
        "source": {
            "entry": source_entry,
            "sha256": source_sha256,
            "tree_sha256": tree_sha256,
            "tree_roots": sorted(tree_roots),
        },
        "target": target,
        "pcr": {"bank": BANK, "indices": sorted(pcr_indices)},
        "builder": {"kind": "tpm2-quote"},
    }
    validate_manifest(manifest)
    return manifest


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


def build_statement(manifest: dict[str, Any], manifest_digest: str, *,
                    prev: str | None = None,
                    valid_until: str | None = None) -> dict[str, Any]:
    """Wrap the manifest in an in-toto Statement v1 (the signed root)."""
    predicate: dict[str, Any] = {
        "schema": SCHEMA,
        "buildType": BUILD_TYPE,
        "externalParameters": {
            "entry": manifest["source"]["entry"],
            "target": manifest["target"],
        },
        "resolvedDependencies": [
            {"uri": "wiz:source",
             "digest": {"sha256": manifest["source"]["tree_sha256"]}},
        ],
        "byproducts": [],
        "manifest": manifest,
        "manifest_sha256": manifest_digest,
    }
    if manifest["wiz"].get("binary_sha256"):
        predicate["resolvedDependencies"].append({
            "uri": "wiz:binary",
            "digest": {"sha256": manifest["wiz"]["binary_sha256"]},
        })
    if prev is not None:
        predicate["prev"] = prev
    if valid_until is not None:
        predicate["valid_until"] = valid_until
    return {
        "_type": STATEMENT_TYPE,
        "subject": [
            {"name": art["path"], "digest": {"sha256": art["sha256"]}}
            for art in manifest["artifacts"]
        ],
        "predicateType": PREDICATE_TYPE,
        "predicate": predicate,
    }


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


def sign_manifest(manifest_path: Path, key_path: Path, *,
                  out: Path | None = None,
                  detached: Path | None = None,
                  prev: str | None = None,
                  valid_until: str | None = None,
                  sigstore: bool = False,
                  sigstore_upload: bool = False,
                  cosign_bin: str | None = None,
                  ssh_keygen: str | None = None) -> dict[str, Any]:
    raw = _read_bytes(manifest_path, "manifest")
    parsed = load_json_strict(raw)
    validate_manifest(parsed)
    if canonical_bytes(parsed) != raw:
        raise SchemaError(
            "manifest is not in canonical form; regenerate it with wiz-attest"
        )
    manifest_digest = sha256_bytes(raw)
    if prev is not None:
        prev = normalize_hex(prev, "--prev")
        if len(prev) != 64:
            raise UsageError("--prev must be 64 hex characters")
    if valid_until is not None:
        valid_until = _iso_utc(valid_until, "--valid-until")
    public = parse_public_key(key_path, ssh_keygen=ssh_keygen)
    statement = build_statement(parsed, manifest_digest, prev=prev,
                                valid_until=valid_until)
    payload = canonical_bytes(statement)
    payload_digest = statement_digest_of_payload(payload)
    signature = sign_pae(key_path, dsse_pae(DSSE_PAYLOAD_TYPE, payload),
                         ssh_keygen=ssh_keygen)
    envelope = {
        "payloadType": DSSE_PAYLOAD_TYPE,
        "payload": _b64(payload),
        "signatures": [{"keyid": public.fingerprint, "sig": _b64(signature)}],
    }
    envelope_path = Path(out) if out else manifest_path.parent / ENVELOPE_NAME
    detached_path = (Path(detached) if detached
                     else Path(str(envelope_path) + DETACHED_SUFFIX))
    _write_canonical(envelope_path, envelope)
    detached_path.parent.mkdir(parents=True, exist_ok=True)
    detached_path.write_bytes(signature)
    result: dict[str, Any] = {
        "schema": SIGN_RESULT_SCHEMA,
        "manifest": str(manifest_path),
        "manifest_sha256": manifest_digest,
        "statement_sha256": payload_digest,
        "envelope": str(envelope_path),
        "detached_signature": str(detached_path),
        "payload_type": DSSE_PAYLOAD_TYPE,
        "keyid": public.fingerprint,
        "signed": True,
        "sigstore": None,
    }
    if prev is not None:
        result["prev"] = prev
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


def verify_statement_payload(payload: bytes, manifest: dict[str, Any],
                             manifest_digest: str, result: "VerifyResult", *,
                             expect_prev: str | None = None,
                             now: datetime.datetime | None = None) -> None:
    try:
        statement = load_json_strict(payload)
    except SchemaError as exc:
        _statement_failure(result, f"signed payload is not JSON: {exc}")
        return
    if not isinstance(statement, dict):
        _statement_failure(result, "signed payload is not a JSON object")
        return
    expected_keys = {"_type", "subject", "predicateType", "predicate"}
    if set(statement) != expected_keys:
        _statement_failure(
            result,
            "statement fields must be exactly "
            f"{', '.join(sorted(expected_keys))}; got {', '.join(sorted(statement))}",
        )
        return
    failures: list[str] = []
    if statement["_type"] != STATEMENT_TYPE:
        failures.append(f"_type is {statement['_type']!r}, expected {STATEMENT_TYPE!r}")
    expected_subjects = [
        {"name": art["path"], "digest": {"sha256": art["sha256"]}}
        for art in manifest["artifacts"]
    ]
    if statement["subject"] != expected_subjects:
        failures.append("subject does not match the manifest artifacts")
    if statement["predicateType"] != PREDICATE_TYPE:
        failures.append(
            f"predicateType is {statement['predicateType']!r}, expected {PREDICATE_TYPE!r}"
        )
    predicate = statement["predicate"]
    if not isinstance(predicate, dict):
        failures.append("predicate is not an object")
    else:
        required = {"schema", "buildType", "externalParameters",
                    "resolvedDependencies", "byproducts", "manifest",
                    "manifest_sha256"}
        unknown = set(predicate) - required - {"prev", "valid_until"}
        missing = required - set(predicate)
        if unknown:
            failures.append(f"unknown predicate fields: {', '.join(sorted(unknown))}")
        if missing:
            failures.append(f"missing predicate fields: {', '.join(sorted(missing))}")
        if not missing and not unknown:
            if predicate["schema"] != SCHEMA:
                failures.append(f"predicate.schema is {predicate['schema']!r}")
            if predicate["buildType"] != BUILD_TYPE:
                failures.append(f"predicate.buildType is {predicate['buildType']!r}")
            if predicate["externalParameters"] != {
                "entry": manifest["source"]["entry"],
                "target": manifest["target"],
            }:
                failures.append("externalParameters do not match the manifest")
            expected_dependencies = [{
                "uri": "wiz:source",
                "digest": {"sha256": manifest["source"]["tree_sha256"]},
            }]
            if manifest["wiz"].get("binary_sha256"):
                expected_dependencies.append({
                    "uri": "wiz:binary",
                    "digest": {"sha256": manifest["wiz"]["binary_sha256"]},
                })
            if predicate["resolvedDependencies"] != expected_dependencies:
                failures.append("resolvedDependencies do not match the manifest")
            if predicate["byproducts"] != []:
                failures.append("byproducts must be empty in this version")
            try:
                validate_manifest(predicate["manifest"])
            except SchemaError as exc:
                failures.append(f"predicate.manifest is invalid: {exc}")
            else:
                embedded = canonical_bytes(predicate["manifest"])
                if embedded != canonical_bytes(manifest):
                    failures.append("predicate.manifest differs from manifest.json")
                if predicate["manifest_sha256"] != manifest_digest:
                    failures.append(
                        "predicate.manifest_sha256 does not match manifest.json"
                    )
                if sha256_bytes(embedded) != predicate["manifest_sha256"]:
                    failures.append(
                        "predicate.manifest_sha256 is not sha256(canonical manifest)"
                    )
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
                   "statement matches manifest, artifacts and build parameters")


def verify_signature(args: argparse.Namespace, result: "VerifyResult",
                     manifest: dict[str, Any], manifest_digest: str) -> None:
    """Verify the DSSE envelope, key allowlist and statement binding."""
    manifest_dir = Path(args.manifest).parent
    envelope_arg = getattr(args, "envelope", None)
    envelope_path = (Path(envelope_arg) if envelope_arg
                     else manifest_dir / ENVELOPE_NAME)
    explicit = envelope_arg is not None
    allow_unsigned = bool(getattr(args, "allow_unsigned", False))
    require_signature = bool(getattr(args, "require_signature", False))
    if not envelope_path.is_file():
        result.signed = False
        if explicit:
            result.add("dsse_envelope", "fail",
                       f"DSSE envelope does not exist: {envelope_path}")
        elif allow_unsigned:
            result.add("signature_policy", "pass",
                       "unsigned manifest accepted explicitly (--allow-unsigned)")
            result.warnings.append(
                "no DSSE signature was checked; --allow-unsigned is for local checks"
            )
        else:
            result.add("signature_policy", "fail",
                       "manifest is unsigned; run wiz-attest sign or pass "
                       "--allow-unsigned for an explicit unsigned check"
                       + (" (--require-signature)" if require_signature else ""))
        return

    try:
        envelope_raw = _read_bytes(envelope_path, "DSSE envelope")
        envelope = load_json_strict(envelope_raw)
    except AttestError as exc:
        result.add("dsse_envelope", "fail", str(exc))
        return
    if not isinstance(envelope, dict):
        result.add("dsse_envelope", "fail", "DSSE envelope must be a JSON object")
        return
    if set(envelope) != {"payloadType", "payload", "signatures"}:
        result.add("dsse_envelope", "fail",
                   "DSSE envelope fields must be exactly payloadType, payload, "
                   "signatures")
        return
    result.add("dsse_envelope", "pass", str(envelope_path))

    payload_type = envelope.get("payloadType")
    if payload_type == DSSE_PAYLOAD_TYPE:
        result.add("dsse_payload_type", "pass", payload_type)
    else:
        result.add("dsse_payload_type", "fail",
                   f"payloadType is {payload_type!r}, expected {DSSE_PAYLOAD_TYPE!r}")
    try:
        payload = _unb64(envelope.get("payload"), "payload")
    except SchemaError as exc:
        result.add("dsse_payload", "fail", str(exc))
        return
    result.add("dsse_payload", "pass", f"{len(payload)} bytes")
    result.statement_sha256 = sha256_bytes(payload)
    pae = dsse_pae(payload_type if isinstance(payload_type, str) else "",
                   payload)

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
        verify_statement_payload(payload, manifest, manifest_digest, result,
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

    verify_statement_payload(payload, manifest, manifest_digest, result,
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
    manifest_path = Path(args.manifest)
    manifest_dir = manifest_path.parent

    # 1. manifest bytes and schema.  Nothing below is trustworthy if this fails,
    # so schema failure stops the run.
    try:
        raw = _read_bytes(manifest_path, "manifest")
        parsed = load_json_strict(raw)
        validate_manifest(parsed)
        if canonical_bytes(parsed) != raw:
            raise SchemaError(
                "manifest is not in canonical form (sorted keys, no whitespace, "
                "no trailing newline); regenerate it with wiz-attest"
            )
    except AttestError as exc:
        result.add("manifest_schema", "fail", str(exc))
        return result

    manifest_digest = sha256_bytes(raw)
    result.manifest_sha256 = manifest_digest
    result.add("manifest_schema", "pass", f"{SCHEMA}, canonical, {len(raw)} bytes")
    result.add("manifest_digest", "pass", manifest_digest)

    if args.expect_digest:
        expected = normalize_hex(args.expect_digest, "--expect-digest")
        if expected == manifest_digest:
            result.add("manifest_pin", "pass", "manifest digest matches --expect-digest")
        else:
            result.add("manifest_pin", "fail",
                       f"manifest is {manifest_digest}, expected {expected}")

    # 2. Every artifact's size and digest.
    artifacts_dir = Path(args.artifacts_dir) if args.artifacts_dir else manifest_dir
    try:
        artifacts_root = artifacts_dir.resolve()
    except OSError as exc:
        result.add("artifacts", "fail", f"cannot resolve --artifacts-dir: {exc}")
        artifacts_root = manifest_dir.resolve()
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
    quote_path = Path(args.quote) if args.quote else manifest_dir / "quote.msg"
    sig_path = Path(args.signature) if args.signature else manifest_dir / "quote.sig"
    pcr_path = Path(args.pcr) if args.pcr else manifest_dir / "quote.pcr"
    ak_path = Path(args.ak) if args.ak else manifest_dir / "ak.pub"

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
        manifest_indices = parsed["pcr"]["indices"]
        if quote.pcr_indices == manifest_indices:
            result.add("quote_pcr_selection", "pass",
                       f"sha256:{','.join(map(str, manifest_indices))}")
        else:
            result.add("quote_pcr_selection", "fail",
                       f"quote selects {quote.pcr_indices}, manifest says {manifest_indices}")

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
    verify_signature(args, result, parsed, manifest_digest)
    expected_statement = getattr(args, "expect_statement_digest", None)
    if expected_statement:
        if result.statement_sha256 is None:
            result.add("statement_pin", "fail",
                       "cannot pin the statement: no signed DSSE payload")
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
        sidecar = manifest_dir / "quote.nonce"
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

    if quote is not None:
        statement_digest = result.statement_sha256
        if statement_digest is None:
            # Unsigned (explicitly allowed) or no envelope: rebuild the
            # deterministic statement so the quote binding can still be checked.
            statement_digest = sha256_bytes(canonical_bytes(
                build_statement(parsed, manifest_digest)))
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


def _relative_out_name(path: Path, out: Path) -> str:
    try:
        rel = path.resolve().relative_to(out.resolve()).as_posix()
    except ValueError:
        rel = path.name
    return _normalize_relative(rel, "artifact path")


def _wiz_version(wiz: Path, override: str | None,
                 commit_override: str | None) -> tuple[str, str | None, str]:
    binary_sha = sha256_file(wiz)
    if override:
        version, commit = override, commit_override
    else:
        proc = _run([str(wiz), "--version"], what="wiz --version", timeout=120)
        line = proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else ""
        match = _VERSION_LINE.match(line)
        if not match:
            raise AttestError(
                f"cannot parse `{wiz} --version` output {line!r}; pass --wiz-version"
            )
        version = match.group(1)
        commit = commit_override or match.group(2)
    if commit is not None and re.fullmatch(r"[0-9a-f]{7,64}", commit) is None:
        raise UsageError("--wiz-commit must be 7-64 lowercase hex characters")
    return version, commit, binary_sha


def _default_target(cc: str | None) -> str:
    compiler = cc or os.environ.get("CC") or "cc"
    try:
        proc = subprocess.run([compiler, "-dumpmachine"], capture_output=True,
                              text=True, timeout=60)
        if proc.returncode == 0 and proc.stdout.strip():
            return proc.stdout.strip().splitlines()[0]
    except (OSError, subprocess.TimeoutExpired):
        pass
    machine = platform.machine() or "unknown"
    return f"{machine}-unknown-linux-gnu"


def _tpm_cmd(tools: dict[str, str], name: str, sudo: bool) -> list[str]:
    prefix = ["sudo", "-n"] if sudo else []
    return prefix + [tools[name]]


def _quote(manifest_path: Path, out: Path, indices: Sequence[int], *,
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
            for name, source in (("manifest.json", manifest_path),
                                 ("ak.pub", ak_pub),
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
    if args.artifact and args.source:
        raise UsageError("give either SOURCE or --artifact, not both")
    if not args.artifact and not args.source:
        raise UsageError("give a SOURCE to build or one or more --artifact files")
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    built: list[Path] = []
    if args.source:
        source = Path(args.source)
        if not source.is_file():
            raise UsageError(f"source file does not exist: {source}")
        wiz = _resolve_executable(args.wiz or "wiz", "wiz executable")
        name = args.output_name or source.stem
        target_path = out / name
        _run([str(wiz), *args.wiz_flag, "build", str(source), "-o", str(target_path)],
             what="wiz build")
        built.append(target_path)
        generated_c = Path(str(target_path) + ".c")
        if generated_c.is_file():
            built.append(generated_c)
    else:
        for item in args.artifact:
            path = Path(item)
            if not path.is_file():
                raise UsageError(f"artifact does not exist: {path}")
            built.append(path)

    artifacts: list[dict[str, Any]] = []
    names: set[str] = set()
    for path in built:
        name = _relative_out_name(path, out)
        if name in names:
            raise UsageError(f"two artifacts would be recorded as {name!r}")
        names.add(name)
        artifacts.append({
            "path": name,
            "size": path.stat().st_size,
            "sha256": sha256_file(path),
        })

    source_path = Path(args.source) if args.source else None
    if source_path is not None:
        try:
            entry = source_path.resolve().relative_to(Path.cwd().resolve()).as_posix()
        except ValueError:
            entry = source_path.name
        source_sha = sha256_file(source_path)
        if args.source_sha256:
            raise UsageError("--source-sha256 is for --artifact; a built SOURCE is hashed")
    else:
        if not args.source_entry:
            raise UsageError(
                "--artifact needs --source-entry (and --source-sha256 when that file "
                "is not in the current directory): a manifest must name its source"
            )
        entry = args.source_entry
        if args.source_sha256:
            source_sha = normalize_hex(args.source_sha256, "--source-sha256")
            if len(source_sha) != 64:
                raise UsageError("--source-sha256 must be 64 hex characters")
        elif Path(entry).is_file():
            source_sha = sha256_file(Path(entry))
        else:
            raise UsageError(
                f"cannot hash source entry {entry!r} from the current directory; "
                "pass --source-sha256"
            )

    if args.tree_root:
        roots = list(args.tree_root)
    else:
        roots = [r for r in ("lib", "runtime") if Path(r).is_dir()]
    tree_sha, roots, tree_files = tree_digest(roots)

    if args.wiz_version:
        version, commit = args.wiz_version, args.wiz_commit
        if args.wiz:
            wiz_path: Path | None = _resolve_executable(args.wiz, "wiz executable")
            binary_sha = sha256_file(wiz_path)
        else:
            binary_sha = None
        if args.wiz_commit is not None and re.fullmatch(r"[0-9a-f]{7,64}",
                                                        args.wiz_commit) is None:
            raise UsageError("--wiz-commit must be 7-64 lowercase hex characters")
    else:
        wiz_path = _resolve_executable(args.wiz or "wiz", "wiz executable")
        version, commit, binary_sha = _wiz_version(wiz_path, None, args.wiz_commit)

    target = args.target or _default_target(args.cc)

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

    manifest = build_manifest(
        artifacts=artifacts,
        wiz_version=version,
        wiz_commit=commit,
        wiz_binary_sha256=binary_sha,
        source_entry=entry,
        source_sha256=source_sha,
        tree_sha256=tree_sha,
        tree_roots=roots,
        target=target,
        pcr_indices=args.pcr_list,
    )
    manifest_path = out / "manifest.json"
    manifest_path.write_bytes(canonical_bytes(manifest))
    manifest_digest = sha256_file(manifest_path)

    summary: dict[str, Any] = {
        "schema": "wiz-attest-result/v1",
        "manifest": str(manifest_path),
        "manifest_sha256": manifest_digest,
        "artifacts": [a["path"] for a in manifest["artifacts"]],
        "pcr_indices": manifest["pcr"]["indices"],
        "tree_sha256": tree_sha,
        "tree_files": tree_files,
        "quoted": False,
        "signed": False,
    }

    signed_info: dict[str, Any] | None = None
    if args.sign_key:
        signed_info = sign_manifest(
            manifest_path, Path(args.sign_key),
            out=Path(args.envelope) if args.envelope else None,
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
    elif args.sigstore or args.sigstore_upload:
        raise UsageError("--sigstore needs --sign-key (the offline DSSE signature)")

    if args.no_quote:
        return summary
    if signed_info is None:
        raise UsageError(
            "a TPM quote must bind a signed statement; pass --sign-key "
            "(generate one with `wiz-attest keygen --key <path>`)"
        )
    if nonce is None:
        nonce = secrets.token_bytes(32)
        summary["nonce_generated"] = True
    (out / "quote.nonce").write_text(nonce.hex() + "\n", encoding="utf-8")
    summary["nonce"] = nonce.hex()
    extra_data = bytes.fromhex(
        quote_extra_data(nonce, signed_info["statement_sha256"]))
    _quote(manifest_path, out, args.pcr_list, extra_data=extra_data,
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
        description="Sign a canonical manifest as an in-toto Statement in a DSSE "
                    "envelope with an offline Ed25519 key.",
    )
    p.add_argument("--manifest", required=True, help="manifest.json")
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
        info = sign_manifest(
            Path(args.manifest), Path(args.key),
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
        print(f"manifest sha256: {info['manifest_sha256']}")
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
        description="Build a Wiz program (or take --artifact), sign the in-toto "
                    "statement with an offline Ed25519 key, and bind its digest to "
                    "a TPM 2.0 quote over selected PCRs.",
    )
    p.add_argument("source", nargs="?", help="Wiz source file to build")
    p.add_argument("--artifact", action="append", default=[],
                   help="take an existing artifact instead of building (repeatable)")
    p.add_argument("--out", default=".", help="output directory (default: .)")
    p.add_argument("--output-name", help="executable name for a built SOURCE")
    p.add_argument("--source-entry", help="source path to record with --artifact")
    p.add_argument("--source-sha256",
                   help="SHA-256 of --source-entry when the file is not in the "
                        "current directory")
    p.add_argument("--tree-root", action="append", default=[],
                   help="relative directory of compiler inputs (repeatable; "
                        "default: lib and runtime when present)")
    p.add_argument("--nonce", help="verifier-supplied hex nonce (16..64 bytes)")
    p.add_argument("--nonce-file", help="read the nonce bytes from a file")
    p.add_argument("--challenge", help=argparse.SUPPRESS)  # deprecated alias
    p.add_argument("--challenge-file", help=argparse.SUPPRESS)
    p.add_argument("--sign-key", help="offline Ed25519 private key used to sign "
                                      "the in-toto statement")
    p.add_argument("--envelope", help="DSSE envelope path (default: "
                                      "manifest.intoto.json next to the manifest)")
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
    p.add_argument("--target", help="target triple (default: cc -dumpmachine)")
    p.add_argument("--cc", help="C compiler whose -dumpmachine names the target")
    p.add_argument("--wiz", help="wiz executable (default: wiz on PATH)")
    p.add_argument("--wiz-version", help="override the version from wiz --version")
    p.add_argument("--wiz-commit", help="record this toolchain commit")
    p.add_argument("--wiz-flag", action="append", default=[],
                   help="extra flag passed to wiz before `build` (repeatable)")
    p.add_argument("--no-quote", action="store_true",
                   help="write only manifest.json (no TPM needed)")
    p.add_argument("--tpm2-bin", help="directory containing tpm2-tools")
    p.add_argument("--sudo", action="store_true",
                   help="run tpm2 commands through `sudo -n` (device nodes are often root-only)")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    return p


def main_attest(argv: Sequence[str]) -> int:
    if argv and argv[0] == "keygen":
        return main_keygen(argv[1:])
    if argv and argv[0] == "sign":
        return main_sign(argv[1:])
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
        print(f"manifest: {summary['manifest']}")
        print(f"manifest sha256: {summary['manifest_sha256']}")
        print(f"artifacts: {', '.join(summary['artifacts'])}")
        print(f"PCRs: sha256:{','.join(map(str, summary['pcr_indices']))}")
        if summary.get("signed"):
            print(f"statement: {summary['statement_sha256']}")
            print(f"envelope: {summary['envelope']}")
            print(f"detached signature: {summary['detached_signature']}")
            print(f"keyid: {summary['keyid']}")
        else:
            print("statement: unsigned (no --sign-key)")
        if summary["quoted"]:
            print("quote: quote.msg, quote.sig, quote.pcr, ak.pub, quote.nonce")
            if summary.get("ak"):
                print(f"AK name: {summary['ak']['name']}")
                print(f"AK SPKI sha256: {summary['ak']['spki_sha256']}")
        else:
            print("quote: not requested (--no-quote)")
    return EXIT_OK


def _verify_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wiz-verify",
        description="Verify a DSSE-signed in-toto statement, a Wiz build manifest, "
                    "a TPM 2.0 quote, an expected PCR policy and the artifact bytes.",
    )
    p.add_argument("--manifest", required=True, help="manifest.json")
    p.add_argument("--envelope", help="DSSE envelope (default: "
                                      "manifest.intoto.json next to the manifest)")
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
                                           "(default: the manifest's directory)")
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
        if not Path(args.policy).is_file():
            raise UsageError(f"policy file does not exist: {args.policy}")
        if args.require_signature and args.allow_unsigned:
            raise UsageError("--require-signature and --allow-unsigned conflict")
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
        print("usage: wiz_attest.py {attest,verify,keygen,sign,ak-info} [options]",
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
