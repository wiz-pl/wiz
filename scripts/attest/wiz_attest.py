#!/usr/bin/env python3
"""Build manifests and TPM 2.0 quote verification for Wiz artifacts.

This module is deliberately standalone and uses only the Python 3 standard
library.  It defines three things:

* a canonical build-manifest format (`SCHEMA`), whose SHA-256 is the value the
  TPM quote's `extraData` must contain;
* `verify`, the verifier CLI (`scripts/attest/wiz-verify`), which checks the
  manifest, every artifact digest, the quote binding, an expected PCR policy
  and, when `tpm2-tools` is installed, the quote signature and PCR digest via
  `tpm2_checkquote` (TPM cryptography is not reimplemented here);
* `attest`, the producer CLI (`scripts/attest/wiz-attest`), which builds a Wiz
  program (or takes `--artifact`) and emits `manifest.json`, `quote.msg`,
  `quote.sig`, `quote.pcr` and `ak.pub`.

The formats and the trust model are documented in `docs/attestation.md`.
Exit codes are the same for both CLIs:

  0  everything ran and passed (verifier: a real signature check ran)
  1  verification or production failed
  2  usage error
  3  incomplete: a required tool is missing, or `--skip-crypto` was used

The producer uses only transient TPM objects (no persistent handle, no NV
write); the AK private blob is discarded after the quote.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
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
    "challenge",
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

    if "challenge" in obj:
        challenge = obj["challenge"]
        _expect(isinstance(challenge, str) and _HEX.match(challenge) is not None,
                "challenge must be a non-empty even-length hex string")
        _expect(16 <= len(challenge) // 2 <= 64,
                "challenge must be 16..64 bytes")


def validate_policy(obj: Any) -> dict[str, Any]:
    """Raise SchemaError unless `obj` is a valid PCR policy; return it normalized."""
    _expect(isinstance(obj, dict), "policy must be a JSON object")
    unknown = set(obj) - {"schema", "bank", "pcr", "ak_sha256"}
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
    challenge: str | None = None,
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
    if challenge is not None:
        manifest["challenge"] = challenge.lower()
    validate_manifest(manifest)
    return manifest


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
        if quote.extra_data == manifest_digest:
            result.add("quote_extra_data", "pass",
                       "extraData equals sha256(manifest)")
        else:
            result.add("quote_extra_data", "fail",
                       f"extraData is {quote.extra_data}, manifest digest is {manifest_digest}")
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

    # 5. AK pin: optional, but a quote signature is only as good as the key.
    expected_ak = args.ak_sha256.lower() if args.ak_sha256 else None
    if policy is not None and "ak_sha256" in policy:
        if expected_ak and expected_ak != policy["ak_sha256"]:
            result.add("ak_pin", "fail",
                       f"--ak-sha256 {expected_ak} conflicts with policy "
                       f"{policy['ak_sha256']}")
        else:
            expected_ak = policy["ak_sha256"]
    if expected_ak:
        try:
            actual_ak = sha256_file(ak_path)
        except OSError as exc:
            result.add("ak_pin", "fail", f"cannot read {ak_path}: {exc.strerror}")
        else:
            if actual_ak == expected_ak:
                result.add("ak_pin", "pass", actual_ak)
            else:
                result.add("ak_pin", "fail",
                           f"AK file is {actual_ak}, expected {expected_ak}")
    else:
        result.add("ak_pin", "skip",
                   "no --ak-sha256 and no policy ak_sha256: the AK is not pinned")

    # 6. Challenge / replay binding.  extraData is the manifest digest, so a
    # challenge inside the manifest is what makes the quote fresh.
    challenge = parsed.get("challenge")
    if args.challenge:
        wanted = normalize_hex(args.challenge, "--challenge")
        if challenge is None:
            result.add("challenge", "fail",
                       "manifest has no challenge; a quote alone can be replayed")
        elif challenge == wanted:
            result.add("challenge", "pass", wanted)
        else:
            result.add("challenge", "fail",
                       f"manifest challenge is {challenge}, expected {wanted}")
    elif args.require_challenge and challenge is None:
        result.add("challenge", "fail", "manifest has no challenge and --require-challenge was given")
    elif challenge is not None:
        result.add("challenge", "pass",
                   f"bound to challenge {challenge} (pass --challenge to check freshness)")
        result.warnings.append(
            "the quote is bound to a challenge, but the verifier was not given it; "
            "replay protection depends on the challenge being fresh"
        )
    else:
        result.add("challenge", "skip",
                   "manifest has no challenge; the quote proves the manifest existed on "
                   "this platform at some time, not that it is fresh (use --require-challenge "
                   "or wiz-attest --challenge)")
        result.warnings.append(
            "no challenge binding: an attacker can replay an older quote for the same "
            "manifest; --require-challenge makes this an error"
        )

    # 7. Signature and PCR digest: tpm2_checkquote, never reimplemented here.
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
           tpm2_bin: str | None, sudo: bool) -> None:
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

    digest = sha256_file(manifest_path)
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

    challenge = args.challenge
    if args.challenge_file:
        challenge = _read_bytes(Path(args.challenge_file), "challenge file").hex()
    if challenge is not None:
        challenge = normalize_hex(challenge, "--challenge")
        if not 16 <= len(challenge) // 2 <= 64:
            raise UsageError("--challenge must be 16..64 bytes of hex")

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
        challenge=challenge,
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
    }
    if args.no_quote:
        return summary

    _quote(manifest_path, out, args.pcr_list,
           tpm2_bin=args.tpm2_bin, sudo=args.sudo)
    summary["quoted"] = True
    summary["quote_files"] = ["quote.msg", "quote.sig", "quote.pcr", "ak.pub"]
    return summary


# --------------------------------------------------------------------------
# CLIs


def _attest_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wiz-attest",
        description="Build a Wiz program (or take --artifact) and bind a canonical "
                    "manifest to a TPM 2.0 quote over selected PCRs.",
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
    p.add_argument("--challenge", help="hex challenge to bind into the manifest")
    p.add_argument("--challenge-file", help="read the challenge bytes from a file")
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
        if summary["quoted"]:
            print("quote: quote.msg, quote.sig, quote.pcr, ak.pub")
        else:
            print("quote: not requested (--no-quote)")
    return EXIT_OK


def _verify_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="wiz-verify",
        description="Verify a Wiz build manifest against a TPM 2.0 quote, an "
                    "expected PCR policy and the artifact bytes.",
    )
    p.add_argument("--manifest", required=True, help="manifest.json")
    p.add_argument("--quote", help="quote.msg (default: next to the manifest)")
    p.add_argument("--signature", help="quote.sig (default: next to the manifest)")
    p.add_argument("--pcr", help="quote.pcr (default: next to the manifest)")
    p.add_argument("--ak", help="ak.pub (default: next to the manifest)")
    p.add_argument("--policy", required=True,
                   help="expected PCR policy JSON (PCR index -> sha256 value)")
    p.add_argument("--artifacts-dir", help="where artifact paths are resolved "
                                           "(default: the manifest's directory)")
    p.add_argument("--challenge", help="expected hex challenge bound in the manifest")
    p.add_argument("--require-challenge", action="store_true",
                   help="fail unless the manifest contains a challenge")
    p.add_argument("--expect-digest", help="pin the expected manifest SHA-256")
    p.add_argument("--ak-sha256", help="pin the SHA-256 of the ak.pub file")
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
        for option in ("challenge", "expect_digest", "ak_sha256"):
            value = getattr(args, option)
            if value:
                value = normalize_hex(value, "--" + option.replace("_", "-"))
                if option == "challenge":
                    if not 16 <= len(value) // 2 <= 64:
                        raise UsageError("--challenge must be 16..64 bytes")
                elif len(value) != 64:
                    raise UsageError(f"--{option.replace('_', '-')} must be 64 hex characters")
                setattr(args, option, value)
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
        print("usage: wiz_attest.py {attest,verify} [options]", file=sys.stderr)
        return EXIT_USAGE
    if argv[0] == "attest":
        return main_attest(argv[1:])
    if argv[0] == "verify":
        return main_verify(argv[1:])
    print(f"unknown command {argv[0]!r}", file=sys.stderr)
    return EXIT_USAGE


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
