#!/usr/bin/env python3
"""AMD SEV-SNP attestation report parsing and verification.

This module is the E2 verifier side.  It parses the raw AMD
``ATTESTATION_REPORT`` (SEV-SNP ABI, 1184 bytes) and, optionally, the
certificate table that an extended guest request appends after it.  It never
trusts a guest's own "verified" flag: the input is evidence, and the result is
computed here.

What is checked:

* the report shape, version, signature algorithm and guest policy bits;
* ``REPORT_DATA == SHA-256("wiz-snp-v1" || nonce || statement_digest) ||
  zeroes`` (the binding to the signed build statement);
* the launch ``MEASUREMENT`` against a pinned digest;
* ``REPORTED_TCB``/``COMMITTED_TCB`` against a per-component floor;
* ``VMPL``, SMT and the other policy bits the policy pins;
* ``VCEK``/``VLEK`` -> ``ASK`` -> ``ARK`` with X.509 chain validation against
  embedded AMD KDS root certificates (no network);
* the report's ECDSA-P384/SHA-384 signature under the leaf certificate;
* certificate validity at the verifier's clock.

Cryptography and X.509 parsing are delegated to ``openssl`` (the same way the
TPM path delegates signature checking to ``tpm2_checkquote``); this module does
not reimplement either.  Python 3 standard library only.

The AMD roots under ``amd-roots/`` were fetched from
``https://kdsintf.amd.com`` and are pinned by SHA-256 in
``amd-roots/README.md`` and in ``AMD_ARK_SHA256`` below.
"""

from __future__ import annotations

import base64
import binascii
import datetime
import glob
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import tempfile
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Sequence

# --------------------------------------------------------------------------
# Constants from the AMD SEV-SNP ABI (publication #56860)

REPORT_SIZE = 0x4A0
SIGNED_SIZE = 0x2A0
SIGNATURE_OFFSET = 0x2A0
ECDSA_RS_SIZE = 72
REPORT_DATA_SIZE = 64
MEASUREMENT_SIZE = 48
CHIP_ID_SIZE = 64

SIGN_ECDSA_P384_SHA384 = 1
REPORT_VERSION_MIN = 2
REPORT_VERSION_MAX = 5

SNP_LABEL = b"wiz-snp-v1"
SNP_POLICY_SCHEMA = "wiz-snp-policy/v1"

GUID_VCEK = uuid.UUID("63da758d-e664-4564-adc5-f4b93be8accd")
GUID_VLEK = uuid.UUID("a8074bc2-a25a-483e-aae6-39c045a0b8a1")
GUID_ASK = uuid.UUID("4ab7b379-bbac-4fe4-a02f-05aef327c782")
GUID_ARK = uuid.UUID("c0b406a4-a803-4952-9743-3fb6014cd0ae")

# AMD KDS ARK SHA-256 fingerprints (DER certificate digests).  These pin the
# files in amd-roots/ so a corrupted checkout cannot silently change the trust
# anchor.  Source: https://kdsintf.amd.com/vcek/v1/<product>/cert_chain.
AMD_ARK_SHA256 = {
    "Milan": "69d063b45344d26a2e94e1f4210de49ef555308287d4c174445c95639a540bcd",
    "Genoa": "4c6598d19c18719c5dfd4a7d335f674e5bfe1d8f800cea2cf270c10d103db2f1",
    "Turin": "1f084161a44bb6d93778a904877d4819cafa5d05ef4193b2ded9dd9c73dd3f6a",
}

TCB_COMPONENTS = {
    "boot_loader": 0,
    "tee": 1,
    "snp": 3,
    "microcode": 4,
    "spl": 6,
}

POLICY_KEYS = {
    "schema",
    "measurement",
    "product",
    "signing_key",
    "vmpl",
    "tcb",
    "policy",
    "chip_id",
    "author_key_digest",
    "valid_until",
}

POLICY_BIT_KEYS = {
    "migration_agent",
    "smt",
    "single_socket",
    "cxl",
    "mem_aes_256_xts",
    "rapl_dis",
    "ciphertext_hiding_dram",
    "page_swap_disable",
}

_HEX = re.compile(r"^(?:[0-9a-fA-F]{2})+$")
_PEM_CERT = re.compile(rb"-----BEGIN CERTIFICATE-----.*?-----END CERTIFICATE-----", re.S)
_JSON_START = re.compile(rb"^\s*[{\[]")


class SnpError(Exception):
    """Base class for SNP evidence errors."""


class SnpSchemaError(SnpError):
    """The evidence or policy is malformed."""


class SnpIncomplete(SnpError):
    """A tool or trust input needed to verify the evidence is missing."""


# --------------------------------------------------------------------------
# Small helpers


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def normalize_hex(value: str, what: str) -> str:
    text = value.strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    if not text or not _HEX.match(text):
        raise SnpSchemaError(f"{what} must be an even-length hex string")
    return text


def _u32(data: bytes, offset: int) -> int:
    return struct.unpack_from("<I", data, offset)[0]


def _u64(data: bytes, offset: int) -> int:
    return struct.unpack_from("<Q", data, offset)[0]


def _reject_constant(value: str) -> None:
    raise SnpSchemaError(f"non-finite JSON number is not allowed: {value}")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise SnpSchemaError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_policy_json(data: bytes) -> Any:
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise SnpSchemaError(f"SNP policy is not UTF-8: {exc}") from None
    try:
        return json.loads(text, object_pairs_hook=_unique_object,
                          parse_constant=_reject_constant)
    except ValueError as exc:
        raise SnpSchemaError(f"SNP policy is not valid JSON: {exc}") from None


def report_data_value(nonce: bytes, statement_digest: str) -> bytes:
    """The 64-byte REPORT_DATA value: H(label || nonce || digest) then zeroes."""
    if not 16 <= len(nonce) <= 64:
        raise SnpSchemaError("nonce must be 16..64 bytes")
    if len(statement_digest) != 64 or _HEX.match(statement_digest) is None:
        raise SnpSchemaError("statement digest must be 64 hex characters")
    digest = hashlib.sha256(SNP_LABEL + nonce + bytes.fromhex(statement_digest)).digest()
    return digest + bytes(REPORT_DATA_SIZE - len(digest))


def find_openssl(explicit: str | None = None) -> str | None:
    """Find an openssl executable without invoking the network or the shell.

    ``WIZ_ATTEST_OPENSSL`` is honoured for tests and non-standard installs.  The
    Nix-store glob is a last resort for development shells that keep openssl
    out of ``PATH``; a normal distribution has it on ``PATH``.
    """
    if explicit:
        return explicit
    env = os.environ.get("WIZ_ATTEST_OPENSSL")
    if env:
        return env
    found = shutil.which("openssl")
    if found:
        return found
    matches = sorted(glob.glob("/nix/store/*-openssl-*-bin/bin/openssl"))
    return matches[-1] if matches else None


def usable_openssl(path: str | None) -> bool:
    return bool(path) and Path(path).is_file() and os.access(path, os.X_OK)


def _run(cmd: Sequence[str], *, what: str, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise SnpIncomplete(f"{what} could not run: {exc}") from None


def _tail(text: str, lines: int = 4) -> str:
    kept = [line for line in text.strip().splitlines() if line.strip()]
    return " | ".join(kept[-lines:])


# --------------------------------------------------------------------------
# Report parsing


@dataclass
class SnpPolicyBits:
    abi_major: int
    abi_minor: int
    smt: bool
    migration_agent: bool
    debug: bool
    single_socket: bool
    cxl: bool
    mem_aes_256_xts: bool
    rapl_dis: bool
    ciphertext_hiding_dram: bool
    page_swap_disable: bool


@dataclass
class SnpReport:
    version: int
    guest_svn: int
    policy: int
    policy_bits: SnpPolicyBits
    family_id: str
    image_id: str
    vmpl: int
    signature_algo: int
    platform_version: int
    platform_info: int
    signer_info: int
    signing_key: str  # "VCEK", "VLEK", "none"
    mask_chip_id: bool
    author_key_en: bool
    report_data: bytes
    measurement: bytes
    host_data: str
    id_key_digest: str
    author_key_digest: str
    report_id: str
    report_id_ma: str
    reported_tcb: int
    committed_tcb: int
    launch_tcb: int
    chip_id: bytes
    cpuid_family: int | None
    cpuid_model: int | None
    cpuid_stepping: int | None
    signature_r: bytes
    signature_s: bytes
    raw: bytes = field(repr=False)

    @property
    def report_data_hex(self) -> str:
        return self.report_data.hex()

    @property
    def measurement_hex(self) -> str:
        return self.measurement.hex()

    @property
    def chip_id_hex(self) -> str:
        return self.chip_id.hex()

    @property
    def signed_bytes(self) -> bytes:
        return self.raw[:SIGNED_SIZE]

    @property
    def tcb_bytes(self) -> bytes:
        return struct.pack("<Q", self.reported_tcb)

    @property
    def committed_tcb_bytes(self) -> bytes:
        return struct.pack("<Q", self.committed_tcb)


def parse_policy_bits(value: int) -> SnpPolicyBits:
    if not value & (1 << 17):
        raise SnpSchemaError("guest policy bit 17 is reserved and must be 1")
    if value >> 26:
        raise SnpSchemaError(f"guest policy has reserved bits set: 0x{value:016x}")
    return SnpPolicyBits(
        abi_minor=value & 0xFF,
        abi_major=(value >> 8) & 0xFF,
        smt=bool(value & (1 << 16)),
        migration_agent=bool(value & (1 << 18)),
        debug=bool(value & (1 << 19)),
        single_socket=bool(value & (1 << 20)),
        cxl=bool(value & (1 << 21)),
        mem_aes_256_xts=bool(value & (1 << 22)),
        rapl_dis=bool(value & (1 << 23)),
        ciphertext_hiding_dram=bool(value & (1 << 24)),
        page_swap_disable=bool(value & (1 << 25)),
    )


def parse_report(data: bytes) -> SnpReport:
    """Parse one 1184-byte ATTESTATION_REPORT.  Format checking only."""
    if len(data) < REPORT_SIZE:
        raise SnpSchemaError(
            f"SEV-SNP report is {len(data)} bytes; ATTESTATION_REPORT is "
            f"{REPORT_SIZE} (0x{REPORT_SIZE:x}) bytes"
        )
    raw = data[:REPORT_SIZE]
    version = _u32(raw, 0x00)
    if not REPORT_VERSION_MIN <= version <= REPORT_VERSION_MAX:
        raise SnpSchemaError(
            f"report version {version} is outside the supported range "
            f"{REPORT_VERSION_MIN}..{REPORT_VERSION_MAX}"
        )
    signature_algo = _u32(raw, 0x34)
    if signature_algo != SIGN_ECDSA_P384_SHA384:
        raise SnpSchemaError(
            f"signature algorithm {signature_algo} is not ECDSA-P384/SHA-384 (1)"
        )
    policy = _u64(raw, 0x08)
    policy_bits = parse_policy_bits(policy)
    signer_info = _u32(raw, 0x48)
    if signer_info >> 5:
        raise SnpSchemaError(f"signer_info has reserved bits set: 0x{signer_info:08x}")
    signing_code = (signer_info >> 2) & 7
    if signing_code in (2, 3, 4, 5, 6):
        raise SnpSchemaError(f"signer_info.signing_key {signing_code} is reserved")
    signing_key = {0: "VCEK", 1: "VLEK", 7: "none"}[signing_code]
    cpuid_family = cpuid_model = cpuid_stepping = None
    if version >= 3:
        cpuid_family = raw[0x188]
        cpuid_model = raw[0x189]
        cpuid_stepping = raw[0x18A]
    return SnpReport(
        version=version,
        guest_svn=_u32(raw, 0x04),
        policy=policy,
        policy_bits=policy_bits,
        family_id=raw[0x10:0x20].hex(),
        image_id=raw[0x20:0x30].hex(),
        vmpl=_u32(raw, 0x30),
        signature_algo=signature_algo,
        platform_version=_u64(raw, 0x38),
        platform_info=_u64(raw, 0x40),
        signer_info=signer_info,
        signing_key=signing_key,
        mask_chip_id=bool(signer_info & 2),
        author_key_en=bool(signer_info & 1),
        report_data=raw[0x50:0x90],
        measurement=raw[0x90:0xC0],
        host_data=raw[0xC0:0xE0].hex(),
        id_key_digest=raw[0xE0:0x110].hex(),
        author_key_digest=raw[0x110:0x140].hex(),
        report_id=raw[0x140:0x160].hex(),
        report_id_ma=raw[0x160:0x180].hex(),
        reported_tcb=_u64(raw, 0x180),
        committed_tcb=_u64(raw, 0x1E0),
        launch_tcb=_u64(raw, 0x1F0),
        chip_id=raw[0x1A0:0x1E0],
        cpuid_family=cpuid_family,
        cpuid_model=cpuid_model,
        cpuid_stepping=cpuid_stepping,
        signature_r=raw[SIGNATURE_OFFSET:SIGNATURE_OFFSET + ECDSA_RS_SIZE],
        signature_s=raw[SIGNATURE_OFFSET + ECDSA_RS_SIZE:SIGNATURE_OFFSET + 2 * ECDSA_RS_SIZE],
        raw=raw,
    )


# --------------------------------------------------------------------------
# Certificate table and PEM bundles


@dataclass
class CertEntry:
    der: bytes
    guid: uuid.UUID | None = None
    source: str = ""
    subject: str = ""
    issuer: str = ""


def _pem_from_der(der: bytes) -> bytes:
    body = base64.encodebytes(der).replace(b"\n", b"")
    return b"-----BEGIN CERTIFICATE-----\n" + _wrap(body) + b"-----END CERTIFICATE-----\n"


def _wrap(body: bytes, width: int = 64) -> bytes:
    return b"\n".join(body[i:i + width] for i in range(0, len(body), width)) + b"\n"


def _der_from_pem(block: bytes) -> bytes:
    body = block
    body = re.sub(rb"-----BEGIN CERTIFICATE-----", b"", body)
    body = re.sub(rb"-----END CERTIFICATE-----", b"", body)
    body = re.sub(rb"\s+", b"", body)
    try:
        return base64.b64decode(body, validate=True)
    except (binascii.Error, ValueError) as exc:
        raise SnpSchemaError(f"invalid PEM certificate: {exc}") from None


def parse_cert_table(data: bytes) -> list[CertEntry]:
    """Parse the ABI certificate table (24-byte headers, then blobs)."""
    if not data:
        return []
    entries: list[CertEntry] = []
    header_size = 0
    pos = 0
    while pos + 24 <= len(data):
        guid_raw = data[pos:pos + 16]
        offset = _u32(data, pos + 16)
        length = _u32(data, pos + 20)
        pos += 24
        header_size = pos
        if guid_raw == bytes(16) and offset == 0 and length == 0:
            break
        if offset < header_size or offset + length > len(data):
            raise SnpSchemaError(
                f"certificate table entry at {pos - 24} has an out-of-range "
                f"offset/length ({offset}, {length}) for {len(data)} bytes"
            )
        entries.append(CertEntry(
            guid=uuid.UUID(bytes_le=guid_raw),
            der=data[offset:offset + length],
            source="table",
        ))
    if not entries:
        raise SnpSchemaError("certificate table is empty or truncated")
    return entries


def split_report_evidence(data: bytes) -> tuple[bytes, bytes]:
    """Split a report file into (1184-byte report, optional cert-table bytes)."""
    if len(data) < REPORT_SIZE:
        raise SnpSchemaError(
            f"evidence is {len(data)} bytes; a report is at least {REPORT_SIZE}"
        )
    trailing = data[REPORT_SIZE:]
    if trailing and not any(trailing):
        trailing = b""
    return data[:REPORT_SIZE], trailing


def _looks_like_der_cert(raw: bytes) -> bool:
    """True for a single DER certificate rather than an ABI cert table.

    A DER certificate starts with a SEQUENCE tag; an ABI table starts with a
    known 16-byte little-endian GUID.  Checking the GUID first keeps a table
    whose GUID happens to begin with 0x30 on the table path.
    """
    if len(raw) < 24 or raw[0] != 0x30:
        return False
    try:
        first = uuid.UUID(bytes_le=raw[:16])
    except ValueError:
        return True
    return first not in {GUID_VCEK, GUID_VLEK, GUID_ASK, GUID_ARK, uuid.UUID(int=0)}


def read_cert_evidence(path: Path) -> list[CertEntry]:
    """Read certificates from a directory, a PEM bundle or an ABI table."""
    if not path.exists():
        raise SnpSchemaError(f"certificate evidence does not exist: {path}")
    files: list[Path]
    if path.is_dir():
        files = sorted(p for p in path.iterdir() if p.is_file())
        if not files:
            raise SnpSchemaError(f"certificate directory is empty: {path}")
    else:
        files = [path]
    entries: list[CertEntry] = []
    for item in files:
        try:
            raw = item.read_bytes()
        except OSError as exc:
            raise SnpSchemaError(f"cannot read certificate evidence {item}: {exc}") from None
        if _JSON_START.match(raw):
            raise SnpSchemaError(
                f"{item} looks like JSON; pass raw report/certificate bytes, not a "
                "guest attestation.json"
            )
        if b"BEGIN CERTIFICATE" in raw:
            for block in _PEM_CERT.findall(raw):
                entries.append(CertEntry(
                    der=_der_from_pem(block),
                    source=item.name,
                ))
        elif _looks_like_der_cert(raw):
            entries.append(CertEntry(der=raw, source=item.name))
        else:
            entries.extend(parse_cert_table(raw))
    if not entries:
        raise SnpSchemaError(f"no certificates found in {path}")
    return entries


# --------------------------------------------------------------------------
# openssl-backed X.509 helpers


def cert_dn(entry: CertEntry, openssl: str) -> tuple[str, str]:
    """Return (subject, issuer) for a DER certificate."""
    with tempfile.TemporaryDirectory(prefix="wiz-snp-dn-") as tmp:
        der = Path(tmp) / "cert.der"
        der.write_bytes(entry.der)
        proc = _run([openssl, "x509", "-inform", "DER", "-noout", "-subject",
                     "-issuer", "-in", str(der)], what="openssl x509")
    if proc.returncode != 0:
        raise SnpSchemaError(
            f"{entry.source or 'certificate'} is not a parseable X.509 certificate: "
            f"{_tail(proc.stderr or proc.stdout)}"
        )
    subject = issuer = ""
    for line in proc.stdout.splitlines():
        line = line.strip()
        if line.startswith("subject="):
            subject = line[len("subject="):].strip()
        elif line.startswith("issuer="):
            issuer = line[len("issuer="):].strip()
    if not subject or not issuer:
        raise SnpSchemaError(
            f"openssl did not report subject/issuer for {entry.source or 'certificate'}"
        )
    entry.subject, entry.issuer = subject, issuer
    return subject, issuer


def cert_validity(entry: CertEntry, openssl: str) -> tuple[datetime.datetime, datetime.datetime]:
    with tempfile.TemporaryDirectory(prefix="wiz-snp-time-") as tmp:
        der = Path(tmp) / "cert.der"
        der.write_bytes(entry.der)
        proc = _run([openssl, "x509", "-inform", "DER", "-noout", "-startdate",
                     "-enddate", "-in", str(der)], what="openssl x509")
    if proc.returncode != 0:
        raise SnpSchemaError(
            f"cannot read certificate validity: {_tail(proc.stderr or proc.stdout)}"
        )
    values: dict[str, datetime.datetime] = {}
    for line in proc.stdout.splitlines():
        if "=" not in line:
            continue
        key, text = line.split("=", 1)
        key = key.strip()
        if key not in ("notBefore", "notAfter"):
            continue
        values[key] = _parse_openssl_time(" ".join(text.split()), text.strip())
    if set(values) != {"notBefore", "notAfter"}:
        raise SnpSchemaError("openssl did not report both notBefore and notAfter")
    return values["notBefore"], values["notAfter"]


_MONTHS = {
    "Jan": 1, "Feb": 2, "Mar": 3, "Apr": 4, "May": 5, "Jun": 6,
    "Jul": 7, "Aug": 8, "Sep": 9, "Oct": 10, "Nov": 11, "Dec": 12,
}


def _parse_openssl_time(normalized: str, original: str) -> datetime.datetime:
    """Parse ``Oct 22 18:24:20 2045 GMT`` without depending on the locale."""
    parts = normalized.split()
    if len(parts) != 5 or parts[0] not in _MONTHS or parts[4] != "GMT":
        raise SnpSchemaError(f"unexpected openssl date {original!r}")
    try:
        hour, minute, second = (int(part) for part in parts[2].split(":"))
        return datetime.datetime(
            int(parts[3]), _MONTHS[parts[0]], int(parts[1]),
            hour, minute, second, tzinfo=datetime.timezone.utc)
    except ValueError:
        raise SnpSchemaError(f"unexpected openssl date {original!r}") from None


def _der_len(length: int) -> bytes:
    if length < 0x80:
        return bytes([length])
    raw = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(raw)]) + raw


def _der_uint(value: int) -> bytes:
    raw = value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big")
    if raw[0] & 0x80:
        raw = b"\x00" + raw
    return b"\x02" + _der_len(len(raw)) + raw


def ecdsa_der_signature(r_bytes: bytes, s_bytes: bytes) -> bytes:
    """Translate the AMD little-endian r/s fields into a DER ECDSA signature."""
    r = int.from_bytes(r_bytes, "little")
    s = int.from_bytes(s_bytes, "little")
    if r == 0 or s == 0:
        raise SnpSchemaError("report signature r/s is zero")
    body = _der_uint(r) + _der_uint(s)
    return b"\x30" + _der_len(len(body)) + body


def report_signature(
    report: SnpReport, leaf: CertEntry, openssl: str
) -> tuple[bool, str]:
    signature = ecdsa_der_signature(report.signature_r, report.signature_s)
    with tempfile.TemporaryDirectory(prefix="wiz-snp-sig-") as tmp:
        tmpdir = Path(tmp)
        der = tmpdir / "leaf.der"
        der.write_bytes(leaf.der)
        pub = _run([openssl, "x509", "-inform", "DER", "-pubkey", "-noout",
                    "-in", str(der)], what="openssl x509 -pubkey")
        if pub.returncode != 0:
            return False, f"cannot extract the leaf public key: {_tail(pub.stderr)}"
        (tmpdir / "leaf.pub").write_text(pub.stdout, encoding="utf-8")
        (tmpdir / "signed.bin").write_bytes(report.signed_bytes)
        (tmpdir / "signature.der").write_bytes(signature)
        proc = _run([openssl, "dgst", "-sha384", "-verify", str(tmpdir / "leaf.pub"),
                     "-signature", str(tmpdir / "signature.der"),
                     str(tmpdir / "signed.bin")], what="openssl dgst")
    if proc.returncode == 0:
        return True, "ECDSA-P384/SHA-384 signature verifies under the leaf certificate"
    return False, f"openssl dgst rejected the report signature: {_tail(proc.stderr or proc.stdout)}"


# --------------------------------------------------------------------------
# Trust anchors


@dataclass
class TrustBundle:
    name: str
    root_pem: bytes
    intermediates: list[bytes] = field(default_factory=list)
    product: str | None = None


def amd_roots_dir() -> Path:
    return Path(__file__).resolve().parent / "amd-roots"


def _load_pem(path: Path) -> tuple[bytes, bytes]:
    """Return (pem bytes, der bytes) for a single-certificate PEM file."""
    raw = path.read_bytes()
    blocks = _PEM_CERT.findall(raw)
    if len(blocks) != 1:
        raise SnpError(f"{path} must contain exactly one PEM certificate")
    return blocks[0] + b"\n", _der_from_pem(blocks[0])


def embedded_trust_bundles() -> list[TrustBundle]:
    """The pinned AMD ARK roots, with their ASK/VLEK-CA intermediates."""
    bundles: list[TrustBundle] = []
    base = amd_roots_dir()
    for product in sorted(AMD_ARK_SHA256):
        product_dir = base / product
        ark_pem, ark_der = _load_pem(product_dir / "ark.pem")
        fingerprint = sha256_hex(ark_der)
        if fingerprint != AMD_ARK_SHA256[product]:
            raise SnpError(
                f"embedded {product} ARK fingerprint is {fingerprint}, pinned value "
                f"is {AMD_ARK_SHA256[product]}; refusing to trust this checkout"
            )
        intermediates: list[bytes] = []
        for name in ("ask.pem", "vlek-ca.pem"):
            path = product_dir / name
            if path.is_file():
                pem, _ = _load_pem(path)
                intermediates.append(pem)
        bundles.append(TrustBundle(
            name=f"AMD {product} KDS root",
            root_pem=ark_pem,
            intermediates=intermediates,
            product=product,
        ))
    return bundles


def user_trust_bundles(paths: Iterable[str]) -> list[TrustBundle]:
    roots: list[bytes] = []
    for value in paths:
        path = Path(value)
        if not path.is_file():
            raise SnpSchemaError(f"--ark is not a file: {value}")
        raw = path.read_bytes()
        blocks = _PEM_CERT.findall(raw)
        if not blocks:
            raise SnpSchemaError(f"--ark {value} contains no PEM certificate")
        roots.extend(block + b"\n" for block in blocks)
    if not roots:
        return []
    product = None
    for block in roots:
        fingerprint = sha256_hex(_der_from_pem(block))
        for name, pinned in AMD_ARK_SHA256.items():
            if fingerprint == pinned:
                product = name
    return [TrustBundle(name="user-supplied root (--ark)",
                        root_pem=b"".join(roots), product=product)]


# --------------------------------------------------------------------------
# Policy


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise SnpSchemaError(message)


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def validate_snp_policy(obj: Any) -> dict[str, Any]:
    """Validate and normalize a ``wiz-snp-policy/v1`` object."""
    _expect(isinstance(obj, dict), "SNP policy must be a JSON object")
    unknown = set(obj) - POLICY_KEYS
    missing = {"schema"} - set(obj)
    _expect(not unknown, f"unknown SNP policy fields: {', '.join(sorted(unknown))}")
    _expect(not missing, "SNP policy needs a schema field")
    _expect(obj["schema"] == SNP_POLICY_SCHEMA,
            f"SNP policy schema must be {SNP_POLICY_SCHEMA!r}")

    policy = dict(obj)
    if "measurement" in policy:
        measurement = policy["measurement"]
        _expect(isinstance(measurement, str) and len(measurement) == 96
                and _HEX.match(measurement) is not None,
                "measurement must be 96 hex characters (48 bytes)")
        policy["measurement"] = measurement.lower()
    if "product" in policy:
        _expect(policy["product"] in ("Milan", "Genoa", "Turin"),
                "product must be Milan, Genoa or Turin")
    if "signing_key" in policy:
        _expect(policy["signing_key"] in ("VCEK", "VLEK", "either"),
                "signing_key must be VCEK, VLEK or either")
    if "vmpl" in policy:
        _expect(_is_int(policy["vmpl"]) and 0 <= policy["vmpl"] <= 3,
                "vmpl must be an integer 0..3")
    if "chip_id" in policy:
        chip = policy["chip_id"]
        _expect(isinstance(chip, str) and len(chip) == 128 and _HEX.match(chip) is not None,
                "chip_id must be 128 hex characters (64 bytes)")
        policy["chip_id"] = chip.lower()
    if "author_key_digest" in policy:
        digest = policy["author_key_digest"]
        _expect(isinstance(digest, str) and len(digest) == 96
                and _HEX.match(digest) is not None,
                "author_key_digest must be 96 hex characters (48 bytes)")
        policy["author_key_digest"] = digest.lower()
    if "tcb" in policy:
        tcb = policy["tcb"]
        _expect(isinstance(tcb, dict) and tcb, "tcb must be a non-empty object")
        unknown_tcb = set(tcb) - set(TCB_COMPONENTS)
        _expect(not unknown_tcb,
                f"unknown TCB components: {', '.join(sorted(unknown_tcb))}")
        for name, value in tcb.items():
            _expect(_is_int(value) and 0 <= value <= 255,
                    f"tcb.{name} must be an integer 0..255")
    if "policy" in policy:
        bits = policy["policy"]
        _expect(isinstance(bits, dict), "policy must be an object")
        unknown_bits = set(bits) - POLICY_BIT_KEYS
        _expect(not unknown_bits,
                f"unknown policy bit expectations: {', '.join(sorted(unknown_bits))}")
        for name, value in bits.items():
            _expect(isinstance(value, bool), f"policy.{name} must be a boolean")
        _expect(bits.get("debug", False) is False,
                "policy.debug must not be true: a debuggable guest is never accepted")
    if "valid_until" in policy:
        _expect(isinstance(policy["valid_until"], str)
                and policy["valid_until"].endswith("Z"),
                "valid_until must be an RFC 3339 UTC timestamp")
        _parse_utc(policy["valid_until"], "policy valid_until")
    return policy


def _parse_utc(value: str, what: str) -> datetime.datetime:
    try:
        return datetime.datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=datetime.timezone.utc)
    except ValueError:
        raise SnpSchemaError(f"{what} is not an RFC 3339 UTC timestamp: {value}") from None


# --------------------------------------------------------------------------
# Verification result


@dataclass
class SnpCheck:
    name: str
    status: str
    detail: str = ""


@dataclass
class SnpResult:
    checks: list[SnpCheck] = field(default_factory=list)
    info: dict[str, Any] | None = None

    def add(self, name: str, status: str, detail: str = "") -> None:
        self.checks.append(SnpCheck(name, status, detail))

    def failed(self) -> bool:
        return any(check.status == "fail" for check in self.checks)

    def incomplete(self) -> bool:
        return any(check.status == "skip" for check in self.checks)


def _select_leaf(
    entries: list[CertEntry],
    signing_key: str,
    openssl: str,
) -> tuple[CertEntry | None, list[CertEntry], CertEntry | None, str]:
    """Pick the report-signing leaf and the intermediates/evidence root."""
    for entry in entries:
        cert_dn(entry, openssl)

    by_guid = {entry.guid: entry for entry in entries if entry.guid is not None}
    wanted = {"VCEK": GUID_VCEK, "VLEK": GUID_VLEK}.get(signing_key)
    if wanted is not None and wanted in by_guid:
        leaf = by_guid[wanted]
    else:
        subjects = {entry.subject for entry in entries}
        issuers = {entry.issuer for entry in entries}
        candidates = [
            entry for entry in entries
            if entry.subject != entry.issuer and entry.subject not in issuers
        ]
        if signing_key == "VLEK":
            candidates = [e for e in candidates if "VLEK" in e.issuer]
        elif signing_key == "VCEK":
            candidates = [e for e in candidates if "VLEK" not in e.issuer]
        if len(candidates) != 1:
            found = ", ".join(e.subject or e.source for e in candidates) or "none"
            return None, [], None, (
                f"cannot identify the {signing_key} leaf certificate "
                f"(leaf candidates: {found})"
            )
        leaf = candidates[0]
    intermediates = [
        entry for entry in entries
        if entry is not leaf and entry.subject != entry.issuer
    ]
    roots = [entry for entry in entries if entry.subject == entry.issuer]
    evidence_root = roots[0] if len(roots) == 1 else None
    return leaf, intermediates, evidence_root, ""


def verify_report(
    *,
    report_path: Path | None = None,
    certs_path: Path | None = None,
    policy_path: Path | None = None,
    statement_digest: str,
    nonce: bytes | None,
    measurement_pin: str | None = None,
    product_pin: str | None = None,
    ark_paths: Sequence[str] = (),
    openssl: str | None = None,
    now: datetime.datetime | None = None,
) -> SnpResult:
    """Verify a raw SNP report and its certificate chain.

    Returns checks and the parsed report fields.  It never raises for bad
    evidence; a missing tool produces a ``skip`` (partial) result.
    """
    result = SnpResult()
    clock = now or datetime.datetime.now(datetime.timezone.utc)

    # 1. Policy (load first: conflicting CLI pins are a usage-shaped failure).
    policy: dict[str, Any] | None = None
    if policy_path is not None:
        try:
            raw_policy = policy_path.read_bytes()
            if not _JSON_START.match(raw_policy):
                raise SnpSchemaError("SNP policy is not JSON")
            loaded = load_policy_json(raw_policy)
            policy = validate_snp_policy(loaded)
            result.add("snp_policy_schema", "pass", SNP_POLICY_SCHEMA)
        except (OSError, SnpError) as exc:
            result.add("snp_policy_schema", "fail", str(exc))

    if measurement_pin and policy and policy.get("measurement") and \
            measurement_pin != policy["measurement"]:
        result.add("snp_measurement_pin", "fail",
                   f"--snp-measurement {measurement_pin} conflicts with the policy "
                   f"{policy['measurement']}")
    if product_pin and policy and policy.get("product") and \
            product_pin != policy["product"]:
        result.add("snp_product_pin", "fail",
                   f"--snp-product {product_pin} conflicts with the policy "
                   f"{policy['product']}")

    # 2. Report.
    if report_path is None:
        result.add("snp_report", "fail", "no SNP report supplied")
        return result
    try:
        raw = report_path.read_bytes()
        if _JSON_START.match(raw):
            raise SnpSchemaError(
                f"{report_path} looks like JSON; pass the raw 1184-byte "
                "ATTESTATION_REPORT (a guest's attestation.json is evidence, not a "
                "result)"
            )
        report_bytes, embedded_table = split_report_evidence(raw)
        report = parse_report(report_bytes)
    except (OSError, SnpError) as exc:
        result.add("snp_report", "fail", str(exc))
        return result

    result.info = {
        "version": report.version,
        "guest_svn": report.guest_svn,
        "policy": f"0x{report.policy:016x}",
        "policy_bits": {
            "abi_major": report.policy_bits.abi_major,
            "abi_minor": report.policy_bits.abi_minor,
            "smt": report.policy_bits.smt,
            "migration_agent": report.policy_bits.migration_agent,
            "debug": report.policy_bits.debug,
            "single_socket": report.policy_bits.single_socket,
            "cxl": report.policy_bits.cxl,
            "mem_aes_256_xts": report.policy_bits.mem_aes_256_xts,
            "rapl_dis": report.policy_bits.rapl_dis,
            "ciphertext_hiding_dram": report.policy_bits.ciphertext_hiding_dram,
            "page_swap_disable": report.policy_bits.page_swap_disable,
        },
        "family_id": report.family_id,
        "image_id": report.image_id,
        "vmpl": report.vmpl,
        "signature_algo": "ECDSA-P384/SHA-384",
        "platform_version": f"0x{report.platform_version:016x}",
        "platform_info": f"0x{report.platform_info:016x}",
        "signing_key": report.signing_key,
        "mask_chip_id": report.mask_chip_id,
        "author_key_en": report.author_key_en,
        "report_data": report.report_data_hex,
        "measurement": report.measurement_hex,
        "host_data": report.host_data,
        "id_key_digest": report.id_key_digest,
        "author_key_digest": report.author_key_digest,
        "report_id": report.report_id,
        "reported_tcb": f"0x{report.reported_tcb:016x}",
        "committed_tcb": f"0x{report.committed_tcb:016x}",
        "launch_tcb": f"0x{report.launch_tcb:016x}",
        "chip_id": report.chip_id_hex,
        "report_sha256": sha256_hex(report.raw),
        "cert_source": "report+certs" if certs_path is None else str(certs_path),
        "cert_chain": [],
    }
    result.add("snp_report", "pass",
               f"version {report.version}, guest SVN {report.guest_svn}, "
               f"VMPL {report.vmpl}, {report.signing_key} signature")

    # 3. REPORT_DATA binding.
    if nonce is None:
        result.add("snp_report_data", "skip",
                   "no verifier nonce; cannot check H(wiz-snp-v1||nonce||"
                   "statement_digest)")
    else:
        expected = report_data_value(nonce, statement_digest)
        if report.report_data == expected:
            result.add("snp_report_data", "pass",
                       "REPORT_DATA = H(wiz-snp-v1||nonce||statement_digest)||0^32")
        else:
            result.add("snp_report_data", "fail",
                       f"REPORT_DATA is {report.report_data_hex}, expected "
                       f"{expected.hex()}")

    # 4. Policy pins (measurement / product / policy bits / TCB / VMPL).
    effective_measurement = measurement_pin or (policy or {}).get("measurement")
    if effective_measurement:
        if report.measurement_hex == effective_measurement:
            result.add("snp_measurement", "pass", effective_measurement)
        else:
            result.add("snp_measurement", "fail",
                       f"MEASUREMENT is {report.measurement_hex}, expected "
                       f"{effective_measurement}")
    else:
        result.add("snp_measurement", "skip",
                   "no --snp-measurement and no policy measurement pin")

    expected_signing = (policy or {}).get("signing_key", "either")
    if expected_signing != "either" and report.signing_key != expected_signing:
        result.add("snp_signing_key", "fail",
                   f"report is signed by {report.signing_key}, policy expects "
                   f"{expected_signing}")
    elif report.signing_key == "none":
        result.add("snp_signing_key", "fail", "report is not signed")
    else:
        result.add("snp_signing_key", "pass", report.signing_key)

    bits = report.policy_bits
    if bits.debug:
        result.add("snp_policy_bits", "fail", "guest policy has debug enabled")
    else:
        expected_bits = (policy or {}).get("policy", {})
        problems: list[str] = []
        if bits.migration_agent and not expected_bits.get("migration_agent", False):
            problems.append("migration agent is enabled")
        expectation_map = {
            "smt": bits.smt,
            "single_socket": bits.single_socket,
            "cxl": bits.cxl,
            "mem_aes_256_xts": bits.mem_aes_256_xts,
            "rapl_dis": bits.rapl_dis,
            "ciphertext_hiding_dram": bits.ciphertext_hiding_dram,
            "page_swap_disable": bits.page_swap_disable,
        }
        for name, actual in expectation_map.items():
            if name in expected_bits and actual != expected_bits[name]:
                problems.append(f"{name} is {actual}, policy expects {expected_bits[name]}")
        if problems:
            result.add("snp_policy_bits", "fail", "; ".join(problems))
        else:
            migration = ("on (policy allows it)" if bits.migration_agent
                         else "off")
            result.add("snp_policy_bits", "pass",
                       f"debug=0, migration agent {migration}"
                       + ("" if not expected_bits else ", pinned bits match"))

    expected_vmpl = (policy or {}).get("vmpl", 0)
    if report.vmpl == expected_vmpl:
        result.add("snp_vmpl", "pass", str(expected_vmpl))
    else:
        result.add("snp_vmpl", "fail",
                   f"VMPL is {report.vmpl}, expected {expected_vmpl}")

    tcb_floor = (policy or {}).get("tcb")
    reported = report.tcb_bytes
    committed = report.committed_tcb_bytes
    tcb_problems: list[str] = []
    if report.reported_tcb == 0:
        tcb_problems.append("reported TCB is zero")
    for name, index in TCB_COMPONENTS.items():
        if tcb_floor and name in tcb_floor:
            floor = tcb_floor[name]
            if reported[index] < floor:
                tcb_problems.append(f"reported {name} is {reported[index]}, floor {floor}")
            if committed[index] < floor:
                tcb_problems.append(f"committed {name} is {committed[index]}, floor {floor}")
    if tcb_problems:
        result.add("snp_tcb", "fail", "; ".join(tcb_problems))
    elif not tcb_floor:
        result.add("snp_tcb", "skip", "no policy TCB floor")
    else:
        result.add("snp_tcb", "pass",
                   f"reported 0x{report.reported_tcb:016x}, "
                   f"committed 0x{report.committed_tcb:016x}, floors met")

    if policy and "chip_id" in policy:
        if report.mask_chip_id:
            result.add("snp_chip_id", "fail",
                       "policy pins CHIP_ID but the host masked it")
        elif report.chip_id_hex == policy["chip_id"]:
            result.add("snp_chip_id", "pass", policy["chip_id"])
        else:
            result.add("snp_chip_id", "fail",
                       f"CHIP_ID is {report.chip_id_hex}, expected {policy['chip_id']}")
    if policy and "author_key_digest" in policy:
        if not report.author_key_en:
            result.add("snp_author_key", "fail",
                       "policy pins AUTHOR_KEY_DIGEST but AUTHOR_KEY_EN is 0")
        elif report.author_key_digest == policy["author_key_digest"]:
            result.add("snp_author_key", "pass", policy["author_key_digest"])
        else:
            result.add("snp_author_key", "fail",
                       f"AUTHOR_KEY_DIGEST is {report.author_key_digest}, expected "
                       f"{policy['author_key_digest']}")

    if policy is not None and "valid_until" in policy:
        if clock > _parse_utc(policy["valid_until"], "policy valid_until"):
            result.add("snp_policy_valid_until", "fail",
                       f"SNP policy expired at {policy['valid_until']}")
        else:
            result.add("snp_policy_valid_until", "pass", policy["valid_until"])

    # 5. Certificate evidence, chain and signature.
    openssl_path = find_openssl(openssl)
    if not usable_openssl(openssl_path):
        result.add("snp_cert_chain", "skip",
                   "openssl not found; install openssl or pass --openssl")
        result.add("snp_cert_expiry", "skip", "openssl not found")
        result.add("snp_signature", "skip", "openssl not found")
        return result

    try:
        if certs_path is not None:
            entries = read_cert_evidence(certs_path)
            result.info["cert_source"] = str(certs_path)
        elif embedded_table:
            entries = parse_cert_table(embedded_table)
            result.info["cert_source"] = "appended to the report"
        else:
            raise SnpSchemaError(
                "no certificate table after the report and no --snp-certs; "
                "supply the VCEK/VLEK certificate chain"
            )
        for entry in entries:
            cert_dn(entry, openssl_path)
    except (OSError, SnpError) as exc:
        result.add("snp_certs", "fail", str(exc))
        return result

    leaf, intermediates, evidence_root, select_error = _select_leaf(
        entries, report.signing_key, openssl_path)
    if leaf is None:
        result.add("snp_certs", "fail", select_error)
        return result
    result.add("snp_certs", "pass", f"{len(entries)} certificate(s)")
    result.info["cert_chain"] = [leaf.subject] + [e.subject for e in intermediates]

    # The evidence ARK is never trusted as a root, but it must match a pinned
    # root when present.
    if evidence_root is not None:
        evidence_fp = sha256_hex(evidence_root.der)
        if ark_paths:
            expected_fps = set()
            for bundle in user_trust_bundles(ark_paths):
                expected_fps.update(
                    sha256_hex(_der_from_pem(block))
                    for block in _PEM_CERT.findall(bundle.root_pem)
                )
            if evidence_fp in expected_fps:
                result.add("snp_ark", "pass", evidence_fp)
            else:
                result.add("snp_ark", "fail",
                           "evidence ARK does not match the --ark trust root")
        elif evidence_fp in AMD_ARK_SHA256.values():
            result.add("snp_ark", "pass", evidence_fp)
        else:
            result.add("snp_ark", "fail",
                       f"evidence ARK {evidence_fp} is not a pinned AMD root")

    bundles = user_trust_bundles(ark_paths) if ark_paths else embedded_trust_bundles()
    if not bundles:
        result.add("snp_cert_chain", "skip", "no trust root")
        result.add("snp_cert_expiry", "skip", "no trust root")
        result.add("snp_signature", "skip", "no leaf certificate")
        return result

    failures: list[str] = []
    chosen: TrustBundle | None = None
    verified_against: list[str] = []
    for bundle in bundles:
        try:
            ok, detail = _openssl_chain(leaf, intermediates, bundle, openssl_path, clock)
        except SnpIncomplete as exc:
            result.add("snp_cert_chain", "skip", str(exc))
            result.add("snp_cert_expiry", "skip", str(exc))
            result.add("snp_signature", "skip", str(exc))
            return result
        if ok:
            if chosen is None:
                chosen = bundle
            verified_against.append(bundle.name)
        else:
            failures.append(f"{bundle.name}: {detail}")
    if chosen is not None:
        result.info["product"] = chosen.product
        extra = (f" (also {', '.join(verified_against[1:])})"
                 if len(verified_against) > 1 else "")
        result.add("snp_cert_chain", "pass",
                   f"{leaf.subject} -> {chosen.name}{extra}")
    else:
        result.add("snp_cert_chain", "fail",
                   "no pinned root verified the certificate chain: "
                   + " | ".join(failures[:3]))

    expected_product = product_pin or (policy or {}).get("product")
    actual_product = result.info.get("product")
    if expected_product:
        if actual_product is None:
            result.add("snp_product", "fail",
                       f"cannot determine the product from the certificate chain, "
                       f"policy expects {expected_product}")
        elif actual_product != expected_product:
            result.add("snp_product", "fail",
                       f"chain product is {actual_product}, expected {expected_product}")
        else:
            result.add("snp_product", "pass", expected_product)

    # Validity at the verifier's clock (independent of openssl verify's own
    # -attime, so an expired chain reports a precise check even when openssl
    # already rejected it).
    problems = []
    checked: list[CertEntry] = [leaf, *intermediates]
    if evidence_root is not None:
        checked.append(evidence_root)
    if chosen is not None:
        for block in _PEM_CERT.findall(chosen.root_pem):
            checked.append(CertEntry(der=_der_from_pem(block), source=chosen.name,
                                     subject=chosen.name))
    for entry in checked:
        try:
            not_before, not_after = cert_validity(entry, openssl_path)
        except SnpIncomplete as exc:
            result.add("snp_cert_expiry", "skip", str(exc))
            return result
        except SnpError as exc:
            problems.append(str(exc))
            continue
        if clock < not_before:
            problems.append(f"{entry.subject} is not valid before {not_before.isoformat()}")
        if clock > not_after:
            problems.append(f"{entry.subject} expired at {not_after.isoformat()}")
    if problems:
        result.add("snp_cert_expiry", "fail", "; ".join(problems))
    else:
        result.add("snp_cert_expiry", "pass",
                   f"chain valid at {clock.strftime('%Y-%m-%dT%H:%M:%SZ')}")

    try:
        ok, detail = report_signature(report, leaf, openssl_path)
    except SnpIncomplete as exc:
        result.add("snp_signature", "skip", str(exc))
    except SnpError as exc:
        result.add("snp_signature", "fail", str(exc))
    else:
        result.add("snp_signature", "pass" if ok else "fail", detail)

    return result


def _openssl_chain(
    leaf: CertEntry,
    intermediates: list[CertEntry],
    bundle: TrustBundle,
    openssl: str,
    clock: datetime.datetime,
) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory(prefix="wiz-snp-chain-") as tmp:
        tmpdir = Path(tmp)
        leaf_path = tmpdir / "leaf.pem"
        leaf_path.write_bytes(_pem_from_der(leaf.der))
        root_path = tmpdir / "root.pem"
        root_path.write_bytes(bundle.root_pem)
        intermediate_pems = [_pem_from_der(entry.der) for entry in intermediates]
        intermediate_pems.extend(bundle.intermediates)
        cmd = [openssl, "verify", "-CAfile", str(root_path)]
        if intermediate_pems:
            untrusted = tmpdir / "untrusted.pem"
            untrusted.write_bytes(b"".join(intermediate_pems))
            cmd += ["-untrusted", str(untrusted)]
        cmd += ["-attime", str(int(clock.timestamp())), str(leaf_path)]
        proc = _run(cmd, what="openssl verify")
    if proc.returncode == 0:
        return True, proc.stdout.strip()
    return False, _tail(proc.stdout or proc.stderr)
