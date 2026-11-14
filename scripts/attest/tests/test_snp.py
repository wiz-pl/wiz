#!/usr/bin/env python3
"""Synthetic AMD SEV-SNP fixtures and verifier tests.

Nothing here uses SNP hardware, an AMD private key or the network.  Each test
class generates a throwaway P-384 root, ASK and VCEK leaf with ``openssl``,
signs a synthetic 1184-byte ATTESTATION_REPORT with the leaf, and appends an
ABI certificate table.  The embedded AMD KDS roots are only checked for
integrity; they never sign a fixture.

The end-to-end tests drive ``wiz-verify`` with the E1 manifest/quote fixture
from ``test_attest`` so the E1 and E2 bindings share one statement digest.
"""

from __future__ import annotations

import datetime
import hashlib
import json
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
import uuid
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import snp  # noqa: E402
import wiz_attest as wa  # noqa: E402
from test_attest import Fixture, run_verify, write_stub  # noqa: E402

MAIN_INDEX = {
    "boot_loader": 0,
    "tee": 1,
    "snp": 3,
    "microcode": 4,
    "spl": 6,
}


# --------------------------------------------------------------------------
# A throwaway certificate chain


class SyntheticChain:
    """root -> ASK -> VCEK leaf, plus root -> VLEK CA -> VLEK leaf."""

    def __init__(self, openssl: str, directory: Path, name: str = "chain"):
        self.openssl = openssl
        self.dir = directory / name
        self.dir.mkdir(parents=True, exist_ok=True)
        self.root_key = self.dir / "root.key"
        self.root = self.dir / "root.pem"
        self.ask_key = self.dir / "ask.key"
        self.ask = self.dir / "ask.pem"
        self.vcek_key = self.dir / "vcek.key"
        self.vcek = self.dir / "vcek.pem"
        self.vlek_ca_key = self.dir / "vlek-ca.key"
        self.vlek_ca = self.dir / "vlek-ca.pem"
        self.vlek_key = self.dir / "vlek.key"
        self.vlek = self.dir / "vlek.pem"
        self._keygen(self.root_key)
        self._self_signed(self.root_key, self.root, "Wiz Test ARK", ca=True)
        self._keygen(self.ask_key)
        self._issue(self.ask_key, self.ask, "Wiz Test ASK", self.root,
                    self.root_key, ca=True)
        self._keygen(self.vcek_key)
        self._issue(self.vcek_key, self.vcek, "Wiz Test VCEK", self.ask,
                    self.ask_key, ca=False)
        self._keygen(self.vlek_ca_key)
        self._issue(self.vlek_ca_key, self.vlek_ca, "Wiz Test VLEK CA", self.root,
                    self.root_key, ca=True)
        self._keygen(self.vlek_key)
        self._issue(self.vlek_key, self.vlek, "Wiz Test VLEK", self.vlek_ca,
                    self.vlek_ca_key, ca=False)

    def run(self, cmd: list[str]) -> subprocess.CompletedProcess[str]:
        proc = subprocess.run([self.openssl, *cmd], cwd=self.dir,
                              capture_output=True, text=True, timeout=120)
        if proc.returncode != 0:
            raise AssertionError(f"openssl {cmd[0]} failed: {proc.stderr or proc.stdout}")
        return proc

    def _keygen(self, key: Path) -> None:
        self.run(["genpkey", "-algorithm", "EC", "-pkeyopt",
                  "ec_paramgen_curve:P-384", "-out", str(key)])

    def _self_signed(self, key: Path, cert: Path, cn: str, *, ca: bool) -> None:
        constraints = "critical,CA:TRUE" if ca else "critical,CA:FALSE"
        usage = "critical,keyCertSign,cRLSign" if ca else "critical,digitalSignature"
        self.run(["req", "-new", "-x509", "-key", str(key), "-out", str(cert),
                  "-days", "3650", "-subj", f"/CN={cn}/O=Wiz Test",
                  "-addext", f"basicConstraints={constraints}",
                  "-addext", f"keyUsage={usage}"])

    def _issue(self, key: Path, cert: Path, cn: str, issuer_cert: Path,
               issuer_key: Path, *, ca: bool) -> None:
        csr = self.dir / f"{cert.stem}.csr"
        self.run(["req", "-new", "-key", str(key), "-out", str(csr),
                  "-subj", f"/CN={cn}/O=Wiz Test"])
        ext = self.dir / f"{cert.stem}.ext"
        if ca:
            ext.write_text("basicConstraints=critical,CA:TRUE\n"
                           "keyUsage=critical,keyCertSign,cRLSign\n"
                           "subjectKeyIdentifier=hash\n"
                           "authorityKeyIdentifier=keyid\n", encoding="utf-8")
        else:
            ext.write_text("basicConstraints=critical,CA:FALSE\n"
                           "keyUsage=critical,digitalSignature\n"
                           "extendedKeyUsage=codeSigning\n"
                           "subjectKeyIdentifier=hash\n"
                           "authorityKeyIdentifier=keyid\n", encoding="utf-8")
        self.run(["x509", "-req", "-in", str(csr), "-CA", str(issuer_cert),
                  "-CAkey", str(issuer_key), "-CAcreateserial", "-out", str(cert),
                  "-days", "3650", "-extfile", str(ext)])

    def der(self, cert: Path) -> bytes:
        out = self.dir / f"{cert.stem}.der"
        if not out.exists():
            self.run(["x509", "-in", str(cert), "-outform", "DER", "-out", str(out)])
        return out.read_bytes()

    def sign(self, key: Path, data: bytes) -> bytes:
        inp = self.dir / "to-sign.bin"
        out = self.dir / "signature.der"
        inp.write_bytes(data)
        self.run(["dgst", "-sha384", "-sign", str(key), "-out", str(out), str(inp)])
        return out.read_bytes()


# --------------------------------------------------------------------------
# Synthetic report + certificate table


def _read_der_len(data: bytes, pos: int) -> tuple[int, int]:
    first = data[pos]
    pos += 1
    if first < 0x80:
        return first, pos
    count = first & 0x7F
    return int.from_bytes(data[pos:pos + count], "big"), pos + count


def der_to_amd_rs(der: bytes) -> tuple[bytes, bytes]:
    assert der[0] == 0x30, "signature is not a DER SEQUENCE"
    length, pos = _read_der_len(der, 1)
    assert pos + length == len(der)
    assert der[pos] == 0x02
    size, pos = _read_der_len(der, pos + 1)
    r = int.from_bytes(der[pos:pos + size], "big")
    pos += size
    assert der[pos] == 0x02
    size, pos = _read_der_len(der, pos + 1)
    s = int.from_bytes(der[pos:pos + size], "big")
    return r.to_bytes(72, "little"), s.to_bytes(72, "little")


def tcb_value(components: dict[str, int]) -> int:
    raw = bytearray(8)
    for name, value in components.items():
        raw[MAIN_INDEX[name]] = value
    return int.from_bytes(raw, "little")


def make_report(
    chain: SyntheticChain,
    *,
    leaf_key: Path,
    report_data: bytes,
    measurement: bytes = b"\xab" * 48,
    version: int = 3,
    debug: bool = False,
    migration_agent: bool = False,
    smt: bool = True,
    signing_key: str = "VCEK",
    vmpl: int = 0,
    reported_tcb: dict[str, int] | None = None,
    committed_tcb: dict[str, int] | None = None,
    chip_id: bytes = b"\xcd" * 64,
    author_key: bytes = bytes(48),
    tamper_after_signing: bool = False,
) -> bytes:
    raw = bytearray(snp.REPORT_SIZE)
    struct.pack_into("<I", raw, 0x00, version)
    struct.pack_into("<I", raw, 0x04, 7)  # guest SVN
    policy = 1 << 17
    if smt:
        policy |= 1 << 16
    if migration_agent:
        policy |= 1 << 18
    if debug:
        policy |= 1 << 19
    struct.pack_into("<Q", raw, 0x08, policy)
    raw[0x10:0x20] = b"\x11" * 16  # family id
    raw[0x20:0x30] = b"\x22" * 16  # image id
    struct.pack_into("<I", raw, 0x30, vmpl)
    struct.pack_into("<I", raw, 0x34, snp.SIGN_ECDSA_P384_SHA384)
    struct.pack_into("<Q", raw, 0x38, 0x0000000000000001)  # platform version
    struct.pack_into("<Q", raw, 0x40, 0x01)  # SMT enabled
    code = {"VCEK": 0, "VLEK": 1}[signing_key]
    struct.pack_into("<I", raw, 0x48, code << 2)
    raw[0x50:0x90] = report_data
    raw[0x90:0xC0] = measurement
    raw[0xC0:0xE0] = b"\x33" * 32
    raw[0xE0:0x110] = b"\x44" * 48
    raw[0x110:0x140] = author_key
    raw[0x140:0x160] = b"\x55" * 32
    raw[0x160:0x180] = b"\x66" * 32
    reported = reported_tcb or {
        "boot_loader": 3, "tee": 0, "snp": 8, "microcode": 115, "spl": 0,
    }
    committed = committed_tcb or dict(reported)
    struct.pack_into("<Q", raw, 0x180, tcb_value(reported))
    if version >= 3:
        raw[0x188] = 0x19
        raw[0x189] = 0x01
        raw[0x18A] = 0x01
    raw[0x1A0:0x1E0] = chip_id
    struct.pack_into("<Q", raw, 0x1E0, tcb_value(committed))
    struct.pack_into("<Q", raw, 0x1F0, tcb_value(reported))
    signature = chain.sign(leaf_key, bytes(raw[:snp.SIGNED_SIZE]))
    r, s = der_to_amd_rs(signature)
    raw[0x2A0:0x2E8] = r
    raw[0x2E8:0x330] = s
    if tamper_after_signing:
        raw[0x04] ^= 0xFF
    return bytes(raw)


def cert_table(entries: list[tuple[uuid.UUID, bytes]]) -> bytes:
    header = (len(entries) + 1) * 24
    offsets: list[tuple[uuid.UUID, int, int]] = []
    cursor = header
    for guid, der in entries:
        offsets.append((guid, cursor, len(der)))
        cursor += len(der)
    out = bytearray(cursor)
    for i, (guid, offset, length) in enumerate(offsets):
        out[i * 24:i * 24 + 16] = guid.bytes_le
        struct.pack_into("<II", out, i * 24 + 16, offset, length)
    cursor = header
    for _, der in entries:
        out[cursor:cursor + len(der)] = der
        cursor += len(der)
    return bytes(out)


# --------------------------------------------------------------------------
# Fixture bundles


class SnpFixture:
    def __init__(self, openssl: str, chain: SyntheticChain, directory: Path):
        self.openssl = openssl
        self.chain = chain
        self.dir = directory
        self.statement_digest = hashlib.sha256(b"statement").hexdigest()
        self.nonce = bytes.fromhex("11" * 32)
        self.measurement = b"\xab" * 48
        self.report_data = snp.report_data_value(self.nonce, self.statement_digest)
        self.report = make_report(
            chain,
            leaf_key=chain.vcek_key,
            report_data=self.report_data,
            measurement=self.measurement,
        )
        self.table = cert_table([
            (snp.GUID_VCEK, chain.der(chain.vcek)),
            (snp.GUID_ASK, chain.der(chain.ask)),
            (snp.GUID_ARK, chain.der(chain.root)),
        ])
        self.report_path = self.dir / "report.bin"
        self.report_path.write_bytes(self.report + self.table)
        self.cert_dir = self.dir / "certs"
        self.cert_dir.mkdir(exist_ok=True)
        for name, path in (("vcek.pem", chain.vcek), ("ask.pem", chain.ask),
                           ("ark.pem", chain.root)):
            shutil.copyfile(path, self.cert_dir / name)
        self.policy = {
            "schema": snp.SNP_POLICY_SCHEMA,
            "measurement": self.measurement.hex(),
            "signing_key": "VCEK",
            "vmpl": 0,
            "tcb": {"boot_loader": 3, "tee": 0, "snp": 8,
                    "microcode": 115, "spl": 0},
            "policy": {"migration_agent": False, "smt": True},
            "valid_until": "2035-01-01T00:00:00Z",
        }
        self.policy_path = self.dir / "snp-policy.json"
        self.write_policy()

    def write_policy(self, policy: dict | None = None) -> None:
        if policy is not None:
            self.policy = policy
        self.policy_path.write_text(json.dumps(self.policy), encoding="utf-8")

    def verify(self, *, policy_path: Path | None = None,
               report_path: Path | None = None,
               certs_path: Path | None = None,
               ark: Path | None = None,
               now: str | None = None,
               statement_digest: str | None = None,
               nonce: bytes | None = None,
               measurement_pin: str | None = None,
               product_pin: str | None = None) -> snp.SnpResult:
        return snp.verify_report(
            report_path=report_path or self.report_path,
            certs_path=certs_path,
            policy_path=policy_path if policy_path is not None else self.policy_path,
            statement_digest=statement_digest or self.statement_digest,
            nonce=self.nonce if nonce is None else nonce,
            measurement_pin=measurement_pin,
            product_pin=product_pin,
            ark_paths=[str(ark or self.chain.root)],
            openssl=self.openssl,
            now=datetime.datetime.strptime(now, "%Y-%m-%dT%H:%M:%SZ").replace(
                tzinfo=datetime.timezone.utc) if now else None,
        )


def checks(result: snp.SnpResult) -> dict[str, snp.SnpCheck]:
    return {check.name: check for check in result.checks}


# --------------------------------------------------------------------------
# Tests


class ParserTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.openssl = snp.find_openssl()
        if not cls.openssl:
            raise unittest.SkipTest("openssl is not available")
        cls.tmp = Path(tempfile.mkdtemp(prefix="wiz-snp-parser-"))
        cls.chain = SyntheticChain(cls.openssl, cls.tmp)

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_report_round_trip(self):
        raw = make_report(self.chain, leaf_key=self.chain.vcek_key,
                          report_data=b"\x01" * 64)
        report = snp.parse_report(raw)
        self.assertEqual(report.version, 3)
        self.assertEqual(report.guest_svn, 7)
        self.assertEqual(report.signing_key, "VCEK")
        self.assertTrue(report.policy_bits.smt)
        self.assertFalse(report.policy_bits.debug)
        self.assertEqual(report.measurement, b"\xab" * 48)
        self.assertEqual(len(report.signed_bytes), snp.SIGNED_SIZE)
        self.assertEqual(report.cpuid_family, 0x19)

    def test_short_report_rejected(self):
        with self.assertRaises(snp.SnpSchemaError):
            snp.parse_report(bytes(100))

    def test_wrong_version_rejected(self):
        raw = bytearray(make_report(self.chain, leaf_key=self.chain.vcek_key,
                                    report_data=b"\x01" * 64))
        struct.pack_into("<I", raw, 0x00, 9)
        with self.assertRaisesRegex(snp.SnpSchemaError, "version"):
            snp.parse_report(bytes(raw))

    def test_wrong_signature_algo_rejected(self):
        raw = bytearray(make_report(self.chain, leaf_key=self.chain.vcek_key,
                                    report_data=b"\x01" * 64))
        struct.pack_into("<I", raw, 0x34, 2)
        with self.assertRaisesRegex(snp.SnpSchemaError, "signature algorithm"):
            snp.parse_report(bytes(raw))

    def test_reserved_policy_bit_rejected(self):
        raw = bytearray(make_report(self.chain, leaf_key=self.chain.vcek_key,
                                    report_data=b"\x01" * 64))
        struct.pack_into("<Q", raw, 0x08, 1 << 16)  # bit 17 not set
        with self.assertRaisesRegex(snp.SnpSchemaError, "reserved"):
            snp.parse_report(bytes(raw))

    def test_report_data_formula(self):
        nonce = bytes.fromhex("ab" * 32)
        digest = hashlib.sha256(b"x").hexdigest()
        value = snp.report_data_value(nonce, digest)
        self.assertEqual(len(value), 64)
        self.assertEqual(value[:32], hashlib.sha256(
            b"wiz-snp-v1" + nonce + bytes.fromhex(digest)).digest())
        self.assertEqual(value[32:], bytes(32))

    def test_cert_table_round_trip(self):
        entries = [(snp.GUID_VCEK, self.chain.der(self.chain.vcek)),
                   (snp.GUID_ASK, self.chain.der(self.chain.ask)),
                   (snp.GUID_ARK, self.chain.der(self.chain.root))]
        parsed = snp.parse_cert_table(cert_table(entries))
        self.assertEqual([e.guid for e in parsed], [g for g, _ in entries])
        self.assertEqual(parsed[0].der, entries[0][1])

    def test_cert_table_out_of_range_rejected(self):
        bad = bytearray(cert_table([(snp.GUID_VCEK, b"\x30\x00")]))
        struct.pack_into("<II", bad, 16, 49, 4)
        with self.assertRaisesRegex(snp.SnpSchemaError, "out-of-range"):
            snp.parse_cert_table(bytes(bad))

    def test_zero_padded_page_is_not_a_table(self):
        report, trailing = snp.split_report_evidence(
            make_report(self.chain, leaf_key=self.chain.vcek_key,
                        report_data=b"\x01" * 64) + bytes(4096 - snp.REPORT_SIZE))
        self.assertEqual(trailing, b"")
        self.assertEqual(len(report), snp.REPORT_SIZE)


class PolicyTests(unittest.TestCase):
    def base(self) -> dict:
        return {
            "schema": snp.SNP_POLICY_SCHEMA,
            "measurement": "ab" * 48,
            "tcb": {"snp": 8},
            "policy": {"smt": True},
        }

    def test_valid_policy(self):
        policy = snp.validate_snp_policy(self.base())
        self.assertEqual(policy["measurement"], "ab" * 48)

    def test_unknown_field_rejected(self):
        policy = self.base()
        policy["extra"] = 1
        with self.assertRaisesRegex(snp.SnpSchemaError, "unknown"):
            snp.validate_snp_policy(policy)

    def test_bad_measurement_rejected(self):
        policy = self.base()
        policy["measurement"] = "ab"
        with self.assertRaisesRegex(snp.SnpSchemaError, "measurement"):
            snp.validate_snp_policy(policy)

    def test_debug_policy_rejected(self):
        policy = self.base()
        policy["policy"] = {"debug": True}
        with self.assertRaisesRegex(snp.SnpSchemaError, "debug"):
            snp.validate_snp_policy(policy)

    def test_unknown_tcb_component_rejected(self):
        policy = self.base()
        policy["tcb"] = {"secrets": 1}
        with self.assertRaisesRegex(snp.SnpSchemaError, "TCB"):
            snp.validate_snp_policy(policy)

    def test_duplicate_json_key_rejected(self):
        with self.assertRaisesRegex(snp.SnpSchemaError, "duplicate"):
            snp.load_policy_json(
                b'{"schema": "wiz-snp-policy/v1", "schema": "wiz-snp-policy/v1"}')

    def test_non_finite_json_rejected(self):
        with self.assertRaisesRegex(snp.SnpSchemaError, "non-finite"):
            snp.load_policy_json(b'{"schema": NaN}')


class EmbeddedRootTests(unittest.TestCase):
    def test_fingerprints_are_pinned(self):
        bundles = snp.embedded_trust_bundles()
        self.assertEqual({b.product for b in bundles}, set(snp.AMD_ARK_SHA256))
        for bundle in bundles:
            der = snp._der_from_pem(snp._PEM_CERT.findall(bundle.root_pem)[0])
            self.assertEqual(hashlib.sha256(der).hexdigest(),
                             snp.AMD_ARK_SHA256[bundle.product])
            self.assertTrue(bundle.intermediates)

    def test_corrupt_root_is_refused(self):
        orig = snp.AMD_ARK_SHA256["Milan"]
        try:
            snp.AMD_ARK_SHA256["Milan"] = "00" * 32
            with self.assertRaisesRegex(snp.SnpError, "refusing"):
                snp.embedded_trust_bundles()
        finally:
            snp.AMD_ARK_SHA256["Milan"] = orig

    def test_user_supplied_amd_root_keeps_its_product(self):
        path = snp.amd_roots_dir() / "Genoa" / "ark.pem"
        bundle = snp.user_trust_bundles([str(path)])[0]
        self.assertEqual(bundle.product, "Genoa")

    def test_embedded_intermediates_chain_to_ark(self):
        openssl = snp.find_openssl()
        if not openssl:
            self.skipTest("openssl is not available")
        with tempfile.TemporaryDirectory(prefix="wiz-snp-roots-") as tmp:
            root = Path(tmp) / "ark.pem"
            for bundle in snp.embedded_trust_bundles():
                root.write_bytes(bundle.root_pem)
                for index, intermediate in enumerate(bundle.intermediates):
                    path = Path(tmp) / f"int-{bundle.product}-{index}.pem"
                    path.write_bytes(intermediate)
                    proc = subprocess.run(
                        [openssl, "verify", "-CAfile", str(root), str(path)],
                        capture_output=True, text=True, timeout=120,
                    )
                    self.assertEqual(proc.returncode, 0,
                                     f"{bundle.product} intermediate {index}: "
                                     f"{proc.stdout or proc.stderr}")


class VerifyReportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.openssl = snp.find_openssl()
        if not cls.openssl:
            raise unittest.SkipTest("openssl is not available")
        cls.tmp = Path(tempfile.mkdtemp(prefix="wiz-snp-verify-"))
        cls.chain = SyntheticChain(cls.openssl, cls.tmp)
        cls.other = SyntheticChain(cls.openssl, cls.tmp, name="other")

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def setUp(self) -> None:
        self.case = Path(tempfile.mkdtemp(prefix="wiz-snp-case-", dir=self.tmp))
        self.fx = SnpFixture(self.openssl, self.chain, self.case)

    def test_full_verification(self):
        result = self.fx.verify()
        self.assertFalse(result.failed(), result.checks)
        self.assertFalse(result.incomplete(), result.checks)
        self.assertEqual(checks(result)["snp_report_data"].status, "pass")
        self.assertEqual(checks(result)["snp_signature"].status, "pass")
        self.assertEqual(checks(result)["snp_measurement"].status, "pass")
        self.assertEqual(checks(result)["snp_tcb"].status, "pass")
        self.assertEqual(result.info["report_data"], self.fx.report_data.hex())

    def test_certs_directory(self):
        result = self.fx.verify(certs_path=self.fx.cert_dir)
        self.assertFalse(result.failed(), result.checks)
        self.assertEqual(checks(result)["snp_certs"].status, "pass")

    def test_wrong_report_data(self):
        wrong = snp.report_data_value(self.fx.nonce, "00" * 32)
        report = make_report(self.chain, leaf_key=self.chain.vcek_key,
                             report_data=wrong, measurement=self.fx.measurement)
        path = self.case / "wrong-data.bin"
        path.write_bytes(report + self.fx.table)
        result = self.fx.verify(report_path=path)
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_report_data"].status, "fail")

    def test_bad_signature(self):
        report = make_report(self.chain, leaf_key=self.chain.vcek_key,
                             report_data=self.fx.report_data,
                             measurement=self.fx.measurement,
                             tamper_after_signing=True)
        path = self.case / "bad-sig.bin"
        path.write_bytes(report + self.fx.table)
        result = self.fx.verify(report_path=path)
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_signature"].status, "fail")

    def test_wrong_chain(self):
        # The report is signed by the other chain's leaf, but the evidence
        # carries the real ARK and the other ASK.  The ARK pin passes and the
        # chain fails.
        report = make_report(self.other, leaf_key=self.other.vcek_key,
                             report_data=self.fx.report_data,
                             measurement=self.fx.measurement)
        table = cert_table([
            (snp.GUID_VCEK, self.other.der(self.other.vcek)),
            (snp.GUID_ASK, self.other.der(self.other.ask)),
            (snp.GUID_ARK, self.chain.der(self.chain.root)),
        ])
        path = self.case / "wrong-chain.bin"
        path.write_bytes(report + table)
        result = self.fx.verify(report_path=path)
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_cert_chain"].status, "fail")
        self.assertEqual(checks(result)["snp_signature"].status, "pass")

    def test_wrong_trust_root(self):
        result = self.fx.verify(ark=self.other.root)
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_cert_chain"].status, "fail")

    def test_expired_certificates(self):
        result = self.fx.verify(now="2050-01-01T00:00:00Z")
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_cert_expiry"].status, "fail")
        self.assertIn("expired", checks(result)["snp_cert_expiry"].detail)

    def test_tcb_floor_mismatch(self):
        policy = dict(self.fx.policy)
        policy["tcb"] = {"microcode": 200}
        self.fx.write_policy(policy)
        result = self.fx.verify()
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_tcb"].status, "fail")

    def test_measurement_mismatch(self):
        policy = dict(self.fx.policy)
        policy["measurement"] = "00" * 48
        self.fx.write_policy(policy)
        result = self.fx.verify()
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_measurement"].status, "fail")

    def test_debug_guest_rejected(self):
        report = make_report(self.chain, leaf_key=self.chain.vcek_key,
                             report_data=self.fx.report_data,
                             measurement=self.fx.measurement, debug=True)
        path = self.case / "debug.bin"
        path.write_bytes(report + self.fx.table)
        result = self.fx.verify(report_path=path)
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_policy_bits"].status, "fail")

    def test_wrong_signing_key_rejected(self):
        policy = dict(self.fx.policy)
        policy["signing_key"] = "VLEK"
        self.fx.write_policy(policy)
        result = self.fx.verify()
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_signing_key"].status, "fail")

    def test_vlek_chain(self):
        report = make_report(self.chain, leaf_key=self.chain.vlek_key,
                             report_data=self.fx.report_data,
                             measurement=self.fx.measurement, signing_key="VLEK")
        table = cert_table([
            (snp.GUID_VLEK, self.chain.der(self.chain.vlek)),
            (snp.GUID_ASK, self.chain.der(self.chain.vlek_ca)),
            (snp.GUID_ARK, self.chain.der(self.chain.root)),
        ])
        path = self.case / "vlek.bin"
        path.write_bytes(report + table)
        policy = dict(self.fx.policy)
        policy["signing_key"] = "VLEK"
        self.fx.write_policy(policy)
        result = self.fx.verify(report_path=path)
        self.assertFalse(result.failed(), result.checks)
        self.assertFalse(result.incomplete(), result.checks)
        self.assertEqual(result.info["signing_key"], "VLEK")
        self.assertEqual(checks(result)["snp_cert_chain"].status, "pass")

    def test_missing_openssl_is_partial(self):
        result = snp.verify_report(
            report_path=self.fx.report_path,
            policy_path=self.fx.policy_path,
            statement_digest=self.fx.statement_digest,
            nonce=self.fx.nonce,
            openssl="/definitely/not/openssl",
        )
        self.assertTrue(result.incomplete())
        self.assertEqual(checks(result)["snp_cert_chain"].status, "skip")

    def test_json_evidence_rejected(self):
        path = self.case / "attestation.json"
        path.write_text('{"snp": {"available": true}}', encoding="utf-8")
        result = self.fx.verify(report_path=path)
        self.assertTrue(result.failed())
        self.assertIn("JSON", checks(result)["snp_report"].detail)

    def test_missing_certificate_chain_fails(self):
        path = self.case / "report-only.bin"
        path.write_bytes(self.fx.report)
        result = snp.verify_report(
            report_path=path,
            policy_path=self.fx.policy_path,
            statement_digest=self.fx.statement_digest,
            nonce=self.fx.nonce,
            openssl=self.openssl,
        )
        self.assertTrue(result.failed())
        self.assertEqual(checks(result)["snp_certs"].status, "fail")


class WizVerifyIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.openssl = snp.find_openssl()
        if not cls.openssl:
            raise unittest.SkipTest("openssl is not available")
        cls.tmp = Path(tempfile.mkdtemp(prefix="wiz-snp-e2e-"))
        cls.chain = SyntheticChain(cls.openssl, cls.tmp)

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def setUp(self) -> None:
        self.fx = Fixture()
        case = Path(tempfile.mkdtemp(prefix="wiz-snp-e2e-case-", dir=self.tmp))
        self.case = case
        self.stub = write_stub(case)
        # Bind the report to the E1 statement digest and the verifier nonce.
        self.report_data = snp.report_data_value(
            bytes.fromhex(self.fx.nonce), self.fx.statement_digest())
        self.report = make_report(self.chain, leaf_key=self.chain.vcek_key,
                                  report_data=self.report_data)
        self.table = cert_table([
            (snp.GUID_VCEK, self.chain.der(self.chain.vcek)),
            (snp.GUID_ASK, self.chain.der(self.chain.ask)),
            (snp.GUID_ARK, self.chain.der(self.chain.root)),
        ])
        self.report_path = case / "report.bin"
        self.report_path.write_bytes(self.report + self.table)
        self.snp_policy = {
            "schema": snp.SNP_POLICY_SCHEMA,
            "measurement": (b"\xab" * 48).hex(),
            "signing_key": "VCEK",
            "vmpl": 0,
            "tcb": {"boot_loader": 3, "snp": 8, "microcode": 115},
            "policy": {"migration_agent": False, "smt": True},
            "valid_until": "2035-01-01T00:00:00Z",
        }
        self.snp_policy_path = case / "snp-policy.json"
        self.snp_policy_path.write_text(json.dumps(self.snp_policy), encoding="utf-8")

    def tearDown(self) -> None:
        self.fx.cleanup()
        shutil.rmtree(self.case, ignore_errors=True)

    def e1_args(self) -> list[str]:
        return self.fx.verify_args() + [
            "--ak-sha256", hashlib.sha256(b"ak-public").hexdigest(),
            "--tpm2-checkquote", str(self.stub),
        ]

    def e2_args(self) -> list[str]:
        return self.e1_args() + [
            "--snp-report", str(self.report_path),
            "--snp-policy", str(self.snp_policy_path),
            "--ark", str(self.chain.root),
            "--openssl", self.openssl,
            "--json",
        ]

    def test_verified_with_snp_evidence(self):
        code, out, err = run_verify(self.e2_args())
        self.assertEqual(code, wa.EXIT_OK, err + out)
        payload = json.loads(out)
        self.assertEqual(payload["status"], "verified")
        self.assertTrue(payload["verified"])
        self.assertIsNotNone(payload["snp"])
        self.assertEqual(payload["snp"]["signing_key"], "VCEK")
        check_map = {check["name"]: check for check in payload["checks"]}
        self.assertEqual(check_map["snp_signature"]["status"], "pass")
        self.assertEqual(check_map["snp_report_data"]["status"], "pass")
        self.assertEqual(check_map["snp_cert_chain"]["status"], "pass")

    def test_snp_with_cert_directory(self):
        args = self.e2_args()
        index = args.index("--snp-report") + 2
        args[index:index] = ["--snp-certs", str(self._cert_dir())]
        code, out, err = run_verify(args)
        self.assertEqual(code, wa.EXIT_OK, err + out)
        self.assertTrue(json.loads(out)["verified"])

    def _cert_dir(self) -> Path:
        directory = self.case / "certs"
        directory.mkdir(exist_ok=True)
        for name, path in (("vcek.pem", self.chain.vcek),
                           ("ask.pem", self.chain.ask),
                           ("ark.pem", self.chain.root)):
            shutil.copyfile(path, directory / name)
        return directory

    def test_missing_report_fails_closed(self):
        args = self.e1_args() + ["--snp-policy", str(self.snp_policy_path), "--json"]
        code, out, _ = run_verify(args)
        self.assertEqual(code, wa.EXIT_FAIL)
        payload = json.loads(out)
        check_map = {check["name"]: check for check in payload["checks"]}
        self.assertEqual(check_map["snp_report"]["status"], "fail")

    def test_allow_machine_only_is_partial(self):
        args = self.e1_args() + [
            "--snp-policy", str(self.snp_policy_path),
            "--allow-machine-only", "--json",
        ]
        code, out, _ = run_verify(args)
        self.assertEqual(code, wa.EXIT_INCOMPLETE)
        payload = json.loads(out)
        self.assertEqual(payload["status"], "partial")
        check_map = {check["name"]: check for check in payload["checks"]}
        self.assertEqual(check_map["snp_report"]["status"], "skip")

    def test_allow_machine_only_does_not_rescue_bad_evidence(self):
        wrong = snp.report_data_value(bytes.fromhex(self.fx.nonce), "00" * 32)
        report = make_report(self.chain, leaf_key=self.chain.vcek_key,
                             report_data=wrong)
        path = self.case / "bad-report.bin"
        path.write_bytes(report + self.table)
        args = self.e1_args() + [
            "--snp-report", str(path),
            "--snp-policy", str(self.snp_policy_path),
            "--ark", str(self.chain.root),
            "--openssl", self.openssl,
            "--allow-machine-only", "--json",
        ]
        code, out, _ = run_verify(args)
        self.assertEqual(code, wa.EXIT_FAIL)
        payload = json.loads(out)
        check_map = {check["name"]: check for check in payload["checks"]}
        self.assertEqual(check_map["snp_report_data"]["status"], "fail")

    def test_report_without_policy_is_partial(self):
        args = self.e1_args() + [
            "--snp-report", str(self.report_path),
            "--ark", str(self.chain.root),
            "--openssl", self.openssl,
            "--json",
        ]
        code, out, _ = run_verify(args)
        self.assertEqual(code, wa.EXIT_INCOMPLETE)
        payload = json.loads(out)
        check_map = {check["name"]: check for check in payload["checks"]}
        self.assertEqual(check_map["snp_signature"]["status"], "pass")
        self.assertEqual(check_map["snp_measurement"]["status"], "skip")

    def test_wrong_report_data_fails_closed(self):
        wrong = snp.report_data_value(bytes.fromhex(self.fx.nonce), "11" * 32)
        report = make_report(self.chain, leaf_key=self.chain.vcek_key,
                             report_data=wrong)
        path = self.case / "wrong-data.bin"
        path.write_bytes(report + self.table)
        args = self.e2_args()
        index = args.index("--snp-report") + 1
        args[index] = str(path)
        code, out, _ = run_verify(args)
        self.assertEqual(code, wa.EXIT_FAIL)
        check_map = {check["name"]: check for check in json.loads(out)["checks"]}
        self.assertEqual(check_map["snp_report_data"]["status"], "fail")

    def test_require_snp_conflicts_with_machine_only(self):
        code, _, err = run_verify(self.e1_args() + [
            "--require-snp", "--allow-machine-only", "--json",
        ])
        self.assertEqual(code, wa.EXIT_USAGE)
        self.assertIn("conflict", err)


if __name__ == "__main__":
    unittest.main()
