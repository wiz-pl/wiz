#!/usr/bin/env python3
"""Tests for the Wiz attestation manifest and verifier.

Run without a TPM or a Wiz build:

    python3 -m unittest discover -s scripts/attest/tests -v

Two tests are opt-in because they need more than Python:

* `ReproducibleBuildTests` needs a built `wiz` and a C toolchain
  (`WIZ_ATTEST_REPRO=1`, `WIZ_BIN=...`, plus the usual `WIZ_CFLAGS`/`WIZ_LDFLAGS`
  if the toolchain needs them).  Run it through `heavy`.
* `TpmIntegrationTests` needs tpm2-tools and readable `/dev/tpmrm0`
  (`WIZ_ATTEST_TPM=1`; `WIZ_TPM2_BIN=...` and `WIZ_ATTEST_TPM_SUDO=1` when the
  device is root-only).  It skips cleanly otherwise.

The non-optional tests use a stub `tpm2_checkquote` only to check that the
verifier invokes it with the right arguments; they never implement TPM
cryptography.
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import shutil
import stat
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
sys.path.insert(0, str(HERE.parent))

import wiz_attest as wa  # noqa: E402

VERIFY = HERE.parent / "wiz-verify"
ATTEST = HERE.parent / "wiz-attest"
WIZ = REPO / ".lake/build/bin/wiz"


# --------------------------------------------------------------------------
# Fixture helpers


def tpm2b(data: bytes) -> bytes:
    return struct.pack(">H", len(data)) + data


def encode_quote(*, extra_data: bytes, indices: list[int], pcr_digest: bytes,
                 magic: int = wa.ATTEST_MAGIC, stype: int = wa.ATTEST_QUOTE,
                 qualified_signer: bytes = b"qualified-ak-name") -> bytes:
    """Encode a TPMS_ATTEST quote (the shape `tpm2_quote -m` writes)."""
    size = 3
    select = bytearray(size)
    for index in indices:
        select[index // 8] |= 1 << (index % 8)
    out = struct.pack(">IH", magic, stype)
    out += tpm2b(qualified_signer)
    out += tpm2b(extra_data)
    out += struct.pack(">QIIB", 123456, 7, 3, 1)  # clockInfo
    out += b"\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11"  # firmwareVersion
    out += struct.pack(">I", 1)  # one bank
    out += struct.pack(">HB", wa.ALG_SHA256, size) + bytes(select)
    out += tpm2b(pcr_digest)
    return out


def pcr_digest(values: list[bytes]) -> bytes:
    return hashlib.sha256(b"".join(values)).digest()


def encode_ak_public(modulus: bytes = b"\x01\x02\x03",
                     exponent: int = 65537,
                     key_type: int = 0x0001) -> bytes:
    """A tiny TPM2B_PUBLIC RSA AK, enough to test Name/DER SPKI parsing."""
    public = struct.pack(">HH", key_type, wa.ALG_SHA256)
    public += struct.pack(">I", 0x00040072)  # objectAttributes (unused)
    public += struct.pack(">H", 0)           # authPolicy
    public += struct.pack(">H", 0x0010)      # symmetric = NULL
    public += struct.pack(">H", 0x0010)      # scheme = NULL
    public += struct.pack(">H", 2048)        # keyBits
    public += struct.pack(">I", exponent)
    public += struct.pack(">H", len(modulus)) + modulus
    return struct.pack(">H", len(public)) + public


def make_key(directory: Path, name: str = "key") -> tuple[Path, Path]:
    key = directory / name
    subprocess.run(
        ["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", "test",
         "-f", str(key)],
        check=True, capture_output=True, text=True, timeout=60,
    )
    return key, Path(str(key) + ".pub")


class Fixture:
    """A complete, valid manifest/quote/policy/artifact bundle in a temp dir."""

    def __init__(self, *, indices=(7, 11), nonce="11" * 32):
        self.dir = Path(tempfile.mkdtemp(prefix="wiz-attest-test-"))
        self.indices = list(indices)
        self.nonce = nonce
        self.artifacts = {
            "prog": b"#!/bin/sh\necho hello\n",
            "prog.c": b"int main(void) { return 0; }\n",
        }
        for name, data in self.artifacts.items():
            (self.dir / name).write_bytes(data)
        # real files for the input manifest (source and one tree input)
        (self.dir / "examples").mkdir()
        (self.dir / "examples/io.wiz").write_bytes(b"source")
        (self.dir / "runtime").mkdir()
        (self.dir / "runtime/wiz.c").write_bytes(b"runtime")
        self.values = {i: hashlib.sha256(f"pcr-{i}".encode()).digest()
                       for i in self.indices}
        self.policy = {
            "schema": wa.POLICY_SCHEMA,
            "bank": "sha256",
            "pcr": {str(i): self.values[i].hex() for i in self.indices},
            "ak_sha256": hashlib.sha256(b"ak-public").hexdigest(),
        }
        self._write_policy()
        (self.dir / "ak.pub").write_bytes(b"ak-public")
        (self.dir / "quote.sig").write_bytes(b"signature-bytes")
        self.manifest = wa.build_manifest(
            artifacts=[{"path": name, "size": len(data),
                        "sha256": hashlib.sha256(data).hexdigest()}
                       for name, data in self.artifacts.items()],
            wiz_version="0.1.0-dev",
            wiz_commit="e3bd36ffd0093d2d72973f01515489e641b8de1b",
            wiz_binary_sha256=hashlib.sha256(b"wiz-binary").hexdigest(),
            source_entry="examples/io.wiz",
            source_sha256=hashlib.sha256(b"source").hexdigest(),
            tree_sha256=hashlib.sha256(b"tree").hexdigest(),
            tree_roots=["lib", "runtime"],
            target="x86_64-linux-gnu",
            pcr_indices=self.indices,
        )
        # a second input so order/root tests have something to reorder
        self.manifest["inputs"].append({
            "role": "tree", "path": "runtime/wiz.c",
            "sha256": hashlib.sha256(b"runtime").hexdigest(),
        })
        self.manifest["inputsRoot"] = wa.inputs_root(self.manifest["inputs"])
        self.write_manifest()
        self.write_quote()

    def write_manifest(self) -> None:
        (self.dir / "manifest.json").write_bytes(wa.canonical_bytes(self.manifest))

    def manifest_digest(self) -> str:
        return hashlib.sha256(wa.canonical_bytes(self.manifest)).hexdigest()

    def statement_digest(self) -> str:
        statement = wa.build_statement(self.manifest, self.manifest_digest())
        return hashlib.sha256(wa.canonical_bytes(statement)).hexdigest()

    def quote_extra(self, nonce: str | None = None,
                    statement_digest: str | None = None) -> bytes:
        nonce = nonce or self.nonce
        digest = statement_digest or self.statement_digest()
        return bytes.fromhex(wa.quote_extra_data(bytes.fromhex(nonce), digest))

    def bind_quote_to_statement(self, statement_digest: str,
                                nonce: str | None = None) -> None:
        self.write_quote(extra_data=self.quote_extra(nonce, statement_digest))

    def write_policy(self, policy: dict | None = None) -> None:
        self.policy = policy or self.policy
        self._write_policy()

    def _write_policy(self) -> None:
        (self.dir / "policy.json").write_text(json.dumps(self.policy), encoding="utf-8")

    def write_quote(self, *, extra_data: bytes | None = None,
                    indices: list[int] | None = None,
                    values: dict[int, bytes] | None = None,
                    qualified_signer: bytes = b"qualified-ak-name") -> None:
        indices = list(indices if indices is not None else self.indices)
        values = values or self.values
        data = b"".join(values[i] for i in indices)
        extra = extra_data if extra_data is not None else self.quote_extra()
        (self.dir / "quote.msg").write_bytes(
            encode_quote(extra_data=extra, indices=indices,
                         pcr_digest=pcr_digest([values[i] for i in indices]),
                         qualified_signer=qualified_signer))
        (self.dir / "quote.pcr").write_bytes(data)

    def verify_args(self, *, allow_unsigned: bool = True,
                    nonce: str | None = None) -> list[str]:
        args = [
            "--manifest", str(self.dir / "manifest.json"),
            "--policy", str(self.dir / "policy.json"),
            "--nonce", self.nonce if nonce is None else nonce,
            "--source-root", str(self.dir),
        ]
        if allow_unsigned:
            args.append("--allow-unsigned")
        return args

    def cleanup(self) -> None:
        shutil.rmtree(self.dir, ignore_errors=True)


def run_verify(args: list[str]) -> tuple[int, str, str]:
    proc = subprocess.run([sys.executable, str(VERIFY), *args],
                          capture_output=True, text=True, timeout=120)
    return proc.returncode, proc.stdout, proc.stderr


def run_attest(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run([sys.executable, str(ATTEST), *args],
                          capture_output=True, text=True, timeout=900)


def write_stub(directory: Path, *, exit_code: int = 0) -> Path:
    stub = directory / "tpm2_checkquote"
    log = directory / "checkquote.args"
    stub.write_text(
        "#!/bin/sh\n"
        f'printf \'%s\\n\' "$@" > "{log}"\n'
        f"exit {exit_code}\n",
        encoding="utf-8",
    )
    stub.chmod(stub.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    return stub


class FixtureTest(unittest.TestCase):
    def setUp(self) -> None:
        self.fx = Fixture()

    def tearDown(self) -> None:
        self.fx.cleanup()

    def base_args(self) -> list[str]:
        return self.fx.verify_args() + [
            "--ak-sha256", hashlib.sha256(b"ak-public").hexdigest(),
        ]


# --------------------------------------------------------------------------
# Canonicalization and schema


class CanonicalTests(unittest.TestCase):
    def test_key_order_does_not_matter(self):
        a = {"b": 1, "a": {"d": 2, "c": [1, 2]}}
        b = {"a": {"c": [1, 2], "d": 2}, "b": 1}
        self.assertEqual(wa.canonical_bytes(a), wa.canonical_bytes(b))
        self.assertEqual(wa.canonical_bytes(a), b'{"a":{"c":[1,2],"d":2},"b":1}')

    def test_no_whitespace_or_trailing_newline(self):
        data = wa.canonical_bytes({"x": "a b", "y": ["z"]})
        self.assertEqual(data, b'{"x":"a b","y":["z"]}')
        self.assertNotIn(b"\n", data)

    def test_unicode_is_utf8_and_stable(self):
        self.assertEqual(wa.canonical_bytes({"k": "\u00e9"}), '{"k":"\u00e9"}'.encode())

    def test_arrays_keep_order(self):
        self.assertNotEqual(wa.canonical_bytes({"x": [1, 2]}),
                            wa.canonical_bytes({"x": [2, 1]}))

    def test_nan_rejected(self):
        with self.assertRaises(ValueError):
            wa.canonical_bytes({"x": float("nan")})

    def test_load_rejects_duplicate_keys(self):
        with self.assertRaises(wa.SchemaError):
            wa.load_json_strict(b'{"a":1,"a":2}')

    def test_tree_digest_is_deterministic(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name, data in (("lib/b.wiz", b"B"), ("lib/a.wiz", b"A"),
                               ("lib/sub/c.wiz", b"C")):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            old = os.getcwd()
            os.chdir(root)
            try:
                first = wa.tree_digest(["lib"])
                second = wa.tree_digest(["./lib"])
                self.assertEqual(first, second)
                (root / "lib/a.wiz").write_bytes(b"A2")
                self.assertNotEqual(first[0], wa.tree_digest(["lib"])[0])
            finally:
                os.chdir(old)


class SchemaTests(FixtureTest):
    def assert_schema_fails(self, mutate) -> None:
        obj = json.loads(wa.canonical_bytes(self.fx.manifest))
        mutate(obj)
        with self.assertRaises(wa.SchemaError):
            wa.validate_manifest(obj)

    def test_valid_manifest(self):
        wa.validate_manifest(self.fx.manifest)

    def test_unknown_field(self):
        self.assert_schema_fails(lambda m: m.update({"timestamp": "2026-01-01"}))

    def test_missing_field(self):
        self.assert_schema_fails(lambda m: m.pop("target"))

    def test_wrong_schema(self):
        self.assert_schema_fails(lambda m: m.update({"schema": "wiz-build-manifest/v2"}))

    def test_unsorted_artifacts(self):
        self.assert_schema_fails(lambda m: m["artifacts"].reverse())

    def test_duplicate_artifact_path(self):
        self.assert_schema_fails(lambda m: m["artifacts"].append(dict(m["artifacts"][0])))

    def test_absolute_artifact_path(self):
        self.assert_schema_fails(lambda m: m["artifacts"][0].update({"path": "/etc/passwd"}))

    def test_parent_artifact_path(self):
        self.assert_schema_fails(lambda m: m["artifacts"][0].update({"path": "../escape"}))

    def test_bool_is_not_an_integer_size(self):
        self.assert_schema_fails(lambda m: m["artifacts"][0].update({"size": True}))

    def test_bad_digest(self):
        self.assert_schema_fails(lambda m: m["artifacts"][0].update({"sha256": "abc"}))

    def test_unsorted_inputs(self):
        self.assert_schema_fails(lambda m: m["inputs"].reverse())

    def test_input_role_and_shape(self):
        self.assert_schema_fails(lambda m: m["inputs"][0].update({"role": "mystery"}))
        self.assert_schema_fails(lambda m: m["inputs"][0].pop("path"))

    def test_inputs_root_shape(self):
        self.assert_schema_fails(lambda m: m.update({"inputsRoot": "sha256:abc"}))

    def test_unknown_builder(self):
        self.assert_schema_fails(lambda m: m["builder"].update({"kind": "sev-snp"}))

    def test_two_outputs_rejected(self):
        self.assert_schema_fails(
            lambda m: m["artifacts"][1].update({"role": "output"}))


# --------------------------------------------------------------------------
# Verification


class VerifyTests(FixtureTest):
    def test_valid_bundle_with_stub_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub(Path(tmp))
            code, out, err = run_verify(self.base_args() + [
                "--tpm2-checkquote", str(stub), "--json"])
            self.assertEqual(code, wa.EXIT_OK, err)
            result = json.loads(out)
            self.assertEqual(result["status"], "verified")
            self.assertTrue(result["ok"])
            self.assertEqual(result["manifest_sha256"], self.fx.manifest_digest())
            args = (Path(tmp) / "checkquote.args").read_text().split()
            self.assertIn("-q", args)
            self.assertEqual(args[args.index("-q") + 1],
                             self.fx.quote_extra().hex())
            self.assertEqual(args[args.index("-l") + 1], "sha256:7,11")

    def test_manifest_digest_matches_file_bytes(self):
        raw = (self.fx.dir / "manifest.json").read_bytes()
        self.assertEqual(wa.sha256_bytes(raw), self.fx.manifest_digest())
        self.assertEqual(wa.canonical_bytes(wa.load_json_strict(raw)), raw)

    def test_verified_json_has_verified_flag(self):
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub(Path(tmp))
            code, out, _ = run_verify(self.base_args() + [
                "--tpm2-checkquote", str(stub), "--json"])
            self.assertEqual(code, wa.EXIT_OK)
            self.assertTrue(json.loads(out)["verified"])

    def test_skip_crypto_is_partial(self):
        code, out, _ = run_verify(self.base_args() + ["--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_INCOMPLETE)
        result = json.loads(out)
        self.assertEqual(result["status"], "partial")
        self.assertTrue(result["ok"])
        self.assertEqual(result["exit_code"], wa.EXIT_INCOMPLETE)

    def test_missing_checkquote_is_partial(self):
        code, out, _ = run_verify(self.base_args() + [
            "--tpm2-checkquote", "/definitely/not/tpm2_checkquote", "--json"])
        self.assertEqual(code, wa.EXIT_INCOMPLETE)
        self.assertEqual(json.loads(out)["status"], "partial")

    def test_checkquote_failure_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub(Path(tmp), exit_code=1)
            code, out, _ = run_verify(self.base_args() + [
                "--tpm2-checkquote", str(stub), "--json"])
            self.assertEqual(code, wa.EXIT_FAIL)
            result = json.loads(out)
            self.assertEqual(result["status"], "failed")
            self.assertTrue(any(c["name"] == "tpm_quote_signature"
                                and c["status"] == "fail" for c in result["checks"]))

    def test_extra_data_mismatch(self):
        self.fx.write_quote(extra_data=b"\x00" * 32)
        with tempfile.TemporaryDirectory() as tmp:
            stub = write_stub(Path(tmp))
            code, out, _ = run_verify(self.base_args() + [
                "--tpm2-checkquote", str(stub), "--json"])
            self.assertEqual(code, wa.EXIT_FAIL)
            checks = {c["name"]: c for c in json.loads(out)["checks"]}
            self.assertEqual(checks["quote_extra_data"]["status"], "fail")

    def test_tampered_artifact(self):
        path = self.fx.dir / "prog"
        path.write_bytes(path.read_bytes() + b"tampered")
        code, out, _ = run_verify(self.base_args() + ["--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["artifact:prog"]["status"], "fail")
        self.assertIn("size is", checks["artifact:prog"]["detail"])

    def test_same_size_artifact_with_different_bytes(self):
        path = self.fx.dir / "prog"
        data = bytearray(path.read_bytes())
        data[0] ^= 0xFF
        path.write_bytes(bytes(data))
        code, out, _ = run_verify(self.base_args() + ["--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["artifact:prog"]["status"], "fail")
        self.assertIn("sha256 is", checks["artifact:prog"]["detail"])

    def test_missing_artifact(self):
        (self.fx.dir / "prog.c").unlink()
        code, _, _ = run_verify(self.base_args() + ["--skip-crypto"])
        self.assertEqual(code, wa.EXIT_FAIL)

    def test_artifact_symlink_escape_rejected(self):
        outside = self.fx.dir.parent / "outside-artifact"
        outside.write_bytes(b"outside")
        try:
            (self.fx.dir / "prog").unlink()
            (self.fx.dir / "prog").symlink_to(outside)
            code, out, _ = run_verify(self.base_args() + ["--skip-crypto", "--json"])
            self.assertEqual(code, wa.EXIT_FAIL)
            self.assertIn("escapes", json.dumps(json.loads(out)))
        finally:
            outside.unlink(missing_ok=True)

    def test_pcr_policy_mismatch(self):
        policy = json.loads(json.dumps(self.fx.policy))
        policy["pcr"]["7"] = "00" * 32
        self.fx.write_policy(policy)
        code, out, _ = run_verify(self.base_args() + ["--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["pcr_policy:7"]["status"], "fail")

    def test_policy_pcr_not_covered(self):
        policy = json.loads(json.dumps(self.fx.policy))
        policy["pcr"]["0"] = "00" * 32
        self.fx.write_policy(policy)
        code, out, _ = run_verify(self.base_args() + ["--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["pcr_policy:0"]["status"], "fail")
        self.assertIn("not covered", checks["pcr_policy:0"]["detail"])

    def test_quote_pcr_selection_mismatch(self):
        self.fx.write_quote(indices=[7])
        code, out, _ = run_verify(self.base_args() + ["--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["quote_pcr_selection"]["status"], "fail")

    def test_quote_pcr_values_wrong_length(self):
        (self.fx.dir / "quote.pcr").write_bytes(b"\x00" * 33)
        code, out, _ = run_verify(self.base_args() + ["--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["pcr_values"]["status"], "fail")

    def test_quote_bad_magic(self):
        (self.fx.dir / "quote.msg").write_bytes(
            encode_quote(extra_data=b"\x00" * 32, indices=[7, 11],
                         pcr_digest=b"\x00" * 32, magic=0xDEADBEEF))
        code, out, _ = run_verify(self.base_args() + ["--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["quote_message"]["status"], "fail")

    def test_quote_truncated(self):
        path = self.fx.dir / "quote.msg"
        path.write_bytes(path.read_bytes()[:-1])
        code, _, _ = run_verify(self.base_args() + ["--skip-crypto"])
        self.assertEqual(code, wa.EXIT_FAIL)

    def test_nonce_match(self):
        code, out, err = run_verify(self.base_args() + ["--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_INCOMPLETE, err)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["nonce"]["status"], "pass")
        self.assertEqual(checks["quote_extra_data"]["status"], "pass")

    def test_nonce_mismatch(self):
        code, out, _ = run_verify(self.fx.verify_args(nonce="22" * 32) + [
            "--ak-sha256", hashlib.sha256(b"ak-public").hexdigest(),
            "--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["quote_extra_data"]["status"], "fail")

    def test_require_nonce_without_one(self):
        args = [
            "--manifest", str(self.fx.dir / "manifest.json"),
            "--policy", str(self.fx.dir / "policy.json"),
            "--allow-unsigned", "--require-nonce",
            "--ak-sha256", hashlib.sha256(b"ak-public").hexdigest(),
            "--source-root", str(self.fx.dir),
            "--skip-crypto", "--json",
        ]
        code, out, _ = run_verify(args)
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["nonce"]["status"], "fail")

    def test_without_nonce_is_partial(self):
        args = [
            "--manifest", str(self.fx.dir / "manifest.json"),
            "--policy", str(self.fx.dir / "policy.json"),
            "--allow-unsigned",
            "--ak-sha256", hashlib.sha256(b"ak-public").hexdigest(),
            "--source-root", str(self.fx.dir),
            "--skip-crypto", "--json",
        ]
        code, out, _ = run_verify(args)
        self.assertEqual(code, wa.EXIT_INCOMPLETE)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["nonce"]["status"], "skip")
        self.assertEqual(checks["quote_extra_data"]["status"], "skip")

    def test_expect_digest(self):
        code, _, _ = run_verify(self.base_args() + [
            "--expect-digest", self.fx.manifest_digest(), "--skip-crypto"])
        self.assertEqual(code, wa.EXIT_INCOMPLETE)
        code, out, _ = run_verify(self.base_args() + [
            "--expect-digest", "00" * 32, "--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["manifest_pin"]["status"], "fail")

    def test_ak_pin_mismatch(self):
        code, out, _ = run_verify(self.fx.verify_args() + [
            "--ak-sha256", "00" * 32, "--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["ak_pin"]["status"], "fail")

    def test_unpinned_ak_is_partial(self):
        policy = json.loads(json.dumps(self.fx.policy))
        policy.pop("ak_sha256")
        self.fx.write_policy(policy)
        code, out, _ = run_verify(self.fx.verify_args() + [
            "--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_INCOMPLETE)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["ak_pin"]["status"], "skip")

    def test_policy_ak_pin(self):
        policy = json.loads(json.dumps(self.fx.policy))
        policy.pop("ak_sha256")
        self.fx.write_policy(policy)
        code, out, _ = run_verify(self.fx.verify_args() + [
            "--ak-sha256", hashlib.sha256(b"ak-public").hexdigest(),
            "--skip-crypto", "--json"])
        self.assertEqual(code, wa.EXIT_INCOMPLETE)
        checks = {c["name"]: c for c in json.loads(out)["checks"]}
        self.assertEqual(checks["ak_pin"]["status"], "pass")


# --------------------------------------------------------------------------
# Producer


class ProducerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="wiz-attest-producer-"))
        (self.tmp / "prog").write_bytes(b"artifact-bytes")
        (self.tmp / "prog.c").write_bytes(b"int main(void){return 0;}\n")

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_manifest_only_is_canonical_and_valid(self):
        proc = run_attest([
            "--artifact", str(self.tmp / "prog"),
            "--artifact", str(self.tmp / "prog.c"),
            "--out", str(self.tmp / "out"), "--no-quote",
            "--wiz-version", "0.1.0-dev",
            "--wiz-commit", "e3bd36ffd0093d2d72973f01515489e641b8de1b",
            "--target", "x86_64-linux-gnu",
            "--source-entry", "examples/io.wiz",
            "--source-sha256", "22" * 32,
        ])
        self.assertEqual(proc.returncode, 0, proc.stderr)
        out = self.tmp / "out"
        raw = (out / "manifest.json").read_bytes()
        manifest = wa.load_json_strict(raw)
        wa.validate_manifest(manifest)
        self.assertEqual(wa.canonical_bytes(manifest), raw)
        self.assertEqual([a["path"] for a in manifest["artifacts"]], ["prog", "prog.c"])
        self.assertEqual(manifest["toolchain"]["wiz"]["version"], "0.1.0-dev")
        self.assertEqual(manifest["builder"]["kind"], "wiz-build")
        self.assertEqual(manifest["inputs"][0]["role"], "source")
        self.assertEqual(manifest["inputsRoot"],
                         wa.inputs_root(manifest["inputs"]))

    def test_source_build_records_binary_and_generated_c(self):
        wiz = self.tmp / "fake-wiz"
        wiz.write_text(
            "#!/bin/sh\n"
            'if [ "$1" = "--version" ]; then echo "wiz 9.9.9 (abcdef0)"; exit 0; fi\n'
            'printf \'%s\\n\' "$@" > "$0.args"\n'
            'out=""; prev=""\n'
            'for a in "$@"; do [ "$prev" = "-o" ] && out="$a"; prev="$a"; done\n'
            'printf "fake binary\\n" > "$out"\n'
            'printf "int main(void){return 0;}\\n" > "$out.c"\n',
            encoding="utf-8",
        )
        wiz.chmod(0o755)
        source = self.tmp / "src.wiz"
        source.write_text("fn main() { }\n", encoding="utf-8")
        out = self.tmp / "out"
        proc = run_attest([
            str(source), "--out", str(out), "--wiz", str(wiz),
            "--output-name", "prog", "--target", "x86_64-linux-gnu",
            "--wiz-flag=-I", "--wiz-flag=lib", "--no-quote",
        ])
        self.assertEqual(proc.returncode, 0, proc.stderr)
        manifest = wa.load_json_strict((out / "manifest.json").read_bytes())
        self.assertEqual([a["path"] for a in manifest["artifacts"]], ["prog", "prog.c"])
        self.assertEqual(manifest["toolchain"]["wiz"]["version"], "9.9.9")
        self.assertEqual(manifest["toolchain"]["wiz"]["revision"], "abcdef0")
        self.assertEqual(manifest["source"]["file"], "src.wiz")
        args = (self.tmp / "fake-wiz.args").read_text().split()
        self.assertEqual(args[:4], ["-I", "lib", "build", str(source)])
        self.assertIn("-o", args)
        self.assertEqual(args[args.index("-o") + 1], str(out / "prog"))

    def test_same_inputs_make_same_manifest(self):
        args = [
            "--artifact", str(self.tmp / "prog"),
            "--out", str(self.tmp / "out"),
            "--wiz-version", "0.1.0-dev",
            "--target", "x86_64-linux-gnu",
            "--source-entry", "examples/io.wiz",
            "--source-sha256", "22" * 32,
            "--no-quote",
        ]
        first = run_attest(args)
        self.assertEqual(first.returncode, 0, first.stderr)
        digest1 = hashlib.sha256((self.tmp / "out/manifest.json").read_bytes()).hexdigest()
        second = run_attest(args)
        self.assertEqual(second.returncode, 0, second.stderr)
        digest2 = hashlib.sha256((self.tmp / "out/manifest.json").read_bytes()).hexdigest()
        self.assertEqual(digest1, digest2)

    def test_manifest_is_challenge_free(self):
        proc = run_attest([
            "--artifact", str(self.tmp / "prog"),
            "--out", str(self.tmp / "out"), "--no-quote",
            "--wiz-version", "0.1.0-dev",
            "--target", "x86_64-linux-gnu",
            "--source-entry", "examples/io.wiz",
            "--source-sha256", "22" * 32,
            "--nonce", "AB" * 32,
        ])
        self.assertEqual(proc.returncode, 0, proc.stderr)
        manifest = wa.load_json_strict((self.tmp / "out/manifest.json").read_bytes())
        self.assertNotIn("challenge", manifest)
        self.assertNotIn("nonce", manifest)
        # The same inputs (with or without a nonce) produce the same manifest.
        second = run_attest([
            "--artifact", str(self.tmp / "prog"),
            "--out", str(self.tmp / "out2"), "--no-quote",
            "--wiz-version", "0.1.0-dev",
            "--target", "x86_64-linux-gnu",
            "--source-entry", "examples/io.wiz",
            "--source-sha256", "22" * 32,
        ])
        self.assertEqual(second.returncode, 0, second.stderr)
        self.assertEqual((self.tmp / "out/manifest.json").read_bytes(),
                         (self.tmp / "out2/manifest.json").read_bytes())

    def test_no_quote_with_sign_key_writes_envelope(self):
        key = self.tmp / "producer-key"
        keygen = run_attest(["keygen", "--key", str(key)])
        self.assertEqual(keygen.returncode, 0, keygen.stderr)
        proc = run_attest([
            "--artifact", str(self.tmp / "prog"),
            "--out", str(self.tmp / "signed"), "--no-quote",
            "--wiz-version", "0.1.0-dev",
            "--target", "x86_64-linux-gnu",
            "--source-entry", "examples/io.wiz",
            "--source-sha256", "22" * 32,
            "--nonce", "cd" * 32,
            "--sign-key", str(key), "--json",
        ])
        self.assertEqual(proc.returncode, 0, proc.stderr)
        info = json.loads(proc.stdout)
        self.assertTrue(info["signed"])
        self.assertTrue(Path(info["envelope"]).is_file())
        self.assertTrue(Path(info["detached_signature"]).is_file())
        manifest = wa.load_json_strict(
            (self.tmp / "signed/manifest.json").read_bytes())
        self.assertNotIn("nonce", manifest)
        self.assertNotIn("challenge", manifest)

    def test_quote_without_signing_key_is_usage_error(self):
        proc = run_attest([
            "--artifact", str(self.tmp / "prog"),
            "--out", str(self.tmp / "out"),
            "--wiz-version", "0.1.0-dev",
            "--target", "x86_64-linux-gnu",
            "--source-entry", "examples/io.wiz",
            "--source-sha256", "22" * 32,
        ])
        self.assertEqual(proc.returncode, wa.EXIT_USAGE)
        self.assertIn("--sign-key", proc.stderr)

    def test_bad_pcr_list_is_usage_error(self):
        proc = run_attest([
            "--artifact", str(self.tmp / "prog"),
            "--out", str(self.tmp / "out"), "--no-quote",
            "--wiz-version", "0.1.0-dev",
            "--target", "x86_64-linux-gnu",
            "--source-entry", "examples/io.wiz",
            "--pcr-list", "sha256:11,7",
        ])
        self.assertEqual(proc.returncode, wa.EXIT_USAGE)

    def test_missing_artifact_is_usage_error(self):
        proc = run_attest([
            "--artifact", str(self.tmp / "nope"),
            "--out", str(self.tmp / "out"), "--no-quote",
            "--wiz-version", "0.1.0-dev",
            "--target", "x86_64-linux-gnu",
            "--source-entry", "examples/io.wiz",
            "--source-sha256", "22" * 32,
        ])
        self.assertEqual(proc.returncode, wa.EXIT_USAGE)


# --------------------------------------------------------------------------
# DSSE signing, key handling and statement binding


class SigningTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fx = Fixture()
        self.tmp = Path(tempfile.mkdtemp(prefix="wiz-sign-test-"))
        self.key, self.pub = make_key(self.tmp, "a")
        self.key2, self.pub2 = make_key(self.tmp, "b")
        self.stub = write_stub(self.tmp)
        self.envelope = self.fx.dir / wa.ENVELOPE_NAME
        self.detached = Path(str(self.envelope) + wa.DETACHED_SUFFIX)
        self.info = self.sign()
        self.fx.bind_quote_to_statement(self.info["statement_sha256"])

    def tearDown(self) -> None:
        self.fx.cleanup()
        shutil.rmtree(self.tmp, ignore_errors=True)

    def sign(self, *extra: str, key: Path | None = None,
             out: Path | None = None) -> dict:
        args = ["sign", "--manifest", str(self.fx.dir / "manifest.json"),
                "--key", str(key or self.key), "--json", *extra]
        if out is not None:
            args += ["--out", str(out)]
        proc = run_attest(args)
        self.last_proc = proc
        self.assertEqual(proc.returncode, 0, proc.stderr)
        return json.loads(proc.stdout)

    def verify_args(self, *, pub: Path | None = None,
                    extras: tuple[str, ...] = (),
                    allow_unsigned: bool = False,
                    envelope: Path | None = None) -> list[str]:
        args = [
            "--manifest", str(self.fx.dir / "manifest.json"),
            "--policy", str(self.fx.dir / "policy.json"),
            "--nonce", self.fx.nonce,
            "--ak-sha256", hashlib.sha256(b"ak-public").hexdigest(),
            "--source-root", str(self.fx.dir),
        ]
        if pub is not None:
            args += ["--public-key", str(pub)]
        if envelope is not None:
            args += ["--envelope", str(envelope)]
        if allow_unsigned:
            args.append("--allow-unsigned")
        return args + list(extras)

    def verify(self, *, pub: Path | None = None,
               extras: tuple[str, ...] = (),
               allow_unsigned: bool = False,
               envelope: Path | None = None,
               stub: bool = False,
               with_key: bool = True) -> tuple[int, dict, str]:
        args = self.verify_args(pub=(pub or self.pub) if with_key else None,
                                extras=extras, allow_unsigned=allow_unsigned,
                                envelope=envelope)
        if stub:
            args += ["--tpm2-checkquote", str(self.stub)]
        else:
            args += ["--skip-crypto"]
        code, out, err = run_verify(args + ["--json"])
        try:
            payload = json.loads(out)
        except json.JSONDecodeError:
            payload = {}
        return code, payload, err

    def envelope_data(self) -> dict:
        return json.loads(self.envelope.read_bytes())

    def write_envelope(self, envelope: dict) -> None:
        self.envelope.write_bytes(wa.canonical_bytes(envelope))

    def checks(self, payload: dict) -> dict[str, dict]:
        return {check["name"]: check for check in payload.get("checks", [])}

    def test_keygen_and_fingerprint(self):
        key = self.tmp / "generated"
        proc = run_attest(["keygen", "--key", str(key), "--json"])
        self.assertEqual(proc.returncode, 0, proc.stderr)
        info = json.loads(proc.stdout)
        self.assertTrue(key.is_file())
        self.assertTrue(Path(str(key) + ".pub").is_file())
        self.assertEqual(stat.S_IMODE(key.stat().st_mode), 0o600)
        self.assertTrue(info["fingerprint"].startswith("SHA256:"))
        listed = subprocess.run(
            ["ssh-keygen", "-lf", str(key) + ".pub", "-E", "sha256"],
            capture_output=True, text=True, check=True,
        ).stdout.split()
        self.assertEqual(listed[1], info["fingerprint"])
        self.assertNotIn("PRIVATE", proc.stdout)

    def test_sign_verify_round_trip(self):
        self.assertTrue(self.envelope.is_file())
        self.assertTrue(self.detached.is_file())
        envelope = self.envelope_data()
        self.assertEqual(envelope["payloadType"], wa.DSSE_PAYLOAD_TYPE)
        self.assertEqual(len(envelope["signatures"]), 1)
        self.assertEqual(envelope["signatures"][0]["keyid"], self.info["keyid"])
        code, payload, err = self.verify(stub=True)
        self.assertEqual(code, wa.EXIT_OK, err)
        self.assertEqual(payload["status"], "verified")
        self.assertTrue(payload["signed"])
        self.assertEqual(payload["statement_sha256"],
                         self.info["statement_sha256"])
        checks = self.checks(payload)
        for name in ("dsse_envelope", "dsse_payload_type", "dsse_signature",
                     "dsse_key", "dsse_statement"):
            self.assertEqual(checks[name]["status"], "pass", name)

    def test_wrong_key(self):
        code, payload, _ = self.verify(pub=self.pub2, stub=True)
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(payload)["dsse_signature"]["status"], "fail")

    def test_tampered_payload(self):
        envelope = self.envelope_data()
        statement = json.loads(base64.b64decode(envelope["payload"]))
        statement["subject"][0]["digest"]["sha256"] = "00" * 32
        envelope["payload"] = base64.b64encode(
            wa.canonical_bytes(statement)).decode()
        self.write_envelope(envelope)
        code, payload, _ = self.verify(stub=True)
        self.assertEqual(code, wa.EXIT_FAIL)
        checks = self.checks(payload)
        self.assertEqual(checks["dsse_signature"]["status"], "fail")
        self.assertEqual(checks["dsse_statement"]["status"], "fail")

    def test_tampered_signature(self):
        envelope = self.envelope_data()
        signature = bytearray(base64.b64decode(envelope["signatures"][0]["sig"]))
        signature[len(signature) // 2] ^= 0x01
        envelope["signatures"][0]["sig"] = base64.b64encode(signature).decode()
        self.write_envelope(envelope)
        code, payload, _ = self.verify(stub=True)
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(payload)["dsse_signature"]["status"], "fail")

    def test_wrong_payload_type(self):
        envelope = self.envelope_data()
        envelope["payloadType"] = "application/json"
        self.write_envelope(envelope)
        code, payload, _ = self.verify(stub=True)
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(payload)["dsse_payload_type"]["status"], "fail")

    def test_unsigned_rejected_by_default(self):
        self.envelope.unlink()
        self.detached.unlink()
        code, payload, _ = self.verify(stub=True)
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(payload)["signature_policy"]["status"], "fail")

    def test_unsigned_allowed_with_explicit_flag(self):
        self.envelope.unlink()
        self.detached.unlink()
        code, payload, err = self.verify(stub=True, allow_unsigned=True)
        self.assertEqual(code, wa.EXIT_OK, err)
        self.assertEqual(payload["status"], "verified")
        self.assertFalse(payload["signed"])
        self.assertEqual(self.checks(payload)["signature_policy"]["status"], "pass")

    def test_require_signature_rejects_unsigned(self):
        self.envelope.unlink()
        self.detached.unlink()
        code, payload, _ = self.verify(
            stub=True, extras=("--require-signature",))
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(payload)["signature_policy"]["status"], "fail")

    def test_key_fingerprint_mismatch(self):
        other = wa.parse_public_key(self.pub2).fingerprint
        code, payload, _ = self.verify(
            stub=True, extras=("--key-fingerprint", other))
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(payload)["dsse_key"]["status"], "fail")

    def test_key_fingerprint_allowlist_accepts(self):
        fingerprint = wa.parse_public_key(self.pub).fingerprint
        code, payload, err = self.verify(
            stub=True, extras=("--key-fingerprint", fingerprint))
        self.assertEqual(code, wa.EXIT_OK, err)
        self.assertEqual(self.checks(payload)["dsse_key"]["status"], "pass")

    def test_deterministic_envelope_with_fixed_key(self):
        first = self.tmp / "first.json"
        second = self.tmp / "second.json"
        info1 = self.sign(out=first)
        info2 = self.sign(out=second)
        self.assertEqual(first.read_bytes(), second.read_bytes())
        self.assertEqual(Path(info1["detached_signature"]).read_bytes(),
                         Path(info2["detached_signature"]).read_bytes())
        self.assertEqual(info1["statement_sha256"], info2["statement_sha256"])

    def test_tampered_manifest_fails_statement(self):
        self.fx.manifest["artifacts"][0]["sha256"] = "00" * 32
        self.fx.write_manifest()
        code, payload, _ = self.verify(stub=True)
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(payload)["dsse_statement"]["status"], "fail")

    def test_statement_and_quote_binding_mismatch(self):
        self.fx.write_quote(extra_data=b"\x00" * 32)
        code, payload, _ = self.verify(stub=True)
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(payload)["quote_extra_data"]["status"], "fail")

    def test_detached_signature_verifies_and_tamper_fails(self):
        code, payload, err = self.verify(
            stub=True, extras=("--detached-signature", str(self.detached)))
        self.assertEqual(code, wa.EXIT_OK, err)
        self.assertEqual(
            self.checks(payload)["dsse_detached_signature"]["status"], "pass")
        signature = bytearray(self.detached.read_bytes())
        signature[len(signature) // 2] ^= 0x01
        self.detached.write_bytes(bytes(signature))
        code, payload, _ = self.verify(
            stub=True, extras=("--detached-signature", str(self.detached)))
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(
            self.checks(payload)["dsse_detached_signature"]["status"], "fail")

    def test_missing_trust_root_fails(self):
        code, payload, _ = self.verify(with_key=False, stub=True)
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(payload)["dsse_key"]["status"], "fail")

    def test_valid_until_expiry(self):
        self.sign("--valid-until", "2020-01-01T00:00:00Z")
        payload = base64.b64decode(
            json.loads(self.envelope.read_bytes())["payload"])
        self.fx.bind_quote_to_statement(wa.sha256_bytes(payload))
        code, result, _ = self.verify(
            stub=True, extras=("--now", "2026-11-14T00:00:00Z"))
        self.assertEqual(code, wa.EXIT_FAIL)
        self.assertEqual(self.checks(result)["dsse_valid_until"]["status"], "fail")

    def test_prev_chain_pin(self):
        previous = "ab" * 32
        self.sign("--prev", previous)
        payload = base64.b64decode(
            json.loads(self.envelope.read_bytes())["payload"])
        self.fx.bind_quote_to_statement(wa.sha256_bytes(payload))
        code, payload, _ = self.verify(stub=True)
        self.assertEqual(code, wa.EXIT_INCOMPLETE)
        self.assertEqual(self.checks(payload)["dsse_prev"]["status"], "skip")
        code, payload, err = self.verify(
            stub=True, extras=("--expect-prev", previous))
        self.assertEqual(code, wa.EXIT_OK, err)
        self.assertEqual(self.checks(payload)["dsse_prev"]["status"], "pass")

    def test_no_secret_leakage(self):
        secret = self.key.read_text(encoding="utf-8")
        body = [line for line in secret.splitlines()
                if line and not line.startswith("-----")][0]
        self.assertNotIn("PRIVATE KEY", self.last_proc.stdout)
        self.assertNotIn("PRIVATE KEY", self.last_proc.stderr)
        self.assertNotIn(body, json.dumps(self.info))
        for path in (self.envelope, self.detached):
            data = path.read_bytes()
            self.assertNotIn(b"PRIVATE KEY", data)
            self.assertNotIn(body.encode(), data)

    def test_sigstore_is_opt_in_and_stubbed(self):
        cosign = self.tmp / "cosign"
        log = self.tmp / "cosign.args"
        cosign.write_text(
            "#!/bin/sh\n"
            f'printf \'%s\\n\' "$@" > "{log}"\n'
            "exit 0\n",
            encoding="utf-8",
        )
        cosign.chmod(0o755)
        out = self.tmp / "sigstore.json"
        info = self.sign("--sigstore", "--cosign-bin", str(cosign), out=out)
        self.assertTrue(info["sigstore"]["bundle"].endswith(
            wa.SIGSTORE_BUNDLE_SUFFIX))
        args = log.read_text().split()
        self.assertIn("sign-blob", args)
        self.assertIn("--bundle", args)
        self.assertIn("--tlog-upload=false", args)
        out2 = self.tmp / "sigstore-upload.json"
        self.sign("--sigstore-upload", "--cosign-bin", str(cosign), out=out2)
        args2 = log.read_text().split()
        self.assertNotIn("--tlog-upload=false", args2)


class AkInfoTests(unittest.TestCase):
    def test_name_and_spki(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "ak.pub"
            path.write_bytes(encode_ak_public())
            info = wa.ak_info(path)
            public = encode_ak_public()[2:]
            self.assertEqual(info.name, "000b" + hashlib.sha256(public).hexdigest())
            self.assertEqual(
                info.spki_sha256,
                "736ff0ca86e0b1605694f0b0082f70ab173ba3b0dad4c942cc9cdb206530eaa2",
            )
            self.assertEqual(info.file_sha256,
                             hashlib.sha256(encode_ak_public()).hexdigest())

    def test_bad_size_and_non_rsa_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "ak.pub"
            path.write_bytes(b"\x00\x09" + b"short")
            with self.assertRaises(wa.SchemaError):
                wa.ak_info(path)
            path.write_bytes(encode_ak_public(key_type=0x0023))  # ECC
            with self.assertRaises(wa.SchemaError):
                wa.ak_info(path)

    def test_policy_pins_and_quote_qualified_signer(self):
        fx = Fixture()
        try:
            (fx.dir / "ak.pub").write_bytes(encode_ak_public())
            info = wa.ak_info(fx.dir / "ak.pub")
            policy = {
                "schema": wa.POLICY_SCHEMA,
                "bank": "sha256",
                "pcr": {str(i): fx.values[i].hex() for i in fx.indices},
                "ak_spki_sha256": info.spki_sha256,
                "ak_name": info.name,
            }
            fx.write_policy(policy)
            fx.write_quote(qualified_signer=bytes.fromhex(info.name))
            code, out, err = run_verify(fx.verify_args() + [
                "--ak-spki-sha256", info.spki_sha256,
                "--ak-name", info.name,
                "--skip-crypto", "--json",
            ])
            self.assertEqual(code, wa.EXIT_INCOMPLETE, err)
            checks = {c["name"]: c for c in json.loads(out)["checks"]}
            self.assertEqual(checks["ak_name"]["status"], "pass")
            self.assertEqual(checks["ak_name_pin"]["status"], "pass")
            self.assertEqual(checks["ak_spki_pin"]["status"], "pass")
            bad = "00" * 32
            code, out, _ = run_verify(fx.verify_args() + [
                "--ak-spki-sha256", bad, "--skip-crypto", "--json",
            ])
            self.assertEqual(code, wa.EXIT_FAIL)
            checks = {c["name"]: c for c in json.loads(out)["checks"]}
            self.assertEqual(checks["ak_spki_pin"]["status"], "fail")
        finally:
            fx.cleanup()


# --------------------------------------------------------------------------
# Optional: two real builds in different directories produce the same C


@unittest.skipUnless(os.environ.get("WIZ_ATTEST_REPRO") == "1",
                     "set WIZ_ATTEST_REPRO=1 (needs a built wiz and a C toolchain)")
class ReproducibleBuildTests(unittest.TestCase):
    def test_two_builds_same_generated_c_digest(self):
        wiz = Path(os.environ.get("WIZ_BIN", str(WIZ)))
        if not wiz.is_file():
            self.skipTest(f"wiz not built at {wiz}")
        source = REPO / "examples/io.wiz"
        self.assertTrue(source.is_file())
        flags: list[str] = []
        if os.environ.get("CC"):
            flags += ["--cc", os.environ["CC"]]
        if os.environ.get("WIZ_CFLAGS"):
            flags += ["--cflags", os.environ["WIZ_CFLAGS"]]
        if os.environ.get("WIZ_LDFLAGS"):
            flags += ["--ldflags", os.environ["WIZ_LDFLAGS"]]

        with tempfile.TemporaryDirectory(prefix="wiz-attest-repro-") as tmp:
            tmp = Path(tmp)
            out_a = tmp / "a/prog"
            out_b = tmp / "b/prog"
            out_a.parent.mkdir(parents=True)
            out_b.parent.mkdir(parents=True)
            env_b = dict(os.environ)
            env_b.update({"TZ": "Asia/Tokyo", "SOURCE_DATE_EPOCH": "1234567890",
                          "HOME": str(tmp / "home")})
            (tmp / "home").mkdir()
            cmd_a = [str(wiz), *flags, "-I", str(REPO / "lib"),
                     "--no-cache", "build", str(source), "-o", str(out_a)]
            cmd_b = [str(wiz), *flags, "-I", str(REPO / "lib"),
                     "--cache", str(tmp / "cache"), "build", str(source),
                     "-o", str(out_b)]
            env_a = dict(os.environ)
            for cmd, env, cwd in ((cmd_a, env_a, str(REPO)),
                                  (cmd_b, env_b, str(tmp))):
                proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True,
                                      text=True, timeout=600)
                self.assertEqual(proc.returncode, 0,
                                 f"{cmd[0]}: {proc.stderr[-2000:]}")
            digest_a = wa.sha256_file(Path(str(out_a) + ".c"))
            digest_b = wa.sha256_file(Path(str(out_b) + ".c"))
            self.assertEqual(digest_a, digest_b)


# --------------------------------------------------------------------------
# Optional: a real TPM quote


def _tpm_tool(name: str) -> str | None:
    binary = os.environ.get("WIZ_TPM2_BIN")
    if binary:
        candidate = Path(binary) / name
        if candidate.is_file():
            return str(candidate)
    return shutil.which(name)


def _tpm_available() -> bool:
    if os.environ.get("WIZ_ATTEST_TPM") != "1":
        return False
    if _tpm_tool("tpm2_quote") is None or _tpm_tool("tpm2_checkquote") is None:
        return False
    if os.access("/dev/tpmrm0", os.R_OK | os.W_OK):
        return True
    return os.environ.get("WIZ_ATTEST_TPM_SUDO") == "1"


TPM_GATE = (os.environ.get("WIZ_ATTEST_TPM") == "1" and _tpm_available())


@unittest.skipUnless(TPM_GATE, "set WIZ_ATTEST_TPM=1 with tpm2-tools and /dev/tpmrm0")
class TpmIntegrationTests(unittest.TestCase):
    PCRS = "sha256:7,11"

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="wiz-attest-tpm-"))
        self.sudo = os.environ.get("WIZ_ATTEST_TPM_SUDO") == "1"
        self.tpm2_bin = os.environ.get("WIZ_TPM2_BIN")

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def _tpm(self, name: str, *args: str) -> subprocess.CompletedProcess[str]:
        cmd = ([_tpm_tool("sudo") or "sudo", "-n"] if self.sudo else [])
        cmd.append(_tpm_tool(name) or name)
        return subprocess.run(cmd + list(args), capture_output=True, text=True,
                              timeout=120)

    def _read_pcrs(self) -> dict[str, str]:
        proc = self._tpm("tpm2_pcrread", self.PCRS)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        values: dict[str, str] = {}
        for line in proc.stdout.splitlines():
            match = re.match(r"\s*(\d+)\s*:\s*0x([0-9A-Fa-f]{64})", line)
            if match:
                values[match.group(1)] = match.group(2).lower()
        self.assertEqual(set(values), {"7", "11"}, proc.stdout)
        return values

    def test_real_quote_verifies_and_detects_tampering(self):
        artifact = self.tmp / "prog"
        artifact.write_bytes(b"tpm integration artifact\n")
        nonce = os.urandom(32).hex()
        out = self.tmp / "out"
        key = self.tmp / "signing-key"
        keygen = run_attest(["keygen", "--key", str(key)])
        self.assertEqual(keygen.returncode, 0, keygen.stderr)
        args = [
            "--artifact", str(artifact), "--out", str(out),
            "--pcr-list", self.PCRS, "--nonce", nonce,
            "--sign-key", str(key),
            "--wiz-version", "0.1.0-dev", "--target", "x86_64-linux-gnu",
            "--source-entry", "examples/io.wiz",
            "--source-sha256", "22" * 32,
        ]
        if self.tpm2_bin:
            args += ["--tpm2-bin", self.tpm2_bin]
        if self.sudo:
            args.append("--sudo")
        proc = run_attest(args)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        for name in ("manifest.json", "manifest.intoto.json",
                     "manifest.intoto.json.sig", "quote.msg", "quote.sig",
                     "quote.pcr", "ak.pub", "quote.nonce"):
            self.assertTrue((out / name).is_file(), name)

        pcrs = self._read_pcrs()
        ak = wa.ak_info(out / "ak.pub")
        policy = {
            "schema": wa.POLICY_SCHEMA,
            "bank": "sha256",
            "pcr": pcrs,
            "ak_spki_sha256": ak.spki_sha256,
            "ak_name": ak.name,
        }
        policy_path = self.tmp / "policy.json"
        policy_path.write_text(json.dumps(policy), encoding="utf-8")

        verify_args = [
            "--manifest", str(out / "manifest.json"),
            "--policy", str(policy_path),
            "--nonce", nonce,
            "--public-key", str(key) + ".pub",
            "--ak-spki-sha256", ak.spki_sha256,
            "--ak-name", ak.name,
            "--artifacts-dir", str(self.tmp),
        ]
        if self.tpm2_bin:
            verify_args += ["--tpm2-bin", self.tpm2_bin]
        code, out_text, err = run_verify(verify_args + ["--json"])
        self.assertEqual(code, wa.EXIT_OK, err + out_text)
        result = json.loads(out_text)
        self.assertEqual(result["status"], "verified")
        self.assertEqual(result["manifest_sha256"],
                         wa.sha256_file(out / "manifest.json"))

        # A different PCR policy fails before any cryptographic check.
        bad_policy = json.loads(json.dumps(policy))
        bad_policy["pcr"]["7"] = "00" * 32
        policy_path.write_text(json.dumps(bad_policy), encoding="utf-8")
        code, _, _ = run_verify([
            "--manifest", str(out / "manifest.json"),
            "--policy", str(policy_path),
            "--nonce", nonce,
            "--public-key", str(key) + ".pub",
            "--ak-spki-sha256", ak.spki_sha256,
            "--ak-name", ak.name,
            "--skip-crypto", "--json",
        ])
        self.assertEqual(code, wa.EXIT_FAIL)

        # Tampering with an artifact is caught by the manifest digest.
        artifact.write_bytes(artifact.read_bytes() + b"x")
        code, _, _ = run_verify(verify_args + ["--json"])
        self.assertEqual(code, wa.EXIT_FAIL)


if __name__ == "__main__":
    unittest.main()
