#!/usr/bin/env python3
"""End-to-end tests: `wiz build --attest` -> `wiz-attest sign` -> `wiz-verify`.

These need a built `wiz` (and `grail` for the package case), a C toolchain and
`ssh-keygen`.  They are opt-in because they build real programs:

    WIZ_ATTEST_E2E=1 WIZ_BIN=.lake/build/bin/wiz \
      python3 -m unittest discover -s scripts/attest/tests -v

The unit suite (`test_attest.py`) runs without a build; this file is skipped in
the `attestation verifier` CI job unless the environment is set.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
WIZ_ATTEST = HERE.parent / "wiz-attest"
WIZ_VERIFY = HERE.parent / "wiz-verify"
WIZ = Path(os.environ.get("WIZ_BIN", REPO / ".lake/build/bin/wiz"))
GRAIL = Path(os.environ.get("GRAIL_BIN", REPO / ".lake/build/bin/grail"))
ENABLED = os.environ.get("WIZ_ATTEST_E2E") == "1" and WIZ.is_file()


def local_settings() -> dict[str, str]:
    """Read the machine's uncommitted `grail.local.wiz` Settings.set values."""
    path = REPO / "grail.local.wiz"
    if not path.is_file():
        return {}
    text = path.read_text(encoding="utf-8")
    return {m.group(1): m.group(2)
            for m in re.finditer(r'Settings\.set\s+"([^"]+)"\s+"([^"]*)"', text)}


def toolchain_flags() -> list[str]:
    settings = local_settings()
    return [
        "--cc", os.environ.get("WIZ_CC", "cc"),
        "--cflags", settings.get("cflags", ""),
        "--ldflags", settings.get("ldflags", ""),
        "--libs", settings.get("libs", "-lm"),
        "--gmp", settings.get("gmp", "-lgmp"),
        "--llc", settings.get("llc", "llc"),
        "--gc-cflags", settings.get("gc-cflags", ""),
        "--gc-ldflags", settings.get("gc-ldflags", ""),
        "-I", str(REPO / "lib"),
    ]


def run(cmd: list[str], cwd: Path, timeout: int = 900) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True,
                          timeout=timeout)


def verify(work: Path, attest: Path, *extra: str) -> subprocess.CompletedProcess[str]:
    return run([sys.executable, str(WIZ_VERIFY), "--attest", str(attest),
                "--statement-only", "--module-root", str(REPO / "lib"),
                "--json", *extra], work)


@unittest.skipUnless(ENABLED, "set WIZ_ATTEST_E2E=1 and build wiz")
class EndToEndTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="wiz-attest-e2e-"))
        self.write_project()
        self.key = self.tmp / "key"
        proc = run([sys.executable, str(WIZ_ATTEST), "keygen",
                    "--key", str(self.key), "--json"], self.tmp)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.pub = Path(str(self.key) + ".pub")

    def tearDown(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    def write_project(self) -> None:
        (self.tmp / "hello.wiz").write_text(
            'import IO\nlink_c "extra.c"\n'
            'def main : IO Unit := IO.println "attested hello"\n',
            encoding="utf-8")
        (self.tmp / "extra.c").write_text(
            "int wiz_attest_extra(void) { return 1; }\n", encoding="utf-8")

    def build(self, attest: str = "prog.attest.json") -> subprocess.CompletedProcess[str]:
        return run([str(WIZ), *toolchain_flags(), "build", "hello.wiz",
                    "-o", "prog", "--attest", attest], self.tmp)

    def sign(self, attest: Path, out: Path, key: Path | None = None) -> dict:
        proc = run([sys.executable, str(WIZ_ATTEST), "sign",
                    "--attest", str(attest), "--key", str(key or self.key),
                    "--out", str(out), "--json"], self.tmp)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        return json.loads(proc.stdout)

    def test_build_sign_verify_and_tamper_cases(self):
        built = self.build()
        self.assertEqual(built.returncode, 0, built.stderr)
        unsigned = self.tmp / "prog.attest.json"
        self.assertTrue(unsigned.is_file())
        signed = self.tmp / "prog.signed.json"
        info = self.sign(unsigned, signed)
        self.assertTrue(info["signed"])

        ok = verify(self.tmp, signed, "--public-key", str(self.pub))
        self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
        result = json.loads(ok.stdout)
        self.assertEqual(result["status"], "verified")
        checks = {c["name"]: c["status"] for c in result["checks"]}
        self.assertEqual(checks["dsse_signature"], "pass")
        self.assertEqual(checks["inputs"], "pass")
        self.assertEqual(result["statement_sha256"], info["statement_sha256"])

        # An unsigned producer envelope is not verified by default.
        refused = verify(self.tmp, unsigned)
        self.assertEqual(refused.returncode, 1, refused.stdout)
        self.assertEqual(json.loads(refused.stdout)["status"], "failed")
        allowed = verify(self.tmp, unsigned, "--allow-unsigned")
        self.assertEqual(allowed.returncode, 0, allowed.stdout + allowed.stderr)
        self.assertFalse(json.loads(allowed.stdout)["signed"])

        # Wrong key.
        other = self.tmp / "other"
        run([sys.executable, str(WIZ_ATTEST), "keygen", "--key", str(other)], self.tmp)
        wrong = verify(self.tmp, signed, "--public-key", str(other) + ".pub")
        self.assertEqual(wrong.returncode, 1, wrong.stdout)

        # Tampered artifact.
        prog = self.tmp / "prog"
        original = prog.read_bytes()
        prog.write_bytes(original + b"x")
        tampered = verify(self.tmp, signed, "--public-key", str(self.pub))
        self.assertEqual(tampered.returncode, 1, tampered.stdout)
        self.assertIn("artifact", json.loads(tampered.stdout)["errors"][0])
        prog.write_bytes(original)

        # Tampered generated C (a byproduct subject, not only the executable).
        c_file = self.tmp / "prog.c"
        original_c = c_file.read_bytes()
        c_file.write_bytes(original_c + b"/* tampered */\n")
        tampered_c = verify(self.tmp, signed, "--public-key", str(self.pub))
        self.assertEqual(tampered_c.returncode, 1, tampered_c.stdout)
        self.assertIn("prog.c", tampered_c.stdout)
        c_file.write_bytes(original_c)

        # Deterministic artefact and envelope.
        first = (self.tmp / "first.json")
        second = (self.tmp / "second.json")
        self.sign(unsigned, first)
        self.sign(unsigned, second)
        self.assertEqual(first.read_bytes(), second.read_bytes())

    def test_rebuild_is_byte_identical(self):
        self.assertEqual(self.build("a.json").returncode, 0)
        first = (self.tmp / "a.json").read_bytes()
        self.assertEqual(self.build("b.json").returncode, 0)
        second = (self.tmp / "b.json").read_bytes()
        self.assertEqual(first, second)

    @unittest.skipUnless(GRAIL.is_file(), "grail is not built")
    def test_grail_build_attest(self):
        pkg = self.tmp / "pkg"
        proc = run([str(GRAIL), "new", "tiny", "--dir", str(pkg)], self.tmp)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        adir = self.tmp / "grail-attest"
        built = run([str(GRAIL), *toolchain_flags(), "-C", str(pkg),
                     "build", "--attest", str(adir)], self.tmp,
                    timeout=1800)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        attest = adir / "tiny.attest.json"
        self.assertTrue(attest.is_file(), list(adir.glob("*")))
        signed = self.tmp / "tiny.signed.json"
        self.sign(attest, signed)
        proc = run([sys.executable, str(WIZ_VERIFY), "--attest", str(signed),
                    "--statement-only", "--artifacts-dir",
                    str(pkg / ".grail/bin"),
                    "--module-root", str(pkg / "src"),
                    "--module-root", str(REPO / "lib"),
                    "--public-key", str(self.pub), "--json"], self.tmp)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)


if __name__ == "__main__":
    unittest.main()
