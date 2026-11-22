#!/usr/bin/env python3
"""Tests for scripts/source-tarball.py --sbom and scripts/release-sbom.py.

Run: python3 scripts/test_release_sbom.py -v

No Wiz build, TPM, network or committed key: the tests build a tiny synthetic source
tree and a fake binary tarball, then check the SBOMs parse, their digests match the
archives and each other, the provenance subjects and inputs are the expected ones, two
runs are byte-identical, and the optional E1 signing path verifies with ssh-keygen.
"""

from __future__ import annotations

import base64
import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def _repo_root() -> Path:
    """The checkout with flake.lock/LICENSE, also when this file is in .release-tools."""
    for candidate in (Path.cwd(), ROOT, ROOT.parent):
        if (candidate / "flake.lock").is_file() and \
           (candidate / "scripts" / "bundle-cc.sources").is_file():
            return candidate
    return ROOT


REPO = _repo_root()
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "attest"))

import sbom  # noqa: E402

SOURCE = HERE / "source-tarball.py"
RELEASE = HERE / "release-sbom.py"
WIZ_ATTEST = HERE / "attest" / "wiz-attest"
REVISION = "0123456789abcdef0123456789abcdef01234567"
EPOCH = "1700000000"
BUILDER = ("https://github.com/wiz-pl/wiz/.github/workflows/release.yml"
           "@refs/tags/v0.1.0")


def sha(path: Path) -> str:
    return sbom.sha256_file(path)


def run(cmd: list[str], *, cwd: Path | None = None,
        env: dict[str, str] | None = None, check: bool = True
        ) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(cmd, cwd=str(cwd or ROOT), env=env,
                          capture_output=True, text=True)
    if check and proc.returncode != 0:
        raise AssertionError(
            f"{' '.join(cmd)} failed ({proc.returncode})\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}")
    return proc


def make_fixture(base: Path) -> Path:
    root = base / "fixture"
    (root / "Wiz").mkdir(parents=True)
    (root / "lib").mkdir()
    (root / "scripts").mkdir()
    (root / ".github" / "workflows").mkdir(parents=True)
    (root / "Wiz" / "Version.lean").write_text(
        'def version : String := "0.1.0-test"\n', encoding="utf-8")
    (root / "lib" / "Prelude.wiz").write_text("module Prelude\n", encoding="utf-8")
    for name in ("LICENSE", "COPYING.RUNTIME"):
        if (REPO / name).is_file():
            shutil.copyfile(REPO / name, root / name)
        else:
            (root / name).write_text("GPL-3.0-or-later\n", encoding="utf-8")
    if (REPO / "flake.lock").is_file():
        shutil.copyfile(REPO / "flake.lock", root / "flake.lock")
    else:
        (root / "flake.lock").write_text(json.dumps({
            "nodes": {"root": {"inputs": {"nixpkgs": "nixpkgs"}},
                      "nixpkgs": {"locked": {
                          "type": "github", "owner": "NixOS", "repo": "nixpkgs",
                          "rev": "0" * 40,
                          "narHash": "sha256-" + base64.b64encode(b"\0" * 32).decode(),
                      }}},
            "root": "root", "version": 7,
        }), encoding="utf-8")
    if (REPO / "lean-toolchain").is_file():
        shutil.copyfile(REPO / "lean-toolchain", root / "lean-toolchain")
    else:
        (root / "lean-toolchain").write_text(
            "leanprover/lean4:v4.35.0\n", encoding="utf-8")
    workflow = REPO / ".github" / "workflows" / "release.yml"
    if workflow.is_file():
        shutil.copyfile(workflow, root / ".github" / "workflows" / "release.yml")
    else:
        (root / ".github" / "workflows" / "release.yml").write_text(
            "runs-on: ubuntu-latest\n"
            "steps:\n"
            "  - uses: actions/checkout@v5\n"
            "  - uses: mymindstorm/setup-emsdk@v14\n"
            "    with:\n"
            "      version: 6.0.9\n", encoding="utf-8")
    sources = REPO / "scripts" / "bundle-cc.sources"
    if sources.is_file():
        shutil.copyfile(sources, root / "scripts" / "bundle-cc.sources")
    else:
        (root / "scripts" / "bundle-cc.sources").write_text(
            "gmp-6.3.0.tar.xz "
            "a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898 "
            "https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz\n"
            "gc-8.2.8.tar.gz "
            "7649020621cb26325e1fb5c8742590d92fb48ce5c259b502faf7d9fb5dabb160 "
            "https://github.com/ivmai/bdwgc/releases/download/v8.2.8/gc-8.2.8.tar.gz\n",
            encoding="utf-8")
    return root


def make_binary_tarball(base: Path, fixture: Path) -> Path:
    top = "wiz-x86_64-linux"
    out = base / f"{top}.tar.gz"
    files = {
        "bin/wiz": (b"#!/bin/sh\nexec wiz \"$@\"\n", 0o755),
        "bin/grail": (b"#!/bin/sh\nexec grail \"$@\"\n", 0o755),
        "share/wiz/.lake/build/bin/wiz": (b"\x7fELF wiz\n", 0o755),
        "share/wiz/.lake/build/bin/grail": (b"\x7fELF grail\n", 0o755),
        "share/wiz/lib/Prelude.wiz": (b"module Prelude\n", 0o644),
        "share/wiz/LICENSE": ((fixture / "LICENSE").read_bytes(), 0o644),
        "share/wiz/COPYING.RUNTIME":
            ((fixture / "COPYING.RUNTIME").read_bytes(), 0o644),
        "share/wiz/NOTICE": (b"Wiz\nCopyright (C) 2026 Reuben Steenekamp\n", 0o644),
        "share/wiz/LICENSES/mimalloc-LICENSE": (b"MIT License\n", 0o644),
        "share/wiz/REVISION": ((REVISION + "\n").encode(), 0o644),
        "share/wiz/TOOLCHAIN": (b"A Wiz toolchain\n", 0o644),
        "share/wiz/cc/VERSIONS": (
            b"clang, ld.lld, compiler-rt: from lean4 "
            b"(Ubuntu clang version 18.1.8)\n"
            b"cadical: from lean4 (2.1.0)\n"
            b"glibc 2.27 (libc6, libc6-dev 2.27-3ubuntu1.6), "
            b"Linux headers 4.15\n"
            b"GMP 6.3.0 (static), Boehm GC 8.2.8\n", 0o644),
    }
    with tarfile.open(out, "w:gz", format=tarfile.GNU_FORMAT) as tf:
        info = tarfile.TarInfo(top)
        info.type = tarfile.DIRTYPE
        info.mode = 0o755
        info.mtime = int(EPOCH)
        info.uid = info.gid = 0
        tf.addfile(info)
        for path in sorted(files):
            data, mode = files[path]
            info = tarfile.TarInfo(f"{top}/{path}")
            info.size = len(data)
            info.mode = mode
            info.mtime = int(EPOCH)
            info.uid = info.gid = 0
            tf.addfile(info, io.BytesIO(data))
    return out


class ReleaseSbomTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.tmp = Path(tempfile.mkdtemp(prefix="wiz-sbom-test-"))
        cls.fixture = make_fixture(cls.tmp)
        cls.a = cls.tmp / "source-a"
        cls.b = cls.tmp / "source-b"
        base_env = os.environ.copy()
        base_env["SOURCE_DATE_EPOCH"] = EPOCH
        run([sys.executable, str(SOURCE), "--root", str(cls.fixture),
             "--out", str(cls.a), "--mode", "tree", "--revision", REVISION],
            cwd=cls.tmp, env={**base_env, "TZ": "UTC", "LANG": "C"})
        env_b = {**base_env, "TZ": "Asia/Tokyo", "LANG": "en_US.UTF-8",
                 "HOME": str(cls.tmp / "home"),
                 "PYTHONPYCACHEPREFIX": str(cls.tmp / "pycache")}
        run([sys.executable, str(SOURCE), "--root", str(cls.fixture),
             "--out", str(cls.b), "--mode", "tree", "--revision", REVISION],
            cwd=cls.tmp, env=env_b)
        cls.manifest_path = cls.a / "wiz-0.1.0-test-src.tar.gz.manifest.json"
        cls.manifest = json.loads(cls.manifest_path.read_bytes())
        cls.source_tar = cls.a / cls.manifest["tarball"]["file"]
        cls.source_cdx = cls.a / cls.manifest["sbom"]["file"]
        cls.binary = make_binary_tarball(cls.tmp, cls.fixture)
        cls.out1 = cls.tmp / "out1"
        cls.out2 = cls.tmp / "out2"
        for out in (cls.out1, cls.out2):
            out.mkdir()
            shutil.copy2(cls.source_tar, out / cls.source_tar.name)
            shutil.copy2(cls.manifest_path, out / cls.manifest_path.name)
            shutil.copy2(cls.source_cdx, out / cls.source_cdx.name)
            shutil.copy2(cls.binary, out / cls.binary.name)
        cls.args = [
            sys.executable, str(RELEASE), "--root", str(cls.fixture),
            "--channel", "tag", "--builder-id", BUILDER,
            "--workflow-file", str(cls.fixture / ".github" / "workflows" / "release.yml"),
            "--workflow-ref", "refs/tags/v0.1.0",
            "--invocation-id", "run-1/attempt-1", "--json",
        ]
        cls.summary1 = json.loads(run(
            cls.args + ["--out", str(cls.out1),
                        "--source-manifest", str(cls.out1 / cls.manifest_path.name),
                        "--binary-tarball", str(cls.out1 / cls.binary.name)]).stdout)
        cls.summary2 = json.loads(run(
            cls.args + ["--out", str(cls.out2),
                        "--source-manifest", str(cls.out2 / cls.manifest_path.name),
                        "--binary-tarball", str(cls.out2 / cls.binary.name)]).stdout)
        cls.binary_cdx = cls.out1 / cls.summary1["binary"]["sbom"]["file"]
        cls.provenance = cls.out1 / cls.summary1["provenance"]["file"]

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_source_manifest_records_a_matching_sbom(self) -> None:
        raw = self.manifest_path.read_bytes()
        self.assertEqual(raw, sbom.canonical_bytes(self.manifest))
        self.assertEqual(self.manifest["schema"], "wiz-source-tarball/v1")
        self.assertEqual(self.manifest["version"], "0.1.0-test")
        recorded = self.manifest["sbom"]
        self.assertEqual(sha(self.source_cdx), recorded["sha256"])
        self.assertEqual(recorded["schema"], "CycloneDX-1.6")
        document = json.loads(self.source_cdx.read_bytes())
        self.assertEqual(document["bomFormat"], "CycloneDX")
        self.assertEqual(document["specVersion"], "1.6")
        top = document["metadata"]["component"]
        self.assertEqual(
            {h["alg"]: h["content"] for h in top["hashes"]}["SHA-256"],
            self.manifest["tarball"]["sha256"])
        by_path = {}
        for component in document["components"]:
            props = {p["name"]: p["value"] for p in component.get("properties", [])}
            if "wiz:path" in props:
                by_path[props["wiz:path"]] = {
                    "sha256": {h["alg"]: h["content"]
                               for h in component.get("hashes", [])}["SHA-256"],
                    "size": props["wiz:size"],
                }
        self.assertEqual(set(by_path), {f["path"] for f in self.manifest["files"]})
        for entry in self.manifest["files"]:
            self.assertEqual(by_path[entry["path"]]["sha256"], entry["sha256"])
            self.assertEqual(str(by_path[entry["path"]]["size"]), str(entry["size"]))
        refs = [c["bom-ref"] for c in document["components"]]
        self.assertEqual(len(refs), len(set(refs)))
        self.assertEqual(len(document["dependencies"]), 1)
        self.assertEqual(set(document["dependencies"][0]["dependsOn"]), set(refs))

    def test_source_sbom_lists_the_build_inputs_and_licences(self) -> None:
        document = json.loads(self.source_cdx.read_bytes())
        by_ref = {c["bom-ref"]: c for c in document["components"]}
        for entry in sbom.parse_bundle_sources(self.fixture):
            component = by_ref[f"input:{entry['file']}"]
            self.assertEqual(
                {h["alg"]: h["content"] for h in component["hashes"]}["SHA-256"],
                entry["sha256"])
            self.assertIn("licenses", component)
        self.assertIn("toolchain:lean", by_ref)
        self.assertIn("nix:nixpkgs", by_ref)
        self.assertIn("gha:actions/checkout@v5", by_ref)
        self.assertIn("gha:mymindstorm/setup-emsdk@v14", by_ref)
        self.assertEqual(by_ref["toolchain:lean"]["version"], "v4.35.0")
        self.assertEqual(
            by_ref["input:gmp-6.3.0.tar.xz"]["licenses"][0]["expression"],
            "LGPL-3.0-or-later OR GPL-2.0-or-later")

    def test_source_tarball_is_deterministic(self) -> None:
        a_tar = self.a / self.manifest["tarball"]["file"]
        b_manifest_path = self.b / self.manifest_path.name
        b_manifest = json.loads(b_manifest_path.read_bytes())
        b_tar = self.b / b_manifest["tarball"]["file"]
        self.assertEqual(a_tar.read_bytes(), b_tar.read_bytes())
        self.assertEqual(self.manifest_path.read_bytes(),
                         b_manifest_path.read_bytes())
        self.assertEqual((self.a / (self.manifest["tarball"]["file"] + ".sha256"))
                         .read_bytes(),
                         (self.b / (b_manifest["tarball"]["file"] + ".sha256"))
                         .read_bytes())
        self.assertEqual(self.source_cdx.read_bytes(),
                         (self.b / b_manifest["sbom"]["file"]).read_bytes())

    def test_binary_sbom_matches_the_tarball(self) -> None:
        document = json.loads(self.binary_cdx.read_bytes())
        self.assertEqual(document["bomFormat"], "CycloneDX")
        self.assertEqual(document["specVersion"], "1.6")
        top = document["metadata"]["component"]
        self.assertEqual(
            {h["alg"]: h["content"] for h in top["hashes"]}["SHA-256"],
            sha(self.binary))
        entries = {}
        with tarfile.open(self.binary, "r:gz") as tf:
            for member in tf.getmembers():
                if not member.isfile():
                    continue
                data = tf.extractfile(member).read()
                entries[member.name.split("/", 1)[1]] = hashlib.sha256(data).hexdigest()
        by_path = {}
        for component in document["components"]:
            props = {p["name"]: p["value"] for p in component.get("properties", [])}
            if "wiz:path" in props:
                by_path[props["wiz:path"]] = {
                    h["alg"]: h["content"] for h in component.get("hashes", [])
                }.get("SHA-256")
        self.assertEqual(set(by_path), set(entries))
        for path, digest in entries.items():
            self.assertEqual(by_path[path], digest)
        refs = {c["bom-ref"] for c in document["components"]}
        self.assertIn("input:gmp-6.3.0.tar.xz", refs)
        self.assertIn("input:gc-8.2.8.tar.gz", refs)
        self.assertIn("wiz:bundled-c-toolchain", refs)
        bundled = next(c for c in document["components"]
                       if c["bom-ref"] == "wiz:bundled-c-toolchain")
        props = {p["name"]: p["value"] for p in bundled["properties"]}
        self.assertIn("GMP 6.3.0", props["wiz:resolved-gmp"])

    def test_provenance_digests_builder_and_no_slsa_level(self) -> None:
        statement = json.loads(self.provenance.read_bytes())
        self.assertEqual(statement["_type"], "https://in-toto.io/Statement/v1")
        self.assertEqual(statement["predicateType"],
                         "https://slsa.dev/provenance/v1")
        subjects = {s["name"]: s["digest"]["sha256"] for s in statement["subject"]}
        for path in (self.source_tar, self.manifest_path, self.source_cdx,
                     self.binary, self.binary_cdx):
            self.assertEqual(subjects[path.name], sha(path))
        predicate = statement["predicate"]
        self.assertEqual(predicate["buildDefinition"]["buildType"],
                         "https://wiz-lang.dev/buildtypes/wiz-release/v1")
        self.assertEqual(predicate["runDetails"]["builder"]["id"], BUILDER)
        self.assertEqual(predicate["runDetails"]["metadata"]["invocationId"],
                         "run-1/attempt-1")
        self.assertIsNone(predicate["wiz:slsaLevelClaimed"])
        self.assertNotIn("slsaLevel", predicate)
        self.assertNotIn(str(self.fixture), self.provenance.read_text())
        dependencies = {d["uri"]: d for d in
                        predicate["buildDefinition"]["resolvedDependencies"]}
        self.assertIn(f"git+https://github.com/wiz-pl/wiz@{REVISION}", dependencies)
        for entry in sbom.parse_bundle_sources(self.fixture):
            self.assertEqual(
                dependencies[f"wiz:bundle-input/{entry['file']}"]["digest"]["sha256"],
                entry["sha256"])
        self.assertIn("wiz:source-tree", dependencies)
        self.assertIn("wiz:lean-toolchain", dependencies)
        self.assertIn("wiz:flake-lock", dependencies)
        self.assertIn("gha:actions/checkout@v5",
                      {d["uri"] for d in
                       predicate["buildDefinition"]["resolvedDependencies"]})
        self.assertNotIn("digest", dependencies["gha:actions/checkout@v5"])
        self.assertEqual(
            dependencies["gha:actions/checkout@v5"]["annotations"]["wiz:pinned"],
            "false")
        self.assertFalse(predicate["wiz:note"].startswith("SLSA L"))

    def test_outputs_are_deterministic(self) -> None:
        self.assertEqual(self.summary1["provenance"]["sha256"],
                         self.summary2["provenance"]["sha256"])
        self.assertEqual((self.out1 / "provenance.intoto.json").read_bytes(),
                         (self.out2 / "provenance.intoto.json").read_bytes())
        self.assertEqual(
            (self.out1 / self.summary1["binary"]["sbom"]["file"]).read_bytes(),
            (self.out2 / self.summary2["binary"]["sbom"]["file"]).read_bytes())

    def test_release_manifest_is_filled_from_the_artifacts(self) -> None:
        skeleton = REPO / "docs" / "release" / "release-manifest.json"
        if not skeleton.is_file():
            self.skipTest("the checked-in release-manifest.json skeleton is absent")
        out = self.tmp / "release-record"
        out.mkdir()
        for path in (self.source_tar, self.manifest_path, self.source_cdx,
                     self.binary):
            shutil.copy2(path, out / path.name)
        summary = json.loads(run(
            self.args + ["--out", str(out),
                         "--source-manifest", str(out / self.manifest_path.name),
                         "--binary-tarball", str(out / self.binary.name),
                         "--release-manifest", str(skeleton),
                         "--tag", "v0.1.0"]).stdout)
        record_path = out / "release-manifest.json"
        record = json.loads(record_path.read_bytes())
        self.assertEqual(summary["releaseManifest"]["sha256"], sha(record_path))
        self.assertEqual(record["version"], "0.1.0-test")
        self.assertEqual(record["commit"], REVISION)
        self.assertEqual(record["tag"], "v0.1.0")
        self.assertEqual(record["source"]["tarball"]["sha256"],
                         self.manifest["tarball"]["sha256"])
        self.assertEqual(record["source"]["tarball"]["sbom"]["sha256"],
                         self.manifest["sbom"]["sha256"])
        self.assertEqual(record["supplyChain"]["provenance"]["sha256"],
                         summary["provenance"]["sha256"])
        self.assertIsNone(record["supplyChain"]["provenance"]["slsaLevelClaimed"])
        names = {artifact["name"] for artifact in record["artifacts"]}
        self.assertIn(self.source_tar.name, names)
        self.assertIn(self.binary.name, names)
        self.assertIn(self.binary_cdx.name, names)
        self.assertIn("provenance.intoto.json", names)
        self.assertTrue(all(artifact["sha256"] for artifact in record["artifacts"]))

    def test_a_tampered_source_sbom_is_rejected(self) -> None:
        out = self.tmp / "tampered"
        out.mkdir()
        for path in (self.source_tar, self.manifest_path, self.source_cdx):
            shutil.copy2(path, out / path.name)
        shutil.copy2(self.binary, out / self.binary.name)
        cdx = out / self.source_cdx.name
        document = json.loads(cdx.read_bytes())
        document["components"][0]["name"] = "changed"
        cdx.write_bytes(sbom.canonical_bytes(document))
        proc = run(self.args[:-1] + ["--out", str(out),
                                     "--source-manifest", str(out / self.manifest_path.name),
                                     "--binary-tarball", str(out / self.binary.name)],
                   check=False)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("SHA-256 does not match manifest", proc.stderr)

    @unittest.skipUnless(shutil.which("ssh-keygen"), "ssh-keygen is required")
    def test_signing_uses_the_e1_key_path(self) -> None:
        out = self.tmp / "signed"
        out.mkdir()
        for path in (self.source_tar, self.manifest_path, self.source_cdx,
                     self.binary):
            shutil.copy2(path, out / path.name)
        key = out / "attest-key"
        run([str(WIZ_ATTEST), "keygen", "--key", str(key), "--json"])
        summary = json.loads(run(
            self.args + ["--out", str(out),
                         "--source-manifest", str(out / self.manifest_path.name),
                         "--binary-tarball", str(out / self.binary.name),
                         "--sign-key", str(key)]).stdout)
        self.assertTrue(summary["provenance"]["signed"])
        self.assertIsNone(summary["provenance"]["slsaLevelClaimed"])
        envelope_path = out / summary["provenance"]["signature"]["envelope"]
        statement = json.loads((out / "provenance.intoto.json").read_bytes())
        payload = sbom.canonical_bytes(statement)
        envelope = json.loads(envelope_path.read_bytes())
        self.assertEqual(envelope["payloadType"], "application/vnd.in-toto+json")
        self.assertEqual(base64.b64decode(envelope["payload"]), payload)
        import wiz_attest  # noqa: PLC0415
        public = wiz_attest.parse_public_key(Path(str(key) + ".pub"))
        signature = base64.b64decode(envelope["signatures"][0]["sig"])
        ok, detail = wiz_attest.verify_pae(
            public, signature,
            wiz_attest.dsse_pae(envelope["payloadType"], payload))
        self.assertTrue(ok, detail)
        self.assertEqual(summary["provenance"]["signature"]["keyid"],
                         public.fingerprint)


if __name__ == "__main__":
    unittest.main(verbosity=2)
