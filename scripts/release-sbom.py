#!/usr/bin/env python3
"""Write the release SBOMs and the SLSA-style provenance statement.

    scripts/release-sbom.py --out dist [options]

It consumes the artifacts the release workflow already writes:

* ``wiz-<version>-src.tar.gz`` and its canonical ``.manifest.json`` (and the source
  SBOM recorded in that manifest, from ``scripts/source-tarball.py``);
* ``wiz-<arch>-linux.tar.gz`` (the binary tarball);

and writes beside them:

* ``wiz-<arch>-linux.tar.gz.cdx.json`` — CycloneDX 1.6 for the binary tarball;
* ``provenance.intoto.json`` — an in-toto Statement v1 whose predicate is the SLSA
  provenance v1 shape.  It records the builder id, the git commit, the source tree,
  the source and binary tarballs, both SBOMs, the Lean toolchain, Nix inputs and the
  bundled C inputs.  It is a claim, not a hosted SLSA level: no level is claimed.
* with ``--sign-key``, ``provenance.intoto.json.dsse`` and ``.sig``: the existing E1
  offline Ed25519/DSSE path from ``scripts/attest``.

Everything is canonical JSON with no timestamp, host name, absolute path or random id.
The same inputs and options produce byte-identical files.

Exit status: 0 written, 2 usage or input error, 3 a required tool is missing (only when
signing was asked for).
"""

from __future__ import annotations

import argparse
import copy
import datetime
import glob
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import sbom  # noqa: E402


def die(message: str, code: int = 2) -> "NoReturn":  # type: ignore[name-defined]
    print(f"release-sbom: {message}", file=sys.stderr)
    raise SystemExit(code)


def _one(pattern: str, what: str) -> Path:
    matches = sorted(Path(p) for p in glob.glob(pattern))
    if not matches:
        die(f"no {what} matching {pattern}")
    if len(matches) > 1:
        die(f"more than one {what} matching {pattern}: "
            + ", ".join(str(p) for p in matches))
    return matches[0]


def _git_revision(root: Path) -> str:
    try:
        return subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                              check=True, capture_output=True, text=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def _verify_source(manifest_path: Path, manifest: dict[str, Any],
                   root: Path, version: str,
                   workflow_file: str | None) -> tuple[Path, dict[str, Any], dict[str, Any], bool]:
    """Verify (or generate) the source SBOM and check it against the manifest."""
    tarball_info = manifest.get("tarball")
    if not isinstance(tarball_info, dict):
        die(f"{manifest_path}: no tarball object")
    tarball_path = manifest_path.parent / str(tarball_info.get("file", ""))
    if not tarball_path.is_file():
        die(f"{manifest_path}: tarball {tarball_path} is missing")
    actual_tar = sbom.sha256_file(tarball_path)
    if actual_tar != tarball_info.get("sha256"):
        die(f"{tarball_path}: SHA-256 does not match the manifest")

    files = manifest.get("files")
    if not isinstance(files, list):
        die(f"{manifest_path}: files is not a list")
    by_path = {str(entry.get("path")): entry for entry in files}

    recorded = manifest.get("sbom")
    generated = False
    if isinstance(recorded, dict) and recorded.get("file"):
        sbom_path = manifest_path.parent / str(recorded["file"])
        if not sbom_path.is_file():
            die(f"{manifest_path}: recorded SBOM {sbom_path} is missing")
        if sbom.sha256_file(sbom_path) != recorded.get("sha256"):
            die(f"{sbom_path}: SHA-256 does not match manifest sbom.sha256")
        document = sbom.read_json(sbom_path)
    else:
        document = sbom.source_sbom(manifest, root, version=version,
                                    workflow_file=workflow_file)
        sbom_path = Path(str(tarball_path) + ".cdx.json")
        sbom.write_canonical(sbom_path, document)
        generated = True

    if document.get("bomFormat") != "CycloneDX" or document.get("specVersion") != sbom.CDX_SPEC:
        die(f"{sbom_path}: not CycloneDX {sbom.CDX_SPEC}")
    top = document.get("metadata", {}).get("component", {})
    top_hashes = {item.get("alg"): item.get("content")
                  for item in top.get("hashes", [])}
    if top_hashes.get("SHA-256") != tarball_info.get("sha256"):
        die(f"{sbom_path}: top component digest does not match the tarball")
    seen: dict[str, dict[str, Any]] = {}
    refs: set[str] = set()
    for component in document.get("components", []):
        ref = component.get("bom-ref")
        if ref in refs:
            die(f"{sbom_path}: duplicate bom-ref {ref}")
        refs.add(ref)
        props = {item.get("name"): item.get("value")
                 for item in component.get("properties", [])}
        path = props.get("wiz:path")
        if path is None:
            continue
        digest = {item.get("alg"): item.get("content")
                  for item in component.get("hashes", [])}.get("SHA-256")
        seen[path] = {"sha256": digest, "size": props.get("wiz:size"),
                      "mode": props.get("wiz:mode")}
    if set(seen) != set(by_path):
        missing = sorted(set(by_path) - set(seen))
        extra = sorted(set(seen) - set(by_path))
        die(f"{sbom_path}: file set differs from the manifest "
            f"(missing {missing[:3]}, extra {extra[:3]})")
    for path, entry in by_path.items():
        if seen[path]["sha256"] != entry.get("sha256"):
            die(f"{sbom_path}: {path}: digest differs from the manifest")
        if str(seen[path]["size"]) != str(entry.get("size")):
            die(f"{sbom_path}: {path}: size differs from the manifest")
    info = {
        "path": sbom_path,
        "sha256": sbom.sha256_file(sbom_path),
        "components": len(document.get("components", [])),
        "generated": generated,
        "recorded": isinstance(recorded, dict) and bool(recorded.get("file")),
    }
    return sbom_path, document, info, generated


def _fill_release_manifest(skeleton: dict[str, Any], *, summary: dict[str, Any],
                           subjects: list[dict[str, Any]], version: str,
                           revision: str, epoch: int | None, tag: str | None,
                           builder_id: str, lean_reference: str | None) -> dict[str, Any]:
    """Fill the checked-in wiz-release/v1 skeleton from the generated artifacts."""
    record = copy.deepcopy(skeleton)
    record["version"] = version
    record["commit"] = revision
    record["sourceDateEpoch"] = epoch
    if tag:
        record["tag"] = tag
    if epoch is not None:
        record["generatedAt"] = datetime.datetime.fromtimestamp(
            int(epoch), tz=datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    record["filledBy"] = builder_id

    source = summary["source"]
    binary = summary["binary"]
    provenance = summary["provenance"]
    record.setdefault("source", {}).setdefault("tarball", {}).update({
        "name": source["tarball"],
        "sha256": source["tarballSha256"],
        "size": source.get("tarballSize"),
        "manifestSha256": source["manifestSha256"],
        "treeSha256": source["treeSha256"],
        "schema": "wiz-source-tarball/v1",
    })
    record["source"]["tarball"]["sbom"] = {
        "name": source["sbom"]["file"],
        "sha256": source["sbom"]["sha256"],
        "schema": "CycloneDX-1.6",
    }
    kinds = {
        "source": ("source", "any"),
        "source-manifest": ("source-manifest", "any"),
        "source-sbom": ("sbom-source", "any"),
        "binary": ("toolchain", "x86_64-linux"),
        "binary-sbom": ("sbom-binary", "x86_64-linux"),
        "release-manifest": ("release-manifest", "any"),
    }
    artifacts = []
    for subject in subjects:
        kind, system = kinds.get(subject["kind"], (subject["kind"], "any"))
        path = Path(subject["name"])
        artifacts.append({
            "name": path.name,
            "kind": kind,
            "system": system,
            "sha256": subject["sha256"],
            "size": subject.get("size"),
            "url": None,
        })
    record["artifacts"] = artifacts
    if lean_reference:
        record.setdefault("toolchain", {})["lean"] = lean_reference
    record.setdefault("supplyChain", {})["sbom"] = {
        "schema": "CycloneDX-1.6",
        "source": source["sbom"],
        "binary": binary["sbom"],
        "sha256": None,
    }
    record["supplyChain"]["provenance"] = provenance
    record.setdefault("checks", {}).setdefault("supplyChain", {})
    record["checks"]["supplyChain"] = {
        "passed": None,
        "sbom": "see supplyChain.sbom",
        "provenance": provenance["file"],
    }
    return record


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        description="write the release CycloneDX SBOMs and SLSA-style provenance")
    ap.add_argument("--out", default=".", help="directory of the release artifacts")
    ap.add_argument("--source-manifest", help="wiz-*-src.tar.gz.manifest.json")
    ap.add_argument("--binary-tarball", help="wiz-*-linux.tar.gz")
    ap.add_argument("--root", default=".", help="the source checkout (inputs/licenses)")
    ap.add_argument("--version", help="release version (default: the source manifest)")
    ap.add_argument("--revision", help="commit to record (default: the source manifest)")
    ap.add_argument("--channel", default="local",
                    help="tag, snapshot or local (default: local)")
    ap.add_argument("--builder-id", default="https://wiz-lang.org/builders/local",
                    help="SLSA runDetails.builder.id")
    ap.add_argument("--workflow-file", help=".github/workflows/release.yml")
    ap.add_argument("--workflow-ref", help="the ref the builder ran from")
    ap.add_argument("--invocation-id",
                    help="CI run id (GITHUB_RUN_ID/GITHUB_RUN_ATTEMPT); omit locally")
    ap.add_argument("--nix-closure-json",
                    help="nix path-info --json --recursive output (optional)")
    ap.add_argument("--sign-key", help="E1 offline Ed25519 key (optional)")
    ap.add_argument("--release-manifest",
                    help="the checked-in docs/release/release-manifest.json skeleton")
    ap.add_argument("--release-manifest-out",
                    help="write the filled record here (default: OUT/release-manifest.json)")
    ap.add_argument("--tag", help="the release tag, when --channel is tag")
    ap.add_argument("--json", action="store_true", help="print a machine-readable summary")
    args = ap.parse_args(argv)

    out = Path(args.out).resolve()
    root = Path(args.root).resolve()
    if not out.is_dir():
        die(f"output directory {out} does not exist")
    if args.channel not in ("tag", "snapshot", "local"):
        die("--channel must be tag, snapshot or local")

    manifest_path = (Path(args.source_manifest).resolve()
                     if args.source_manifest
                     else _one(str(out / "wiz-*-src.tar.gz.manifest.json"),
                               "source manifest"))
    raw_manifest = manifest_path.read_bytes()
    manifest = sbom.read_json(manifest_path)
    if sbom.canonical_bytes(manifest) != raw_manifest:
        die(f"{manifest_path}: not canonical JSON")
    if manifest.get("schema") != "wiz-source-tarball/v1":
        die(f"{manifest_path}: not a wiz-source-tarball/v1 manifest")
    version = (args.version or manifest.get("version")
               or (str(manifest.get("name", ""))[4:]
                   if str(manifest.get("name", "")).startswith("wiz-")
                   else sbom.version_of(root)))
    revision = args.revision or manifest.get("revision") or _git_revision(root)
    epoch = manifest.get("sourceDateEpoch")
    workflow_file = (str(Path(args.workflow_file).resolve())
                     if args.workflow_file else None)

    source_sbom_path, _, source_info, generated = _verify_source(
        manifest_path, manifest, root, str(version), workflow_file)

    binary_path = (Path(args.binary_tarball).resolve() if args.binary_tarball
                   else _one(str(out / "wiz-*-linux.tar.gz"), "binary tarball"))
    if not binary_path.is_file():
        die(f"binary tarball {binary_path} is missing")
    document, top, _ = sbom.binary_sbom(
        binary_path, root, version=str(version), revision=str(revision),
        workflow_file=workflow_file)
    binary_sbom_path = Path(str(binary_path) + ".cdx.json")
    sbom.write_canonical(binary_sbom_path, document)
    binary_info = {
        "path": binary_sbom_path,
        "sha256": sbom.sha256_file(binary_sbom_path),
        "components": len(document.get("components", [])),
        "top": top,
    }

    subjects: list[dict[str, Any]] = []
    for kind, path in (
        ("source", manifest_path.parent / str(manifest["tarball"]["file"])),
        ("source-manifest", manifest_path),
        ("source-sbom", source_sbom_path),
        ("binary", binary_path),
        ("binary-sbom", binary_sbom_path),
    ):
        subjects.append({"name": Path(path).name, "kind": kind,
                         "sha256": sbom.sha256_file(path),
                         "size": Path(path).stat().st_size})

    inputs = sbom.collect_inputs(root, workflow_file)
    closure = (sbom.load_nix_closure(args.nix_closure_json)
               if args.nix_closure_json else [])
    tree_sha = manifest.get("tree", {}).get("sha256")
    statement = sbom.build_provenance(
        subjects=subjects, revision=str(revision), version=str(version),
        source_date_epoch=epoch, channel=args.channel,
        builder_id=args.builder_id, invocation_id=args.invocation_id,
        inputs=inputs, tree_sha256=tree_sha,
        workflow_ref=args.workflow_ref, nix_closure=closure,
    )
    provenance_path = out / "provenance.intoto.json"
    sbom.write_canonical(provenance_path, statement)
    signature: dict[str, Any] | None = None
    if args.sign_key:
        try:
            signature = sbom.sign_statement(statement, args.sign_key, out)
        except sbom.SbomError as exc:
            die(str(exc), 3)
        except Exception as exc:  # ssh-keygen absent, bad key, ...
            die(f"signing failed: {exc}", 3)

    summary = {
        "schema": "wiz-supply-chain/v1",
        "version": version,
        "revision": revision,
        "channel": args.channel,
        "source": {
            "tarball": str(manifest["tarball"]["file"]),
            "tarballSha256": manifest["tarball"]["sha256"],
            "tarballSize": manifest["tarball"].get("size"),
            "manifest": manifest_path.name,
            "manifestSha256": sbom.sha256_file(manifest_path),
            "treeSha256": tree_sha,
            "sbom": {"file": source_info["path"].name,
                     "sha256": source_info["sha256"],
                     "components": source_info["components"],
                     "manifestRecorded": source_info["recorded"]},
        },
        "binary": {
            "tarball": binary_path.name,
            "tarballSha256": sbom.sha256_file(binary_path),
            "tarballSize": binary_path.stat().st_size,
            "sbom": {"file": binary_info["path"].name,
                     "sha256": binary_info["sha256"],
                     "components": binary_info["components"]},
        },
        "provenance": {
            "file": provenance_path.name,
            "sha256": sbom.sha256_file(provenance_path),
            "predicateType": sbom.PROVENANCE_PREDICATE,
            "builderId": args.builder_id,
            "signed": signature is not None,
            "signature": signature,
            "slsaLevelClaimed": None,
        },
        "inputs": {
            "bundle": [entry["file"] for entry in inputs["bundle"]],
            "nix": [node["name"] for node in inputs["flake"]],
            "actions": [action["name"] for action in inputs["workflow"]["actions"]],
        },
    }
    if args.release_manifest:
        skeleton = sbom.read_json(args.release_manifest)
        if not isinstance(skeleton, dict):
            die(f"{args.release_manifest}: not a JSON object")
        record = _fill_release_manifest(
            skeleton, summary=summary, subjects=subjects, version=str(version),
            revision=str(revision), epoch=epoch, tag=args.tag,
            builder_id=args.builder_id,
            lean_reference=(inputs["lean"]["reference"] if inputs["lean"] else None),
        )
        for checksum in (Path(str(manifest["tarball"]["file"]) + ".sha256"),
                         Path(binary_path.name + ".sha256")):
            path = out / checksum.name
            if path.is_file():
                record["artifacts"].append({
                    "name": path.name, "kind": "checksum", "system": "any",
                    "sha256": sbom.sha256_file(path),
                    "size": path.stat().st_size, "url": None,
                })
        record["artifacts"].append({
            "name": provenance_path.name, "kind": "provenance", "system": "any",
            "sha256": summary["provenance"]["sha256"],
            "size": provenance_path.stat().st_size, "url": None,
        })
        if signature:
            for name, kind in ((signature["envelope"], "provenance-signature"),
                               (signature["signature"], "provenance-signature")):
                path = out / name
                record["artifacts"].append({
                    "name": name, "kind": kind, "system": "any",
                    "sha256": sbom.sha256_file(path),
                    "size": path.stat().st_size, "url": None,
                })
        target = (Path(args.release_manifest_out) if args.release_manifest_out
                  else out / "release-manifest.json")
        target.write_text(json.dumps(record, sort_keys=True, indent=2) + "\n",
                          encoding="utf-8")
        summary["releaseManifest"] = {
            "file": target.name,
            "sha256": sbom.sha256_file(target),
        }
    if args.json:
        print(sbom.canonical_bytes(summary).decode("utf-8"))
    else:
        print(source_sbom_path)
        print(binary_sbom_path)
        print(provenance_path)
        if signature:
            print(out / signature["envelope"])
            print(out / signature["signature"])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
