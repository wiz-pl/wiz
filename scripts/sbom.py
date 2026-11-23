#!/usr/bin/env python3
"""CycloneDX SBOMs and SLSA-style provenance for Wiz release artifacts.

This module is standard-library only.  ``scripts/source-tarball.py`` imports it to
write the source SBOM beside the deterministic source tarball; ``scripts/release-sbom.py``
uses it for the binary tarball and the provenance statement.

The output is deliberately canonical JSON (sorted keys, compact separators, UTF-8, no
trailing newline) and contains no timestamps, absolute paths, host names or random
identifiers, so the same inputs produce byte-identical files.  A CycloneDX serial
number is derived with UUIDv5 from the artifact name and digest, not generated randomly.

What this is *not*: a vulnerability report, a statement that a component is safe, or a
claim that a build ran on a hosted SLSA platform.  The provenance says what the release
workflow claims its inputs and outputs were; only a signature and an independent rebuild
add evidence about who built it and whether the bytes reproduce.
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import sys
import tarfile
import uuid
from pathlib import Path
from typing import Any, Iterable, Sequence

CDX_SPEC = "1.6"
CDX_SCHEMA_URL = "http://cyclonedx.org/schema/bom-1.6.schema.json"
SBOM_SCHEMA = "wiz-sbom/v1"
PROVENANCE_SCHEMA = "wiz-provenance/v1"
STATEMENT_TYPE = "https://in-toto.io/Statement/v1"
PROVENANCE_PREDICATE = "https://slsa.dev/provenance/v1"
BUILD_TYPE = "https://wiz-lang.dev/buildtypes/wiz-release/v1"
GENERATOR = "wiz-release-sbom"
GENERATOR_VERSION = "1"
SLSA_NOTE = ("SLSA-style provenance only: an in-toto Statement v1 with the SLSA "
             "provenance v1 predicate. No hosted SLSA build level is claimed.")
DEFAULT_SOURCE = "https://github.com/wiz-pl/wiz"

_VERSION_RE = re.compile(r'def\s+version\s*:\s*String\s*:=\s*"([^"]+)"')
_SRI_SHA256_RE = re.compile(r"^sha256-([A-Za-z0-9+/=]+)$")
_HEX40_RE = re.compile(r"^[0-9a-f]{40}$")

# The licence expressions for the external inputs and the bundled toolchain.  The prose
# source is scripts/release-licenses/NOTICE; keep the two in step when an input changes.
_INPUT_LICENCES = {
    "gmp": "LGPL-3.0-or-later OR GPL-2.0-or-later",
    "gc": "MIT",
    "glibc": "LGPL-2.1-or-later",
    "linux-headers": "GPL-2.0-only WITH Linux-syscall-note",
    "clang": "Apache-2.0 WITH LLVM-exception",
    "compiler-rt": "Apache-2.0 WITH LLVM-exception",
    "cadical": "MIT",
    "lean": "Apache-2.0",
    "libuv": "MIT",
    "mimalloc": "MIT",
}


class SbomError(Exception):
    """An input or output error that the CLI reports as a failure."""


def canonical_bytes(obj: Any) -> bytes:
    """The one JSON serialization used for SBOMs, manifests and statements."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode("utf-8")


def write_canonical(path: os.PathLike[str] | str, obj: Any) -> bytes:
    data = canonical_bytes(obj)
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return data


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: os.PathLike[str] | str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_json(path: os.PathLike[str] | str) -> Any:
    try:
        raw = Path(path).read_bytes()
        return json.loads(raw.decode("utf-8"))
    except OSError as exc:
        raise SbomError(f"cannot read {path}: {exc}") from None
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SbomError(f"{path} is not valid JSON: {exc}") from None


def sri_sha256_to_hex(value: str) -> str | None:
    """Turn a Nix ``sha256-<base64>`` SRI hash into lowercase hex, if possible."""
    match = _SRI_SHA256_RE.match(value.strip())
    if not match:
        return None
    try:
        digest = base64.b64decode(match.group(1), validate=True)
    except (ValueError, TypeError):
        return None
    if len(digest) != 32:
        return None
    return digest.hex()


def _uuid_urn(*parts: str) -> str:
    return "urn:uuid:" + str(uuid.uuid5(uuid.NAMESPACE_URL, "\x1f".join(parts)))


def version_of(root: os.PathLike[str] | str) -> str:
    try:
        text = (Path(root) / "Wiz" / "Version.lean").read_text(encoding="utf-8")
    except OSError:
        return "0.0.0"
    match = _VERSION_RE.search(text)
    return match.group(1) if match else "0.0.0"


def _property(name: str, value: str | int | bool) -> dict[str, str]:
    return {"name": name, "value": str(value)}


def _hash(alg: str, content: str) -> dict[str, str]:
    return {"alg": alg, "content": content}


def _component(*, type_: str, bom_ref: str, name: str, version: str | None = None,
               hashes: Sequence[dict[str, str]] = (),
               licenses: Sequence[dict[str, Any]] = (),
               properties: Sequence[dict[str, str]] = (),
               supplier: str | None = None) -> dict[str, Any]:
    component: dict[str, Any] = {
        "type": type_,
        "bom-ref": bom_ref,
        "name": name,
    }
    if version:
        component["version"] = version
    if hashes:
        component["hashes"] = list(hashes)
    if licenses:
        component["licenses"] = list(licenses)
    if supplier:
        component["supplier"] = {"name": supplier}
    if properties:
        component["properties"] = list(properties)
    return component


def file_component(path: str, sha256: str, size: int, *, mode: str | None = None,
                   role: str = "artifact") -> dict[str, Any]:
    props = [_property("wiz:path", path), _property("wiz:size", size),
             _property("wiz:role", role)]
    if mode:
        props.append(_property("wiz:mode", mode))
    return _component(type_="file", bom_ref=f"file:{path}", name=path,
                      hashes=[_hash("SHA-256", sha256)], properties=props)


def _input_metadata(filename: str) -> tuple[str, str, str]:
    """(name, version, licence) for one scripts/bundle-cc.sources input."""
    if filename.startswith("libc6-dev"):
        return "glibc (libc6-dev)", "2.27", _INPUT_LICENCES["glibc"]
    if filename.startswith("libc6"):
        return "glibc (libc6)", "2.27", _INPUT_LICENCES["glibc"]
    if filename.startswith("linux-libc-dev"):
        return "Linux UAPI headers", "4.15", _INPUT_LICENCES["linux-headers"]
    if filename.startswith("gmp-"):
        match = re.match(r"gmp-([0-9][0-9.]*)", filename)
        return "GMP", (match.group(1) if match else ""), _INPUT_LICENCES["gmp"]
    if filename.startswith("gc-"):
        match = re.match(r"gc-([0-9][0-9.]*)", filename)
        return "Boehm GC", (match.group(1) if match else ""), _INPUT_LICENCES["gc"]
    return filename, "", ""


def parse_bundle_sources(root: os.PathLike[str] | str) -> list[dict[str, Any]]:
    """The external inputs listed by scripts/bundle-cc.sources (comments ignored)."""
    path = Path(root) / "scripts" / "bundle-cc.sources"
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return []
    entries: list[dict[str, Any]] = []
    for line in lines:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) < 2:
            continue
        name, digest, urls = fields[0], fields[1].lower(), fields[2:]
        if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
            raise SbomError(f"bundle-cc.sources: {name}: not a SHA-256")
        entries.append({"file": name, "sha256": digest, "urls": urls})
    return entries


def parse_flake_lock(root: os.PathLike[str] | str) -> list[dict[str, Any]]:
    """Locked Nix inputs, one per node in flake.lock (the root node is not an input)."""
    path = Path(root) / "flake.lock"
    if not path.is_file():
        return []
    data = read_json(path)
    nodes = data.get("nodes", {}) if isinstance(data, dict) else {}
    out: list[dict[str, Any]] = []
    for name, node in nodes.items():
        if name == "root" or not isinstance(node, dict):
            continue
        locked = node.get("locked")
        if not isinstance(locked, dict):
            continue
        out.append({"name": name, "locked": locked})
    return sorted(out, key=lambda item: item["name"])


def parse_lean_toolchain(root: os.PathLike[str] | str) -> dict[str, str] | None:
    path = Path(root) / "lean-toolchain"
    try:
        text = path.read_text(encoding="utf-8").strip()
    except OSError:
        return None
    if not text:
        return None
    version = text
    if ":" in text:
        version = text.rsplit(":", 1)[1]
    return {"reference": text, "version": version, "sha256": sha256_file(path)}


def parse_workflow(root: os.PathLike[str] | str,
                   workflow_file: os.PathLike[str] | str | None = None) -> dict[str, Any]:
    """What the release workflow pins: actions, runner image, Emscripten and elan."""
    candidates = []
    if workflow_file:
        candidates.append(Path(workflow_file))
    candidates.append(Path(root) / ".github" / "workflows" / "release.yml")
    path = next((p for p in candidates if p.is_file()), None)
    if path is None:
        return {"file": None, "actions": [], "runner": None, "emscripten": None,
                "elan": None}
    text = path.read_text(encoding="utf-8")

    actions: dict[str, dict[str, Any]] = {}
    for match in re.finditer(r"^\s*(?:-\s*)?uses:\s*([^\s#]+)", text, re.MULTILINE):
        ref = match.group(1).strip()
        if not ref or ref.startswith("./"):
            continue
        name, _, version = ref.partition("@")
        if not version:
            continue
        actions[name] = {"name": name, "ref": version,
                         "pinned": bool(_HEX40_RE.match(version))}

    runner = None
    match = re.search(r"^\s*runs-on:\s*(\S+)", text, re.MULTILINE)
    if match:
        runner = match.group(1).strip()

    emscripten = None
    match = re.search(r"setup-emsdk@[^\n]*\n(?:.*\n){0,8}?\s*version:\s*([^\s#]+)",
                      text)
    if match:
        emscripten = match.group(1)

    elan = None
    match = re.search(r"https://raw\.githubusercontent\.com/([^\s'\"]*elan[^\s'\"]*)",
                      text)
    if match:
        elan = match.group(1)

    return {
        "file": str(path),
        "actions": [actions[name] for name in sorted(actions)],
        "runner": runner,
        "emscripten": emscripten,
        "elan": elan,
    }


def parse_cc_versions(text: str) -> dict[str, str]:
    """The resolved versions bundle-cc.sh writes into cc/VERSIONS."""
    out: dict[str, str] = {}
    for line in text.splitlines():
        low = line.lower()
        if low.startswith("clang"):
            out["clang"] = line
        elif low.startswith("cadical"):
            out["cadical"] = line
        elif low.startswith("glibc"):
            out["glibc"] = line
        elif low.startswith("gmp"):
            out["gmp"] = line
    return out


def collect_inputs(root: os.PathLike[str] | str,
                   workflow_file: os.PathLike[str] | str | None = None) -> dict[str, Any]:
    return {
        "_root": os.fspath(root),
        "bundle": parse_bundle_sources(root),
        "flake": parse_flake_lock(root),
        "lean": parse_lean_toolchain(root),
        "workflow": parse_workflow(root, workflow_file),
    }


def _input_components(root: os.PathLike[str] | str,
                      inputs: dict[str, Any]) -> list[dict[str, Any]]:
    components: list[dict[str, Any]] = []
    for entry in inputs["bundle"]:
        name, version, licence = _input_metadata(entry["file"])
        props = [
            _property("wiz:role", "build-input"),
            _property("wiz:input-file", entry["file"]),
            _property("wiz:source-file", "scripts/bundle-cc.sources"),
        ]
        if entry["urls"]:
            props.append(_property("wiz:url", entry["urls"][0]))
        components.append(_component(
            type_="data", bom_ref=f"input:{entry['file']}", name=name,
            version=version or None,
            hashes=[_hash("SHA-256", entry["sha256"])],
            licenses=[{"expression": licence}] if licence else [],
            properties=props,
        ))
    for node in inputs["flake"]:
        locked = node["locked"]
        nar_hash = str(locked.get("narHash", ""))
        digest = sri_sha256_to_hex(nar_hash)
        version = str(locked.get("rev", ""))[:12]
        props = [
            _property("wiz:role", "nix-input"),
            _property("wiz:nix-type", str(locked.get("type", ""))),
            _property("wiz:nar-hash", nar_hash),
        ]
        for key in ("owner", "repo", "rev", "url", "path"):
            if locked.get(key):
                props.append(_property(f"wiz:nix-{key}", str(locked[key])))
        components.append(_component(
            type_="library", bom_ref=f"nix:{node['name']}", name=node["name"],
            version=version or None,
            hashes=[_hash("SHA-256", digest)] if digest else [],
            properties=props,
        ))
    lean = inputs["lean"]
    if lean:
        components.append(_component(
            type_="framework", bom_ref="toolchain:lean", name="lean",
            version=lean["version"],
            hashes=[_hash("SHA-256", lean["sha256"])],
            licenses=[{"expression": _INPUT_LICENCES["lean"]}],
            properties=[
                _property("wiz:role", "build-only"),
                _property("wiz:source-file", "lean-toolchain"),
                _property("wiz:reference", lean["reference"]),
            ],
        ))
    workflow = inputs["workflow"]
    for action in workflow["actions"]:
        components.append(_component(
            type_="application", bom_ref=f"gha:{action['name']}@{action['ref']}",
            name=action["name"], version=action["ref"],
            properties=[
                _property("wiz:role", "ci-action"),
                _property("wiz:pinned", "true" if action["pinned"] else "false"),
                _property("wiz:source-file", ".github/workflows/release.yml"),
            ],
        ))
    if workflow["runner"]:
        components.append(_component(
            type_="platform", bom_ref=f"runner:{workflow['runner']}",
            name="GitHub runner", version=workflow["runner"],
            properties=[
                _property("wiz:role", "build-only"),
                _property("wiz:pinned",
                          "false" if workflow["runner"].endswith("-latest") else "true"),
            ],
        ))
    if workflow["emscripten"]:
        components.append(_component(
            type_="framework", bom_ref="toolchain:emscripten", name="Emscripten",
            version=workflow["emscripten"],
            properties=[_property("wiz:role", "build-only"),
                        _property("wiz:source-file",
                                  ".github/workflows/release.yml")],
        ))
    if workflow["elan"]:
        components.append(_component(
            type_="application", bom_ref="toolchain:elan", name="elan",
            version="master (unpinned)",
            properties=[
                _property("wiz:role", "build-only"),
                _property("wiz:pinned", "false"),
                _property("wiz:url", "https://raw.githubusercontent.com/"
                                      + workflow["elan"]),
            ],
        ))
    return components


def _dedupe_sorted(components: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    by_ref: dict[str, dict[str, Any]] = {}
    for component in components:
        ref = component["bom-ref"]
        if ref in by_ref:
            # A file and an input may legitimately share a name, not a bom-ref; a
            # duplicate bom-ref makes the document invalid, so fail loudly.
            raise SbomError(f"duplicate bom-ref: {ref}")
        by_ref[ref] = component
    return [by_ref[ref] for ref in sorted(by_ref, key=lambda r: r.encode("utf-8"))]


def _top_component(*, kind: str, name: str, version: str, sha256: str,
                   properties: Sequence[dict[str, str]],
                   licenses: Sequence[dict[str, Any]]) -> dict[str, Any]:
    return _component(
        type_="application" if kind == "binary" else "data",
        bom_ref=f"wiz:{kind}:{name}@{version}",
        name=name, version=version,
        hashes=[_hash("SHA-256", sha256)],
        licenses=licenses,
        properties=list(properties),
    )


def build_sbom(*, kind: str, name: str, version: str, revision: str,
               tarball_sha256: str, components: Sequence[dict[str, Any]],
               properties: Sequence[dict[str, str]],
               licenses: Sequence[dict[str, Any]]) -> dict[str, Any]:
    top = _top_component(kind=kind, name=name, version=version,
                         sha256=tarball_sha256, properties=properties,
                         licenses=licenses)
    components = _dedupe_sorted(components)
    refs = [component["bom-ref"] for component in components]
    return {
        "$schema": CDX_SCHEMA_URL,
        "bomFormat": "CycloneDX",
        "specVersion": CDX_SPEC,
        "serialNumber": _uuid_urn("wiz-sbom", kind, name, version, tarball_sha256),
        "version": 1,
        "metadata": {
            "component": top,
            "tools": {
                "components": [{
                    "type": "application",
                    "name": GENERATOR,
                    "version": GENERATOR_VERSION,
                }],
            },
            "properties": [
                _property("wiz:schema", SBOM_SCHEMA),
                _property("wiz:commit", revision),
                _property("wiz:source", DEFAULT_SOURCE),
                _property("wiz:sbom-kind", kind),
                _property("wiz:slsa-level-claimed", "none"),
            ],
        },
        "components": components,
        "dependencies": [{"ref": top["bom-ref"], "dependsOn": refs}],
    }


def source_sbom(manifest: dict[str, Any], root: os.PathLike[str] | str, *,
                version: str | None = None,
                workflow_file: os.PathLike[str] | str | None = None) -> dict[str, Any]:
    """CycloneDX for a wiz-source-tarball/v1 manifest (every file is a component)."""
    if manifest.get("schema") != "wiz-source-tarball/v1":
        raise SbomError("not a wiz-source-tarball/v1 manifest")
    name = str(manifest.get("name", "wiz-source"))
    tarball = manifest.get("tarball", {})
    digest = str(tarball.get("sha256", ""))
    if len(digest) != 64:
        raise SbomError("source manifest has no tarball SHA-256")
    version = version or version_of(root)
    entries = manifest.get("files", [])
    if not isinstance(entries, list):
        raise SbomError("source manifest files is not a list")

    components = [
        file_component(str(entry["path"]), str(entry["sha256"]),
                       int(entry.get("size", 0)), mode=str(entry.get("mode", "")),
                       role="source")
        for entry in entries
    ]
    inputs = collect_inputs(root, workflow_file)
    components.extend(_input_components(root, inputs))
    tree = manifest.get("tree", {})
    props = [
        _property("wiz:sbom-kind", "source"),
        _property("wiz:commit", str(manifest.get("revision", "unknown"))),
        _property("wiz:source-date-epoch", int(manifest.get("sourceDateEpoch", 0))),
        _property("wiz:tree-sha256", str(tree.get("sha256", ""))),
        _property("wiz:files", int(tree.get("files", len(entries)))),
        _property("wiz:tarball-file", str(tarball.get("file", ""))),
        _property("wiz:license-exception",
                  "COPYING.RUNTIME (not an SPDX-registered exception)"),
    ]
    return build_sbom(kind="source", name=name, version=version,
                      revision=str(manifest.get("revision", "unknown")),
                      tarball_sha256=digest, components=components,
                      properties=props,
                      licenses=[{"license": {"id": "GPL-3.0-or-later"}}])


def _tar_inventory(path: os.PathLike[str] | str) -> tuple[str, list[dict[str, Any]]]:
    """(top directory, regular file entries) for a binary tarball, without extracting."""
    try:
        tf = tarfile.open(path, "r:*")
    except (OSError, tarfile.TarError) as exc:
        raise SbomError(f"cannot read tarball {path}: {exc}") from None
    with tf:
        members = tf.getmembers()
        if not members:
            raise SbomError(f"empty tarball: {path}")
        tops = {m.name.split("/", 1)[0] for m in members if m.name}
        if len(tops) != 1:
            raise SbomError(f"tarball {path} has {len(tops)} top directories")
        top = tops.pop()
        entries: list[dict[str, Any]] = []
        for member in members:
            if member.isdir():
                continue
            rel = member.name[len(top):].lstrip("/")
            if not rel:
                continue
            props = []
            if member.issym() or member.islnk():
                props.append(_property("wiz:link", member.linkname))
                entries.append({"path": rel, "type": "link", "size": 0,
                                "mode": f"{member.mode & 0o777:04o}",
                                "sha256": None, "link": member.linkname})
                continue
            if not member.isfile():
                raise SbomError(f"{member.name}: unsupported tar member type")
            extracted = tf.extractfile(member)
            if extracted is None:
                raise SbomError(f"{member.name}: cannot read the member")
            digest = hashlib.sha256()
            size = 0
            for chunk in iter(lambda: extracted.read(1 << 20), b""):
                digest.update(chunk)
                size += len(chunk)
            entries.append({"path": rel, "type": "file", "size": size,
                            "mode": f"{member.mode & 0o777:04o}",
                            "sha256": digest.hexdigest()})
        entries.sort(key=lambda item: item["path"].encode("utf-8"))
        return top, entries


def binary_sbom(tarball: os.PathLike[str] | str, root: os.PathLike[str] | str, *,
                version: str | None = None, revision: str | None = None,
                workflow_file: os.PathLike[str] | str | None = None) -> tuple[dict[str, Any], str, list[dict[str, Any]]]:
    """CycloneDX for a binary release tarball; returns (sbom, top dir, entries)."""
    top, entries = _tar_inventory(tarball)
    digest = sha256_file(tarball)
    version = version or version_of(root)
    revision = revision or "unknown"
    components = [
        file_component(entry["path"], str(entry["sha256"]), int(entry["size"]),
                       mode=entry["mode"], role="artifact")
        for entry in entries if entry["type"] == "file"
    ]
    for entry in entries:
        if entry["type"] == "link":
            components.append(_component(
                type_="file", bom_ref=f"file:{entry['path']}", name=entry["path"],
                properties=[_property("wiz:path", entry["path"]),
                            _property("wiz:link", entry["link"]),
                            _property("wiz:role", "artifact")],
            ))
    inputs = collect_inputs(root, workflow_file)
    components.extend(_input_components(root, inputs))
    if top:
        # The bundled C toolchain's own VERSIONS file is the resolved-version record.
        versions = next((entry for entry in entries if entry["path"] == "share/wiz/cc/VERSIONS"), None)
        if versions is not None:
            try:
                with tarfile.open(tarball, "r:*") as tf:
                    member = next(m for m in tf.getmembers()
                                  if m.name.endswith("/share/wiz/cc/VERSIONS"))
                    extracted = tf.extractfile(member)
                    text = extracted.read().decode("utf-8", "replace") if extracted else ""
            except (OSError, tarfile.TarError, StopIteration):
                text = ""
            resolved = parse_cc_versions(text)
            if resolved:
                components.append(_component(
                    type_="application", bom_ref="wiz:bundled-c-toolchain",
                    name="bundled C toolchain",
                    version=resolved.get("clang", "").split("(")[-1].rstrip(")") or None,
                    properties=[_property("wiz:role", "bundled"),
                                _property("wiz:versions-file", "share/wiz/cc/VERSIONS")]
                               + [_property(f"wiz:resolved-{key}", value)
                                  for key, value in sorted(resolved.items())],
                ))
    props = [
        _property("wiz:sbom-kind", "binary"),
        _property("wiz:commit", revision),
        _property("wiz:target", top),
        _property("wiz:files", len([e for e in entries if e["type"] == "file"])),
        _property("wiz:license-exception",
                  "COPYING.RUNTIME (not an SPDX-registered exception)"),
    ]
    sbom = build_sbom(kind="binary", name=top, version=version,
                      revision=revision, tarball_sha256=digest,
                      components=components, properties=props,
                      licenses=[{"license": {"id": "GPL-3.0-or-later"}}])
    return sbom, top, entries


def _resource(uri: str, digest: dict[str, str] | None = None,
              *, annotations: dict[str, str] | None = None) -> dict[str, Any]:
    resource: dict[str, Any] = {"uri": uri}
    if digest:
        resource["digest"] = digest
    if annotations:
        resource["annotations"] = annotations
    return resource


def build_provenance(*, subjects: Sequence[dict[str, Any]], revision: str,
                     version: str, source_date_epoch: int | None,
                     channel: str, builder_id: str,
                     invocation_id: str | None,
                     inputs: dict[str, Any], tree_sha256: str | None,
                     workflow_ref: str | None,
                     nix_closure: Sequence[dict[str, Any]] = ()) -> dict[str, Any]:
    """An in-toto Statement v1 with a SLSA provenance v1 predicate (no level claim)."""
    dependencies: list[dict[str, Any]] = [
        _resource(f"git+{DEFAULT_SOURCE}@{revision}", {"gitCommit": revision}),
    ]
    if tree_sha256:
        dependencies.append(_resource("wiz:source-tree", {"sha256": tree_sha256}))
    for entry in inputs["bundle"]:
        dependencies.append(_resource(
            f"wiz:bundle-input/{entry['file']}",
            {"sha256": entry["sha256"]},
            annotations={"wiz:role": "bundled-input"},
        ))
    lean = inputs["lean"]
    if lean:
        dependencies.append(_resource(
            "wiz:lean-toolchain", {"sha256": lean["sha256"]},
            annotations={"wiz:version": lean["version"],
                         "wiz:reference": lean["reference"]},
        ))
    if inputs["flake"]:
        flake_path = Path(inputs["_root"]) / "flake.lock"
        dependencies.append(_resource(
            "wiz:flake-lock", {"sha256": sha256_file(flake_path)},
            annotations={"wiz:role": "nix-inputs"},
        ))
    for node in inputs["flake"]:
        locked = node["locked"]
        digest = sri_sha256_to_hex(str(locked.get("narHash", "")))
        annotations = {"wiz:nix-type": str(locked.get("type", ""))}
        if locked.get("rev"):
            annotations["wiz:nix-rev"] = str(locked["rev"])
        dependencies.append(_resource(
            f"nix:{node['name']}", {"sha256": digest} if digest else None,
            annotations=annotations,
        ))
    workflow = inputs["workflow"]
    if workflow.get("file"):
        dependencies.append(_resource(
            "wiz:release-workflow",
            {"sha256": sha256_file(workflow["file"])},
            annotations={"wiz:ref": workflow_ref or "unknown"},
        ))
    for action in workflow["actions"]:
        digest = {"gitCommit": action["ref"]} if action["pinned"] else None
        dependencies.append(_resource(
            f"gha:{action['name']}@{action['ref']}", digest,
            annotations={"wiz:pinned": "true" if action["pinned"] else "false"},
        ))
    for item in nix_closure:
        dependencies.append(_resource(
            "nix-store:" + str(item["path"]),
            {"sha256": item["sha256"]} if item.get("sha256") else None,
            annotations={"wiz:role": "nix-closure",
                         "wiz:nar-size": str(item.get("nar_size", ""))},
        ))
    dependencies.sort(key=lambda item: item["uri"].encode("utf-8"))

    external: dict[str, Any] = {
        "version": version,
        "revision": revision,
        "channel": channel,
        "target": next((s["name"] for s in subjects if s.get("kind") == "binary"), None),
        "wiz:source": DEFAULT_SOURCE,
        "wiz:source-date-epoch": source_date_epoch,
    }
    external = {key: value for key, value in external.items() if value is not None}
    predicate: dict[str, Any] = {
        "buildDefinition": {
            "buildType": BUILD_TYPE,
            "externalParameters": external,
            "resolvedDependencies": dependencies,
        },
        "runDetails": {
            "builder": {"id": builder_id, "version": {"wiz-release-sbom": GENERATOR_VERSION}},
            "metadata": {},
        },
        "wiz:schema": PROVENANCE_SCHEMA,
        "wiz:slsaLevelClaimed": None,
        "wiz:note": SLSA_NOTE,
    }
    if invocation_id:
        predicate["runDetails"]["metadata"]["invocationId"] = invocation_id
    return {
        "_type": STATEMENT_TYPE,
        "subject": [
            {"name": subject["name"],
             "digest": {"sha256": subject["sha256"]}}
            for subject in sorted(subjects, key=lambda s: s["name"].encode("utf-8"))
        ],
        "predicateType": PROVENANCE_PREDICATE,
        "predicate": predicate,
    }


def load_nix_closure(path: os.PathLike[str] | str) -> list[dict[str, Any]]:
    """Read `nix path-info --json --recursive` output into closure components."""
    data = read_json(path)
    if not isinstance(data, dict):
        raise SbomError(f"{path} is not a nix path-info JSON object")
    out: list[dict[str, Any]] = []
    for store_path, info in data.items():
        info = info if isinstance(info, dict) else {}
        nar_hash = str(info.get("narHash", ""))
        digest = sri_sha256_to_hex(nar_hash)
        out.append({
            "path": store_path,
            "sha256": digest,
            "nar_size": info.get("narSize", 0),
            "nar_hash": nar_hash,
            "references": info.get("references", []),
        })
    out.sort(key=lambda item: item["path"])
    return out


def sign_statement(statement: dict[str, Any], key_path: os.PathLike[str] | str,
                   out_dir: os.PathLike[str] | str, *,
                   stem: str = "provenance.intoto.json") -> dict[str, Any]:
    """Sign the statement as DSSE with the E1 offline Ed25519 key path."""
    attest_dir = Path(__file__).resolve().parent / "attest"
    if not (attest_dir / "wiz_attest.py").is_file():
        raise SbomError("scripts/attest/wiz_attest.py is not present; cannot sign")
    sys.path.insert(0, str(attest_dir))
    try:
        import wiz_attest  # type: ignore
    finally:
        sys.path.pop(0)

    payload = canonical_bytes(statement)
    public = wiz_attest.parse_public_key(Path(key_path))
    signature = wiz_attest.sign_pae(
        Path(key_path), wiz_attest.dsse_pae(wiz_attest.DSSE_PAYLOAD_TYPE, payload))
    envelope = {
        "payloadType": wiz_attest.DSSE_PAYLOAD_TYPE,
        "payload": base64.b64encode(payload).decode("ascii"),
        "signatures": [{
            "keyid": public.fingerprint,
            "sig": base64.b64encode(signature).decode("ascii"),
        }],
    }
    out = Path(out_dir)
    envelope_path = out / (stem + ".dsse")
    signature_path = out / (stem + ".sig")
    write_canonical(envelope_path, envelope)
    signature_path.write_bytes(signature)
    return {
        "signed": True,
        "keyid": public.fingerprint,
        "payload_sha256": sha256_bytes(payload),
        "envelope": envelope_path.name,
        "signature": signature_path.name,
    }


__all__ = [
    "SbomError", "canonical_bytes", "write_canonical", "sha256_bytes", "sha256_file",
    "read_json", "version_of", "source_sbom", "binary_sbom", "build_provenance",
    "collect_inputs", "load_nix_closure", "sign_statement", "CDX_SPEC",
    "STATEMENT_TYPE", "PROVENANCE_PREDICATE", "BUILD_TYPE",
]
