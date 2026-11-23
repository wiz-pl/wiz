#!/usr/bin/env python3
"""Check that a packaged `wiz` installs the web assets `wiz doc` copies.

`Wiz.Doc.run` (`Wiz/Doc/Build.lean`) copies the site's scripts from the web assets:
always `scroll.css`, `scroll.js`, `tagged.js`, `scroll-search.js`, `highlight.css`, and
with `--serve` `lsp-client.js`, `goals.js`, `doc-live.js`, `doc-live.css`. A checkout
finds them in `web/`; a release finds them beside its `lib/`, in `share/wiz/web`
(`Main.webDir`).
`flake.nix`'s `wiz` installs exactly its `docSiteAssets` fileset there.

This compares the two source lists and checks that every named file exists. It needs
no nix build, so the release job can run it before building the tarball:

    scripts/check-release-web-assets.py

Exit status: 0 clean, 1 a missing or unlisted asset, 2 usage error.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ASSET_LOOP = re.compile(r"for f in \[(.*?)\] do", re.S)
FLAKE_LIST = re.compile(r"docSiteAssets\s*=\s*\[(.*?)\];", re.S)
QUOTED = re.compile(r'"([^"]+)"')
# (`run` also copies the Wasm module when --web has one; it is built by `wiz-web`,
# not installed by the `wiz` package, and `share/wiz/web` is not its only home.)
WASM = (".mjs", ".wasm")


def quoted(text: str) -> list[str]:
    return QUOTED.findall(text)


# `Wiz.Doc.run` copies these from the assets' `framework/` subdirectory, but the
# `for f in [ … ]` loop names the files only; normalize them to their real paths.
FRAMEWORK = {"mount.js", "driver.js", "runtime.js"}


def build_assets(text: str) -> list[str]:
    names: list[str] = []
    for match in ASSET_LOOP.finditer(text):
        names.extend(n for n in quoted(match.group(1)) if not n.endswith(WASM))
    return [f"framework/{n}" if n in FRAMEWORK else n for n in names]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".", help="checkout to check (default: .)")
    args = parser.parse_args()
    root = Path(args.root)
    flake_path = root / "flake.nix"
    build_path = root / "Wiz" / "Doc" / "Build.lean"
    if not flake_path.is_file() or not build_path.is_file():
        print(f"check-release-web-assets: {root} is not a wiz checkout", file=sys.stderr)
        return 2

    flake = flake_path.read_text()
    match = FLAKE_LIST.search(flake)
    if not match:
        print("check-release-web-assets: flake.nix has no `docSiteAssets = [ … ];` "
              "list for the wiz package's share/wiz/web", file=sys.stderr)
        return 1
    installed = quoted(match.group(1))
    # The list has to be what the install phase copies; a list nobody reads would
    # pass the comparison and still ship a release that cannot serve.
    if "docSiteSource" not in flake or "$share/web" not in flake:
        print("check-release-web-assets: flake.nix's docSiteAssets is not copied to "
              "$share/web (docSiteSource)", file=sys.stderr)
        return 1

    copied = build_assets(build_path.read_text())
    if not copied:
        print("check-release-web-assets: Wiz/Doc/Build.lean has no `for f in [ … ]` "
              "asset lists", file=sys.stderr)
        return 1

    bad = False
    for name in copied:
        if name not in installed:
            print(f"check-release-web-assets: web/{name} is copied by Wiz.Doc.run but "
                  f"not in flake.nix's docSiteAssets", file=sys.stderr)
            bad = True
    for name in installed:
        if not (root / "web" / name).is_file():
            print(f"check-release-web-assets: flake.nix lists web/{name}, which does "
                  f"not exist", file=sys.stderr)
            bad = True
    if bad:
        return 1

    print("check-release-web-assets: clean "
          f"({len(copied)} file(s): {', '.join(copied)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
