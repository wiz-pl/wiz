#!/usr/bin/env python3
"""Check the one-way boundary between the Hdl package and the rest of the tree.

`hdl/` is a package of its own (`separate-repos.md` §1.2, P0.4), and its dependency is
one-way: it uses the toolchain's standard library (`lib/`), and nothing in `lib/` may use
it back. The rule was convention until this check; a `lib/` module that imports `Hdl.*`
now fails CI instead of only showing up when someone tries to build the std alone.

Rules (all read from source; no build, no network):

  lib-consumer          no module under `lib/` imports `Hdl.*`. `lib/` is the
                        toolchain's standard library and ships without the package.
  hdl-imports-std       every import in `hdl/src/Hdl/*.wiz` is either `Hdl.*` (the
                        package's own modules) or a module that exists under `lib/`
                        (the std). An import of `Scry.*`, `Web.*`, `Wgpu.*`, a root
                        example or anything else outside those two roots fails.
  declared-consumers    a `.wiz` file outside `hdl/` that imports `Hdl.*` must live in
                        `examples/`, `bench/` or `drafts/`. Those are the declared
                        co-development consumers (the root `grail.wiz` adds `hdl/src`
                        as a module root for them); anything else (`tools/`, `web/`,
                        `selfhost/`, ...) would be a second, undeclared dependency.
  no-escaping-paths     no committed file under `hdl/` names a path outside the package
                        (`../`) or reaches into the checkout's build output (`.lake`).
                        The package must be relocatable: `HDL_ROOT` can point at a copy
                        (`hdl/scripts/check-standalone.sh` proves it with a real build).

The Hdl package's roots are relative to the package (`hdl/grail.wiz`: `Package.lib
"hdl" "src"`, `Package.tests "examples" "examples"`), and the std root is the
toolchain's own `lib/`; this check is the static half of that boundary.

Usage
  scripts/check-boundaries.py             report every violation; exit 1 if there is one
  scripts/check-boundaries.py --quiet     the CI gate: no output on a clean tree
  scripts/check-boundaries.py --self-test run the fixtures (a violation and a clean tree)
  scripts/check-boundaries.py --root DIR  check another checkout (default: this one)

Exit status: 0 clean, 1 a violation, 2 usage or I/O error.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

#: Imports that would point up out of the package (and out of the std). `Web.*` and
#: `Scry.*` are not here: `lib/Web/` and `lib/Scry/` are part of the std today.
PACKAGE_PREFIXES = ("Hdl.",)

#: Where an import of `Hdl.*` outside the package is declared (the co-development
#: consumers). `drafts/` is explicitly outside the migration, like the name checks.
CONSUMER_PREFIXES = ("examples/", "bench/", "drafts/")

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)


def wiz_files(root: Path, sub: str) -> list[Path]:
    base = root / sub
    if not base.is_dir():
        return []
    return sorted(p for p in base.rglob("*.wiz") if p.is_file())


def rel(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def imports(path: Path) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as e:
        raise SystemExit(f"check-boundaries: {path}: {e}")
    return IMPORT_RE.findall(text)


def lib_module_exists(root: Path, module: str) -> bool:
    """Is `module` a std module (`lib/A/B.wiz` for `A.B`, `lib/A.wiz` for `A`)?"""
    parts = module.split(".")
    candidate = root / "lib" / Path(*parts[:-1]) / f"{parts[-1]}.wiz"
    return candidate.is_file()


def check(root: Path) -> list[str]:
    problems: list[str] = []

    # lib-consumer
    for path in wiz_files(root, "lib"):
        for name in imports(path):
            if name.startswith(PACKAGE_PREFIXES):
                problems.append(
                    f"{rel(root, path)}: lib/ imports {name}; the dependency is one-way "
                    "(hdl -> lib), so the std cannot use the package"
                )

    # hdl-imports-std
    for path in wiz_files(root, "hdl/src"):
        for name in imports(path):
            if name.startswith("Hdl."):
                continue
            if not lib_module_exists(root, name):
                problems.append(
                    f"{rel(root, path)}: imports {name}, which is neither an Hdl module "
                    "nor a std module in lib/"
                )

    # declared-consumers
    for path in sorted((root).rglob("*.wiz")):
        if not path.is_file() or {".lake", ".grail", "node_modules"} & set(path.parts):
            continue
        r = rel(root, path)
        if r.startswith("hdl/"):
            continue
        for name in imports(path):
            if name.startswith(PACKAGE_PREFIXES):
                if not r.startswith(CONSUMER_PREFIXES):
                    problems.append(
                        f"{r}: imports {name} but is not a declared consumer "
                        f"(examples/, bench/ or drafts/)"
                    )

    # no-escaping-paths
    for path in sorted((root / "hdl").rglob("*")):
        if not path.is_file() or ".grail" in path.parts or ".lake" in path.parts:
            continue
        if path.suffix not in {".wiz", ".md", ".sh", ".py"}:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        r = rel(root, path)
        if re.search(r"(?<![\w.])\.\./", text):
            problems.append(f"{r}: names a path outside the package (`../`)")
        if re.search(r"(?<![\w.])\.lake(?:/|\b)", text):
            problems.append(f"{r}: names the checkout's `.lake` build output")

    return problems


def self_test() -> int:
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        files = {
            # a clean package: Hdl imports Hdl and a std module
            "lib/Prelude.wiz": "def x : Nat := 1\n",
            "lib/Trace.wiz": "import Prelude\n",
            "hdl/src/Hdl/Core.wiz": "import BitVec\n",
            "lib/BitVec.wiz": "import Prelude\n",
            "hdl/src/Hdl/Bus.wiz": "import Hdl.Core\nimport Trace\n",
            "hdl/examples/bus.wiz": "import Hdl.Bus\n",
            "hdl/README.md": "nothing escapes here\n",
            "examples/tour.wiz": "import Hdl.Core\n",
            "bench/bench.wiz": "import Hdl.Core\n",
            "drafts/probe.wiz": "import Hdl.Core\n",
            "tools/helper.wiz": "import Prelude\n",
        }
        for name, text in files.items():
            p = root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text, encoding="utf-8")
        clean = check(root)
        if clean:
            print("check-boundaries self-test: the clean fixture has violations:")
            for p in clean:
                print("  " + p)
            return 1

        # each mutation must be found, by name
        mutations = [
            ("lib/Leak.wiz", "import Hdl.Core\n", "lib/Leak.wiz: lib/ imports Hdl.Core"),
            ("hdl/src/Hdl/Leak.wiz", "import Scry.Wil\n", "hdl/src/Hdl/Leak.wiz: imports Scry.Wil"),
            ("tools/leak.wiz", "import Hdl.Core\n", "tools/leak.wiz: imports Hdl.Core"),
            ("hdl/examples/escape.wiz", "-- see ../lib\n", "hdl/examples/escape.wiz: names a path outside"),
            ("hdl/scripts/build.sh", "exec .lake/build/bin/grail\n", "hdl/scripts/build.sh: names the checkout's"),
        ]
        for name, text, expected in mutations:
            p = root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text, encoding="utf-8")
            found = check(root)
            if not any(expected in v for v in found):
                print(f"check-boundaries self-test: {name} was not reported as:\n  {expected}")
                print("  got:", found)
                return 1
            p.unlink()

    print("check-boundaries self-test: ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check the one-way Hdl package boundary and its declared consumers."
    )
    parser.add_argument("--root", type=Path, help="checkout to check (default: this one)")
    parser.add_argument("--quiet", action="store_true", help="print nothing on a clean tree")
    parser.add_argument("--self-test", action="store_true", help="run the fixtures")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    root = (args.root or Path(__file__).resolve().parent.parent).resolve()
    if not (root / "hdl").is_dir():
        print(f"check-boundaries: {root} has no hdl/ directory", file=sys.stderr)
        return 2
    problems = check(root)
    if problems:
        for p in problems:
            print(p)
        print(f"{len(problems)} boundary violation(s); see scripts/check-boundaries.py")
        return 1
    if not args.quiet:
        print("boundaries: ok (lib/ does not import Hdl; hdl/src imports only Hdl and the std)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
