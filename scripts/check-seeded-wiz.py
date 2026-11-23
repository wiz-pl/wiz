#!/usr/bin/env python3
"""Guard a package derivation built with a *seeded* wiz.

`nix build .#hdl` / `.#scry` / `.#tower` uses the pure `wiz` derivation, whose build
inputs include `wiz-unwrapped`. CI instead passes the lean job's `wiz` store path
through `lib.<system>.<package>With (builtins.storePath …)`: the seeded path is a store
input, so Nix substitutes it and never starts `wiz-unwrapped`. This script proves that
on the derivation graph, before the build:

  * the seeded wiz is in the inspected derivation's input sources and in its
    `nativeBuildInputs`;
  * no `wiz` derivation is among its input drvs (a pure `wiz-<version>.drv`, or a
    direct `wiz-unwrapped`).

Usage
  scripts/check-seeded-wiz.py DRV_JSON WIZ
  scripts/check-seeded-wiz.py DRV_JSON WIZ --through tower-unwrapped
  scripts/check-seeded-wiz.py --self-test

DRV_JSON is `nix derivation show <drv>` output. `--through NAME` treats the given
derivation as a wrapper and inspects the input derivation whose name contains NAME
(the tower wrapper and `tower-unwrapped`). Nix 2.34's `inputs.{drvs,srcs}` and the
older `inputDrvs`/`inputSrcs` shapes are both read. Exit 0 on success, 1 on a failed
guard, 2 on usage.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

WIZ_PREFIX = "/nix/store/"


class GuardError(Exception):
    """A derivation that would build a wiz instead of using the seeded one."""


def graph(document: dict) -> dict:
    return document.get("derivations", document)


def drvs(derivation: dict) -> dict:
    """The input derivations, as Nix 2.34 (`inputs.drvs`) or older (`inputDrvs`)."""
    return derivation.get("inputs", {}).get("drvs", derivation.get("inputDrvs", {}))


def srcs(derivation: dict) -> list[str]:
    """The input sources with full store paths (Nix 2.34 stores bare basenames)."""
    raw = derivation.get("inputs", {}).get("srcs", derivation.get("inputSrcs", []))
    return [s if s.startswith("/") else WIZ_PREFIX + s for s in raw]


def only(document: dict, what: str) -> dict:
    entries = graph(document)
    if len(entries) != 1:
        raise GuardError(f"expected one derivation in {what}, got {len(entries)}")
    return next(iter(entries.values()))


def show(path: str) -> dict:
    try:
        return json.loads(
            subprocess.check_output(["nix", "derivation", "show", path], text=True)
        )
    except (OSError, subprocess.CalledProcessError, json.JSONDecodeError) as exc:
        raise GuardError(f"cannot read the derivation {path}: {exc}") from exc


def check(derivation: dict, wiz: str) -> None:
    if wiz not in srcs(derivation):
        raise GuardError(f"the seeded wiz {wiz} is not an input source")
    if wiz not in derivation.get("env", {}).get("nativeBuildInputs", ""):
        raise GuardError(f"the seeded wiz {wiz} is not in nativeBuildInputs")
    bad = [p for p in drvs(derivation) if "-wiz-" in p or "-wiz-unwrapped-" in p]
    if bad:
        raise GuardError(f"a wiz derivation is still an input: {', '.join(sorted(bad))}")


def guard(path: Path, wiz: str, through: str | None) -> None:
    derivation = only(json.loads(path.read_text()), str(path))
    if through:
        found = [p for p in drvs(derivation) if f"-{through}-" in p]
        found = [p if p.startswith("/") else WIZ_PREFIX + p for p in found]
        if len(found) != 1:
            raise GuardError(
                f"expected one {through} input derivation, got {found or 'none'}"
            )
        derivation = only(show(found[0]), found[0])
    check(derivation, wiz)


# --- self-test ---------------------------------------------------------------------


def fixture(wiz: str, *, src: bool, inputs: dict | None = None, old: bool = False) -> dict:
    env = {"nativeBuildInputs": wiz if src else ""}
    if old:
        return {"derivations": {"x.drv": {
            "env": env, "inputSrcs": [wiz] if src else [], "inputDrvs": inputs or {}}}}
    return {"derivations": {"x.drv": {
        "env": env,
        "inputs": {"srcs": [wiz.removeprefix(WIZ_PREFIX)] if src else [],
                   "drvs": inputs or {}},
    }}}


def self_test() -> int:
    wiz = "/nix/store/aaaa-wiz-0.1.0"
    failures = 0
    checks = 0

    def expect(label: str, document: dict, ok: bool) -> None:
        nonlocal failures, checks
        checks += 1
        try:
            check(only(document, label), wiz)
            got = True
        except GuardError:
            got = False
        if got != ok:
            failures += 1
            print(f"self-test FAIL: {label}: guard returned {got}", file=sys.stderr)

    expect("the seeded path is an input source", fixture(wiz, src=True), True)
    expect("the old Nix inputSrcs shape", fixture(wiz, src=True, old=True), True)
    expect("a missing source", fixture(wiz, src=False), False)
    expect(
        "a wiz derivation input",
        fixture(wiz, src=True, inputs={"zzzz-wiz-0.1.0.drv": {}}),
        False,
    )
    expect(
        "a wiz-unwrapped derivation input",
        fixture(wiz, src=True, inputs={"zzzz-wiz-unwrapped-0.1.0.drv": {}}),
        False,
    )

    if failures:
        print(f"check-seeded-wiz self-test: {failures} of {checks} failed", file=sys.stderr)
        return 1
    print(f"check-seeded-wiz self-test: ok ({checks} graph cases)")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check that a seeded-wiz package derivation cannot build a wiz."
    )
    parser.add_argument("derivation", nargs="?", help="`nix derivation show` JSON")
    parser.add_argument("wiz", nargs="?", help="the seeded wiz store path")
    parser.add_argument(
        "--through",
        metavar="NAME",
        help="inspect the input derivation whose name contains NAME (e.g. tower-unwrapped)",
    )
    parser.add_argument("--self-test", action="store_true", help="check the guard's fixtures")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    if not args.derivation or not args.wiz:
        parser.error("DRV_JSON and WIZ are required")
    try:
        guard(Path(args.derivation), args.wiz, args.through)
    except (OSError, json.JSONDecodeError, GuardError) as exc:
        print(f"seeded wiz guard: {exc}", file=sys.stderr)
        return 1
    print(f"seeded wiz guard: {args.wiz} is an input source; no wiz derivation")
    return 0


if __name__ == "__main__":
    sys.exit(main())
