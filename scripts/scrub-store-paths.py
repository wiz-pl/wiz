#!/usr/bin/env python3
"""Remove every absolute Nix store path from a binary, in place, leaf only.

This is deliberately *not* what a Nix package does. An intermediate store path may
name its build inputs (a RUNPATH, a copied command line, a diagnostic string); Nix
tracks those references and keeps the inputs alive. The release tarball is the one
exception: it leaves the store and has to run on a machine with no `/nix/store`, so
the final leaf step scrubs the references instead of shipping them. Do not call this
on an intermediate derivation's output.

The replacement is same-length (`x` bytes), so every ELF offset stays valid. The
paths this removes are build metadata, never data the program reads: the tarball's
binaries are linked statically against every non-glibc library and their interpreter
and RUNPATH are fixed by `patchelf` in the same leaf step.

    scripts/scrub-store-paths.py FILE...

Exit status: 0 clean or rewritten, 1 a file could not be written, 2 usage error.
"""

from __future__ import annotations

import re
import sys

# `/nix/store/<32 base-32 chars>-<name>`, stopping at whitespace, NUL, a quote, a
# colon or one of the characters a command line or JSON string uses as a delimiter.
STORE = re.compile(rb"/nix/store/[0-9a-z]{32}-[^\x00\s\"'`<>]+")


def scrub(path: str) -> int:
    with open(path, "rb") as f:
        data = f.read()
    out = STORE.sub(lambda m: b"x" * len(m.group(0)), data)
    if out == data:
        return 0
    with open(path, "wb") as f:
        f.write(out)
    return len(STORE.findall(data))


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    for path in argv:
        try:
            n = scrub(path)
        except OSError as e:
            print(f"scrub-store-paths: {path}: {e}", file=sys.stderr)
            return 1
        print(f"scrub-store-paths: {path}: {n} store path(s) removed")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
