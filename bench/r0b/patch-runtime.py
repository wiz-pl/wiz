#!/usr/bin/env python3
"""Patch the Lean toolchain's runtime, as `wiz build` hands it to cc, for R0(b).

R0(b) of the runtime convergence measures what masking object pointers with
`WIZ_OBJ(v) = v & ~0xE` (the selfhost runtime's offset bits) costs the Lean toolchain's
generated programs. `wiz build` pastes the runtime into the program's C (C target) or
writes it to `wiz_runtime.c` (LLVM target); this rewrites that text.

    patch-runtime.py VARIANT FILE.c      rewrite FILE.c in place; print the number of sites

Variants:
  base      no change (0 sites)
  mask      the plan's sites: the header casts in wiz_inc, wiz_dec, wiz_free,
            wiz_immortal and wiz_mark_mt go through WIZ_OBJ (5 functions)
  mask-all  every `(wiz_hdr *)v`, `(wiz_hdr *)x` and `(wiz_hdr *)y_` cast in the runtime
            (an upper bound: tag reads, apply, thunks, arrays ... masked too)
  check     as mask, but WIZ_OBJ traps when one of the bits is set: the masked builds
            are only meaningful if no Lean object pointer has bits 1-3 set (16-byte
            alignment), so this variant is run once to show that
A file without the runtime is left alone (prints 0). Exit 1 when a variant other than
base finds fewer sites than it expects (the runtime changed under the patch).
"""
import re
import sys

MARK = "void wiz_inc(wiz_val v)"
SCALAR = "#define WIZ_IS_SCALAR(v) ((v) & 1)"
FUNCS = ["wiz_inc", "wiz_dec", "wiz_free", "wiz_immortal", "wiz_mark_mt"]


def define(variant):
    if variant == "check":
        return ("#define WIZ_OBJ(v) ((((wiz_val)(v)) & 0xE) ? (__builtin_trap(), (wiz_val)(v))"
                " : ((wiz_val)(v) & ~(wiz_val)0xE))")
    return "#define WIZ_OBJ(v) (((wiz_val)(v)) & ~(wiz_val)0xE)"


def patch_funcs(text):
    """The header casts of `v`/`x` in the definition of each of FUNCS (counts functions)."""
    n = 0
    for f in FUNCS:
        m = re.search(r"\b" + f + r"\(wiz_val [a-z_]+\)\s*\{", text)
        if not m:
            continue
        end = text.find("\n}\n", m.end())
        body = text[m.end():end]
        new, k = re.subn(r"\(wiz_hdr \*\)(v|x)\b", r"(wiz_hdr *)WIZ_OBJ(\1)", body)
        if k == 0:
            continue
        text = text[:m.end()] + new + text[end:]
        n += 1
    return text, n


def patch_all(text):
    # only inside the runtime: from the scalar macro to the end of the pasted runtime is
    # not delimited, so restrict to casts of the runtime's own variable names
    return re.subn(r"\(wiz_hdr \*\)(v|x|y_)\b", r"(wiz_hdr *)WIZ_OBJ(\1)", text)


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    variant, path = sys.argv[1], sys.argv[2]
    with open(path, encoding="utf-8", errors="surrogateescape") as f:
        text = f.read()
    if variant == "base" or MARK not in text:
        print(0)
        return
    if SCALAR not in text:
        sys.exit(f"patch-runtime: {path} has the runtime but not `{SCALAR}`")
    text = text.replace(SCALAR, SCALAR + "\n" + define(variant), 1)
    if variant in ("mask", "check"):
        text, n = patch_funcs(text)
        want = len(FUNCS)
    elif variant == "mask-all":
        text, n = patch_all(text)
        want = len(FUNCS)
    else:
        sys.exit(f"patch-runtime: unknown variant {variant}")
    with open(path, "w", encoding="utf-8", errors="surrogateescape") as f:
        f.write(text)
    print(n)
    if n < want:
        sys.exit(f"patch-runtime: {variant} patched {n} sites in {path}, expected >= {want}")


main()
