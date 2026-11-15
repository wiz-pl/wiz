# Bootstrapping Wiz from a C seed

This directory is the prototype of the post-Lean bootstrap described in
`wiz-notes/post-lean-workflow.md` §2.  The seed is the fixpoint's own stage-1 C
(`self1.c`), compiled by the host `cc` with `selfhost/rt.c`.  Once that fixpoint
artifact exists, building and checking the seed needs no Lean, no Wiz binary, no
network and no state outside the checkout.

Nothing here is checked in as a binary or as generated C: the generated
`bootstrap/seed*/` directories are git-ignored.  The generator, the checks and this
note are the committed artefact; a concrete `seed.c` + `SEED` pair is a release
artefact, rebuilt from a fixpoint run and verified with the scripts below.

## The chain

```
scripts/fixpoint.sh                    (Lean, once, produces the artifact)
  └─ self1.c, self2.c, run/input.wiz   self1.c == self2.c is the fixpoint
       │
       ├─ make-seed.sh  →  seed.c (copy of self1.c) + SEED (manifest)
       │
       └─ cc -I selfhost seed.c -o seed   one C invocation; rt.c is #included
            │
            ├─ T(seed)   = c1              seed compiles the toolchain
            ├─ cc c1     = stage 1
            └─ T(stage 1) = c2             c1 == c2 == self1.c == self2.c
```

`T(B)` is the C text binary `B` emits for the toolchain's own source
(`run/input.wiz`).  The seed is *not* a new compiler: it is the fixpoint's
stage-1 compiler, rebuilt by the reader's own `cc` from the C the fixpoint already
produced and compared.

### What is trusted

| component | trusted for | notes |
|---|---|---|
| `seed.c` (the generated C) | everything the compiler does | 7.6 MB (GC) / 12.4 MB (RC); generated, deterministic, and the exact artefact the fixpoint compares |
| the *diff* in `selfhost/*.wiz` since the seed | the compiler's behaviour beyond the seed | the reviewable part; small if seeds are bumped at releases |
| `selfhost/rt.c` | values, RC/GC, FFI marshalling, 63-bit `Nat` | ordinary reviewed C, `#include`d by the generated C |
| the C compiler | the seed and every `wiz build` | `gcc`/`clang` are interchangeable for this C (DDC-1) |
| libc and the OS | everything | unchanged from any C program |

The seed's *semantics* come from the compiler source you already review; its
*bytes* are a 7–13 MB opaque artefact.  That is the honest trade: the trusted code
gets smaller, the trusted artefact gets bigger.

## Files

| file | purpose |
|---|---|
| `make-seed.sh` | copy a fixpoint's `self1.c` to `seed.c`, check `self1.c == self2.c`, write `SEED`, optionally build the seed |
| `check-seed.sh` | seed → C → stage 1 → C; assert every stage equals the fixpoint's `self1.c`/`self2.c` |
| `ddc1.sh` | build the seed with two C compilers (default `gcc -O2`, `clang -O2`) and compare the compilers they produce |
| `verify.sh` | `make-seed` + `check-seed`, optionally `--ddc` |
| `seed*/` | generated output (git-ignored): `seed.c`, `SEED`, `seed`, check/DDC work dirs |

## Usage

```sh
# 1. Once, with Lean: produce the fixpoint (the normal repository script).
#    `--rc` is the recommended seed mode; the default is GC.
scripts/fixpoint.sh --rc .lake/fixpoint-rc

# 2. Everything below needs only a C compiler and libc.
bootstrap/verify.sh --fixpoint .lake/fixpoint-rc --ddc

# GC mode instead: source the toolchain environment for the Boehm flags.
. /workspace/wiz-env.sh
scripts/fixpoint.sh .lake/fixpoint
bootstrap/verify.sh --fixpoint .lake/fixpoint \
  --cflags "$WIZ_GC_CFLAGS" --ldflags "$WIZ_GC_LDFLAGS" --ddc
```

For an RC fixpoint, do not pass the GC flags: RC C defines `WIZ_RC` and uses no
Boehm collector.  `make-seed.sh` detects the mode from the C itself and records
it in `SEED`; `check-seed.sh` and `ddc1.sh` pass `--rc` accordingly.

The seed can also be built by hand, which is the whole point:

```sh
cc -O0 -w -I selfhost seed.c -o seed          # RC mode
cc -O2 -w -I selfhost seed.c -o seed          # recommended for stage 1
```

## The `SEED` manifest

`make-seed.sh` writes a text manifest next to `seed.c`:

```
format: 1
mode: rc                     rc | gc
source: <git commit of the tree>
sha256: <of seed.c>
bytes: <size>                lines: <line count>
fixpoint: self1.c == self2.c
fixpoint_sha256: <of self1.c>
rt.c_sha256: <of selfhost/rt.c>
input_sha256: <of run/input.wiz>
cc: <cc --version, first line>
cflags: <flags>              ldflags: <flags>
build: <the exact cc command>
```

A reviewer reads `SEED`; a machine checks `sha256`.  Both change only at a seed
bump (release time or an exceptional mid-cycle PR), not per commit.

## What DDC-1 proves, and what it does not

DDC-1 builds the *same* `seed.c` with two independent C compilers and compares the
compilers they produce.  Every seed variant must emit `self1.c`; every resulting
stage-1 compiler must emit `self1.c` again.  This catches:

* undefined behaviour in the generated C (pointer tagging, offset chains,
  statement expressions, signed overflow) that one compiler happens to implement
  differently;
* evaluation-order or optimisation-level dependence (`-O0`/`-O1`/`-O2`);
* “works only with gcc 16”.

It does **not** catch:

* a backdoor already present in `seed.c`: both sides compile the same bytes, so
  both reproduce it faithfully.  This is the Thompson problem and it defeats
  DDC-2 as well, because every Wiz seed descends from the same lineage;
* a wrong or malicious `rt.c`, which the seed does not compile and which is
  reviewed as C;
* a compromised C compiler, libc, or OS.

**Remaining gap.**  This prototype still depends on Lean to produce
`run/input.wiz`: `scripts/GenSelfhost.lean` concatenates `selfhost/*.wiz` with the
parser tables and the driver.  The seed compiles that generated toolchain, not yet
a checked-in `selfhost/Tables.wiz` + `selfhost/Main.wiz`.  §1.6 of
`post-lean-workflow.md` is the fix: check in the tables (about 38 KB of `Cat.mk`
lines) and a real driver, and the seed can assemble the toolchain from
`selfhost/*.wiz` alone.  Until then the chain is `seed + generated input + rt.c +
cc + libc`, not `seed + selfhost/*.wiz + rt.c + cc + libc`.

## Reviewability: a diff audit, not a reading

The generated C is not human-auditable as a whole.  Measured at `6f2fee5d`:

| mode | bytes | lines | mean line | longest line | lines > 1 KB | > 10 KB | > 50 KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| GC | 7,580,954 | 37,519 | 202 B | 166,028 B | 585 | 51 | 6 |
| RC | 12,444,752 | 17,230 | 722 B | 373,125 B | 1,165 | 200 | 20 |

A single expression can be a 166 KB line; the RC backend emits statement-heavy
one-line functions.  Reading it is not the audit.  The audit is:

1. **Review the Wiz diff**, not the C: every change to the seed's behaviour is a
   change to `selfhost/*.wiz`, which is ordinary language-level code.
2. **Regenerate and diff mechanically.**  `seed.c` is a pure function of the
   source; diff the old and new C and confirm only the functions that correspond
   to the changed declarations moved.  Function names are mechanical
   (`d_<Wiz name>`, `get_<name>`), so the mapping is direct.
3. **Hash the artefact.**  `SEED` records `sha256(seed.c)` and the fixpoint hash;
   `fixpoint.json` at release records `sha256(c2)`/`sha256(c3)`.
4. **DDC-1 every release**, and a diverse seed (DDC-2) when one exists.

The RC form is preferable for the seed because it removes the collector from the
trusted runtime and makes leaks a hard error, but its C is *less* line-structured
than the GC form; the diff-audit method is the same either way.

## Repository policy

* **Do not commit** a seed binary, `seed.c`, or the check/DDC work products.
  They are large, generated, and reproducible from the fixpoint.
* **Do commit** this directory: the generator, the checks, and the manifest
  format.  At a seed bump, publish `seed.c` + `SEED` + `rt.c` + `SHA256SUMS` as
  release artefacts, and optionally put `seed.c` in the tag if the project
  decides a source release must be self-contained.  The prototype deliberately
  keeps it out of the tree so a normal PR does not carry 7–13 MB of generated C.
* **Pin the seed at release time**, not per commit.  `master` between bumps is
  built by the last released seed; CI's `seed-compat` job is what catches drift.
* A fresh checkout without a released seed cannot bootstrap.  That is why the
  release must ship the seed, and why `post-lean-workflow.md` §5.5 makes it a
  `wiz 1.0` promise.  This prototype documents the gap rather than hiding it.

## Measured prototype

Commit `6f2fee5d` (`origin/master`), 2026-11-15.  The fixpoint artifact is the one
produced by the `#338` branch (`b39b15b3`); every input that `GenSelfhost` reads
(`selfhost/*.wiz`, `Wiz/Parser/Builtin.lean`, `Wiz/Version.lean`) is byte-identical
between that commit and `6f2fee5d`, and the GC `self1.c` was re-emitted with the
fixpoint's stage-1 compiler to confirm it.  Compilers: gcc 16.2.0 (the repository's
Nix dev shell) and clang 21.1.8.  The RC seed was generated by the same stage-1
compiler with `--rc`; its `self2.c` is `c2` below.

| artefact | mode | bytes | lines | sha256 |
|---|---:|---:|---:|---|
| `seed.c` | RC | 12,444,752 | 17,230 | `c27b1f96…d20042e` |
| `seed.c` | GC | 7,580,954 | 37,519 | `72d64ef8…58a587df` |
| `compiler.wiz` (input) | — | 860,512 | 16,730 | `fe64f39a…f07755` |
| `selfhost/rt.c` | — | 52,013 | 1,270 | `09839863…0afa14` |

Build and self-host timings (shared machine, not a `perf-run` window; treat as
upper bounds).  The RC chain is the recommended one:

| step | compiler | wall | peak RSS | result |
|---|---|---:|---:|---|
| `cc seed.c → seed` | gcc -O1 | 184.2 s | 2,129 MB | 12,814,136 B, `9547cf94…` |
| `T(seed)` → c1 | gcc-built seed | 230.6 s | 1,687 MB | c1 == `self1.c` |
| `cc c1 → stage 1` | gcc -O1 | 166.4 s | 2,114 MB | 12,814,136 B, `7ff4dce0…` |
| `T(stage 1)` → c2 | gcc-built stage 1 | 244.7 s | 1,685 MB | c2 == `self1.c` |
| `cc seed.c → seed` | clang -O1 | 273.1 s | 1,626 MB | 19,297,728 B, `9d34302e…` |
| `T(seed)` → c1 | clang-built seed | 182.2 s | 1,650 MB | c1 == `self1.c` |
| `cc c1 → stage 1` | clang -O1 | 233.9 s | 1,640 MB | 19,297,728 B, `0b266e30…` |
| `T(stage 1)` → c2 | clang-built stage 1 | 149.5 s | 1,654 MB | c2 == `self1.c` |

**Result:** `c1(gcc) == c1(clang) == c2(gcc) == c2(clang) == self1.c == self2.c`
(sha256 `c27b1f96…`).  DDC-1 passes: the seed built by gcc and the seed built by
clang produce the same compiler, and both resulting compilers reproduce the
fixpoint.  The binaries themselves differ (gcc 12.8 MB vs clang 19.3 MB; different
build-ids and code layout), which is expected and irrelevant to the claim: the
emitted C is the artefact.

For the GC seed, only the build was measured: gcc -O0 took 72.2 s / 2,686 MB and
produced a 19,554,720-byte seed; gcc -O2 took 236.1 s / 2,340 MB and produced
8,964,752 bytes.  A GC self-compile is the fixpoint's ~775 s stage, which did not
fit the bounded light scopes used for this run; the RC chain above is complete.

**Run note:** the requested `heavy --mem 6G` job was queued for ~18 minutes while
the shared 10 GB heavy budget was fully reserved by other agents, so the live run
used `light` scopes with an explicit 4 GB cap (the 2 GB default was too small for
`cc` on the 12 MB C).  The DDC matrix was therefore run at `-O1` for both
compilers; `-O0` seed builds were measured but their self-compile exceeded the
300 s light limit.  The commands and results are independent of the wrapper; rerun
`verify.sh` under `heavy --mem 6G` for the full O0/O2 matrix.
