# CAF caching of closed top-level definitions: verification (2026-11-19)

**Finding: already implemented on master; no prototype is needed.** `IR.cafs`
(`Wiz/Compiler/IR.lean:139-182`), `wiz_caf_init` (`runtime/rt_core.inc:197-213`) and the
C and LLVM backends landed as `3ef38ad8` ("Closed top-level definitions (CAFs) computed
once in compiled code", PR #207) on 2026-11-12, and are documented in
`docs/stages/15-performance.md`, 15i; the Wasm backend got the same protocol later
(`a6a3927f`, Wasm tail calls and CAF caching). The "big rock" in
`docs/notes/dogfood-new-features.md` (and `wiz-notes/dogfood-new-features.md`) predates
that commit. This note reproduces the cost and the win deterministically, and records
the rule and the risks; it changes no compiler code.

## The rule (what qualifies as closed)

`IR.cafs` selects a declaration when all of the following hold:

* it has no parameters **after erasure** (`d.params.isEmpty`), so erased proofs, types
  and quantities do not make a definition open;
* it is not `wiz.entry`, not a `wiz.export.*` wrapper and not a `wiz.native.*` foreign
  wrapper (`cafExcluded`);
* its body *does work* (`Expr.isWork` / `Body.isWork`): an allocation (`ctor` with
  fields, an integer literal ≥ 2^62), a call of a function with parameters, a partial
  application, a primitive, `reset` or `reuse`. A body that only returns a scalar, a
  projection, an erased value, or an alias of another nullary definition is left alone
  (the alias's callee is a CAF already, so the alias is one load anyway).

The decision is made on untyped IR, so "pure" is the language's type discipline rather
than a separate effect analysis: a value of a non-`IO` type is pure; a nullary `IO A`
is a closure (or has the world as a parameter), so caching it does not run it.

For each selected definition the native backend emits a `_build` function, a static
slot and a getter: a getter does one acquire load plus `wiz_inc` on the fast path, and
on the first use calls `wiz_caf_init`, which builds the value, makes it **immortal**
(`rc = 0`, recursively, `wiz_live--`, untracked by the leak checker), and publishes it
with a compare-and-swap. It is lazy, so a definition used only in an untaken branch is
never evaluated (even a diverging one). LLVM and Wasm emit the same protocol; the
self-hosted C backend has its own unconditional `get_g()` cache for nullary globals
(`selfhost/Backend.wiz:1864-1875, 2847-2863`).

## Reproduction

`examples/closed-table-bench.wiz` is the synthetic bounded case already in the tree: a
256-entry list and a balanced ROM tree built from it, both closed definitions, read
100000 times in a loop. I also used a copy that builds the **real**
`hdl/src/Hdl/Display.wiz` type (`Display.romBuild 7` font table, `Display.romBuild 8`
program table) and reads it with a pure `RomT` descent; it is the OLED project's
`Fx.fontT` / `Prog.tree` shape.

Measurements are **deterministic malloc counts**, not wall clock (this machine is
shared, and wall-clock claims belong to the perf window). A small `LD_PRELOAD` shim
counted `malloc`/`calloc`/`realloc`/`free` and the bytes requested; the program itself
is unchanged.

| program | build | mallocs | bytes requested | frees |
|---|---|---:|---:|---:|
| `closed-table`, C | `a916e13` (parent of 15i) | 204,900,055 | 6,352,006,160 | 204,900,073 |
| `closed-table`, C | `3ef38ad8` (15i) | 1,851 | 63,504 | 1,097 |
| `closed-table`, C | `c2efe881`, `IR.cafs := {}` | 204,900,067 | 6,352,006,544 | 204,900,085 |
| `closed-table`, C | `c2efe881` (CAF on) | 1,856 | 64,144 | 1,098 |
| `closed-table`, LLVM | `a916e13` | 204,900,055 | 6,352,006,160 | 204,900,073 |
| `closed-table`, LLVM | `3ef38ad8` | 1,851 | 63,504 | 1,097 |
| `hdl/src/Hdl/Display.RomT` bench, C | `c2efe881`, `IR.cafs := {}` | 511,800,067 | 16,376,006,544 | 511,800,085 |
| `hdl/src/Hdl/Display.RomT` bench, C | `c2efe881` (CAF on) | 5,568 | 185,920 | 4,427 |

For 100000 iterations, the old `closed-table` code did ~2049 allocations per iteration
(the table and the ROM rebuilt at every use); the cached code does none. The HDL-shaped
case does ~5118 per iteration before, none after. The checksums are identical with the
cache on and off (`24207140` and `24840543`), so the comparison is the same computation,
not a different program. The ~758 objects still live after the cached `closed-table` run
are the two tables and their closures (the intended retention); the RomT bench retains
1,141 objects for its two tables and their lists. The byte column is total requested over
the run (churn), not peak RSS: 6.35 GB → 64 kB and 16.38 GB → 186 kB.

A `--split 4` build of the same program keeps the cache too: 100000 lookups gave the
same 1,856 mallocs, 64,144 bytes and checksum `24207140` as the single-unit build.

The current-master "before" rows were produced by temporarily making `IR.cafs` return the
empty set and rebuilding `wiz`; that patch is not part of this branch. The historical
`a916e13`/`3ef38ad8` rows are the prebuilt C and LLVM binaries from the perf scratch
directory: the same benchmark source compiled by the compiler one commit before and
after 15i.

## Risks

* **Memory retention.** Everything reachable from a CAF becomes immortal and is never
  freed; `wiz_immortal` also retains objects that other code drops later. A large table
  used once stays for the whole run, and a CAF nested in another CAF extends the
  other's lifetime. The leak checker does not report immortal objects, by design.
* **Uniqueness is lost.** `rc = 0` means never unique, so `reset`/`reuse` copies a CAF's
  cells instead of updating them in place. A program that used to rebuild a table and
  then own it may now copy it on the first update. This is the GHC trade-off.
* **Initialisation order.** There is no global init order: each CAF is built on first
  use, so an unused one costs nothing. A definition that uses itself while being built
  recurses exactly as it did before (there is no black hole). Under threads, a race can
  build the same CAF twice; the loser's copy is made immortal and is never used, so the
  cost is bounded wasted work and memory, not a wrong result.
* **Effect assumptions.** The rule finds "closed", not "pure": a nullary definition
  that calls a foreign/native operation typed as a pure value is cached, so such a
  foreign operation must really be pure (or return `IO`). An effectful `IO` action is a
  value and is not run by caching. A CAF that is never used is never evaluated; a CAF
  that diverges still diverges on first use.
* **Self-hosted backend.** Its `get_g()` cache is unconditional (it caches cheap
  scalars and aliases too) and its guard is a plain `static int`/`static V`, not the
  atomic load/CAS the Lean backends use; the concurrency plan (R-f) already lists this.
  Do not "fix" one backend without the other's parity story.
* **First-use cost.** `wiz_immortal` walks the whole value with an explicit stack and a
  temporary `malloc`; the first use of a huge constant pays a traversal proportional to
  its size.

## Verification commands

```
# allocation-count shim (in .scratch, not committed): then
LD_PRELOAD=.scratch/libmalloctrack.so <binary> 100000
```

Before/after binaries are the perf scratch builds
`wiz-tools/bench/scratch/window-8/closed-table-{c,llvm}-{a916e13,3ef38ad}`;
the current-master check used the worktree's own `.lake/build/bin/wiz` built from
`c2efe881`.

No compiler or library code is changed. The only repository change on this branch is
this note (and the stale-candidate status in the dogfooding note).

## Appendix: the `hdl/src/Hdl/Display.RomT` benchmark

```wiz
import Prelude
import IO
import Text
import Hdl.Display

def Caf.fontGo : Nat → List Nat → List Nat
  | .zero, acc => acc
  | .succ i, acc =>
    let v := Nat.mod (i * 37 + Nat.div (i * i) 7 + 11) 256
    Caf.fontGo i (.cons v acc)

def Caf.font : List Nat := Caf.fontGo 128 .nil

def Caf.fontT : Display.RomT := Display.romBuild 7 Caf.font

def Caf.progGo : Nat → List Nat → List Nat
  | .zero, acc => acc
  | .succ i, acc =>
    let v := Nat.mod (i * 1103515245 + 12345 + Nat.div (i * i * i) 13) 256
    Caf.progGo i (.cons v acc)

def Caf.prog : List Nat := Caf.progGo 256 .nil

def Caf.progT : Display.RomT := Display.romBuild 8 Caf.prog

-- a pure read (the value simulation's `Display.romAt`, on Nats)
def Caf.read : Nat → Display.RomT → Nat
  | a, .leaf v => v
  | a, .node k hi lo => match Nat.testBit a k with
    | .true => Caf.read a hi
    | .false => Caf.read a lo

def Caf.loop : Nat → Nat → Nat
  | .zero, acc => acc
  | .succ n, acc =>
    let a := Nat.mod (n * 37) 256
    let f := Caf.read (Nat.mod a 128) Caf.fontT
    let p := Caf.read a Caf.progT
    Caf.loop n (Nat.mod (acc + f + p) 1000000007)

def Caf.arg : List String → Nat
  | .cons s _ => match String.parseNat s with
    | .some n => n
    | .none => 100000
  | .nil => 100000

def main : IO Unit :=
  IO.bind IO.args (fun as => IO.println (Nat.toString (Caf.loop (Caf.arg as) 0)))
```

Build it with the worktree's `wiz build` (pass `--cc` when the Slurm node's PATH has no C
compiler) and run it with `100000`.
