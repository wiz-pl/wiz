# Stage 8: the backend

## 8a: IR and Perceus reference counting

```wiz no-check
#ir twice          -- def twice x0 x1 :=  dup x0;  let x2 := ap x0 x1;  let x3 := ap x0 x2;  ret x3
#run fact 10       -- 3628800, through the IR, on a heap that checks reference counts
```

* **IR** (`Compiler/IR.lean`): A-normal form, first order: objects (`ctor`), fields
  (`proj`), direct calls (`fap`), closures (`pap`/`ap`), native operations (`prim`),
  `case` on tags, join points. Constructors without fields and numbers are unboxed
  scalars.
* **Lowering** (`Compiler/Lower.lean`): lambda lifting, closure conversion, arities,
  join points for non-tail `case`s (closed over their variables). The generic
  eliminators are written in the erased language (`Compiler/PrimCode.lean`) and
  compiled like user code. The output is sorted by name, so it's deterministic.
* **Perceus** (`Compiler/RC.lean`): every variable is owned (until 8e's borrowed
  parameters); `dup` an argument that is still needed, and `drop` a variable as soon as
  it's dead (garbage free).
* **Checked heap** (`Compiler/IRRun.lean`): `#run` runs the IR with explicit reference
  counts and fails on use after free, double free, or leaks. All the examples give the
  same results under `#run` as under `#eval`.

| #   | Where             | What                                     |
|-----|-------------------|------------------------------------------|
| 8.1 | `Compiler/RC.lean`| `insertRC`: Perceus `dup`/`drop`        |

## 8b: C

```
$ wiz run fact.wiz        # def main : Nat := fact 30
265252859812191058636308480000000
```

* `wiz build FILE -o OUT` compiles the definition `main` to C and then to an
  executable; `wiz run FILE` also runs it and reads the printed result back with
  `main`'s type. The C compiler is `--cc X` (default `cc`), with `--cflags "…"` and
  `--ldflags "…"` for GMP ([stage 23a](23-grail.md): flags, not environment variables). The C tests
  skip themselves if GMP isn't found.
* **Runtime** (`runtime/`, embedded in the compiler): a value is a word; scalars
  have the low bit set; objects have a header (reference count, tag, size). Closures
  point to a boxed entry and share or move their captured arguments when applied.
  Numbers that don't fit in 62 bits are GMP integers. Projecting a number gives its
  unary view. The program checks at exit that every object was freed.
* **Codegen** (`Compiler/C.lean`): one C function per IR function (plus a boxed
  version for closures); `case` is a `switch`, join points are labels, `dup`/`drop`
  call the runtime.

| #   | Where              | What                                   |
|-----|--------------------|----------------------------------------|
| 8.2 | `Compiler/C.lean`  | `body`: C statements for an IR body    |

## 8c: reuse

`Compiler/Reuse.lean` pairs each `drop x` with a later allocation in the same block:
`let w := reset x; …; let y := reuse w in ctor t args`. At runtime, if `x` was unique,
its fields are dropped and the new object is written into its cell (if the sizes
match), so updating data you own happens in place. Constructor functions are inlined
when fully applied, so user code takes part. The generic eliminators already reuse
their payload pairs.

A cell is often taken apart in one block and rebuilt in another: a tree node is
projected and dropped at once, but the new node is built two `case`s later, after
comparing keys. So `reuseAcross` runs first and follows a dropped cell into the
branches (as Perceus and Lean 4 do): the `reset` stays where the drop was, each branch
that builds an object reuses the token, and the others free it at once
(`reuse w in ctor 0`, which needs no cell). The IR has no types, and a `Bool` returned
by a function has no cell to give, so only variables known to be objects (projected
from, or built) go across, outermost first; the local pass pairs what is left. A
zipper's insertion loop then allocates nothing per level. A drop that finds no
allocation is remembered and not tried again further down the path: the answer could
only be the same, and asking again (with the drop's parts each time) was exponential
along a chain of projections, the shape of a wide structure's fields read by a
bundle's `pack` (a 20-field bundle took two minutes).

| #   | Where                 | What                                          |
|-----|-----------------------|-----------------------------------------------|
| 8.3 | `Compiler/Reuse.lean` | `insertReuse`: pair drops with allocations    |

## 8d: LLVM

`wiz build FILE -o OUT --llvm` and `wiz run FILE --llvm` go through textual LLVM IR
(`Compiler/LLVM.lean`) and `llc` (`--llc X`). The runtime is the same C file,
compiled separately with `-DWIZ_API=` so that its functions are exported. In SSA form,
join point parameters live in stack slots, and a variable bound in several branches
gets one name per branch. The LLVM tests are the C tests, through LLVM.

The self-hosted compiler's first slice of this path (a closed `main : Nat`, with no
ownership or runtime yet) is stage 21aq: it ports the `ETm` → `IR.Decl` lowering and this
emitter for the allocating-free subset, and refuses the rest precisely.

Still to do in the backend: specialise the eliminators for known descriptions (flat
constructor objects instead of nested pairs, direct recursion instead of walking the
description).

## 8e: borrowed parameters and drop specialisation

```wiz no-check
#ir len            -- def len @&x0 :=  case x0 of | 0 => … | 1 => let x2 := proj 1 x0;  let x3 := len x2; …
```

* **Borrowed parameters** (`Compiler/Borrow.lean`, Lean 4's borrow inference): a
  parameter the function never consumes is borrowed (`@&` in `#ir`): the caller keeps its
  reference and lends it for the call, and the fields read from it are borrowed too, so
  the length of a list, a left fold or a lookup in a tree count nothing on the structure
  they walk. Consumed means returned, stored, captured, applied, passed to a native
  operation or to an owned parameter. A parameter whose cell (or a field's cell) is
  reused stays owned (no lost in-place updates), and so does one that receives an owned
  value in a tail call within its recursive group (loops stay loops); a greatest fixed
  point over the whole program, join points included.
* `proj` now reads a field without a new reference; `RC.lean` `dup`s the field of an
  owned object, lends arguments in borrowed positions, and `dup`s a variable that is
  both lent and passed to an owned position of the same call.
* **Closures** call with owned arguments: a partially applied function with borrowed
  parameters goes through a wrapper `f._owned`, which drops them after the call.
* **Drop specialisation** (`Compiler/DropSpec.lean`, Perceus §2.3): `dup`ing the fields
  of an object and then dropping it becomes one runtime operation, `dropMoved x mask`:
  if `x` is unique the fields move out and only its cell is freed, otherwise the fields
  get their references and `x` is decremented. A pair returned by a call and taken
  apart costs no reference counting when it is unique.
* **Borrowed comparisons**: the native comparisons `nat.beq` and `nat.blt` only look
  at their arguments, so they borrow them (`Expr.primBorrows`; the runtime's
  `wiz_nat_beq`/`wiz_nat_blt` no longer decrement): a lookup in a tree counts neither
  the key nor the keys it compares it with.
* **Borrowed tag inspections**: `tag` and `natTag` also only read the argument (a
  header tag, or whether a number is zero); they borrow it too, and
  `wiz_tag_of`/`wiz_nat_tag` no longer decrement. The scrutinee of every `match` is
  kept by the caller and dropped at its last use instead of being duplicated before
  the inspection, so a recursive `Nat` function saves an `inc` and a `dec` per step
  (`#ir` of a `Nat` counter has no `dup` before `natTag`).

## 8f: WebAssembly

`wiz build FILE -o OUT --target wasm` writes a binary WebAssembly module directly from
the IR and `wiz run FILE --target wasm` runs it under Node with a small JS host (big
integers only; values live in linear memory). `--wasm` is the older spelling of the same
target. It is additive: C and LLVM are unchanged. The supported subset is enforced when
the module is emitted, and every module is parsed and type-checked by a small validator
before it is written (so an encoder bug is a compile error). Its representation, limits,
the validator and the 34-case `wasm` test group are in
[08-backend/wasm.md](08-backend/wasm.md).

## 8g: WebGPU (WGSL) prototype

`webgpu/` emits WGSL for a small, data-parallel subset of Wiz and runs it on a WebGPU
device, comparing every value with the interpreter. This is a **prototype, not a
`--target`**: `wiz build --target wgpu` does not exist and the C/LLVM/Wasm backends are
untouched. It reads the syntax tree from `wiz parse` (so it is pre-elaboration and sees
builtin syntax only), accepts `U32`/`Bool`/`Nat`-index/`Array U32` values with `let`,
`match` on `Bool`, acyclic scalar helpers and the `UIntN` arithmetic/comparison
primitives, and refuses everything else (floats, IO, strings, `Nat` arithmetic,
allocation, closures, recursion, division) with a diagnostic naming the construct.

`webgpu/check.sh` runs three kernels over 8 narrow and 130 wide inputs (three
workgroups) and gets 414/414 values equal to the interpreter under Deno's wgpu/naga and
Mesa's lavapipe; `webgpu/tests/reject.mjs` checks 18 rejected fixtures. The browser demo
is `webgpu/index.html` over `webgpu/serve.mjs`. The subset, the host ABI, the counts and
the three blockers (unbounded `Nat` and the heap, closures and recursion, the async host
and the missing `Float32`) are in [08-backend/webgpu.md](08-backend/webgpu.md).

## 8h: eBPF (P0)

`wiz build FLOW.toml -o flow.c --target bpf` accepts a narrow, verifier-shaped subset and
writes freestanding C plus `bpf_rt.h`; `clang -target bpf` is the next step. The input is
a `bpf-core/1` typed core, **not** the IR: the IR is untyped and a `match` on a recursive
type has already become the generic `wiz.ind` interpreter, so the target needs the
elaborated types. The P0 cut (typed core, checker, C emitter skeleton, the exact
rejection messages, and what the first build/verifier run must establish) is in
[08-backend/bpf.md](08-backend/bpf.md). The P0 code builds and its pure group is green
(22/22); the object/verifier half (`clang -target bpf`, a privileged load) is still
pending, so do not treat the presence of `--target bpf` as the P0 exit criterion.
