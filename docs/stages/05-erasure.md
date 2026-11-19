# Stage 5: erasure and the interpreter

```wiz no-check
#eval fib (.succ (.succ (.succ (.succ (.succ .zero)))))   -- .succ (… 8 …)
#erase Vec.cons                                          -- the erased code
```

* **Erasure** (`Compiler/Erase.lean`) is type-directed and bidirectional, like the
  kernel. Types, proofs, sizes, quantities, and everything of quantity `0` become `◾`.
  QTT guarantees the erased parts are never needed. Binders are kept, and an erased
  argument is passed as `◾`.
* **A 0-quantity position is not evaluated — not merely deferred.** That is the value of
  a `let 0 x := v`, a `0` field of a constructor or structure, the scrutinee of a
  `split` at 0, and an argument of a `0`-quantity Π binder. The kernel checks exactly
  these positions in erased mode (`Ctx.erasedAt`) and erasure replaces exactly these
  with `◾`: both ask `QPoly.isErased`, so a term valid only because it is never computed
  cannot reach runtime. `let 0 x := spin (); b` does not diverge, `f (spin ())` with
  `f : (0 x : A) → B` does not either, and a `0` field holding `spin ()` is not built.
  So a 0 position cannot carry an effect: effects live in `IO`, whose world token is
  linear (quantity 1), and a foreign function outside `IO` must be pure
  ([Stage 9a](09-ffi.md)); compiled code may drop its call. If a value has to run for its
  effect, it is used at quantity `1` or ω, and erasure keeps it. The tests that pin this
  are "a 0 position is never evaluated" (group `eval`, both interpreters) and the
  `ffi` group's "compiled code never evaluates a 0 position" (C and LLVM).
* **Erasure is not divergence-preserving, by design.** A call whose *result type* is a
  proposition is erased with its arguments, even though the kernel checked those
  arguments at their own (ω) quantities: `f (spin ())` with `f : Nat → 0 = 0` prints
  nothing and does not diverge. That is the proof-irrelevance assumption erasure is
  built on, and it is why an effect must be in `IO` (a function into `World`, never a
  proposition) rather than hidden in a proof. `partial` is a convenience for
  computations whose value is observed, not a promise that erasure keeps them.
* **What erasure still carries.** Binders are kept, so an erased parameter is a real
  parameter: it is passed as a boxed `◾` (`WIZ_BOX(0)` in C, `i64 1` in Wasm), and
  reference counting dup/drops it like any scalar. The *index* of a `μ`/`ν` is a
  runtime value too (the generic eliminators `ind`, `coit`, `sfix`, `scase` receive it);
  it is erased only when its own type is (a phantom tail, `Unit`). A description is
  runtime data, so its fields are erased field by field.
* **A function into `Unit`** — `(0 x₁ : D₁) → … → (0 xₙ : Dₙ) → Unit`, `n ≥ 1` — has one
  inhabitant up to η (`fun _ … _ => ()`), so its values have no runtime content
  (`erasedFunTy`): phantom tails ([22e](22-numbers.md)) and a structure's marker are of
  this shape, and applying one is `◾`. That is a *type-shape* test, not a binder-name
  test, so a hand-written type of the same shape converts to the structure and gets the
  same representation (R3). The self-hosted backend (`selfhost/Backend.wiz`,
  `erasable`/`erasedFunTy`) follows the same rule; it used to check only propositions,
  so such a field survived there as a closure.
* **Data at runtime**: a value of `μ D i` is its payload (nested pairs with a tag), and
  descriptions are runtime values. `ind`, `Desc.elim` and the `map` behind
  coiteration are runtime primitives that walk the description.
* **The interpreter** (`Compiler/Run.lean`) is strict, with lazy codata (`coit`,
  `scofix`) that unfolds under `out`. `#eval` reads results back with their type, so
  they print with constructor names.

| #   | Where                   | What                                              |
|-----|-------------------------|---------------------------------------------------|
| 5.1 | `Compiler/Erase.lean`   | `eraseCheck`, `eraseInfer`                         |
| 5.2 | `Compiler/Run.lean`     | `run`                                             |
| 5.3 | `Compiler/Run.lean`     | `ind` (hypotheses) and `out` (coiteration's `map`) |

Next: an ANF intermediate representation with join points and explicit closures,
specialising the primitives for known descriptions (flat constructor objects), and
then macros (stage 6), which run in this interpreter.
