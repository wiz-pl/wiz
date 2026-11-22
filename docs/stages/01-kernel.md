# Stage 1: the core kernel

```
Wiz/
  Rig.lean               Rig / QRig classes: the algebra of quantities
  Rig/Instances.lean     Unit (plain MLTT), Nat (exact counts), ZeroOneMany (Idris 2)
  Core/Term.lean         core syntax (de Bruijn indices), Decl, Globals
  Core/Value.lean        semantic domain: neutrals + closures (de Bruijn levels)
  Core/Eval.lean         eval, vApp, Closure.inst, quote, nf
  Core/Conv.lean         definitional equality with η
  Core/Usage.lean        usage vectors
  Core/Check.lean        bidirectional QTT checker, addDecl
  Core/Pretty.lean       pretty printer
  Core/Raw.lean          named terms + a tiny DSL, until stage 2 adds a parser
Tests/                   the exercise tests
```

## Conventions to keep straight

* **Terms** use de Bruijn **indices**: `var 0` is the nearest binder.
* **Values** use de Bruijn **levels**: `Val.var 0` is the *outermost* binder.
  Converting in a context of size `l`: `index = l - level - 1`.
* Environments and usage vectors are lists with the **innermost** binder at the head,
  so `env[ix]` is the value of `var ix`. The kernel's typing context (`Ctx`) stores its
  names, quantities and types as arrays indexed by **level** (outermost first), so
  `bind` appends and a de Bruijn lookup is `lvl - 1 - ix`. Usage vectors are sparse:
  they stop after the last variable used, and `Usage.zeros n` is `[]`.

## Exercises

Work through them in order, because later tests depend on earlier code.

| #   | Where                        | What                                                        |
|-----|------------------------------|-------------------------------------------------------------|
| 0.1 | `Rig/Instances.lean`         | `ZeroOneMany.add`, `mul`, `le` tables                        |
| 0.2 | `Rig/Instances.lean`         | prove the `QRig ZeroOneMany` laws                           |
| 1.1 | `Core/Eval.lean`             | `eval`                                                      |
| 1.2 | `Core/Eval.lean`             | `vApp`, `Closure.inst`                                      |
| 1.3 | `Core/Eval.lean`             | `quote`                                                     |
| 1.4 | `Core/Conv.lean`             | `conv`, including η for functions                           |
| 1.5 | `Core/Check.lean`            | `popUsage`: the heart of QTT                                |
| 1.6 | `Core/Check.lean`            | `check`: the `lam`, `let` and mode-switch rules              |
| 1.7 | `Core/Check.lean`            | `infer`                                                     |

The typing rules are written out in the docstring of `Core/Check.lean`.

## Optional extensions to stage 1

These have no tests. Write your own tests in `Tests/` as you go.

* **0.3** Atkey's erasure theorem needs extra conditions on the rig: *zero-sum-free*
  (`a + b = 0 → a = 0 ∧ b = 0`) and *zero-divisor-free* (`a * b = 0 → a = 0 ∨ b = 0`).
  Add them as a class and prove them for `ZeroOneMany` and `Nat`. Then find a rig
  where they fail and work out what goes wrong.
* **0.4** Add an affine rig `{0, ≤1, ω}`, where linear variables may be dropped, and
  a test showing a program it accepts that `ZeroOneMany` rejects.
* **0.5** Prove `Usage.add` commutative and `Usage.scale` distributive, using the
  `Rig` laws.
* **1.8** Implement Atkey's σ ∈ {0, 1} modes properly (see "Simplification vs. Atkey" in
  `Core/Check.lean`), so the checker stops verifying linearity inside type positions.
  ([Stage 4d](04-data.md) adds a light version, `Ctx.erased`, which only relaxes projections: in an erased position they are free, elsewhere they need an unrestricted pair.)
* **1.9** Σ-types with a QTT-friendly eliminator, `let q (x, y) := p; b`, which uses
  `p` `q` times and binds both components at that quantity. ([Stage 4b](04-data.md) has
  it; projections `p.1`, `p.2` are for unrestricted pairs only, since each drops a
  component.)
* **1.10** Glued evaluation: stop unfolding globals eagerly, keeping both the stuck
  and the unfolded form, so error messages print `Nat` and not its Church encoding.
* **1.11** Universe cumulativity (`Type i ≤ Type j`) and/or universe polymorphism.
