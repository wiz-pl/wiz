# Regularity at inert types, decided by conversion

Regularity is the equation `cast A A e t ≡ t`. Wiz keeps it off in general (decision D1)
and keeps it only at *inert* types, first-order data such as `Enum`, `Unit`, `Σ`s of inert
types and `μ` types with inert indices and fields. This document describes how that
restricted rule, InReg_conv, is decided: as a rule of **conversion**, in both kernels,
with ground equality as the evaluator's fast path. It replaced an evaluator rule whose
side condition was syntactic equality, which was not invariant under conversion (issue P1
in the [soundness ledger](../Status.md)). It merged as PR #138, on top of the
[proof marker](prf-marker.md) (#128). The specification is
[CoreSpec §8.4](../CoreSpec.md) ("The rule is InReg_conv").

## Background

[AC20] shows that definitional regularity, together with an impredicative `Prop` and
proof-irrelevant equality, breaks normalisation of proofs. Wiz met this: an Abel–Coquand
program looped in both kernels with regularity on (D1 in Status.md). Decision D1 (a)
turned regularity off, so `cast` computes on data constructor by constructor. TTobs and
CCobs have no definitional regularity either; they have the proof term `castrefl`, which
is Wiz's `castRefl` axiom ([PT22], [PT23]; CoreSpec §8.4a). CICobs [PLT25] has
definitional regularity at all types, as the conversion rule Cast-Refl, and proves
conversion decidable for a fragment with an algorithm that never reduces proofs.

Wiz keeps regularity at inert types, where a cast between equal types never creates a
redex (an inert value has no λ) and agrees with the structural cast up to proof
irrelevance. InReg_conv is [PLT25]'s Cast-Refl restricted to inert types. The restriction
is Wiz's own. That it preserves decidability is a **conjecture**, argued relative to the
system without regularity (Status.md, D1).

The first implementation fired in the evaluator, with syntactic equality (`sameVal`) as
the side condition. A rule of evaluation with a side condition must give the same answer
for convertible inputs (S1) and must keep firing after a substitution (S2), or one side
of a conversion reduces while the other is stuck. Syntactic equality fails S1: `Fin (f p)`
and `Fin (f q)` for two proofs `p`, `q` are convertible but not syntactically equal, and
so are a glued name and its unfolding.

## The rule

```
A inert     Γ ⊢ A ≡ B     Γ ⊢ e : A ≡ B     Γ ⊢ t : A
───────────────────────────────────────────────────────  InReg_conv
Γ ⊢ cast A B e t ≡ t : B
```

It is a rule of conversion, not a reduction: the evaluator never calls conversion, so
there is no circularity between the two ([PLT25] §5 makes the same choice).

**In the Lean kernel** (`unCast` in `Wiz/Core/Conv.lean`, applied after weak head
normalisation in both `conv` and `convTy`): a neutral `cast A B e t · sp`, with any
eliminations `sp`, where `inertTy A` or `inertTy B` holds and `convTy A B`, is replaced by
`whnf (t · sp)` (`vElims`), repeatedly. The `convTy` call covers a *type* that is stuck on
a cast, such as `P i (cast …)` computed by an eliminator.

**In the self-hosted kernel** (`stripCast` and `convNeW` in `selfhost/Kernel.wiz`).
`Kernel.wiz`'s `conv` leaves glued values folded for lazy unfolding, so it has no point
after weak head normalisation at which to look for a cast. The step goes where neutrals
are compared: a strippable neutral on either side, against a neutral or a canonical
value, re-enters `conv` at the neutral's type (`typeOfNe`) with `forceSp t sp`. `stripCast`
and `forceSp` match every head and spine former by name, with no catch-all arm, so a new
former is a compile error, not a dropped elimination.

**"`A` or `B` inert".** `inertTy` (`Eval.lean`; `inertTy`/`inertW` in `Kernel.wiz`) reads a
`Σ`'s component sorts. When sorts were optional, of two convertible types one could be
inert and the other not, so asking either endpoint was needed for symmetry. With
[mandatory sorts](mandatory-sorts.md) conversion compares the sorts, and two convertible
types are both inert or both not. `inertTy` is a walk bounded at depth 8 that instantiates
binders with reserved atoms (`groundAtom`), never with variables a context could look up.

**The evaluator's fast path: ground equality.** `vCast` still removes a cast when
`groundEqTy A B` holds (`castReg` in `Kernel.wiz`): two inert types that are equal and have
no free variable in a relevant position. Values are compared by their inert type (tags,
numerals and constructors by their parts; `Unit` and propositions skipped; `Σ` by
projections), and a neutral equals only the same reserved atom. At an inert type
convertible values have the same canonical skeleton, so S1 holds; a ground type has
nothing to substitute, so S2 holds. Whenever it fires `A ≡ B`, so InReg_conv gives the
same equation. It keeps closed computations (casts at `Nat`, `Fin 3`) from leaving stuck
casts in values. What it leaves stuck, such as `cast (Fin n) (Fin n) e k` for variables
`n` and `k`, conversion removes.

**Flags.** `Globals.inertReg : InertReg` is `conv` by default; `--inert ground` keeps only
the fast path (`kernelInertConv := .false` in `Kernel.wiz`). `Globals.regularity` is `off`
by default; `--regularity full` (`kernelRegularity`) is Cast-Refl at *every* type, also in
conversion only, as an experiment. Each non-default value turns the elaboration cache off.

**Termination.** The side condition `convTy A B` compares two components of the neutral
under comparison, as the congruence rule for two casts already does. Each step removes one
cast from a finite nest. After stripping, `t · sp` for a canonical `t` may compute, but it
is a well-typed relevant term by the rule itself. The rule never looks at `e`, and the
kernel does not evaluate proofs.

**Strategy.** Strip whenever the rule applies, else congruence, with no backtracking
([PLT25] backtracks between congruence and two refl rules). Stripping one side first is
argued to lose no derivation, relative to a transitive `convTy`. This is an argument, not
a proof.

## Regularity while comparing propositions

A later extension, called PF-C in the code and the test names (merged as PR #324,
2026-11-14), applies Cast-Refl at every type while `convTy` compares two
propositions: the comparison and every comparison below it then strip a stuck cast at any
type with convertible endpoints. The reason given in the code is that the two sides are
truth values in the model, which validates Cast-Refl at every type. It lets two proofs
whose proposition types differ only by a `cast` (inside or outside a projection, in a
`transp` motive) compare. Equality of two data *types* still uses the inert-only rule. In
the Lean kernel this is `convTy` setting `regularity := .full` when `propSort?` says both
sides are propositions; in `Kernel.wiz` it is `TCtx.propGate` and the `reg` flag that
`stripCast` reads. It is not yet described in CoreSpec or Status.md.

## Alternatives considered

* **Syntactic side condition in the evaluator** (`--inert syntactic`, and the numeral
  shortcut in `vCastData`). Not invariant under conversion; removed, together with
  `sameVal`.
* **Ground equality alone.** Sound and stable, but incomplete: a cast at an inert type with
  an open index stays stuck. Kept as the fast path and as `--inert ground`.
* **Regularity modes in the evaluator** (`--regularity nonprop` and `refl`). The evaluator
  cannot call conversion, so without syntactic equality these had no rule left; `refl`
  also inspected a proof. Both were deleted. The tests that expected checking not to
  terminate with regularity and eager proofs now expect the program to check.
* **Widening to `Desc l I`, or to every type.** Not done. `Desc l I` is not inert (a
  description holds functions), and widening to it needs a logical relation at `Desc`,
  which no paper has. [PLT25]'s decidability proof covers Π, ℕ, ⊥, the impredicative
  `Prop` and ∃ with two universe levels, and not general inductive types, `μ` over a
  generic description, `ν`, sizes, `ULift`, quantities, or an equality type that computes
  alongside Cast-Refl. `--regularity full` exists to measure what breaks.

## Limits and what remains open

* Decidability with regularity at inert types is a conjecture (Status.md, D1).
* Completeness of "strip whenever possible, else congruence" against the declarative rules
  is argued, not proved.
* `refl : T = T` at a `μ` type still needs the elaborator's help: the equation of the codes
  leaves a stuck cast at `Desc l I`, which is not inert.
* Syntactic shortcuts that remain in comparisons all have a fallback or rest on stated
  preconditions: the comparison of two folded inductions on numerals by read-back
  (`convGlued`, falls back to full comparison) and `Kernel.wiz`'s `secase` shortcut
  (`tmEq` over the same environment, with a fallback).

## Tests

* Group `observational equality` (`Tests/Groups/Ott.lean`): "P1: InReg decided by
  conversion accepts the nine probes, open indices too (the default)"; "P1: the fast path
  alone (ground) accepts the value probes (PF-C) and rejects the type-position control";
  "regularity at inert types: an indexed recursor computes at a data motive (Vec.length)";
  the D1 (Abel–Coquand) cases, including "the cast's source type by name or as inferred:
  the same verdict and the same termination in every mode" and "with regularity and eager
  proofs the program checks too (regularity is a rule of conversion, not of evaluation)";
  and the cases on Cast-Refl inside an equation at a variable type (PF-C).
* Group `selfhost` (`Tests/Groups/SelfHost.lean`): "P1/PF-C: regularity is decided by
  conversion in both kernels (the probes as core terms; the type-position control)".
* Group `desceq` (`Tests/Groups/DescEq.lean`): "a cast at a variable element type stays a
  cast (no regularity)" and the Abel–Coquand cases with two box descriptions.
* Group `meta` (`Tests/Meta.lean`): "T0 against T1: InReg decides an inert cast in the
  spec; PF-C also lets the kernel use a cast at a type variable under a proposition".
* Group `language` (`Tests/Groups/Language.lean`): "castRefl: a propositional regularity
  axiom in the Prelude; it doesn't compute (D1)".
