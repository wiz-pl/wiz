# Linear case analysis

Wiz's kernel tracks how often each variable is used (quantities `0`, `1`, `ω`), and data
types can declare a quantity per constructor field. Until the work described here, a
value of an inductive type held at quantity 1 could be built and passed on but never
taken apart: every eliminator handed the payload over at ω. This page explains the
problem, the rules that now exist (a quantity on the sized case `scase`, the unit
eliminator `let () := u; b`, and the generated `T.casesOnA` and `T.casesOn1`), what is
still open, the alternatives that were rejected and why, and where the tests are. The
normative rules and the soundness argument are in [the core specification](../CoreSpec.md),
§10.2 and §10.2a; [stage 4h](../stages/04-data.md) is the user-facing summary.

## The problem

Three kinds of program want linear values inside data:

- **A variable used once in each alternative.** A linear `t` used once in every
  alternative of a `match` on ordinary data was rejected, because the generated
  `T.casesOn` takes one ω argument per constructor, and the uses in separate arguments
  add up.
- **Data that holds a resource.** A result type whose `ok` (and `err`) carry a linear
  value, `inductive Res1 (A : Type) | ok (1 a : A) | err (e : Nat) (1 back : A)`, could be
  built, but a `match` on a `Res1` held at 1 was rejected.
- **Borrow handles.** The region library and Feral's lowering of Rust-style borrows want
  a `&mut` handle that is used exactly once and handed back on every path, including the
  error path. With handles as ω values, duplicating a `&mut` or packing it with its
  region was a library invariant the kernel could not see.

The design also found a hole: raw `ind` charged its scrutinee once but bound its payload
at ω, so `ind (fun _ _ => Tok × Tok) (fun i xs ih => (xs.1, xs.1)) b` duplicated the
content of a linear box `b`. `sfix`, `scase`, and the seeds of `coit` and `scofix` had
the same shape. `match` was not affected, since the generated recursors take their
scrutinee at ω. This was a runtime linearity bug, not a proof of `False`.

## What the kernel already had

Most of the rules were there. `ecase` on a tag joins its branches (`U + (V₀ ⊔ … ⊔ Vₙ)`),
the additive rule. `split` at `q` binds a Σ's components at `q·p` and `q`. The
interpretation of a description, `⟦arg q S D⟧ = (q s : S) × …`, puts a field's declared
quantity into the payload type, so `con` already charges each field at its declared
quantity. What was missing was an eliminator for `μ` that hands over the payload at a
quantity other than ω, and a way to use up the payload's final `Unit`.

## The rules as implemented

**Eliminators scale what they take apart (K0).** `ind` and `sfix` now charge
`ω·(U_m + U_x)`, and `coit`/`scofix` scale their seed by ω: an eliminator that binds at
ω needs an unrestricted value. The negative tests (`dup`, `dropTok`) are in
`Tests/Groups/Language.lean`. `ind` stays the ω eliminator; it gets no quantity, because
a linear `ind` is the wrong shape: its method receives both the payload and the induction
hypotheses computed from the same recursive fields, so each recursive field is used twice
by construction.

**A quantity on `scase` (K1).** `Term.scase` carries a quantity term `q`, checked like
`split`'s:

```
m ⇐ (0 j : Size< s) → (0 i : I) → (q xs : ⟦D⟧ (μ^j D) i) → P i (con xs)   ⊣ U_m
x ⇐ μ^s D i                                                              ⊣ U_x
────────────────────────────────────────────────────────────────────────────
scase_q P m s i x ⇒ P i x                                                ⊣ U_m + q·U_x
```

The method runs once, so it is not scaled. At `q = ω` this is the ordinary case; at 1 a
value held at 1 is taken apart; at 0 the scrutinee is erased, and the method cannot
branch on the tag, because `ecase` charges its scrutinee once and `1 ≤ 0` is false. That
gives Idris 2's restriction of erased matches to single-constructor types without a side
condition, and it also means a branching case at a quantity variable is rejected
(`QPoly.le` must hold under every assignment, including 0). Conversion compares `q`
(`convNe`); evaluation ignores it, and erasure ignores it except that a case at 0 passes
`◾` as the payload. Both kernels have the rule: `Term.scase` and `check` in
`Wiz/Core/Check.lean`, `Tm.scase` and `Spine.sscase` in `selfhost/Kernel.wiz`.

There is no new term former and no separate rule for fields. The method takes the
payload apart with rules that exist: `split` at `q` gives the tag at `q·ω` and the rest
at `q`; `ecase` on the tag joins the branches; each further `split` gives a field
declared `p` at `q·p`, the index equation at `q·0 = 0`, and the final `Unit` at `q`.

**The unit eliminator.** `let () := u; b` consumes a `u` whose type is `Unit` itself
after `whnf`, charging `U₁ + U₂` (`checkUnit` in `Wiz/Core/Check.lean`; `Tm.letUnit` and
`checkUnit` in `selfhost/Kernel.wiz`). It is linear logic's 1-elimination and the only
way a `Unit` held at 1 is used up. It evaluates to `b` by η; erasure compiles it to a
strict `let _ := u'; b'`, so `u` is still run (`Wiz/Compiler/Erase.lean`). The
self-hosted backend refuses it, since its `let`s are lazy. A linear token must therefore
not be a named unit type (`def Tk : Type := Unit`): anyone could discard one. Tokens are
axioms or opaque types.

**Generated eliminators.** `mkRecursor` in `Wiz/Elab/Recursor.lean` generates, next to
`T.casesOn`:

- `T.casesOnA` (`additive := true`): the methods bundled into one argument at quantity 1,
  a function from the tag, `(1 m : (t : Enum ls) → ecase t [ULift M_c…])`. `match` passes
  `fun t => ecase t [up m_c…]`, whose branches are alternatives, so a variable used once
  in each branch is used once. Its body is `scase` at `∞`, so it needed no kernel change.
- `T.casesOn1` (`linear := true`): the same for a scrutinee held at 1. Its body is
  `scase` at 1, takes the payload apart with `split`s at 1 (a projection would use the
  pair ω times), and ends with `let () := u` on the final `Unit`. Fields come out at
  their declared quantities, which is what `con` charged for them.

**Choosing.** `match` (`Wiz/Elab/Term.lean`) uses `T.casesOn1` when the scrutinee
mentions a variable bound at 1 (`linearLvls`), binding the scrutinee at 1 too;
`T.casesOnA` when a variable bound at 1 is in scope but the scrutinee is unrestricted;
and the old eliminators otherwise, so existing code elaborates to the same terms. A
field bound at 1 is linear again, so a nested `match` on it uses `casesOn1`. The
destructuring `let q (x, y) := s` (`elabLetPair`) binds its components at `q·p` and `q`
(`splitQtys`), so a component taken at 1 is linear for a later `match`. Erasure
recognises calls of `casesOn1` and `casesOnA` like those of `casesOn`, so compiled linear
matches take the same fast path.

## The soundness argument, in brief

CoreSpec §10.2 gives it in full. Every variable is charged once for the method and `q`
times for the scrutinee, so a 1-variable can occur in one of them, and in the scrutinee
only at `q ∈ {0, 1}`. On a constructor, `scase_q P m s i (con xs)` and its reduct
`m ∞ i xs` are charged the same usage vector, so reduction neither copies nor drops what
the payload uses. At `q = 1` the payload must be used exactly once, and a field declared
`p` comes out at `p`. At `q = 0` the scrutinee is never computed. Linearity is not
uniqueness (an ω value can be passed to a 1 binder), so `scase_1` does not license
in-place update; reference counts are still checked at run time.

The supporting literature is standard for the rule itself: Linear Haskell's `case_π`
(Bernardy et al., POPL 2018), Atkey's QTT (LICS 2018), Idris 2's erased matches (Brady,
ECOOP 2021) and graded dependent type theories with graded Σ eliminators (Choudhury et
al., POPL 2021; Abel, Danielsson and Eriksson, ICFP 2023). None of them covers Wiz's
first-class descriptions or its observational equality, so the specification states an
argument, not a citation of a proof.

## Rejected alternatives

- **K2a: an unused binder of a unit-shaped type may be dropped.** Proposed as the
  smallest way to deal with the payload's final `Unit` (justified by η), implemented, and
  withdrawn after review. Any rule that trusts a type to "hold nothing" fails once the
  type has a closure inhabitant: `stash (1 t : T) : (0 e : T = Unit) → Unit` hides a
  linear `t` in a function into `Unit`, and dropping it forgot a lock guard, so the next
  `acquire` deadlocked in compiled code. Restricting the rule to structure tails or to
  literally written types does not help. The explicit unit eliminator replaces it.
- **K2b: any type that is a singleton by η may go unused.** Fails for the same reason.
- **A separate `case_π` term former.** The same rule as a quantity on `scase`, with one
  more constructor in every term, value and spine type of both kernels, for no gain.
- **A catamorphic linear `ind`.** It would need a new method-type template and ι-rule in
  trusted code, and methods still could not capture linear variables (they run once per
  node). Linear recursion is planned through `sfix` instead (below).
- **Sums encoded as `(t : Enum ls) × ecase t [A₁, …]`.** This works with no kernel change
  and was the check that the rule chain is right, but it is not an `inductive`: no
  patterns, no `deriving`, no recursion, and structural rather than nominal typing.
- **Church encodings and continuation-passing style.** Sound and possible before, but a
  linear effect tree cannot be inspected, protocols with choice nest closures, and every
  linear library re-derives the encoding.
- **An explicit `match1`.** `match` chooses the eliminator from the quantities of the
  locals involved instead.

## What is open

- **Linear structures.** A structure held at 1 still cannot be taken apart: field access
  is a projection, and a nested `let 1` leaves the structure's marker tail unconsumed.
  Linear data is a one-constructor `inductive` with fields at 1. Re-encoding structures
  with the marker in a 0-quantity first component would make the tail an erased position;
  it has not been done.
- **Linear recursion (K3).** `sfix` has no quantity yet. The planned rule binds `x` and
  the recursive argument at `π` and charges `ω·U_f + π·U_x`, with state threaded through
  the motive. It is needed for linear containers and an inspectable linear effect tree,
  and to close the remaining borrow gap below.
- **`split` in `selfhost/Kernel.wiz`.** The self-hosted kernel has no `split`, so a pair
  held at 1 cannot be consumed in its fragment, and its descriptions carry no field
  quantities (fields are ω; `scase_1` still binds the payload at 1).
- **Default field quantity.** Fields default to ω. Linear-by-default fields (as in Linear
  Haskell) would change what `con` charges for every existing type; not proposed now.
- **Borrow handles.** With `Uniq1` (a one-constructor inductive with a private
  constructor, taken at 1) the kernel rejects duplicating a `&mut` and packing a handle
  with its region (group `regions`, and the Feral test for one local mutably borrowed
  twice). Reading a lender under another name is still a pinned known gap: the lender is
  an ω value, and closing it needs linear lenders and K3.

## Tests

- `Tests/Groups/LinearCase.lean`, group `linear-case`: a linear field matched out of a
  linear scrutinee and handed back in both alternatives; a resource dropped or duplicated;
  the scrutinee reused after the match; a field at 0 used at run time; indexed families;
  nested linear matches; a borrow scope over a linear handle; linear `Unit` and tokens;
  the counterexamples to K2a; and compiled runs, including a lock ticket released in `IO`
  exactly once under the C and LLVM backends.
- `linearCaseRule` in `Tests/Elab.lean`: raw kernel terms for `scase` at 0, 1 and ω and
  the unit eliminator, checked differentially against both kernels
  (`Tests/Groups/SelfHost.lean`).
- `Tests/Groups/Language.lean`: `ind` on a linear scrutinee rejected, and the current
  limits on linear structures and tuple patterns.
- `Tests/Groups/Regions.lean` and `Tests/Feral.lean`: the borrow-handle cases.
