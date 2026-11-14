# The Wiz core: reference specification

This document states the calculus that Wiz's kernel checks, as inference rules, so that
someone who knows type theory can review it without reading the implementation first.
It is derived from the code, not from the stage docs ([stages/](stages/)). Where the two disagree, §14 lists the
disagreement. What is proved about the calculus, and what is not, is in
[Status.md](Status.md).

* **Kernel (reference):** `Wiz/Core/` (Lean 4). `Check.lean` (typing), `Conv.lean`
  (definitional equality, subtyping, sizes), `Eval.lean` (evaluation and the computation
  rules), `Level.lean` (universe levels), `QPoly.lean` and `Usage.lean` (quantities),
  `Templates.lean` (the generic operations on descriptions).
* **Mirror:** `selfhost/Kernel.wiz`, the same kernel written in Wiz. It covers a fragment
  (§15) and differs in places, listed per rule and in §15.
* **Line numbers** refer to commit `9717950` (on `master`). They drift as the
  code changes. The function names are the stable reference.

Each rule is tagged:

* **[std: X]**: the rule is the standard one from reference X (§16);
* **[wiz]**: the rule, or this form of it, is specific to Wiz. That does not make it
  wrong, but no published system checked by us contains it;
* **[impl]**: a rule that exists for the implementation only (glued evaluation, numerals),
  meant to be invisible in the theory.

"Unverified" marks a claim we did not check.

---

## Contents

1. [Reading guide](#1-reading-guide)
2. [Syntax](#2-syntax)
3. [Judgment forms](#3-judgment-forms)
4. [Universes and levels](#4-universes-and-levels) (4.1 [Lifting](#41-lifting-ulift-q4))
5. [Quantities](#5-quantities)
6. [Variables, Π, λ, application, let](#6-variables-π-λ-application-let)
7. [Σ, Unit, Empty, True, False, enumerations](#7-σ-unit-empty-true-false-enumerations)
8. [Observational equality](#8-observational-equality)
9. [Descriptions, μ and induction](#9-descriptions-μ-and-induction)
10. [Sizes, ν and sized (co)recursion](#10-sizes-ν-and-sized-corecursion)
11. [Definitional equality and subtyping](#11-definitional-equality-and-subtyping)
12. [Evaluation strategy](#12-evaluation-strategy)
13. [Global declarations and universe polymorphism](#13-global-declarations-and-universe-polymorphism)
14. [Where the code and the stage docs disagree](#14-where-the-code-and-the-stage-docs-disagree)
15. [The self-hosted kernel (`Kernel.wiz`)](#15-the-self-hosted-kernel-kernelwiz)
16. [What is not in the core, and who checks what](#16-what-is-not-in-the-core-and-who-checks-what)
17. [References](#17-references)

---

## 1. Reading guide

The kernel is a **bidirectional type checker with normalisation by evaluation (NbE)**.
Terms use de Bruijn indices. Types are evaluated into a semantic domain of values
(closures, neutrals), and definitional equality is decided on values, directed by their
type. In the rules below, a substitution such as `B[a/x]` is what the kernel computes by
instantiating a closure (`Closure.inst`, `Eval.lean:282`). `≡` is the conversion
algorithm of §11, and `≤` is subtyping (§11.5).

Three features make Wiz's core unusual, and they interact everywhere:

1. **Quantities (QTT).** Every binder carries a quantity from a rig, and every judgment
   also outputs a *usage vector*: how often the term uses each variable at run time.
2. **Observational equality (OTT).** `a = b` is not an inductive type. It is a proposition
   that computes by the type of `a`, and `cast` computes by the two types. Propositions are
   definitionally proof-irrelevant, and `Prop` is impredicative.
3. **Anonymous data.** Inductive and coinductive types are `μ D i` / `ν D i` for a
   *description* `D` (a first-class value), with **sizes** on both.

---

## 2. Syntax

`Wiz/Core/Term.lean:41–159`. Binders are written with names here, for readability.

```
q, r     ::= qlit ρ   (ρ ∈ R, the rig)   |  x  (a variable of type Qty)        quantities
l, u     ::= 0 | l+1 | max l u | imax l u | ν   (ν a level parameter)          levels
s        ::= ∞ | ↑s | x                                                      sizes (terms of type Size)

t, A, B ::=
  x | c.{l…}                                      variables, global constants
  Sort l                                          universes (Prop = Sort 0, Type u = Sort (u+1))
  (q x : A) →^σ B                                 Π; σ = ⟨i, j⟩ the sorts of A and of B (mandatory)
  λx. t | t u                                     no domain or quantity on λ
  let x :q A := t; u | (t : A)                    let, ascription
  (q x : A) ×^σ B | (t, u) | t.1 | t.2            Σ; σ = ⟨i, j⟩ as for Π (mandatory)
  let q (x, y) := t as z. M; u                    Σ elimination (`split`)
  Unit_l | tt | Empty_l | absurd M t              Unit_0 = True, Empty_0 = False
  ULift.{k,l} A | up t | down t                   lifting to a bigger universe (§4.1, Q4); k the sort of A
  prf.{l} t                                       the proof marker (§8.6): `t`, whose type is in `Sort l`
  t = u   (written eq A t u)                      observational equality of elements
  A ≡ B   (written eqTy A B)                      equality of types
  refl A t | reflTy A | cast A B e t | transp A a P p b e
  Qty | qlit ρ                                    the type of quantities, literals
  Enum [ℓ₀…ℓₙ₋₁] | tag k | ecase t as z. M [b₀…bₙ₋₁]   (labels ℓ are metadata)
  Desc.{l} I | ret i | arg q S D | rec q j D | hrec q H j D
  Desc.elim.{v} P mret marg mrec mhrec D
  μ.{l} I D i ^s | con t | ind.{l,v} I D P m i t
  ν.{l} I D i ^s | out t | cocon t | coit.{l} I D S step i t
  Size | ∞ | ↑s | Size< s
  sfix.{l,v} I D P f s i t | scase.{l,v} I D P m s i t | scofix.{l} I D A f s i a
  n  (natLit)                                     numerals of the type registered by `builtin nat`
  ?m (mvar)                                       elaborator only: the kernel rejects it
```

**Mandatory sorts.** Every Π and Σ carries the sorts of its two components,
`σ = ⟨i, j⟩` (`BinderSorts`: `i` the domain's or first component's, `j` the codomain's or
second component's, under the binder), and every `ULift` the sort `k` of its content. They
are written, never inferred by evaluation: the rules *pi*, *sigma* and *ulift* check each
one against the inferred sort of its own component (structurally, never a combination such
as `imax i j`), and evaluation reads them (whether a type is a proposition, §8.3; whether a
cast computes, §8.4, D2). The level `_` (a *hole*, `Level.hole`) exists only in the
elaborator, before its sorts pass; the kernel rejects it. `σ.piSort = imax i j`,
`σ.sigmaSort = max i j`.

`natOp` (`Term.lean:158`) is produced only by evaluation and never type-checked. `μ` and `ν`
also carry a *display hint* (the nominal name to print) that conversion ignores.
`BinderInfo` (explicit/implicit) is ignored by the kernel.

---

## 3. Judgment forms

```
Γ ⊢ t ⇒ A ⊣ U        infer:  t synthesises type A, using the variables of Γ as U       (Check.lean:338)
Γ ⊢ t ⇐ A ⊣ U        check:  t checks against A, using U                              (Check.lean:256)
Γ ⊢ A type@l         A ⇒ Sort l, checked in erased mode, usage discarded             (checkType, Check.lean:660)
Γ ⊢ q qty ↦ p        q ⇐ Qty, and its value is the quantity polynomial p             (checkQty, Check.lean:654)
Γ ⊢ a ≡ b : A        conversion (decided)                                            (conv, Conv.lean:252)
Γ ⊢ A ≡ B type       type conversion                                                 (convTy, Conv.lean:326)
Γ ⊢ A ≤ B            subtyping (sizes)                                               (subTy, Conv.lean:474)
Γ ⊢ s ≤ s'  /  Γ ⊢ s < s'   size order                                              (sizeLe, sizeBelow, Conv.lean:126, 143)
⊢ l ≡ l'             level equivalence                                               (Level.equiv, Level.lean:291)
```

**Contexts** (`Ctx`, `Check.lean:169`): a list of entries `x :p A` (a quantity polynomial
`p` and a type value `A`) or `x :p A := v` (a `let`), together with a flag `erased`
(written `Γ⁰` when set). Index 0 is the innermost entry.

**Usage vectors** `U` (`Usage.lean`) have one quantity polynomial per context entry. `0ₙ`
is the zero vector, `𝟙ₓ` is "x used once" (`Usage.single`), `U + V` is pointwise sum,
`p·U` is pointwise scaling. The rules below write `⊣ 0` for `⊣ 0ₙ`.

**Erased mode** `Γ⁰` is a light version of Atkey's σ = 0 (§5.4). It is switched on for
type positions, proofs and sizes, and for every position whose usage is scaled by a
constant 0 (`Ctx.erasedAt`): an argument to a `0`-quantity binder, the value of a `let` at
0, the first part of a pair checked at a 0 field, the scrutinee of a `split` at 0. Such a
position is never computed (erasure replaces it by `◾`, `Erase.lean`); the kernel and
erasure decide "constant 0" with one predicate, `QPoly.isErased`, because a term in such a
position may be valid *only* erased. Its effect is on
projections only (§7.1): in `Γ⁰` any field of any pair may be read, erased fields
included, and a projection counts its pair's usage unscaled (which the position then
multiplies by 0, or discards).

---

## 4. Universes and levels

`Level.lean`. Levels are Lean 4's: `0`, `l+1`, `max`, `imax`, parameters, and level
metavariables (elaborator only).

```
                                  ─────────────────────────── sort        [std: CIC/Lean]   Check.lean:353
                                  Γ ⊢ Sort l ⇒ Sort (l+1) ⊣ 0
```

* **Non-cumulative.** There is no rule `Sort l ≤ Sort (l+1)`; `Type 0 : Type 1` only.
  (`subTy`, `Conv.lean:474`, has no universe case.) Cumulativity is optional exercise 1.11.
* **Impredicative `Prop`.** Π takes `imax` (rule *pi*, §6), so `(x : A) → P` is in `Prop`
  whenever `P` is, whatever `A`'s universe. [std: CIC/Lean]
* **Level equivalence** `⊢ l ≡ l'` (`Level.equiv`, `Level.lean:291`): both sides are
  normalised to a sorted list of `(atom, offset)` meaning their `max`
  (`normalize`, `Level.lean:265`); an `imax a b` whose `b` is not visibly nonzero stays
  an atom. If the normal forms differ, the algorithm case-splits on a parameter that
  decides some `imax` (`p = 0` or `p = p'+1`), with fuel 8. This is sound (equal answers
  hold under every instantiation of the parameters) and complete without `imax`; with
  `imax` it is incomplete, as in Lean. [std: Lean 4 kernel; the comment in `Level.lean`
  says so; not checked against Lean's source]
* `l ≤ l'` is `max l l' ≡ l'` (`Level.le`, `Level.lean:301`). `isNeverZero l`
  (`Level.lean:278`) means some entry of the normal form has offset ≥ 1.

Level metavariables never reach the kernel in a checked declaration (the elaborator
solves or defaults them). The kernel does not reject them explicitly; it treats them as
opaque atoms.

### 4.1 Lifting: `ULift` (Q4)

Universes are not cumulative, so a type in a small universe is moved up explicitly.
`ULift.{k,l} A` (`Term.ulift`) is a copy of `A : Sort k` in `Sort l`, for `k ≤ l`; `k` is
written in the term (mandatory sorts) and checked. Its only
use in the core is in descriptions: a description field must be in exactly `Sort (l+1)`
(§9.1), and the elaborator wraps smaller fields. [std: Agda's `Lift`, Lean's `ULift`;
the levitated descriptions of [CDMM10] fix the field level and use `Lift` the same way]

```
     Γ ⊢ A type@k'   ⊢ k ≡ k'   k ≤ l      Γ ⊢ a ⇐ A ⊣ U                   Γ ⊢ t ⇒ ULift.{k,l} A ⊣ U
     ───────────────────────────── ulift   ──────────────────────── up    ───────────────────────── down
     Γ ⊢ ULift.{k,l} A ⇒ Sort l ⊣ 0         Γ ⊢ up a ⇐ ULift.{k,l} A ⊣ U  Γ ⊢ down t ⇒ A ⊣ U

     down (up a) ⟶ a                                                       (β)      vDown, Eval.lean
     t ≡ t' : ULift A   iff   down t ≡ down t' : A                         (η)      conv, Conv.lean
     ULift.{k,l} A ≡ ULift.{k',l'} A'   iff   l ≡ l', k ≡ k' and A ≡ A'                convTy
```

`up` is checked only (its type can't be inferred). `down` is an elimination: it is stuck on
a neutral and quotes back as `down t`. Usages pass through (`up a` and `down t` use what `a`
and `t` use).

**Propositions.** `ULift.{l} P` for a proposition `P` is a proposition only when `l ≡ 0`
(then `P : Sort 0`, and `ULift.{0} P` is equivalent to `P`). For `l` never `0` it is not a
proposition: its inhabitants are **boxed proofs**. They are not all convertible by proof
irrelevance at their own type (`typeSort? (ULift.{l} P) = l`), but they are by η, since
`down t ≡ down t' : P` by proof irrelevance at `P`. So a lifted proposition has one
inhabitant up to conversion, like `Unit`. Whether a type is a proposition stays a property of
the type itself (its sort, `propSort?`), never of the sort it is used at.

**Observational equality** (`vEq`, `vEqType`, `vCast`; the given lines at the top of each):

```
a =_{ULift.{k,l} A} b  ⟶  True                         if A is a proposition (k ≡ 0)
                       ⟶  down a =_A down b            if A is not one (k never 0)
                       ⟶  stuck                        if unknown (k depends on a parameter)
ULift.{u} A ≡ ULift.{w} B ⟶  (X → Y) × (Y → X)         if both are propositions (u ≡ w ≡ 0)
                       ⟶  A ≡ B                        if u ≡ w
                       ⟶  False                        if u, w are closed and different; else stuck
ULift A ≡ B, B another canonical former  ⟶  False      (ULift is in `canonical`: no confusion)
cast (ULift.{k,u} A) (ULift.{k',w} B) e t
                       ⟶  up (cast A B e (down t))     if u ≡ w, u is never 0, and k ≡ k' (D2)
                       ⟶  stuck                        if both are propositions (the cast is a proof, §8.6)
                       ⟶  stuck                        otherwise
```

These follow the pattern of the other formers [std: PT22's rules for a type former with
one constructor]: the code equation is injective (`ULift A ≡ ULift B` iff `A ≡ B`) and
the cast goes through the eliminator. They agree with the casts on data (§8.4, D1): the
payload cast of a constructor casts each field, and a lifted field `up x` is cast to
`up (cast S S' ê₁ x)`, so a lifted proof field becomes the equivalence applied to the
proof (a stuck proof), exactly as an unlifted proof field did: the D1 argument (no proof
returned unchanged) still holds. `ULift A` is inert when `A` is (`inertTy`), and a lifted
proposition is not. The rule for `cast` requires `u` never `0` (not merely "not known to
be 0"), so the choice between the two rules is stable under level substitution. It also
requires the contents to be in one sort (`k ≡ k'`, written in the terms): the reduct
`cast A B e (down t)` is formed only within one sort (D2, §8.4). Reading `k` instead of
asking `propSort?` of the content makes `x = y : ULift X` compute for a type variable `X`
(its sort is written).

**Subject reduction for the new rules.** *β*: `down (up a)` has type `A` because `up a ⇐
ULift A` needs `a ⇐ A`. *η* only adds conversions between terms of the same type.
*`vEq`*: `a =_{ULift A} b` is formed when `ULift A` is in a never-zero sort, and `down a`,
`down b : A`, so `down a =_A down b` is a well-formed proposition when `A` is not a
proposition; when `A` is one, the equation is about boxed proofs, which are all equal
(η + irrelevance), so `True` is its value. *`vEqType`*: `ULift.{l} A ≡ ULift.{l} B` is
formed at one level `l`; `A ≡ B` may relate types at different levels `k, k' ≤ l`, which
`eqTy` would not form directly, but (as with the Π/Σ decomposition, §8.3) it then
computes to `False` or stays stuck: the levels of `A` and `B` are visible in their
shapes. *`vCast`*: with `e : ULift A ≡ ULift B`, which computes to `A ≡ B`, `cast A B e
(down t) : B` and `up` of it is a `ULift B`.

**Erasure.** `ULift` has no runtime content: `up a` erases to `a`, `down t` to `t`, and
`ULift A` is erasable exactly when `A` is (a lifted proof is still erased). A description
whose tag is lifted (`arg q (ULift (Enum ls)) F`) is still marked as starting with a tag.
So lifting changes no runtime representation (`#ir` is unchanged). A field of an
infinitary constructor with a lifted domain is read as `fun h => f (up h)`, which erases to
`f` (an η-step in `eraseCheck`).

---

## 5. Quantities

### 5.1 The rig

`Wiz/Rig.lean`. A `QRig` is a commutative semiring `(R, +, 0, ·, 1)` with a decidable
preorder `le used declared`, monotone in `+` and `·` (the laws are fields of the class, so
every instance carries their proofs). The kernel is parametric in `R`. The `wiz` command
line and the test suite use `ZeroOneMany = {0, 1, ω}` (`Wiz/Rig/Instances.lean:76`,
`Main.lean:48`):

```
+ : 0+a = a,  1+1 = 1+ω = ω+ω = ω          · : 0·a = 0,  1·a = a,  ω·ω = ω
le used declared  ⇔  used = declared  ∨  declared = ω                     (so 0 ≤ 1 is FALSE: 1 is linear)
```

Other instances: `Unit` (plain MLTT) and `Nat` (exact counting, `le` is `=`). Each rig also
fixes a default quantity for binders the kernel generates itself, `explicitDefault`
(`ω` for `ZeroOneMany`, `1` for `Nat`, `()` for `Unit`).

### 5.2 Quantity terms and polynomials

Quantities are terms of type `Qty` (stage 4d). `Qty : Sort 1`, `qlit ρ : Qty`. A binder's
quantity is evaluated to a **polynomial** over the rig whose variables are `Qty`-typed
locals (`QPoly.lean`); anything else (a stuck computation) is rejected (`qtyPoly`,
`Check.lean:223`).

```
     Γ⁰ ⊢ q ⇐ Qty     eval q = p polynomial
     ──────────────────────────────────────── qty         [wiz]   checkQty, Check.lean:654
     Γ ⊢ q qty ↦ p

     ───────────────────── Qty                ───────────────────── qlit                    Check.lean:485–486
     Γ ⊢ Qty ⇒ Sort 1 ⊣ 0                     Γ ⊢ qlit ρ ⇒ Qty ⊣ 0
```

`p ≤ p'` (`QPoly.le`, `QPoly.lean:88`) is `le` on constants; on polynomials with variables
it must hold under **every** assignment of the variables to rig elements, which needs a
finite rig (`elements?`); for an infinite rig only syntactically equal polynomials are
related (`leSymbolic`, `QPoly.lean:75`). Note that `checkQty`'s usage is discarded and its
check is **not** in erased mode (`Check.lean:655`); a quantity is a type-level object, so
this is harmless.

### 5.3 Usage accounting

The judgments output usage vectors with these operations [std: Atkey18; McBride16]:

* **variables** use themselves once: `𝟙ₓ`;
* **application** to a `q`-binder scales the argument's usage by `q`: `U₁ + q·U₂`;
* **leaving a binder** declared `q` pops its usage `u` and requires `u ≤ q`
  (**subusaging**, `popUsage`, `Check.lean:231`); a linear
  `Unit` is not exempt (K2a was withdrawn, §10.2a); it is consumed by the unit
  eliminator `let () := u; b`, whose usage is `U_u + U_b`;
* **types, quantities and proofs use nothing** (their usage is discarded). For proofs this
  is a rule of `check` and `infer` (both kernels): a term whose type is a proposition (its
  sort computed and `0`) is checked in an erased position and its usage is `0`, at every
  level of the proof. So a variable at `0` may appear in a proof, and a linear one must
  still be used in relevant code. (Proofs are erased by compilation and never run.) For
  the same reason a **binder whose type is a proposition takes any usage** (`popUsageAt`):
  a linear proof may be used once, never or twice, and `let 1 (a, h) := p` at
  `(1 x : A) × P x` is fine.
* **branches** of an `ecase` combine by the **join** `⊔` (least upper bound in `≤`) of
  their usages (`QPoly.join?`, `QPoly.lean:105`); `0 ⊔ 1 = ω` in `{0,1,ω}`, and if
  there is no join the case is rejected [wiz: Atkey's QTT has no case analysis on
  enumerations of this form; booleans in Atkey18 require both branches to use the same
  context, which is the `1 ⊔ 1 = 1` instance];
* **a case at a quantity** `scase_q` (K1, §10.2) uses its method once and its scrutinee
  `q` times, `U_m + q·U_x`, and binds the payload at `q` [std: Linear Haskell's
  `case_π`, Idris 2; wiz: on descriptions];
* **eliminators that run a method once per node** (`ind`, `Desc.elim`, `sfix`, `scofix`,
  `coit`) scale the method's usage by the rig's unrestricted quantity `QRig.many?` (ω);
  a rig without one (exact counting, `Nat`) rejects methods that use local variables
  outside erased positions (`methodUsage`) (§9, §10) [wiz]. (Before `a986c02` the scale
  was `explicitDefault`, which under-counted in the `Nat` rig: Status.md, Q2.)

### 5.4 Erased mode, versus Atkey's σ

Atkey's system has judgments at σ ∈ {0, 1} and does not track usage at σ = 0. Wiz checks
everything in the σ = 1 style and then discards the usage of type positions
(`checkType`, `Check.lean:660`) and of arguments to `0`-binders (scaled by 0). The
module docstring (`Check.lean:131–137`) says this "is sound but rejects a few erased terms
that Atkey would accept". The `erased` flag (`Ctx.erased`, `Check.lean:180`) restores one
of them: projecting an erased Σ field. Whether this simplification is sound in Atkey's
sense is **unverified** (it is plausible: it only rejects more, and discarding usage is
what the 0-fragment does anyway).

---

## 6. Variables, Π, λ, application, let

```
     ─────────────────────────────── var            [std]            Check.lean:346
     Γ ⊢ x ⇒ Γ(x) ⊣ 𝟙ₓ

     Γ ⊢ q qty ↦ p   Γ ⊢ A type@i'   ⊢ i ≡ i'   Γ, x :p A ⊢ B type@j'   ⊢ j ≡ j'   (σ = ⟨i, j⟩, no hole)
     ──────────────────────────────────────────────────────────────── pi      Check.lean `inferCore`
     Γ ⊢ (q x : A) →^σ B ⇒ Sort (imax i j) ⊣ 0
```
[std: Atkey18 for the quantity, Lean for `imax`; the component sorts σ are [wiz] (mandatory
sorts), checked by `checkComponentSort`, each against the inferred sort of its own component.
Their purpose is §8.3 and §8.4. **Structural**: a combination (`imax i j`) would not do,
since `imax 2 2` would then pass as the sort of `X → Type` with `X : Sort 1`, while the cast
rules read the domain's sort (`wiz-notes/prf-marker.md` §8.1, item 6). `λ ⇐ Π` and
`(a, b) ⇐ Σ` trust the expected type's σ: it was formed by this rule, or written by the
kernel's own templates (§16, trust 4–5).]

```
     Γ, x :p A ⊢ b ⇐ B ⊣ (u :: U)     u ≤ p         (p = value of q)
     ──────────────────────────────────────────── lam     [std: Atkey18]    Check.lean:259–262
     Γ ⊢ λx. b ⇐ (q x : A) → B ⊣ U

     Γ ⊢ f ⇒ T ⊣ U₁     whnf T = (q x : A) → B     p = value of q
     Γ' ⊢ a ⇐ A ⊣ U₂    where Γ' = Γ⁰ if p is the constant 0, else Γ
     ──────────────────────────────────────────── app     [std: Atkey18]    Check.lean:368–375
     Γ ⊢ f a ⇒ B[a/x] ⊣ U₁ + p·U₂

     Γ ⊢ q qty ↦ p   Γ ⊢ T type@_   Γ' ⊢ v ⇐ T ⊣ U₁   Γ, x :p T := v ⊢ b ⇐ A ⊣ (u :: U₂)   u ≤ p
     (Γ' = Γ⁰ if p is the constant 0, else Γ)
     ──────────────────────────────────────────── let (⇐; the ⇒ form is the same)    Check.lean:263–270, 376–383
     Γ ⊢ let x :q T := v; b ⇐ A ⊣ p·U₁ + U₂

     Γ ⊢ T type@_     Γ ⊢ t ⇐ T ⊣ U
     ──────────────────────────────── ann                       Check.lean:384–388
     Γ ⊢ (t : T) ⇒ T ⊣ U

     Γ ⊢ t ⇒ A' ⊣ U     Γ ⊢ A' ≤ A
     ──────────────────────────────── switch (subsumption)      Check.lean:311–315
     Γ ⊢ t ⇐ A ⊣ U
```

`λ` cannot be inferred (`Check.lean:366`). `let` is transparent: the body sees
`x := v` (`Ctx.define`, `Check.lean:196`), so `x` unfolds during conversion. The switch rule
uses **subtyping**, not conversion; subtyping differs from conversion only on sizes (§11.5).

*Kernel.wiz.* `app` evaluates the argument only if the codomain may mention it
(`usesVar`, `Kernel.wiz:1719`, a conservative syntactic test; `Kernel.wiz:1772–1782`).
The `lam` rule is `Kernel.wiz:2116`. Quantities are the three literals only.

---

## 7. Σ, Unit, Empty, True, False, enumerations

### 7.1 Σ

```
     Γ ⊢ q qty ↦ p   Γ ⊢ A type@i'  ⊢ i ≡ i'   Γ, x :p A ⊢ B type@j'  ⊢ j ≡ j'   (σ = ⟨i, j⟩, no hole)
     ──────────────────────────────────────────────────────── sigma               Check.lean `inferCore`
     Γ ⊢ (q x : A) ×^σ B ⇒ Sort (max i j) ⊣ 0

     Γ' ⊢ a ⇐ A ⊣ U₁     Γ ⊢ b ⇐ B[a/x] ⊣ U₂     (Γ' = Γ⁰ if p is the constant 0, else Γ)
     ──────────────────────────────────────── pair  (check only)                  Check.lean `check`
     Γ ⊢ (a, b) ⇐ (q x : A) × B ⊣ p·U₁ + U₂

     Γ ⊢ t ⇒ T ⊣ U    whnf T = (q x : A) × B    1 ≤ p    ω·U fits Γ
     ──────────────────────────────────────── fst                                  Check.lean `infer`, `projUsage`
     Γ ⊢ t.1 ⇒ A ⊣ ω·U

     Γ ⊢ t ⇒ T ⊣ U    whnf T = (q x : A) × B    ω·U fits Γ
     ──────────────────────────────────────── snd                                  Check.lean `infer`, `projUsage`
     Γ ⊢ t.2 ⇒ B[t.1/x] ⊣ ω·U

     Γ⁰ ⊢ t ⇒ T ⊣ U    whnf T = (q x : A) × B
     ──────────────────────────────────────── fst⁰, snd⁰  (erased positions)
     Γ⁰ ⊢ t.1 ⇒ A ⊣ U         Γ⁰ ⊢ t.2 ⇒ B[t.1/x] ⊣ U

     Γ ⊢ r qty ↦ ρ     Γ' ⊢ s ⇒ T ⊣ U₁     whnf T = (q x : A) × B   (p = value of q)
     (Γ' = Γ⁰ if ρ is the constant 0, else Γ)
     Γ, z :0 T ⊢ M type@_
     Γ, x :ρ·p A, y :ρ B ⊢ b ⇐ M[(x,y)/z] ⊣ (u_y :: u_x :: U₂)     u_y ≤ ρ    u_x ≤ ρ·p
     ──────────────────────────────────────── split                               Check.lean `infer`
     Γ ⊢ let r (x, y) := s as z. M; b ⇒ M[s/z] ⊣ ρ·U₁ + U₂
```

* Σ with `split` is Atkey's dependent tensor ⊗ [std: Atkey18]. η for pairs holds
  (§11.2).
* **Projections are [wiz], and available only on unrestricted pairs** (R1; Status.md,
  Q1/R1). Atkey's tensor has only the `let` eliminator. A projection keeps one component
  and drops the other, and the second component of a Σ has no quantity of its own that
  could say whether it may be dropped. So the rule does not look at the component types:
  outside erased positions `t.1` and `t.2` use `t` **ω times** (`projUsage`; a rig
  without an unrestricted quantity, `QRig.many? = none`, allows them only when `t` uses no
  local variable).
  * `t` may be any expression: `(act w).1` uses `w` ω times, so it is rejected when `w`
    is linear. (Before, a projection of an expression passed the expression's usage
    through, and the world `act` returns was dropped.)
  * "`ω·U` fits `Γ`" is checked at the projection, to give an error that says what to
    write (`cannot project p.1: a projection needs an unrestricted pair … take the pair
    apart with let 1 (x, y) := p`): every variable `x :p' A` with `U(x) ≠ 0` needs
    `ω·U(x) ≤ p'`. This is what leaving the binder of `x` would check anyway: usages only
    grow on the way out (`+`, scaling by a non-zero quantity, the join of branches), except
    under a scaling by a constant 0, and those positions are `Γ⁰`, where this rule does
    not apply.
  * A pair held at any other quantity is consumed by `split`, which binds both
    components: `let 1 (x, y) := p; …` for a linear pair. A `split` at ω
    (`let (x, y) := p`, the surface default) uses `p` ω times like a projection.
  * **Quantity variables.** For `p :π A × B` with `π` a quantity variable, `p.1` is
    rejected: `ω ≤ π` fails at `π = 1` (and at `π = 0`). `let π (x, y) := p; …` works
    at every `π`. Only the constant ω, or an erased position, admits a projection.
  * **Fields.** The first field's quantity `q` matters only for `fst`: an erased field
    (`¬ 1 ≤ p`) cannot be projected at runtime. `snd` has no side condition on `q`: an
    unrestricted pair's first field is held at `ω·p`, which may always go unused. (The
    earlier rules, `mustUse`/`mustUseType?` for `.1` and the `0 ≤ q` test for `.2`,
    inspected the dropped part's declared field quantities; the rule above subsumes them
    and they are gone, together with the evaluation of the pair they needed.)
  * **Structures** are right-nested Σ types ending in a marker tail (§R3 of the audit;
    `structTailName`), and `s.field` is a chain of projections. So a structure held at a
    quantity other than ω has no usable field access, and it has no destructuring form
    either (`match` does not split a Σ linearly, and a nested `let 1 (x, y)` leaves the
    marker tail, a linear variable of type `(0 fields✝ : …) → Unit`, with nothing to
    consume it). The elaborator's error says so. Linear data is a tuple, taken apart with
    `let 1 (x, y) := …`, or a one-constructor `inductive` with fields at 1, taken apart by
    `match` (`T.casesOn1`, §10.2). (Exempting the marker tail is unsound: §10.2a.)
  * **η for Σ** (§11.2) is part of conversion: it compares `vFst`/`vSnd` of *values* and
    never builds projection *terms* for the checker, so no usage is computed for an
    η-expansion. Types are checked in `Γ⁰` and their usage is discarded, so a type may
    mention `p.1` for a linear `p`.
  * **The elaborator** inserts projections in four places: field access `t.f`
    (`elabFields`), tuple patterns in `match` (two `let`s at ω of `p.1` and `p.2`),
    structure field projections `C.x` (functions of an ω `self`), and the payloads of
    constructors inside `ind`/`scase` methods (bound at ω). All of them are on ω
    variables, or are rejected for a linear scrutinee exactly as before (a tuple pattern
    used `p` twice). None of them elaborates a linear scrutinee to `split`: only
    `let q (x, y) := s` does. `do`/`do1` binds go through `bind`/`bind1`, which are
    library functions written with `let 1 (a, w') := x w` (`lib/IO.wiz`).
* `split`'s motive variable `z` has quantity 0 (`ctx.bind z []`).
* The component sorts `σ` are not checked for `split`'s scrutinee; they are checked where the
  Σ type is formed.
* **Positions at 0.** The `pair` rule's first part at a 0 field, `split`'s scrutinee at
  `ρ = 0` and `let`'s value at 0 (§6) are erased positions, like `app`'s argument to a 0
  binder. Before R1 only `app` did this; the usage was multiplied by 0 in all four, so the
  difference is only that a projection there is `fst⁰`/`snd⁰`. Erasure agrees: each of
  these positions compiles to `◾` and is never evaluated (`Erase.lean`: `pair`, `letE`,
  `split`, the application spine).

* **The eliminators use what they take apart ω times** (§9, §10; found by the
  linear-case design, probe `p05`). `ind`, `sfix` and `scase` hand the scrutinee's
  payload to the method as an ω variable (`ω xs`), `coit` and `scofix` hand the seed to
  the step function as an ω variable, and `Desc.elim` the description's parts. Charging
  the scrutinee once (`ω·U_m + U_x`, as before) let a method copy or ignore the content
  of a scrutinee held at 1: `ind (fun _ _ => Tok × Tok) (fun i xs ih => (xs.1, xs.1)) b`
  for `1 b : Box` was accepted. The rules now scale the scrutinee (seed) by ω:
  `ω·(U_m + U_x)`, and `U_m + ω·U_x` for `scase`, whose method runs once. This is the
  same statement as the projection rule: an eliminator that binds at ω needs an
  unrestricted value. `match` was never affected (the generated `casesOn`/`rec` take the
  scrutinee as an ω argument). A value of an inductive type held at 1 is taken apart by
  the case at quantity 1 (`scase_1`, K1, §10.2), which `match` reaches through the
  generated `T.casesOn1`.
* **Usability, and the follow-up.** After R1, linear data is a Σ tuple taken apart with
  `let 1 (x, y) := …`. What stopped working: reading the single field of a one-field
  structure held at 1 (`structure Coin where value : Nat`, `c.value`: it dropped only
  the marker tail, so it was sound; such a wrapper is now written as a definition,
  `def Coin : Type := Nat`), besides the unsound reads of one field among several.
  Follow-up (not in the kernel): a destructuring `let 1 (.mk a b) := s` for structures,
  compiled to nested splits, and tuple patterns in `match` compiled to `split`; both in
  `wiz-notes/linear-case-design.md`. The accepted follow-up is the linear-case plan (`wiz-notes/linear-case-design.md`): K2a (an unused variable may leave its binder when its type is `Unit`, so a linear `Unit` needs no consumer), re-encoding B of structures (the marker in a 0-quantity first component, so a nested `let 1` leaves no marker tail to consume), and a quantity on `scase` (`scase_π`: the scrutinee is used π times and its fields are bound at π·q), which gives structures a destructuring form and linear inductive values an eliminator. Landed (stage 4h): the quantity on `scase` (K1) and the unit eliminator `let () := u; b`; K2a was withdrawn (§10.2a), and re-encoding B is not done, so structures still have no linear destructuring form.

*Kernel.wiz* has no `split` (no `let (x, y)` in its term syntax). Its `fst`/`snd` rules
are the ones above (usage scaled by ω outside erased positions; no check at the
projection, so the error surfaces when the variable's binder is left), and its `let` and
`pair` rules use the same erased positions (`erasedIf`). Without `split`, **a pair held at
quantity 1 cannot be consumed inside Kernel.wiz's fragment** (§15). The same holds
for the self-hosted *language* (what `Frontend.wiz` elaborates): it has no
`let (x, y) := …`, its `Prod` is a structure whose `.fst`/`.snd` are ω functions, and its
`IO` is `World → Prod A World` at ω. So a linear pair cannot be consumed at all in the
self-hosted language; programs that need one are checked by the Lean kernel only.
`Backend.wiz` erases the value of a `letq .qz` (and of a 0 argument and a 0 field) as
`Erase.lean` does; the frontend does not produce `letq` today.

### 7.2 Unit, Empty, True, False

`Unit_l` and `Empty_l` exist at every level; `True = Unit_0`, `False = Empty_0`.

```
     ─────────────────────── unit    ───────────────────── tt (check only)   ──────────────────────── empty
     Γ ⊢ Unit_l ⇒ Sort l ⊣ 0         Γ ⊢ tt ⇐ Unit_l ⊣ 0                    Γ ⊢ Empty_l ⇒ Sort l ⊣ 0
                                                                                  Check.lean:425–426, 276

     Γ ⊢ M type@_      Γ⁰ ⊢ t ⇒ T     whnf T = Empty_l
     ──────────────────────────────────────── absurd                                Check.lean:427–433
     Γ ⊢ absurd M t ⇒ M ⊣ 0
```

η for Unit: all elements of `Unit_l` are definitionally equal (§11.2). `absurd` never
computes (`vAbsurd`, `Eval.lean:84`). Its usage is **0**: `t` is checked in erased mode
and its usage discarded [wiz; see §14, the docstring says `⊣ U`].

### 7.3 Enumerations

```
     ───────────────────────── enum     i < n
     Γ ⊢ Enum ls ⇒ Sort 1 ⊣ 0           ─────────────────────────── tag                     Check.lean:491–494
                                        Γ ⊢ tag ls i ⇒ Enum ls ⊣ 0      (n = |ls|)

     Γ ⊢ t ⇒ T ⊣ U    whnf T = Enum ls    |bs| = |ls|    Γ, z :0 Enum ls ⊢ M type@_
     Γ ⊢ bₖ ⇐ M[tag k/z] ⊣ Vₖ   (each k)      V = V₀ ⊔ … ⊔ Vₙ₋₁  (defined)
     ──────────────────────────────────────── ecase                                  Check.lean:495–510
     Γ ⊢ ecase t as z. M [b₀…] ⇒ M[t/z] ⊣ U + V

     ecase (tag k) as z. M [b…]  ⟶  bₖ                                              vEcase, Eval.lean:335
```

[std for finite types; the join of branch usages is wiz, §5.3]. **Labels are metadata**:
`Enum [a, b]` and `Enum [c, d]` are convertible (`Conv.lean:342`) and equal
(`Eval.lean:592`); only the number of tags matters. `ecase` on an empty enumeration has
no branches and usage `U`.

---

## 8. Observational equality

Stage 4c. This section follows Pujet and Tabareau's TTobs [PT22] and the earlier OTT
[AMS07] in outline. Wiz-specific parts are marked.

### 8.1 Typing

```
     Γ ⊢ A type@l    isNeverZero l    Γ ⊢ a ⇐ A    Γ ⊢ b ⇐ A
     ──────────────────────────────────────── eq                                    Check.lean:435–442
     Γ ⊢ a =_A b ⇒ Prop ⊣ 0

     Γ ⊢ A type@l    Γ ⊢ B type@l'    ⊢ l ≡ l'
     ──────────────────────────────────────── eqTy                                  Check.lean:443–447
     Γ ⊢ A ≡ B ⇒ Prop ⊣ 0

     Γ ⊢ A type@l    isNeverZero l    Γ ⊢ a ⇐ A                Γ ⊢ X type@_
     ───────────────────────────────────── refl                 ─────────────────────────── reflTy
     Γ ⊢ refl A a ⇒ (a =_A a) ⊣ 0                               Γ ⊢ reflTy X ⇒ (X ≡ X) ⊣ 0
                                                                       Check.lean:448–457

     Γ ⊢ A type@l   Γ ⊢ B type@l'   ⊢ l ≡ l'   Γ⁰ ⊢ e ⇐ (A ≡ B)   Γ ⊢ t ⇐ A ⊣ U
     ──────────────────────────────────────── cast                                  Check.lean:458–466
     Γ ⊢ cast A B e t ⇒ B ⊣ U

     (all premises in Γ⁰)  Γ⁰ ⊢ A type@l   isNeverZero l   Γ⁰ ⊢ a ⇐ A   Γ⁰ ⊢ b ⇐ A
     Γ⁰ ⊢ P ⇐ (b :0 A) → (_ :0 a =_A b) → Prop
     Γ⁰ ⊢ p ⇐ P a (refl A a)    Γ⁰ ⊢ e ⇐ (a =_A b)
     ──────────────────────────────────────── transp                                Check.lean:467–484
     Γ ⊢ transp A a P p b e ⇒ P b e ⊣ 0
```

* `a = b` is only formed at a type whose sort is **never** `Prop` (`isNeverZero`).
  Equality of proofs is not expressible, which is consistent with proof irrelevance.
* `transp` has the same premise (since the F9 fix; found by the second audit). Its rule
  builds the motive's type `(b :0 A) → (_ :0 a =_A b) → Prop` and the type `a =_A b` of `e`
  as values, without the `eq` rule, so with only `Γ ⊢ A type@_` it was accepted at a
  proposition (`transp True tt P p tt tt`), where those are equations the `eq` rule
  rejects. Harmless (an equation at a proposition computes like one at `Unit`, and proofs
  are irrelevant), but the type of a well-typed term was not a type.
* The written type `A` of `eq` and `refl` is not tied to `a`'s type by anything other than
  `a ⇐ A`.
* `cast` is the only operation whose *result* is relevant; `transp` (transport into a
  `Prop`-valued family) is a proof. Together they give J (`examples/equality.wiz`).
  [std: PT22]
* Proofs have no usage (`⊣ 0`) and **never compute**: `refl`, `reflTy` and `transp`
  evaluate to stuck neutral heads (`Eval.lean:157–161`). Only `cast` computes.

### 8.2 Computation of `a =_A b`

`vEq`, `Eval.lean:514–549`, by the weak head normal form of `A`:

| `A` | `a =_A b` reduces to | tag | line |
|---|---|---|---|
| `(q x : A₁) → B` | `(0 x : A₁) → a x =_{B x} b x` (funext) | [std: PT22] | 523–525 |
| a proposition (`propSort? A = true`) | `True` (**proof irrelevance**) | [wiz: Prop components] | `vEq` |
| `(q x : A₁) ×^⟨i,j⟩ B` | `(0 e : a.1 =_{A₁} b.1) × (cast (B a.1) (B b.1) ê a.2 =_{B b.1} b.2)`, where `ê = transp A₁ a.1 (λy _. B a.1 ≡ B y) (reflTy (B a.1)) b.1 e`; if `i ≡ 0` (`A₁` is a proposition), the first component is `True` and `ê = reflTy (B a.1)`; if `j ≡ 0` (`B` is a family of propositions), the second component is `True` | [std: PT22; wiz] | `vEq` |
| `Unit_l`, `Empty_l` | `True` | [std] | 533 |
| `Enum ls`, with `a = tag i`, `b = tag j` | `True` if `i = j`, else `False` | [wiz: finite types] | 534–536 |
| `μ D i`, with `a = con x`, `b = con y` | `x =_{⟦D⟧ (μ D) i} y`, **by the description** (`vEqPayload`, below) | [wiz: OTT for descriptions] | `vEqPayload` |
| `Sort l`, `l ≡ 0` | `(a → b) × (b → a)` (**propext**) | [std: PT22] | 540–543 |
| `Sort l`, `isNeverZero l` | `a ≡ b` (type equality, §8.3) | [std: PT22] | 544 |
| `ULift A` | `True` if `A` is a proposition; `down a =_A down b` if it is not; else stuck | [std; Q4] | §4.1 |
| `Desc_l I` | **by the constructors** (`vEqDesc`, §8.4b): `ret j = ret j' ⟶ j =_I j'`, `arg`/`rec`/`hrec` componentwise, different constructors `False` | [wiz: 4g] | `vEqDesc` |
| anything else (a neutral type, `ν`, `Sort u` with `u` possibly 0, a non-constructor element of `μ`/`Enum`) | stuck: the neutral `a =_A b` | | 545–546 |
| numerals `n`, `m` (any `A`) | `True` if `n = m`, else `False` | [impl] | 516 |

The first row and the Σ rule's proof case are Wiz's [nu-transp]: in PT22 the components of
a Σ are types, but a Wiz Σ may have a proof component (`(x : A) × P x`, `(0 h : P) × B`), and
the equation of its components must not be formed at a proposition (the `eq` rule rejects
it, as `transp` along a proposition, §8.1). Both are justified by conv-irr (§8.5):

* at a proposition `A`, `a ≡ b` already holds, so `a =_A b` is `True`: it is never `False`
  (two proofs, however written, are equal), so the rule gives no new inhabitant of `Empty`;
* if `A₁` is a proposition, `a.1 ≡ b.1`, so `B a.1 ≡ B b.1` and `reflTy (B a.1) : B a.1 ≡ B b.1`
  is well typed; `transp` along `A₁` would not be.

Without them the computed equation was ill typed (a normal form the kernel rejects), and the
kernel rejected well-typed programs that let-bound `h.2` for `h : p = q` at a subtype. The
tests are stable under substitution (a proposition stays one; `i ≡ 0` holds at every
instance). **Neutral propositions** (closed by mandatory sorts): the Σ rule reads whether a
component is a proposition off the Σ's component sorts `⟨i, j⟩`, not off the component's head
(`propSort?`), so it also sees a neutral proposition (`P q.1` for a variable `P : A → Prop`,
or a variable `P : Prop`): `(x : A) × P x` gives `True` as its second component's equation,
and `(0 k : P) × B` gives `True` and `ê = reflTy`. (Before, the equation was formed at the
proposition and the kernel rejected it; that was pinned in the 'observational equality' group
and in the property harness as NU-TRANSP-NEUTRAL.)

Equality of payloads by the description (`vEqPayload`), so that `succ m = succ n` is
`m = n` and not, through the Σ rule, an equation with a cast along the tags'
equation (which, without regularity, would be stuck at the field's type):

```
x = y  at ⟦ret j⟧ X i         ⟶  True                      (the payload is an index proof and ())
x = y  at ⟦arg q (Enum ls) E⟧ ⟶  x.1, y.1 both tags: equal ⟶ x.2 = y.2 at ⟦E tag⟧
       (or ULift (Enum ls): the tags are down x.1, down y.1, and E gets up tag)
                                                      different ⟶ the Σ rule (first component False)
                                 not both tags ⟶ the whole equation a =_μ b is stuck
x = y  at ⟦arg q S E⟧, S not an Enum  ⟶  the Σ rule
x = y  at ⟦rec q j E⟧          ⟶  (x.1 =_{X j} y.1) × (x.2 = y.2 at ⟦E⟧), or just x.1 = y.1 if E is ret
x = y  at ⟦hrec q H j E⟧       ⟶  (x.1 =_{(h:H) → X (j h)} y.1) × (x.2 = y.2 at ⟦E⟧), likewise
neutral D                      ⟶  stuck
```

Which rule applies depends only on `D` and on whether the tags are canonical, and the
alternative to computing is being stuck (whose quotation is the original equation), so
the result is stable under substitution. The `rec`/`hrec` pairs are non-dependent, since
`E` does not depend on a recursive field. Dropping the `ret` leaf's `True` (and the equal
tags' `True`) makes the nesting independent of how a number is written: `succ^k zero =
succ^k zero` computes to `True`, as the numerals `k = k` do, and `0 = .zero` (a numeral
against a constructor, seen through `vNatView`) gives the same `True`.

Equality at `ν` stays stuck (no bisimulation): a design decision (4d, [stages/04-data.md](stages/04-data.md)). All
binders generated by these rules have quantity 0, and the generated Π/Σ carry their
component sorts: `⟨0, 0⟩` for a Σ of two propositions, `⟨i, 0⟩` for the funext Π over the
domain `A₁ : Sort i` (read off the Π at hand, which is why the components must be written).

### 8.3 Computation of `A ≡ B` (type equality)

`vEqType`, `Eval.lean:563–597`. First the **proposition test** [wiz]:

```
propSort?(T) (Eval.lean `propSort?`, by the sorts written in T) =
  Π^⟨i,j⟩:   true if j ≡ 0, false if j is never 0, else unknown
  Σ^⟨i,j⟩:   true if i ≡ j ≡ 0, false if i or j is never 0, else unknown
  Unit_l, Empty_l, ULift.{k,l} A:   true if l ≡ 0, false if isNeverZero l, else unknown
  Sort, Qty, Enum, Desc, μ, ν, Size, Size<:   false
  a stuck eq / eqTy (empty spine):   true
  anything else (a neutral):   unknown
"unknown" now means only: depends on a level parameter (or the type is a neutral).
```

Then:

```
both true                         ⟶  (X → Y) × (Y → X)          propositions are equal when equivalent
either unknown                    ⟶  stuck
one true, one false               ⟶  False
both false, by shape:
  ((q x:A)→B) ≡ ((q' x:A')→B')    ⟶  False if q, q' are different constants (both closed: F6);
                                     stuck if either has a variable and they are not equivalent;
                                     else (0 e : A' ≡ A) × ((0 x : A') → B (cast A' A e x) ≡ B' x)
  ((q x:A)×B) ≡ ((q' x:A')×B')    ⟶  (same quantity test)  (0 e : A ≡ A') × ((0 x : A) → B x ≡ B' (cast A A' e x))
  Sort u ≡ Sort w, Unit_u ≡ Unit_w, Empty_u ≡ Empty_w
                                  ⟶  True if u ≡ w; False if both closed and different; else stuck
  Enum ls ≡ Enum ls'              ⟶  True if |ls| = |ls'|, else False
  Desc_l I ≡ Desc_l' I'          ⟶  I ≡ I' if l ≡ l', else stuck                          [wiz]
  ULift.{u} A ≡ ULift.{w} B      ⟶  A ≡ B if u ≡ w; False if both closed and different; else stuck   [Q4, §4.1]
  μ^s_l I D i ≡ μ^s'_l' I' D' i'  ⟶  (I, D, i) =_T (I', D', i'),  T = (J : Sort (l+1)) × Desc_l J × J
  (the same for ν)                    if l ≡ l' and s ≡ s' as sizes (sizeEq); else stuck        [wiz, 4g, §8.4b]
  two different canonical formers (Π, Σ, Sort, Unit, Empty, Enum, Desc, μ, ν, ULift)
                                  ⟶  False                        (no-confusion of type formers)
  otherwise                       ⟶  stuck
```

* **The quantity test** must be stable under substitution. `False` needs two *closed*
  quantities. A variable `q` and `1` are different polynomials, but `q := 1` makes them
  equal. Deciding `False` there proved `False` (Status.md, F6).
* The Π/Σ decomposition and "different formers ⇒ False" are TTobs's [std: PT22]. The
  Π case puts the domain equation backwards (`A' ≡ A`), as in CCobs ([PT23] Fig. 4, rule
  Eq-Π). TTobs has it forwards and casts along the inverse ([PT22] Fig. 4).
* **Propositions compared by equivalence, and the component sorts** are [wiz]. They exist
  because comparing propositions by shape proved `False` (Status.md, issue F1). A Π or Σ
  can't tell by its parts alone whether it is a proposition (a neutral part carries no
  type), so it carries its components' sorts `σ`, which the kernel checks when the type is
  formed (rules *pi*, *sigma*). They are mandatory: before, a Π/Σ without an annotation made
  type equality *stuck* (U5), so two convertible types could compute differently.
* **The Π/Σ decomposition is Cross** (decision Q5, the user's): it decomposes whatever the
  component sorts are, so the reduct can relate components in different sorts (`A' ≡ A` with
  `A : Sort i`, `A' : Sort i'`, `i ≢ i'`); such an equation then computes to `False` or stays
  stuck, as below. The Levelled variant (decompose only if `i ≡ i'` and `j ≡ j'`) is not
  implemented.
* **Quantities are part of a type's identity**: `(1 x : A) → B ≡ (ω x : A) → B` is
  `False` [wiz]. Conversion agrees (§11.3), except at propositions.
* `Size ≡ Size`, `Size< s ≡ Size< t`, `Qty ≡ Qty` are **stuck** in the Lean kernel
  (`Size`, `Size<` and `Qty` are not in `canonical`, `Eval.lean:572`). In `Kernel.wiz` they
  reduce to `False` (§15, and Status.md: this is a proof of `False` in the self-hosted
  kernel).
* Different universes: `eqTy` requires equal levels, but the Π/Σ decomposition can
  compare domains at different levels (e.g. `Nat ≡ True` from `(x : Nat) → Unit ≡
  (x : True) → Unit`). Then the proposition test answers `False`, and two non-propositional
  types at different levels are compared by shape (`Sort 0 ≡ Sort 1` is `False`).

### 8.4 Computation of `cast`

`vCast`, `Eval.lean:610–638`. With `A`, `B` in whnf:

```
propSort? A = propSort? B = true   ⟶  stuck (the cast is itself a proof, §8.6)                             [std: PT23, PLT25]
Π/Π, quantities equal, both not propositions, σ₁ ≡ σ₂
                                   ⟶  λx. cast (B₁ x̂) (B₂ x) (e.2 x) (t x̂),  x̂ = cast A₂ A₁ e.1 x  619–624 [std: PT22]
Π/Π or Σ/Σ, quantities not known equal ⟶  stuck
Π/Π or Σ/Σ, a sort not known (U5b)  ⟶  stuck: `propSort?` of either side is unknown (a level with
                                       parameters that may be 0), so the equation `e` proves is stuck
                                       (§8.3) and is no pair to project
Π^⟨i₁,j₁⟩/Π^⟨i₂,j₂⟩, Σ/Σ, unless i₁ ≡ i₂ and j₁ ≡ j₂ (D2)  ⟶  stuck: the reducts cast between the
                                       components, and `cast` is formed only within one sort. With
                                       the sorts written this is decided by the terms, and it is stable
                                       under level substitution (`≡` holds at every instance). (Closed
                                       by mandatory sorts; before, these rules computed across sorts and
                                       the normal form of an accepted term could be rejected; test "D2 …")
Σ/Σ, quantities equal, both not propositions, σ₁ ≡ σ₂
                                   ⟶  (c₁, cast (B₁ t.1) (B₂ c₁) (e.2 t.1) t.2),  c₁ = cast A₁ A₂ e.1 t.1   625–629 [std: PT22]
Sort u/Sort w, Empty_u/Empty_w     ⟶  t if u ≡ w, else stuck                                         630
Unit_u/Unit_w                      ⟶  tt if u ≡ w, else stuck                                        631
Enum/Enum, same number of tags     ⟶  t                                                             632
ULift.{k,u}/ULift.{k',u}, u never 0, k ≡ k' ⟶  up (cast A B e (down t))                          [Q4, §4.1, D2]
groundEqTy A B (equal, inert, ground) ⟶  t        (regularity at inert types: the evaluator's fast path
                                                    for InReg_conv, below)        CONJECTURE (argued) [wiz, D1, P1]
Desc_l I / Desc_l I'               ⟶  by the description (below)                                  [wiz, D1]
μ^s I D i / μ^s I' D' i', t = con x ⟶ con (cast (⟦D⟧ μ^s' i) (⟦D'⟧ μ^s' i') ê x)               [std: PT22, D1, 4g]
(a numeral at its own type: the inert-regularity line above, since the numeral type is ground)
ν^s I D i / ν^s I' D' i', t = cocon x ⟶ cocon (cast (⟦D⟧ ν^s' i) (⟦D'⟧ ν^s' i') ê x)           [wiz, D1, 4g]
otherwise                          ⟶  stuck
```

and `out (cast (ν^s D i) (ν^s D' i') e t) ⟶ cast (⟦D⟧ ν^s' i) (⟦D'⟧ ν^s' i') ê (out t)`
(an unfolding is cast as it is observed). The μ/ν rules apply to **any** two μ (ν) types
with equivalent levels and sizes equal by their heads (`sizeEqTrue`: `∞ = ∞`,
`↑s = ↑s'` when `s = s'`, a size variable equals itself); `s = ↑s'` or `s = s' = ∞`.
Since 4g there is no syntactic test (`sameFamily?` is gone): `e : μ I D i ≡ μ I' D' i'`
is a proof of `(I, D, i) =_T (I', D', i')` (§8.3), and the payload equation is one `transp`
along it:

```
ê := transp T (I, D, i) (λ t _. ⟦D⟧ (λj. μ^s' I D j) i ≡ ⟦t.2.1⟧ (λj. μ^s' t.1 t.2.1 j) t.2.2)
       (reflTy (⟦D⟧ (λj. μ^s' I D j) i)) (I', D', i') e
     :  ⟦D⟧ (λ j. μ^s' I D j) i ≡ ⟦D'⟧ (λ j. μ^s' I' D' j) i'
```

At `t = (I, D, i)` the motive is reflexive, so `ê` is well typed (the kernel quotes it
into terms it checks again, so this matters). Descriptions are cast along `e : I ≡ I'` (`Desc_l I ≡ Desc_l I'`
computes to `I ≡ I'`):

```
cast (ret i)       ⟶  ret (cast I I' e i)
cast (arg q S E)   ⟶  arg q S (λ s. cast (Desc I) (Desc I') e (E s))
cast (rec q j E)   ⟶  rec q (cast I I' e j) (cast … e E)
cast (hrec q H j E) ⟶ hrec q H (λ h. cast I I' e (j h)) (cast … e E)
```

Until P2 (§8.6) the first line was "`e.1 t`: apply the equivalence" [wiz]. That rule
evaluated the proof `e`. `wiz check --eager-proofs` (and `kernelLazyProofs := .false` in
`Kernel.wiz`) restores it while the transition lasts.

**No regularity** (D1, decision (a)). Until D1, the last line was "`t` if the two types
quote equal, whatever `e` is". With an impredicative `Prop` and definitionally irrelevant
equality that is exactly Abel and Coquand's setting [AC20], and a closed 18-line program
made both kernels loop (Status.md, D1). Regularity is now off in both kernels
(`Globals.regularity := .off`; `kernelRegularity` in `Kernel.wiz`); `wiz check
--regularity full` restores it for experiments. In its place, `cast` computes on data:

* **Why the μ rule is sound (subject reduction).** `x : ⟦D⟧ X i` (rule *con*, `X` at
  the predecessor size), and `ê : ⟦D⟧ X i ≡ ⟦D'⟧ X' i'` is well typed (its motive is
  reflexive at `(I, D, i)` and `e` proves the code equation), so the inner cast has type
  `⟦D'⟧ X' i'` and `con` of it has type `μ^s I' D' i'`. The rule uses nothing but `e`, the
  levels and the sizes' heads, so it is stable under substitution: no syntactic test
  decides whether it fires (§8.4b). (Until 4g the rule fired only when `I`, `D`, the level
  and the size agreed syntactically and was stuck otherwise; a theory review showed that
  syntactic inequality is not stable: two stuck casts at convertible but syntactically
  different families could stop being convertible after a substitution made one fire.)
  The type equation is **stronger** than the one of CICobs [PLT25 §4]: there, an equation
  between two instances of an inductive type gives only the equations between the *types
  of the constructor arguments* (for a forded family, `(j = i) ≡ (j = i')` at each
  constructor), not `i = i'`, because CIC lets an inductive type live in a universe
  smaller than its indices, where injectivity gives Russell's paradox [PLT25 §2.3]. Wiz's
  rule is injective in the index and, since 4g, in the description. That holds in a
  setoid/inductive-recursive model where `μ I D i` is a code (§8.4b), and it relies on the
  level rules of §9.1 and §9.3: the index type and every field type are in the family's
  own universe (`I, S : Sort (l+1)`).
* **Why it blocks the D1 loop.** The rule casts *every* field, along the components of
  `ê`. A `Prop` field is cast between propositions, which is a stuck proof (§8.6; before
  P2 it applied the equivalence, `ê`'s component `.1`, also a stuck proof). Abel–Coquand's
  box therefore yields a stuck cast of `δ`, not `δ`, and `Ω` has a normal form. A field at a neutral type (`cast A A e a` for a variable `A`)
  is stuck, as in TTobs.
* **Regularity at inert types (CONJECTURE).** `inertTy` (`Eval.lean`; `inertTy` in
  `Kernel.wiz`) is a syntactic, conservative test: `Enum`, `Unit_l` with `l` never 0,
  `Σ` whose sort (`max i j`, written) is never zero, of inert types, and `μ` types whose index type
  is inert and whose description, walked with its tags (and with a fresh variable for a
  non-enum field), has only `ret`, `rec` and `arg` at inert types (no `hrec`, no `Prop`
  field, no function, no neutral type, so no variable parameter: `List A` is not inert,
  `List Nat` is). At an inert `A`, `cast A A e t ⟶ t`. The argument that normalisation
  is preserved:
  - on a **neutral** `t`, the rule rewrites one neutral (`cast A A e t`) to another
    (`t`); neither is a redex for any eliminator of an inert type (`ind`, `ecase`,
    projections, `vNatView`), so no reduction is enabled that was blocked before;
  - on a **canonical** `t`, the structural rule computes a value equal to `t` except for
    the index proofs at its `ret` leaves (which become `ê`-components applied to them):
    convertible to `t` by proof irrelevance, and since an inert value contains no λ (its
    proofs are proofs of equations at inert index types, which compute to `True`, `False`
    and Σs of them, with no Π), no later reduction can tell the two apart;
  - after a substitution, a neutral `t` may become canonical; by the two cases the result
    is the same up to proof irrelevance, so reduction stays confluent up to conversion.
  Abel–Coquand's loop needs a cast that returns a *proof* (or a λ) unchanged; inert types
  hold neither. Conversion stays decidable as before: the new rules are evaluation rules
  that terminate (the inertness walk is bounded by the nesting depth 8 and by the finite
  enumerations; the payload cast follows the finite constructor value), and conversion
  only removes a stuck cast whose two types it finds convertible (`unCast`, InReg_conv
  below). It is a conjecture for Wiz. A published system has
  the rule at *every* type, with a proof that conversion stays decidable, but for an
  algorithm that never reduces proofs and for a fragment without general inductive types
  (CICobs [PLT25]; see "Related work" below).

  **A more careful argument** (`wiz-notes/inert-regularity.md`) corrects the
  one above in three places:
  1. The first bullet is too strong. Removing a stuck cast can make two types syntactically
     equal, and that *does* enable rules with syntactic side conditions (`sameFamily?`,
     the μ case of `vEqType`, before 4g removed them). Those are rules of the system without regularity, so
     termination is not at risk, but "no new redex" does not prove it.
  2. Inert values do contain proofs (the index equations). Convertible proofs can *reduce*
     differently, and the evaluator reduced proofs when this was argued (since P2, §8.6,
     only those bound by `let` or passed as arguments), so "no reduction can tell them
     apart" is not the reason. The reason is that inert types are **rigid**: their reducibility
     candidate does not depend on the interpretation of `Prop` or of type variables. At
     such a type, a rule that returns its argument unchanged keeps Girard's candidates
     argument valid, provided environments must agree at inert types, and that
     restriction is not circular because inert types mention no `Prop`. Abel–Coquand's
     construction needs a non-rigid type: one whose candidate is an impredicative
     intersection (`⊤ → ⊤`), or depends on a `Prop` variable (the box).
  3. The side condition was syntactic (`sameVal`), so algorithmic conversion was not a
     congruence for the rule (now fixed by ground equality, below: P1). For example, `cast (Fin (f p)) (Fin (f q)) e k` stays stuck
     for a variable `k`, although `Fin (f p) ≡ Fin (f q)` by irrelevance and the reflexive
     cast reduces to `k`. So conversion is not stable under substitution (Status.md, D1).
     That is incompleteness, not unsoundness. The fix is to decide the side condition with
     conversion.

  The note sketches three arguments:
  * consistency: the rule holds wherever `μ` is an initial algebra and `Prop` is
    proof-irrelevant;
  * normalisation of relevant terms: one trivial new case in a Pujet–Tabareau-style
    logical relation;
  * normalisation of proofs, which the evaluator needs because it reduces them: the
    candidates argument above.

  All three are **relative to the same property of the system without regularity**, which
  is itself unproved for Wiz. No counterexample was found. The note lists what one would
  need.
* **Related work: cast on reflexivity in CICobs** (`wiz-notes/plt-vs-inert.md`).
  Pujet, Leray and Tabareau's CICobs [PLT25] has the conversion rule *Cast-Refl*:
  `cast A B e t ≡ t` whenever `Γ ⊢ A ≡ B`, for any proof `e` and **any** type `A`, next to
  an impredicative proof-irrelevant sort. So regularity at inert types, read with a
  judgmental side condition, is a special case of a published rule, and is not new.
  - *What they prove* (Agda): weak-head normalisation of proof-relevant terms and
    decidability of conversion ([PLT25] Theorem 5.6), for a fragment with Π, ℕ, ⊥, the
    impredicative sort and two universe levels. General inductive types are covered by
    their rules and by a set model (consistency, Theorem 6.5), not by the decidability
    proof.
  - *How.* Cast-Refl is not a reduction rule. On a canonical argument the structural
    rules compute. A stuck cast is removed by the conversion checker when it compares
    two neutrals, if the cast's two types are convertible (as η is decided). And **proofs
    are never reduced**: there is no weak-head normal form for a proof, so
    Abel–Coquand's term, which exists in CICobs, is never run. This answers open
    problem (2) of [AC20].
  - *What this means here.* The restriction to inert types was needed in Wiz because the
    evaluator reduced proofs. Since P2 (§8.6) it no longer runs the proofs in `cast` and
    `transp`, and `--regularity full` no longer makes the Lean kernel loop on
    Abel–Coquand's program; proofs bound by `let` or passed as arguments are still
    evaluated, so the restriction stays for now. The side condition they use is
    conversion, not syntactic equality (Status.md, D1, on the incompleteness of
    `sameVal`). Their indexed families are elaborated to parametrised ones with an
    equation in each constructor (Fordism), which is the encoding of §9.2; their
    equality of two instances of an inductive type is deliberately *not* injective in
    parameters or indices, because CIC allows an inductive type in a universe smaller
    than its indices. Wiz's μ equation (the equation of the codes `(I, D, i)`, §8.4b) is
    injective in the index and the description, and is kept from
    Russell's paradox by the level rules of §9.1 and §9.3 (`I, S : Sort (l+1)`).
  - *Not covered by their proofs*: descriptions as first-class codes, `μ`/`ν` over them,
    sizes, quantities, `ULift`, an equality type that computes together with Cast-Refl,
    and any evaluator that reduces proofs (Wiz's still does, for `let`-bound and
    argument proofs, §8.6).
* **Cost.** Casting a constructor of a non-inert type walks the whole value (each field
  is cast). At inert types the cast is the identity.
* **The rule is InReg_conv** (decision P1; `wiz-notes/conv-regularity.md`,
  `p1-stable.md`, `plt-vs-inert.md`):

  ```
  A inert     Γ ⊢ A ≡ B     Γ ⊢ e : A ≡ B     Γ ⊢ t : A
  ───────────────────────────────────────────────────────  InReg_conv
  Γ ⊢ cast A B e t ≡ t : B
  ```

  It is [PLT25]'s Cast-Refl restricted to inert `A`, and like theirs it is a rule of
  **conversion**, not a reduction: the evaluator never calls conversion.
  * *In the conversion checker* (`unCast` in `Conv.lean`, applied in `conv` and in
    `convTy`; `stripCast` in `Kernel.wiz`, applied where neutrals are compared, with a
    typed re-entry). A neutral `cast A B e t · sp` (any eliminations `sp`) with `A` or
    `B` inert and `A ≡ B` by `convTy` is replaced by `t · sp`, on either side, before
    the comparison goes on. A cast on a canonical value takes a structural rule of
    `vCast` instead; where that rule is stuck (a size variable) the cast is removed here
    like any other.
  * *"`A` or `B` inert"*: `inertTy` reads a `Σ`'s component sorts. They are mandatory, and
    conversion compares them (§11.3), so two convertible types are both inert or both not.
    (While sorts were optional, of two convertible types one could be inert and the other
    not, and conversion was not transitive at such types: `cast A A' e t ≡ t` could fail for
    two unannotated types where both held through an annotated third. Mandatory sorts
    closed this.)
  * *Termination.* The side condition compares two components of the neutral, as the
    congruence rule for two casts already does; each step removes one cast; and
    `inertTy` is a bounded walk that instantiates binders with reserved atoms (never
    with variables a context could give a type to). The evaluation of `t · sp` for a
    canonical `t` is the evaluation of a term that is well typed by the rule itself.
  * *Strategy.* Strip whenever the rule applies, else congruence; no backtracking
    ([PLT25] backtracks between congruence and the two refl rules). Argued complete
    relative to a transitive `convTy`, not proved.
  * `--inert ground` (`kernelInertConv := .false`) turns the conversion rule off and
    leaves the fast path alone.
* **The evaluator's fast path is ground equality** (`groundEqTy` in both kernels). A
  rule of evaluation with a side condition must give the same answer for convertible
  inputs (S1), and an answer of "fires" must survive substitution (S2). Otherwise one
  side of a conversion reduces and the other is stuck. Syntactic equality fails S1
  (proof arguments inside an index, `Fin (f p)` against `Fin (f q)`; a glued name
  against its unfolding), and it is gone from both kernels.
  `groundEqTy A B` holds for two inert types that are equal and have no free variable in
  a relevant position:
  * types and descriptions are compared part by part (an `arg` at a non-tag field is
    compared under an atom, a variable bound by the comparison);
  * values are compared by their inert type: tags, numerals and constructors; `Unit` and
    propositions skipped; `Σ` by projections;
  * a neutral equals only the same atom (atoms have a reserved head, so they can't
    collide with a variable of the context).
  At an inert type, convertible values have the same canonical skeleton and neutrals in
  the same places, so S1 holds. A ground type has nothing to substitute, so S2 holds.
  Whenever it fires, `A ≡ B`, so InReg_conv gives the same equation: it decides a
  fragment of the rule without conversion. What it alone leaves stuck (a neutral value
  at an inert type with an open index: `cast (Fin n) (Fin n) e k` for variables `n`,
  `k`) the conversion checker removes.
* **`--regularity full`** (an experiment; `kernelRegularity := .true`) is the same rule
  at *every* type, [PLT25]'s Cast-Refl, also in conversion only. The modes `nonprop`
  and `refl`, which fired in the evaluator by syntactic equality (and, for `refl`, by
  inspecting a proof), are gone.
* **Not widened.** [PLT25]'s decidability proof covers Π, ℕ, ⊥, the impredicative `Prop`
  and ∃. What regularity at `Desc l I`, or at all types, would need is in
  `conv-regularity.md` §8.

### 8.4a Propositional regularity: the `castRefl` axiom

The Prelude declares

```
axiom castRefl.{u} {0 A : Type u} (0 e : A = A) (0 a : A) : (cast e a : A) = a
```

It is an **axiom**: a proof, so it is a stuck neutral and never computes (`#reduce`
leaves `castRefl e a` alone), and `#print axioms` lists it for any declaration that uses it.
It is the propositional form of regularity that §8.4 removed from conversion, and it is a
primitive of TTobs and CCobs (`castrefl`, rule Cast-Refl in Fig. 2 of [PT22] and of
[PT23]). Proofs use it to
get rid of a stuck cast at a type variable: `Vec.map f (cons x xs)` is
`cons (cast B B _ (f x)) …`, and `Vec.map_cons` (`lib/Vec.wiz`) proves it equal to
`cons (f x) (Vec.map f xs)` by one `castRefl` at `Vec B (n+1)`. The cast in its type
computes to the same stuck casts as the definition, up to the proofs inside them, which
conversion ignores.

* **Consistency** [std: setoid model]. In the setoid/observational model, `cast A A e` is
  the identity up to the setoid equality of `A`, for any proof `e : A ≡ A`. So `castRefl`
  holds there, and it is consistent with the rest of the theory. A propositional equation
  can't break normalisation: it is a proof, irrelevant, and never reduces. The
  Abel–Coquand loop needs the *definitional* rule.
* **Canonicity.** As with any axiom, closed proofs mentioning it are not canonical, which
  is harmless because proofs are irrelevant and erased.

### 8.4b Equality of descriptions (4g)

Decision (2026-11-10): the kernel computes equality between *different* descriptions, so
that `List A = List B` computes down to `A = B`, and `UIntN 8 = UIntN 16` is refutable.
Before, `μ ≡ μ` computed only for one family (`sameFamily?`, syntactic) and stayed stuck
otherwise. `vEqDesc`, `vEqType`, `famPayloadEq?` in `Eval.lean`; `vEqDesc`, `famEqTy`,
`famPayload` in `Kernel.wiz`.

**Rules.** Equality *at* `Desc_l I`, by the two heads:

```
ret j          = ret j'            ⟶  j =_I j'
arg q S E      = arg q' S' E'      ⟶  (0 e : S ≡ S') × ((0 s : S) → E s =_{Desc I} E' (cast S S' e s))
rec q j E      = rec q' j' E'      ⟶  (0 _ : j =_I j') × (E =_{Desc I} E')
hrec q H j E   = hrec q' H' j' E'  ⟶  (0 _ : (0 e : H ≡ H') × ((0 h : H) → j h =_I j' (cast H H' e h))) × (E = E')
q, q' two closed (constant) quantities that differ ⟶ False (`qtyApart`);  otherwise (a variable) ⟶ stuck
two different constructors         ⟶  False
a neutral on either side           ⟶  stuck
```

Equality *of* `μ`/`ν` types (§8.3), for any two families, is equality of their codes:

```
μ^s_l I D i ≡ μ^s'_l' I' D' i'  ⟶  (I, D, i) =_T (I', D', i'),   T := (J : Sort (l+1)) × (D : Desc_l J) × J
     if l ≡ l' and s ≡ s' as sizes (`sizeEq`: any ↑ᵏ∞ is ∞; ↑ᵏx = ↑ᵏx); else stuck
```

which the Σ rule (§8.2) computes to

```
(0 e : I ≡ I') × ((0 e' : cast (Desc I) (Desc I') ê₁ D = D') × (cast I' I' ê₂ (cast I I' ê₃ i) = i'))
```

(the `ê`s are `transp`s of `e`, `e'`). The outer cast at `I'` is the identity when `I'`
is inert, but only through regularity at inert types (§8.4), whose side condition is
syntactic (`sameVal`). So the *computed form* of a μ equation inherits that rule's
non-congruence (an index type written in two convertible but syntactically different
ways can leave the cast stuck in one case and not in the other). The decomposition itself
is head-directed.
and `cast` between them computes constructor by constructor (§8.4), generalising D1's
one-family rule. The tail of each Σ is a closure: `D = D'` computes only when it is looked
at, so a big description costs nothing until a proof is projected.

**No shortcut, nothing simplified (stability).** The shape of every result is decided by
the heads of the two sides (and literal quantities), never by syntactic equality or by
what a component computes to. In particular:

* `μ D i ≡ μ D i'` is **no longer** `i = i'`. It is the general form, whose components
  are `I ≡ I`, `cast _ D = D` and `cast _ i = i'`. Keeping `i = i'` for one family and
  the general form for two would not be stable: a substitution can make `List A` and
  `List B` one family (`B := A`), and the general form's instance `(0 e : A ≡ A) × …` is
  not convertible to `i = i'` without regularity. Then a proof `e : List A ≡ List B` that
  was projected (`e.1`) would be ill-typed after the substitution. For the same reason a
  `True` component is not dropped: a stuck component (`A ≡ B`) may become `True` after a
  substitution, and `(0 e : True) × P` is not convertible to `P`. (Theory review,
  2026-11-10: a rule that fires on syntactic equality and is stuck otherwise also breaks
  the congruence of conversion: two convertible but syntactically different stuck terms
  can stop being convertible after a substitution makes one of them fire.)
* The sizes are compared as conversion compares them (`sizeEqTrue`, the normal form of
  `sizeEq` in `Conv.lean`): any `↑ᵏ ∞` is `∞`, and `↑ᵏ x = ↑ᵐ y` when `k = m` and `x`, `y`
  are the same variable. So the gate is invariant under conversion of the sizes.
  Otherwise (`∞` against `↑s`, two different variables) the equation is stuck.
* Tag fields are not special: `arg (Enum ls) E = arg (Enum ls') E'` is the general rule,
  `(0 e : Enum ls ≡ Enum ls') × ((0 t : Enum ls) → E t = E' (cast … t))`, and the cast at
  `Enum` is the identity. Applying the Π to a tag computes that constructor's equation.
  (Expanding the Π into a product over the tags would depend on the field type being a
  literal `Enum`, which a substitution can create.)
* Nothing in these rules, or in regularity at inert types (§8.4: ground equality in the
  evaluator, conversion in the checker), is decided by syntactic equality any more.

**What it gives.** For `inductive L (A : Type) | nil | cons (x : A) (xs : L A)`
(`I = Unit`, `D = arg ω (Enum [nil, cons]) E`), `e : L A ≡ L B` has

```
e.1                 : Unit ≡ Unit                                  (True)
e.2.1               : cast e.1 D = D'
e.2.1.2 'cons       : E 'cons = E' 'cons          (after the cast at Enum and at Desc compute)
(e.2.1.2 'cons).1   : A ≡ B
```

so `List Nat ≡ List Bool` is refuted through `Nat ≡ Bool` (by their descriptions: at the
tag `succ`, `rec` against `ret` is `False`). For `UIntN w` the width is in the index type
(phantom tails, README 22e), so `e.1 : I₈ ≡ I₁₆` already refutes `UIntN 8 ≡ UIntN 16`.
A cast between `L A` and `L B` along `e` computes to the list of the casts of its elements
(`cast A B _ x`, stuck at type variables as always).

**User-facing change.** A proof of `i = i'` no longer inhabits `μ D i ≡ μ D i'` directly:
`Vec A n = Vec A m` is a Σ now. Build such proofs by congruence (`congrArg (Vec A) h`, or
`transp` with `reflTy`, which is what the elaborator does for index equations and
pattern matching). `refl (Vec A n)` proves `Vec A n = Vec A n`, and so does `rfl`. The
computed equation has a part over the constructor tags, `(0 t : Enum ls) → cast e (E t) =
E t`, which is stuck under the binder (`E t` is a stuck `ecase t`) and computes at each
tag. The elaborator's `rfl` (`rflProof`, `Elab/Term.lean`) therefore proves a Π over a tag
type by a case split, `λ t. transp Unit () (λ _ _. G t) (ecase t [p₀, …]) () ()`: the
`transp` along `() = ()` is there because the binder has quantity 0 and its premises are
checked erased (§8.1). This is an ordinary kernel-checked term; the kernel rules are not
involved, and are deliberately not specialised to tag fields (above).
**The payload equation is not shape-stable (known, pre-4g; kernel-lint, 2026-11-10).**
The rule for `con x = con y` (`vEqPayload`, §8.2) is *not* head-directed in the sense used
above. At an `arg` field whose type `S` is neutral it gives the Σ rule, `(0 e : x.1 = y.1)
× (cast … x.2 = y.2)`; once `S` is instantiated by an `Enum` and the two tags are equal it
gives the rest's equation alone. So `Box.mk x = Box.mk y` at a variable `A` has one shape
and its instance at `A := Enum [a, b]` another, and the two are not convertible. A proof
term checked at the first shape (`h.1`) can therefore meet a value of the second.

* *Consequence.* None for consistency: both shapes are equivalent propositions, the
  mismatch is confined to proofs, and with lazy proofs (the default, §12) proofs are never
  run. With `--eager-proofs`, evaluating such an `h.1` reaches `vFst ()`: a failure of
  subject reduction for proof terms, i.e. a crash, not a proof of `False`.
* *Why the code equation refuses the same shortcut but this rule keeps it.* Both uniform
  alternatives cost what the rule exists for. The Σ rule everywhere makes `succ m = succ n`
  (and every `cons x xs = cons y ys`) an equation with a cast along the tags' equation;
  that cast is the identity only at ground inert payloads (§8.4), so at `List A` it leaves
  `cast A A _ x = y`, usable only through `castRefl`. Making a neutral `S` stuck instead
  gives up injectivity of constructors by computation at every polymorphic type.
* *Decision.* Not changed in 4g. The uniform Σ rule becomes right once a cast along a
  reflexive equation is the identity up to conversion (regularity decided by conversion,
  the direction chosen for later); until then the instability is recorded here and is
  unobservable under the default. (A cheaper partial fix, should eager proofs matter:
  make `vFst`/`vSnd` total on proofs of `True`.)

**Casts need their target type.** `cast e t` with no expected type is elaborated by
reading `X = Y` off the type of `e`, which works only while that equation is stuck. An
equation between two data types now always computes (to the equation of the codes), so
an un-ascribed cast between them is rejected ("its proof's type is an equation that has
computed … write `(cast e t : T)`"); write the ascription, or use the cast where its type
is expected. Before 4g this already held for two instances of one family (`μ D i = μ D i'`
computed to `i = i'`) and for `Π`/`Σ` types; what is new is two *different* descriptions
(`Box T2 = Box A`), whose equation used to be stuck. Nothing in `lib/`, `examples/` or
`selfhost/` has such a cast; the Abel–Coquand test programs did, and are ascribed now.

**Expected limit of `rfl`** (not observed in `lib/` or the tests). At a non-tag field the
equation is `(0 s : S) → cast e (E s) = E (cast S S ê s)`. When `S` is a type *variable*,
`cast S S ê s` is stuck (no regularity), so if a later index of the type depends on that
field (`E s` mentions `s` in a `ret`/`rec` index) the two sides differ by a stuck cast and
`rfl` cannot close the goal: that needs `castRefl` (§8.4a). `refl T` still proves `T = T`
there, since it is `reflTy T`, whose type is the same computed equation.

**Soundness: the setoid model.** We interpret the theory in the setoid (observational)
model of TTobs/CCobs [PT22, PT23], extended as follows. This is an argument, not a
proof; the obligations are recorded in Status.md ("Description equality", 4g).

1. *Codes.* Each `Type l` is an inductive-recursive universe `U_l` of codes with
   decoding `El`, as in [PT22]. Descriptions over an index code are a *nested* inductive
   `Desc(U_l, I)` with constructors `ret (i : El I)`, `arg (q) (S : U_l) (E : El S →
   Desc)`, `rec (q) (j : El I) (E : Desc)`, `hrec (q) (H : U_l) (j : El H → El I) (E :
   Desc)`, and `U_l` gets a code `μ (I : U_l) (D : Desc(U_l, I)) (i : El I)` (likewise
   `ν`). `Desc` is positive in `U_l`; it uses `El` in domains (as Π-codes do) and as a
   field type (`ret`, `rec`; as Σ-codes do). This is **not plain IR**: `El (μ I D i)` is
   itself an inductive family, the initial algebra of `⟦D⟧`, defined inside the recursive
   definition of `El`: an inductive definition nested in an IR decoding. That exists in a
   classical set-theoretic metatheory (well-founded trees), and it is what generic
   universe constructions provide (Gratzer 2022, *An inductive-recursive universe generic
   for small families*, used by Pujet's CIC^obs model; unverified detail). Field types are
   *exactly* in `Sort (l+1)` (§9.1), so every field is a code of `U_l`.
2. *Equality of codes* is the structural relation, defined by recursion on both codes:
   for μ it is the relation on `(I, D, i)` above, and on descriptions it is the table
   above (heterogeneous through `cast`, as for Π-codes). Different code constructors are
   unrelated (`False`). Quantities are part of a code, so different quantities are
   unrelated, as for Π (§8.3). This relation is what `vEqType`/`vEqDesc` compute.
3. *Cast* between `El (μ I D i)` and `El (μ I' D' i')` along a proof of the relation is
   defined by recursion on the (well-founded) element, field by field, along the
   components; this is what `vCastData` computes, with the payload equation obtained by
   one `transp` along the code equation.
4. *Propositions inside codes.* A field type is never a proposition (it is in `Sort
   (l+1)`), and a proof field is a lifted proposition `ULift P`, whose code equality is
   `P ↔ Q` (`ULift P ≡ ULift Q ⟶ P ≡ Q`, both propositions). So the A0 issue (comparing
   propositions by shape) does not arise: codes see propositions only up to equivalence,
   which is what the model's `Prop` (proof-irrelevant, with propext) identifies.

**Large-into-small injectivity (Hur, D4).** The rule makes `μ` injective in its
description: from `μ D i ≡ μ D' i'` one gets `D = D'` with `D : Desc_l I : Type (l+1)` and
`μ D i : Type l`. Hur's paradox needs an injection of `Type l → Type l` (or `Type l →
Prop`) into `Type l`. Here:

* the shape is the same as Π-injectivity, which TTobs already has (`(x : A) → B ≡ (x :
  A') → B'` gives `B x ≡ B' x`, an injection of `A → Type l` into `Type l`), and the code
  model above validates both, because `Desc(U_l, I)` only mentions codes of `U_l`, never
  families over `U_l` itself;
* a description can't quantify over `Type l`: a field type must be in exactly `Sort
  (l+1)`, and `Type l : Sort (l+2)`. So the encoding `D_F := arg (Type l) (λ X. arg (F X) …)`
  of `F : Type l → Prop` is rejected at level `l`; at level `l+1` it is accepted and
  `μ D_F : Type (l+1)`, which is not a paradox (the adversarial test in
  `Tests/Elab.lean`, group `desceq`, checks both);
* **the `l = 0` case with `Prop`.** `Prop : Sort 1`, so `Prop` *is* a valid field type of
  a `Desc.{0}`, and `D_F := arg Prop (λ P. arg (ULift (F P)) (λ _. ret ()))` gives an
  injection `(Prop → Prop) ↪ Type` (and, with `F : Prop → Type`, `(Prop → Type) ↪ Type`
  up to the field level). That is the shape of CCobs's Π-injectivity over a `Prop`
  domain, which has a model [PT23]: classically `Prop ≅ 2`, so a tagged pairing realises
  it. It is not Hur's `(Type → Type) ↪ Type`. (`hrec` with `H := Prop` is the same.)

**Termination, D1.** The new rules are evaluation rules: each step looks at two heads,
and the rests are closures, so evaluating an equation terminates when the descriptions'
evaluation does. A cast walks the constructor value as before. The Abel–Coquand programs
still check: the box's cast still casts its proof field along an equivalence (now a
component of `ê` built from the *user's* proof of the type equation when the two box
descriptions differ; with `tautext` that equivalence is `λ _. a`, and `Ω` normalises).
Tests: the D1 group, plus the box written with two different (equal) descriptions.

### 8.5 Proof irrelevance

At a type that is a proposition, any two elements are convertible (§11.2):

```
     Γ ⊢ A ⇒ Sort 0      (as computed by typeSort?, Conv.lean:213)
     ──────────────────────────────────────── conv-irr      [std: PT22; Gilbert et al. (unverified)]   Conv.lean:263
     Γ ⊢ a ≡ b : A
```

There are **no inductive propositions** (`μ` always lives in `Sort (l+1)`, §9), so there
is no large elimination out of `Prop` except through `absurd` (from `False`) and `split`
on a Σ of propositions (whose components are propositions too: subsingleton elimination).

### 8.6 Proofs are never evaluated (P2)

The evaluator does not run proofs. This is the design of TTobs, CCobs and CICobs
[PT22, PT23, PLT25]: there is no reduction relation on terms of a proposition, and
conversion never compares two proofs. It is `Globals.lazyProofs` in the Lean kernel and
`kernelLazyProofs` in `Kernel.wiz`, both on by default.

```
eval (cast A B e t)        e is suspended:  neutral (prf ⟨env, e⟩ : A ≡ B)
eval (transp A a P p b e)  p and e are suspended
cast A B e t, A and B propositions   ⟶  stuck                       (the cast is a proof)
let q (x, y) := p as z. M; u,  p a proof   ⟶  u[p.1/x, p.2/y]        (η for Σ; Lean kernel only: Kernel.wiz has no split)
conv at a proposition       true, before either side is unfolded
```

* **A suspended proof** is a neutral head (`Head.prf`, `hprf`) holding the term and its
  environment. It has no type of its own (§8.6a). Projections and applications of it grow
  its spine. The
  rules of §8.4 only project the equation (`e.1`, `e.2 x`) and pass the parts on, so no
  rule needs a proof's value.
* **Why no rule needs it.** Every elimination of a proof yields a proof: Σ is
  predicative, so a Σ that is a proposition has proof components; a Π into `Prop`
  applied to anything is a proof; there are no inductive propositions; `absurd` is
  stuck; `eq` is rejected at propositions. `split` with a relevant motive is the one
  exception, and η for Σ covers it.
* **Reading back.** The kernel's own read-back (`quoteErasesProofs`; `quoteM .false` in
  `Kernel.wiz`) reads every proof head as `()`: it neither evaluates nor compares proofs.
  It is used by the kernel's messages and, in the Lean kernel, by the shortcut that
  compares two folded inductions on numerals (which falls back to conversion). Regularity
  does not read values back at all (`groundEqTy` and `convTy`, §8.4).
  Reading a value back into a term *outside* the kernel (the elaborator's `quote`,
  `#reduce`, hover, the elaborator's messages) evaluates the suspended proof, so that the
  term is a normal form, and writes it back marked. It has to evaluate: a proof read back
  by substitution alone can be `(p, q).1`, and the bidirectional checker cannot infer a
  type for that when the elaborated term is checked again. So the elaborator may still
  run a proof, within a **step budget** (below). The kernel does not, in its error
  messages either: they read a suspended proof back as `()`.
  - *Erasure stops at `absurd`.* `absurd M p : M` for any `M`, so what is done to a
    proof after an `absurd` need not be a proof. The erased reading keeps the
    eliminations from the last `absurd` on, applied to `()`: two different values of a
    data type never read back alike. A suspended proof does not reach an `absurd` from
    a checked term (it only sits in the proof positions of `cast` and `transp`); the
    rule is there so that this does not have to be argued (test "P2: comparing types
    erases suspended proofs, but not what follows an absurd").
* **The step budget** (`Budget` in `Term.lean`; `--proof-steps N`, default 1 000 000).
  A proof need not have a normal form (Abel–Coquand's, under `--regularity full`). So
  each read-back of a suspended proof outside the kernel runs within a budget of
  *steps*, counted and not timed: the same on every machine and in every run, so a file
  that checks once always checks.
  - A step is one instantiation of a closure: a β-step, or going under a binder to read
    it back. Every loop of the evaluator takes one.
  - When the budget runs out the evaluator stops computing, and the proof reads back as
    a constant whose name is the message ("a proof was not read back: it needs more than
    N evaluation steps …"). No declaration has that name, so a term that contains it is
    rejected by the kernel with that message; in `#reduce`, hover and messages it is
    what is printed.
  - The kernel's own evaluation has no budget and needs none: it never evaluates a proof.
  - The self-hosted toolchain has the same budget (`forceProof` in `selfhost/Kernel.wiz`,
    review F7): its `quote` reads a suspended proof back within 1 000 000 steps (a step
    is `instC`, a closure's instantiation) and writes the same message, as a constant
    (`proofStub`) that its kernel rejects with that message. The counter is the
    runtime's (`wiz_proof_start`/`tick`/`end` in `runtime/` and `selfhost/rt.c`);
    a step is always granted while no read-back runs, so the kernel's checks never see
    it. There is no `--proof-steps` flag there: the message is Lean's, word for word.
  - Not covered: the elaborator's own evaluation of a term it has not marked yet (a
    `let`-bound proof while its body is elaborated). A proof without a normal form there
    still makes elaboration loop. Nothing is accepted by a loop.
* **The other positions: the proof marker** (`wiz-notes/prf-marker.md`). Only `cast`'s
  equation and `transp`'s proofs are marked by the syntax. A proof bound by `let`, passed
  as an argument, or stored in a pair or a constructor would be evaluated, because `eval`
  has no types. The marker closes that, and the kernel checks it: see §8.6a.
* **What the literature proves, and for what.** [PLT25] Theorem 5.6 is decidability of
  conversion for a system whose algorithm never reduces proofs, with full regularity
  (Cast-Refl) decided when two neutrals are compared. It is mechanised for a fragment:
  Π, ℕ, ⊥, the impredicative `Ω`, a proof-irrelevant ∃, the observational equality and
  `cast`, with two universe levels and no general inductive types. Wiz's descriptions,
  `μ`/`ν`, sizes, quantities, `ULift` and its computing equality type are outside that
  theorem (§8.4, "Related work"; `wiz-notes/plt-vs-inert.md`).

### 8.6a The proof marker

`Term.prf` / `Tm.prf`; "the proof marker" in `Check.lean` and `Kernel.wiz`;
`wiz-notes/prf-marker.md`.

```
eval (prf.{l} t)   =  neutral (prf ⟨env, t⟩)     if l is 0          (never looks at t)
eval (prf.{l} t)   =  eval t                      otherwise

Γ ⊢ T : Sort s    s ≡ l    Γ ⊢ t ⇐ T  (as a proof if l is 0; else t itself is exempt)
──────────────────────────────────────────────────────────────────────────────────────  Prf
Γ ⊢ prf.{l} t ⇐ T                                      (and the same for ⇒)
```

* **The level.** `l` is the sort of the type. "`l` is 0" is `Level.isZero` (`lvlIsZero`):
  a closed level is computed, and a level with parameters is `0` only if `Level.equiv`
  says so. Instantiating a constant's level parameters instantiates `l`, so a
  level-generic term, marked at `Sort u`, is a suspended proof at the instance `u := 0`
  and an ordinary term elsewhere. While the declaration itself is checked, `u` is a
  parameter and the term is evaluated: that is the generic computation.
* **Verified.** A marker at the wrong level is rejected. A marker at level `0` on a term
  of a data type would be unsound (a neutral where a constructor is expected, and any two
  suspended proofs are convertible), so the kernel does not trust the elaborator's
  marking. The test is the computation of the type's sort (`typeSort?`, `sortOf`), the one
  proof irrelevance in conversion relies on; if the sort cannot be computed the term is
  rejected.
* **Required.** The checker has two modes. *Proof mode*: under a marker at level `0`, and
  in `cast`'s equation and `transp`'s proofs. *Relevant mode*: everywhere else, including
  a declaration's body. In relevant mode a term whose type is in a sort that may be `0`
  (`Sort l` with `l` not never-zero: `Prop`, or `Sort u` for a level parameter `u`) must be

  ```
  marked:          prf.{l} t
  neutral-shaped:  x | c | () | n a | n.1 | n.2 | down n | (n : T)      (n any term accepted here)
  a stuck proof:   refl A a | reflTy X | transp A a P p b e
  ```

  Anything else there (a `fun`, a pair, a `let`, a cast, `absurd`, a case analysis or an
  induction with such a motive, `up`) is the kernel error "unmarked proof". The stuck
  proofs need no marker because `eval` makes each a stuck head: it evaluates their
  relevant parts (`A`, `a`, `X`, `b`, and the motive `P`, which is a family of
  propositions and so a relevant term) and suspends `transp`'s `p` and `e`. The body of a marked `fun` is exempt: `Sort (imax a l)` is `0` exactly when
  `Sort l` is, so where the body's sort is `0` the whole `fun` is suspended.
* **Inside a proof** (audit-2's I-1). Two rules make proof mode keep the same promise:
  - *the mode of a subterm is decided by its type*: a subterm of a proof whose type is not
    a proposition (the argument of a type, an index) is a relevant term again, since the
    checker may evaluate it, so the proofs in it must be marked. For a term whose type is
    only known afterwards: the argument of an application is checked in relevant mode
    when the function's type is not a proposition; the value of a `let`-bound proof after
    the body, in relevant mode when the body's type is not a proposition; `absurd`'s
    argument by the motive's sort; `split`'s scrutinee likewise. A type is always
    checked in relevant mode;
  - *bind by type*: where the checker needs a term's value to bind a variable or to
    instantiate a type (`let`, a dependent argument, a pair's first part, `split`'s
    scrutinee, `.2`, `transp`'s endpoints), inside a proof a proof is suspended, not
    evaluated.

  So the checker never evaluates a term that was checked in proof mode. (Before this, a
  `let` inside a marked proof evaluated its value to bind it: a Church tower of twos in
  `Prop`, 2^65536 steps at height 4, hung the checker. It now checks at once, with no
  step budget involved: the kernel has none.)
* **The invariant.** Call a value *proof-safe* if it is a neutral, `()`, or a glued
  constant that unfolds to one. Every value the kernel's evaluator builds at a
  proposition is proof-safe: a variable of proposition type is only ever bound (by a
  `let`, a β-step, a field of a pair or constructor, a fresh variable) to the value of a
  term that was checked in relevant mode, or put there by one of the kernel's templates;
  and applying or projecting a proof-safe value grows a spine. So **the kernel never
  performs a β, projection or ι step inside a proof**, and a term that would make it do
  so is rejected. `Globals.strictProofs` (off) asks for the marker on neutral-shaped
  proofs too.
* **Who writes the marker.** The elaborator's marking pass (`Wiz/Elab/Mark.lean`; in
  `Kernel.wiz`, outside the kernel proper, `markCheck`/`markInfer`), a typed traversal.
  It is untrusted: a missing or wrong marker is a kernel error. It costs about as much as
  the kernel's check, so it runs **on demand**: a declaration goes to the kernel as it
  is, and is marked and checked again only if the kernel answers "unmarked proof" (a
  theorem is marked at once). What is stored, and cached, is the term the kernel
  accepted. `quote` outside the kernel writes proofs back marked.
* **Conversion.** At a proposition, conversion answers before it looks (§8.5). A proof
  can sit inside a neutral that is compared at a relevant type only under `absurd`:

  ```
  a = h · sp · absurd M · sp₂     b = h' · sp' · absurd M' · sp₂'     (the same number of eliminations after the absurd)
  h · sp and h' · sp' are proofs of False     M ≡ M'     sp₂ ≡ sp₂' (typed by M)
  ───────────────────────────────────────────────────────────────────────────────
  a ≡ b
  ```

  The proofs and their heads are not compared (a suspended proof on one side, a
  hypothesis on the other). "A proof of `False`": it starts at a proof head and has
  passed through no `absurd`, or its type is computed to be `Empty_0`. So a suspended
  proof needs no type: what follows an `absurd` is typed by the motive.
* **Erasure** is unchanged (by type). A marker at level `0` is erased; one at another
  level is transparent.
* **Mandatory sorts** (`wiz-notes/mandatory-sorts.md`): every `Π`/`Σ`, the kernel's own
  templates' included, carries its components' sorts, so "may be `0`" for a canonical type
  is decided by its head and the sorts written in it (U5 closed). Relevance marks on
  binders are a later step (`wiz-notes/prf-marker.md` §8).

---

## 9. Descriptions, μ and induction

Stage 4d. Inductive types are least fixed points of **descriptions**, first-class data,
in the style of levitation [CDMM10] (Wiz's `Desc` is a primitive, not levitated: `Desc`
itself is not `μ` of a description).

### 9.1 Descriptions

```
     Γ ⊢ I type@k    ⊢ k ≡ l+1
     ───────────────────────────────────── desc                                     Check.lean:511–514
     Γ ⊢ Desc.{l} I ⇒ Sort (l+2) ⊣ 0

     Γ ⊢ i ⇐ I ⊣ U
     ───────────────────────────────── ret                                           Check.lean:283
     Γ ⊢ ret i ⇐ Desc.{l} I ⊣ U

     Γ ⊢ q qty   Γ ⊢ S type@k   ⊢ k ≡ l+1   Γ ⊢ D ⇐ (ω s : S) → Desc.{l} I ⊣ U
     ───────────────────────────────── arg                                           Check.lean:284–289
     Γ ⊢ arg q S D ⇐ Desc.{l} I ⊣ U

     Γ ⊢ q qty   Γ ⊢ j ⇐ I ⊣ U₁   Γ ⊢ D ⇐ Desc.{l} I ⊣ U₂
     ───────────────────────────────── rec                                           Check.lean:290–294
     Γ ⊢ rec q j D ⇐ Desc.{l} I ⊣ U₁ + U₂

     Γ ⊢ q qty   Γ ⊢ H type@k   ⊢ k ≡ l+1   Γ ⊢ j ⇐ (ω h : H) → I ⊣ U₁   Γ ⊢ D ⇐ Desc.{l} I ⊣ U₂
     ───────────────────────────────── hrec                                          Check.lean:295–302
     Γ ⊢ hrec q H j D ⇐ Desc.{l} I ⊣ U₁ + U₂
```

(`ω` stands for the rig's `explicitDefault`.) `rec` is a recursive field at index `j`;
`hrec` is an infinitely branching recursive field `(h : H) → μ D (j h)`. Strict positivity
holds by construction: there is no way to mention the type being defined except through
`rec`/`hrec`. Fields carry quantities [wiz]; `ret`, `arg`, `rec` are levitation's
constructors [std: CDMM10]; `hrec` is the usual infinitary extension (unverified which
paper; Dagand's thesis has `Π`-fields).

**Field levels (Q4, fixed).** A field type (and the domain `H` of an infinitary field) must
be in **exactly** `Sort (l+1)`. The eliminator's method types (`delimMethodTys`) quantify
over `S : Sort (l+1)` and `H : Sort (l+1)`, and universes are not cumulative. Until Q4 the
rule was `k ≤ l+1`, and `Desc.elim` on a description with a smaller field passed `S :
Sort k` where `Sort (l+1)` was expected, so the reduct was not well typed (`getS D : Type`
reduced to `True : Prop`). With `k ≡ l+1`:

* **Subject reduction for `Desc.elim`.** `arg q S E ⇐ Desc.{l} I` gives `S : Sort (l+1)`
  and `E ⇐ (ω s : S) → Desc.{l} I`. The reduct `marg q S E (λ s. Desc.elim P m… (E s))` is
  then well typed against `marg`'s type: `q : Qty`, `S : Sort (l+1)` (now exactly the
  binder's sort), `E : S → Desc I`, and the hypothesis has type `(s : S) → P (E s)`, by the
  rule for `Desc.elim` at `E s : Desc I`; the result `P (arg q S E)` is the redex's type.
  `hrec` is the same with `H`. `ret` and `rec` were already fine. The templates of §9.2
  are closed terms typed by these rules, so `⟦D⟧`, `All`, `hyps` and `map` are well typed
  on every description; `ind`, `scase`, `sfix` and `coit`, whose reducts are built from
  them, inherit subject reduction (as far as it held before; their own arguments are
  unchanged).
* **Small fields are lifted by the elaborator** (§4.1, `Elab/Inductive.lean`: `ctorDesc`,
  `fieldLevels`, `FieldLift`). A field `x : S` with `S : Sort k`, `k ≢ l+1`, becomes
  `arg q (ULift.{l+1} S) (λ x. D[down x / x])`, the domain of an infinitary field
  `hrec q (ULift.{l+1} H) (λ h. js[down h / h]) D`, and the tag of a type above `Type`
  (`Enum ls : Type`, when `l+1 ≢ 1`) `arg ω (ULift.{l+1} (Enum ls)) (λ t. ecase (down t) …)`.
  So a proof field of a datatype in `Type` is lifted, and so is every field `A : Type u`
  of a type in `Type (max u v)` (`Prod.{u,v}`), and the tag of every level-polymorphic
  inductive type. Constructors take the field itself and put `up x` (or `fun h => f
  (down h)`) in the payload; recursors (`casesOn`, `rec`), and so patterns and structural
  recursion, receive `down` of it (or `fun h => f (up h)`), with the induction hypotheses
  of a lifted infinitary field read the same way. The printer hides `up` and `down`.
  The surface `Desc.arg` already required `S : Sort (l+1)` exactly.
* `Kernel.wiz` has the same rule (`lvlEquiv`), and the same `ULift` (§15). Its frontend
  (`Frontend.wiz`) builds descriptions at `Desc.{0}` from a surface language without
  `Prop`, equations or universe polymorphism, so every field it can build is in `Type`
  and needs no lifting.

The eliminator:

```
     Γ ⊢ D ⇒ T ⊣ U_D    whnf T = Desc.{l} I
     Γ ⊢ P ⇐ (ω _ : Desc.{l} I) → Sort v
     Γ ⊢ mret ⇐ (i : I) → P (ret i)                                       ⊣ U₁
     Γ ⊢ marg ⇐ (q : Qty) → (S : Sort (l+1)) → (E : S → Desc I) → (ih : (s : S) → P (E s)) → P (arg q S E)   ⊣ U₂
     Γ ⊢ mrec ⇐ (q : Qty) → (j : I) → (E : Desc I) → (ih : P E) → P (rec q j E)                               ⊣ U₃
     Γ ⊢ mhrec ⇐ (q : Qty) → (H : Sort (l+1)) → (j : H → I) → (E : Desc I) → (ih : P E) → P (hrec q H j E)   ⊣ U₄
     ─────────────────────────────────────────────── Desc.elim     [wiz]        Check.lean:515–526
     Γ ⊢ Desc.elim.{v} P mret marg mrec mhrec D ⇒ P D ⊣ ω·(U₁+U₂+U₃+U₄ + U_D)

     Desc.elim P m… (ret i)       ⟶ mret i                                                   vDelim, Eval.lean:355–371
     Desc.elim P m… (arg q S E)   ⟶ marg q S E (λs. Desc.elim P m… (E s))
     Desc.elim P m… (rec q j E)   ⟶ mrec q j E (Desc.elim P m… E)
     Desc.elim P m… (hrec q H j E) ⟶ mhrec q H j E (Desc.elim P m… E)
```

All binders in these method types have quantity `ω` (`explicitDefault`).

### 9.2 Interpretation, All, hyps, map (templates)

`⟦D⟧ X i`, `All D X P i xs`, `hyps` and `map` are **not kernel rules**. They are closed
terms built with `Desc.elim` (`Templates.lean`), evaluated like any term:

```
⟦ret j⟧ X i        = (0 _ : j =_I i) × Unit_{l+1}
⟦arg q S D⟧ X i    = (q s : S) × ⟦D s⟧ X i
⟦rec q j D⟧ X i    = (q _ : X j) × ⟦D⟧ X i
⟦hrec q H j D⟧ X i = (q _ : (h : H) → X (j h)) × ⟦D⟧ X i
All (ret j) …            = Unit
All (arg …) P i xs       = All (D xs.1) P i xs.2
All (rec …) P i xs       = P j xs.1 × All D P i xs.2
All (hrec …) P i xs      = ((h : H) → P (j h) (xs.1 h)) × All D P i xs.2
```

Indices are handled by an **equation** `j = i` in the payload (the "Henry Ford"
encoding), so `μ` needs no index unification. The templates are **trusted**: the kernel
never type-checks them, and their Π/Σ types carry hand-written component sorts
(`Templates.lean`), from the levels at hand (`l`, `v`). An error there would be a kernel bug (Status.md, kernel trust).

### 9.3 μ, con, ind

```
     Γ ⊢ I type@k   ⊢ k ≡ l+1   Γ ⊢ D ⇐ Desc.{l} I   Γ ⊢ i ⇐ I
     ───────────────────────────────────── mu       (the size s is NOT checked; see below)   Check.lean:527–533
     Γ ⊢ μ.{l} I D i ^s ⇒ Sort (l+1) ⊣ 0

     s = ↑s'  or  s = ∞ (then s' = ∞)      Γ ⊢ x ⇐ ⟦D⟧ (λj. μ^{s'} D j) i ⊣ U
     ───────────────────────────────────── con   (check only)                              Check.lean:303–306
     Γ ⊢ con x ⇐ μ.{l} I D i ^s ⊣ U

     Γ ⊢ I type@k   ⊢ k ≡ l+1   Γ ⊢ D ⇐ Desc.{l} I
     Γ ⊢ P ⇐ (ω i : I) → (ω _ : μ D i ^∞) → Sort v
     Γ ⊢ m ⇐ (0 i : I) → (ω xs : ⟦D⟧ (μ D) i) → (ω ih : All D (μ D) P i xs) → P i (con xs)   ⊣ U_m
     Γ ⊢ i ⇐ I    Γ ⊢ x ⇐ μ D i ^∞ ⊣ U_x
     ───────────────────────────────────── ind                                               Check.lean:534–546
     Γ ⊢ ind P m i x ⇒ P i x ⊣ ω·(U_m + U_x)

     ind P m i (con xs)  ⟶  m i xs (hyps D (μ D) P (λj y. ind P m j y) i xs)                vIndStep, Eval.lean:409–423
```

* `μ` is always in `Sort (l+1)`: there are no inductive propositions.
* **The hint** [impl, Lean kernel only]. A `μ`/`ν` term carries an optional hint
  `(T, us, args)`, its nominal form `T.{us} args`. Conversion ignores it; the elaborator
  reads it back (a type's name, constructors and arguments), and `eval` evaluates `args`.
  So the `mu`/`nu` rule checks it (`checkHint`): if `T` is declared, `Γ⁰ ⊢ T.{us} args ⇒ _`;
  if not (the definition of `T` itself, whose hint lists its own parameters),
  `Γ⁰ ⊢ a ⇒ _` for every argument. Before, the hint was not checked and a raw core term in
  it was run by the evaluator unchecked (a `panic!`, a loop, a constant at too few
  levels). That the hint equals the type is not checked; nothing in the kernel relies on
  it. `Kernel.wiz` has no hints.
* The size argument of `μ` (and `ν`) is checked erased: `Γ⁰ ⊢ s ⇐ Size` (since
  `4605514`; Status.md, K3).
* The method's usage is scaled by ω (`QRig.many?`) because the method may run once per
  node (§5.3; Status.md, Q2).
* `x` is checked against `μ^∞`; a value of a smaller size is accepted by subtyping.
* **The index type's level in the eliminators (audit F3, fixed).** `ind`, and likewise
  `sfix`, `scase` (§10.2), `coit` and `scofix` (§10.3), take `I` and `D` as arguments and
  repeat the premise of the type former: `I` is in **exactly** `Sort (l+1)`
  (`checkIndexLevel`, in both kernels). Exactly, not `≤`, for the same reason as for fields
  (§9.1): universes are not cumulative, `Desc.{l} I` and `Desc.elim`'s method types take
  `I : Sort (l+1)`, and a smaller index type is lifted with `ULift` (§4.1). The premise is
  not redundant. These rules check the scrutinee against the *value* `μ.{l} I D i`, check
  `D` against the value `Desc.{l} I`, and (`coit`, `scofix`) return the value `ν.{l} I D i`,
  none of which goes through the `mu`/`nu`/`desc` rules. Until the fix they only required
  `Γ ⊢ I type@_`, so a core term could have a type `ν.{0} (Unit.{2}) D i` that the type
  former rejects, and the method of an `ind` could bind variables at such a type: the
  judgment did not have the property "the type of a well-typed term is a type". No proof of
  `False` came out of it (the ill-levelled type could not be written as a term, so no
  equation, cast, annotation or binder could mention it; see
  `wiz-notes/elim-levels.md`), but "index level ≤ family level" is the side
  condition under which the type formers may be injective [PLT25 §2.3] (§8.3), so every
  rule that produces a `μ`/`ν` type enforces it. `con`, `cocon` and `out` need no premise:
  they take the type from the context (checked against it, or inferred), and `Desc.elim`
  infers its description, whose type then went through the `desc` rule.

### 9.4 Numerals [impl]

After `builtin nat := N` (and `nat.zero`, `nat.succ`, `nat.add`, …), a numeral `n`
infers `N` (`Check.lean:341–343`), and evaluation treats it as `succⁿ zero`, unfolding one
step whenever something looks inside (`vNatView`, `Eval.lean:376`). The registered
operations compute natively on two literals and otherwise use their definitions
(`vNatOp`, `Eval.lean:386`). `a =_N b` on two literals is decided directly
(`Eval.lean:516`). `ind` on a numeral is glued (`Val.lazyInd`) so that it computes lazily.
**Nothing checks that a registration is correct** (that `N` is a natural-number type and
that the native operation agrees with the registered definition). The registrations are
trusted like axioms (§13, Status.md, O3).

---

## 10. Sizes, ν and sized (co)recursion

Stage 4f. Sizes follow Abel's sized types [AVW17 and earlier work], with Wiz's own
choices marked.

### 10.1 Sizes

```
  ──────────────────── Size      ────────────── ∞      Γ⁰ ⊢ s ⇐ Size            Γ⁰ ⊢ s ⇐ Size
  Γ ⊢ Size ⇒ Sort 1 ⊣ 0          Γ ⊢ ∞ ⇒ Size ⊣ 0     ──────────────── ↑       ──────────────────── Size<
                                                       Γ ⊢ ↑s ⇒ Size ⊣ 0         Γ ⊢ Size< s ⇒ Sort 1 ⊣ 0
                                                                                 Check.lean:487–490

     Γ⁰ ⊢ t ⇐ Size      Γ ⊢ t < s
     ──────────────────────────────── size-lt (check only)        Check.lean:277–282
     Γ ⊢ t ⇐ Size< s ⊣ 0
```

Evaluation identifies `↑∞` with `∞` (`Eval.lean:182–184`). A size is viewed as `↑ᵏ ∞` or
`↑ᵏ x` for a variable `x` (`sizeView`, `Conv.lean:105`). The order (`Conv.lean:126–150`):

```
s ≤ ∞                       for every s
↑ᵏ x ≤ ↑ᵐ x                 when k ≤ m
↑ᵏ x ≤ b                    when x : Size< u in Γ and ↑ᵏ⁻¹ u ≤ b   (k ≥ 1),  or u ≤ b (k = 0)
∞ ≤ ↑ᵐ x                    never

a < b   (b not ∞)           ⇔ ↑a ≤ b
a < ∞                       ⇔ a = ↑ᵏ x for a variable x : Size< u        (DECISION D2)
```

* **D2 [wiz]: `∞` is not below itself.** Because `↑∞ = ∞`, the rule `a < b ⇔ ↑a ≤ b`
  would give `∞ < ∞`. Agda's `∞ < ∞` makes well-founded induction on sizes inconsistent
  (Agda issue #3026). Wiz admits below `∞` only `↑ᵏ x` for a *bounded* variable `x`; a
  variable of type `Size` is not below `∞` (it may stand for `∞`). Fixed in `fb9074d`
  (Status.md, F2).
* Size equality in conversion is **syntactic on the view** (`sizeEq`, `Conv.lean:117`):
  same base variable and same number of `↑`s, or both `∞`.

### 10.2 Sized μ: sfix, scase

```
     (I, D, P as for ind, including  Γ ⊢ I type@k,  ⊢ k ≡ l+1)
     Γ ⊢ f ⇐ (0 s : Size) → (ω rec : (0 j : Size< s) → (ω i : I) → (ω y : μ^j D i) → P i y)
                         → (ω i : I) → (ω x : μ^s D i) → P i x                        ⊣ U_f
     Γ⁰ ⊢ s ⇐ Size    Γ ⊢ i ⇐ I    Γ ⊢ x ⇐ μ^s D i ⊣ U_x
     ───────────────────────────────────── sfix                     Check.lean:553–565, sfixFunTy Conv.lean:162
     Γ ⊢ sfix P f s i x ⇒ P i x ⊣ ω·(U_f + U_x)

     sfix P f s i (con xs)  ⟶  f ∞ (λj i y. sfix P f j i y) i (con xs)                     vSfix, Eval.lean:436–449

     Γ ⊢ q qty ↦ π     Γ⁰ ⊢ s ⇐ Size
     Γ ⊢ m ⇐ (0 j : Size< s) → (0 i : I) → (q xs : ⟦D⟧ (λj'. μ^j D j') i) → P i (con xs)   ⊣ U_m
     Γ ⊢ i ⇐ I    Γ^{π} ⊢ x ⇐ μ^s D i ⊣ U_x          (Γ^{π} = Γ⁰ when π is the constant 0)
     ───────────────────────────────────── scase_q                  Check.lean (`.scase`), scaseMethodTy Conv.lean
     Γ ⊢ scase_q P m s i x ⇒ P i x ⊣ U_m + π·U_x

     scase_q P m s i (con xs)  ⟶  m ∞ i xs        (q plays no part)                       vScase, Eval.lean
```

* `sfix` unfolds **only on a constructor** (as in MiniAgda / AVW17), so its unfolding can't
  loop on a neutral argument. Its recursive calls are typed at sizes below the generic
  `s`; at run time they are taken at `∞`, since sizes are irrelevant. In the unfolding,
  `f ∞` expects `rec : (j : Size< ∞) → …`; the reduct is typed by subtyping
  (`μ^s ≤ μ^∞`).
* `scase`'s method runs once, so it is not scaled.
* **The quantity (K1, linear-case stage 2).** `scase` carries a quantity term `q`
  (`Term.scase l q …`), checked like `split`'s. `q = ω` is the ordinary case (and what
  every eliminator generated before stage 2 uses); `q = 1` takes a value held at 1
  apart; `q = 0` is a case on an erased scrutinee. Conversion compares `q`
  (`convNe`, as `split`'s quantity); computation and erasure ignore it, except that a
  case at 0 passes `◾` as the payload. The method then takes the payload apart with
  the rules that exist: `split` at `q` gives the tag at `q·ω` and the rest at `q`,
  `ecase` on the tag joins the branches, each further `split` gives a field declared `p`
  at `q·p`, the index equation at `q·0 = 0`, and the final `Unit` at `q`, which the unit
  eliminator `let () := u; b` consumes (§10.2a). The elaborator's `T.casesOn1` is exactly this chain
  (`Recursor.lean`, `linear := true`); `match` uses it when the scrutinee mentions a
  variable bound at 1, binding the scrutinee at 1.

#### Why K1 does not let a 1-variable be used twice, or a 0-variable at run time

The argument is the usual one for a graded case [std: Linear Haskell (Bernardy et al.
2018) `case_π`; Abel, Danielsson, Eriksson 2023 for graded Σ eliminators in a dependent
setting; neither covers Wiz's descriptions or its observational equality, so this is
an argument, not a citation of a proof]:

1. *Accounting.* Every variable of `Γ` is charged once for the method (it runs once:
   the only reduct is `m ∞ i xs`, one application) and `π` times for the scrutinee. A
   1-variable `t` can therefore occur in `m` or in `x`, not both, and in `x` only if
   `π ≠ ω` (`π·1 ≤ 1` needs `π ∈ {0, 1}`; at `π = 0` the occurrence is erased).
2. *Subject reduction of usage.* On a constructor, `scase_π P m s i (con xs)` is charged
   `U_m + π·U_xs` (`con` charges its payload once), and the reduct `m ∞ i xs`, an
   application to the `π`-binder `xs`, is charged `U_m + 0·∅ + 0·∅ + π·U_xs` (the size
   and index binders are at 0): the same vector. So reduction neither copies nor drops
   what `xs` uses; inside the method, `xs` itself is used `≤ π` times (the λ rule), and
   from there on the trusted rules (`split`, `ecase`, `app`) carry the count.
3. *Exactly once at 1.* With `π = 1`, `xs` must be used exactly once (`le u 1` iff
   `u = 1` in `{0,1,ω}`): a method that ignores the payload or puts it in an ω position
   (a projection, the first component of an ω pair) is rejected. A field declared `p`
   comes out at `1·p = p`, the declared quantity, which is what the constructor charged
   for it (`con` via `⟦arg p S D⟧ = (p s : S) × …`): what was put in once comes out once.
4. *0-variables.* At `π = 0` the scrutinee is checked in `Γ⁰` and charged `0·U_x`, so it
   is never computed (erasure passes `◾`); the method binds `xs` at 0, so `xs` occurs
   only in erased positions. In particular the method cannot branch on the tag: `ecase`
   charges its scrutinee once, and `1 ≤ 0` is false. So an erased value is never
   inspected at run time (Idris 2's restriction of erased matches to types with at most
   one constructor, obtained without a side condition). A quantity *variable* `q` that
   could be 0 is checked under every assignment (`QPoly.le`), so a branching case at a
   variable quantity is rejected for the same reason.
5. *Neutral scrutinee.* `scase_π … x` on a neutral is stuck and computes nothing; it is
   charged as above, so it uses no more than the reduct would. Comparing two stuck cases
   compares `π` too, so no conversion identifies a case at 1 with one at ω.
6. *What is not claimed.* Linearity is not uniqueness (an ω value can be passed to a 1
   binder), so `scase_1` does not license in-place update; field quantities in
   `Kernel.wiz` are all ω (§15), where `scase_1` still binds the payload at 1.

Tests: `linearCaseRule` (both kernels, differential), the `linear-case` cases in the
elaborator tests (the M4 probes of `wiz-notes/cohesion-resources.md` §7 and their
negatives: a payload dropped in one branch, duplicated, the scrutinee used after the
match, a 0 field used at run time).

### 10.2a The unit eliminator; K2a withdrawn

```
     Γ ⊢ u ⇒ Unit_l ⊣ U₁     Γ ⊢ b ⇒ B ⊣ U₂        (u has the type `Unit` itself, after whnf)
     ───────────────────────────────────── letUnit                 checkUnit, Check.lean
     Γ ⊢ let () := u; b ⇒ B ⊣ U₁ + U₂             (and the ⇐ version)

     let () := u; b  ⟶  b          (η: every u is ())                                  eval, Eval.lean
     erasure:  let _ := u'; b'      (strict: u is evaluated first)                     Erase.lean
```

* **What it is.** Linear logic's 1-elimination (Atkey's `let () = u in b`). It is the
  only way a `Unit` held at 1 is used up: a binder at 1 never goes unused, whatever its
  type. `T.casesOn1` ends its chain of splits with it (the payload's final `Unit`); the
  surface syntax is `let () := u; b`.
* **Why it does not let a 1-variable be used twice, or a 0-variable at run time.** `u`
  is charged once and `b` as itself (`U₁ + U₂`, the `let` rule at 1 without a binder),
  in the same context: a 1-variable occurs in one of them, a 0-variable in neither
  outside erased positions. Unlike K2a it never discharges an obligation: whatever `u`
  uses is counted, and `u` is used up by being evaluated.
* **Run time.** In the kernel's evaluator (types, conversion) it computes to `b` by η.
  Erasure compiles it to `let _ := u'; b'`, a strict `let` that dead-code elimination
  keeps when `u'` is a call (it drops only pure values). The linearity guarantee is about
  counting, in the kernel; at run time it rests on a **trust assumption about foreign
  code**:
* **Trust assumption: effects live in `IO`.** A foreign function or implementation
  outside `IO` (`extern f : Nat → Nat`, `attribute [implemented_by g] f`) must be pure:
  no observable effect. Erasure and dead-code elimination may drop or duplicate such a
  call (in an erased position, in an erased closure, a dead `let`), so an effect there can
  be lost. linear-review's b4 is a pure `Nat → Nat` extern with an effect, applied inside
  `(fun (0 k : Nat) => (fun (x : Nat) => ()) (cRel n)) 0`: its call is dropped. b5, a
  polymorphic `{0 A : Type} → Nat → A` instantiated at `Unit`, is the same. Effects belong
  in `IO`, whose `World` is linear. **What holds without trusting anything more**: an
  `IO` effect can't sit in an erasable term, because running it needs a `World`, and a
  `World` can't escape into a value with no runtime content (it must reach `main`'s
  result).
* **The checks that enforce what can be checked.** `extern` and `implemented_by` refuse a
  result type with no runtime content: `Unit`, a proposition, a type, an erased function
  into such, or a Σ of such, after `whnf` (a named `def Tk := Unit` counts); `implemented_by`
  allows a proposition (the implementation is a proof, erased too). The decision
  uses the predicate erasure itself uses (`contentless`/`resultContentless`, Erase.lean,
  built on `erasable`), so the two can't drift. A foreign call is also kept where its
  type is erasable (`externCall`: defence in depth for polymorphic natives). Tested with
  a lock released in `IO` through a linear ticket (C and LLVM: a skipped release would
  hang the second acquire, and a doubled one would show in the count).
* **Tokens must not be named units.** `let () := t` consumes any `t` whose type reduces
  to `Unit`, so a library must not use a named unit type (`def Tk : Type := Unit`, or anything
  that reduces to `Unit`) as a linear token: anyone can discard one. Linear tokens are
  axioms (`Pts`, `Owned`) or opaque types.
* **Only `Unit` itself.** `checkUnit` requires the `whnf` of `u`'s type to be `Unit_l`,
  never a type that is a singleton by η: a function into `Unit` may be a closure holding
  a resource, and consuming it would mean applying it, to an argument nobody may have.
* **Kernel.wiz** has the same rule (`Tm.letUnit`, `checkUnit`). `Backend.wiz` refuses it:
  its `let`s are lazy and an unused one is dropped, so it can't promise to run `u`. The
  self-hosted frontend never produces it.

**K2a (withdrawn).** The design proposed that a binder whose type is unit-shaped (`Unit`,
or `(0 x : D) → … → Unit`) may go unused at any quantity, justified by η. It was
implemented on this branch and withdrawn after review (linear-review): **any rule that
trusts a type to "hold nothing" fails as soon as the type has a closure inhabitant.**
Counterexamples, all negative tests now (group `linear-case`, and `linearCaseRule` in both
kernels):

* `stash (1 t : T) : (0 e : T = Unit) → Unit := fun e => Eq.subst (fun X => X) e t`
  hides any linear `t` in a closure of a unit-shaped type; `let 1 g := stash t; k`
  dropped it. Compiled: a forgotten `Lock` guard, and the next `acquire` deadlocked.
* The same closure in a λ binder, a `let`, the second component of a pair.
* A unit-valued consumer `useU : (1 t : Tok) → Unit` whose result is dropped,
  `(fun (1 u : Unit) => 0) (useU t)`: the reduct does not mention `t`, and erasure need
  never evaluate it. Linear values are consumed explicitly, so even `Unit` is not exempt.
* Restricting K2a to a structure's marker tail does not help: a structure value built as
  a raw pair can put a closure of the tail's type in the tail slot, whose phantom domain
  is a user-chosen parameter (`S (Tok = Unit)`, or `S (PL (Tok = Unit))` with a
  propositional wrapper).
* Restricting it to types written literally (not unfolding globals) does not help:
  `stash`'s type is literal.

So a linear structure still can't be taken apart (§7.1); linear data that must be taken
apart is a one-constructor `inductive` with fields at 1 (`T.casesOn1`). Re-encoding
structures with the marker in a 0-quantity first component (repr-shape B) would make the
tail an erased position (a closure built there is charged `0·U`, so it can't capture a
linear variable): a possible later stage.

### 10.3 ν, out, cocon, coit, scofix

```
     (same premises as mu)
     ───────────────────────────────────── nu   (size not checked)                          Check.lean:527–533
     Γ ⊢ ν.{l} I D i ^s ⇒ Sort (l+1) ⊣ 0

     Γ ⊢ x ⇒ T ⊣ U    whnf T = ν D i ^s    s = ↑s' or s = ∞ (s' = ∞)
     ───────────────────────────────────── out                                               Check.lean:547–552
     Γ ⊢ out x ⇒ ⟦D⟧ (λj. ν^{s'} D j) i ⊣ U

     s = ↑s' or s = ∞ (s' = ∞)      Γ ⊢ x ⇐ ⟦D⟧ (λj. ν^{s'} D j) i ⊣ U
     ───────────────────────────────────── cocon (check only)                                Check.lean:307–310
     Γ ⊢ cocon x ⇐ ν D i ^s ⊣ U

     (I, D as for ind:  Γ ⊢ I type@k   ⊢ k ≡ l+1   Γ ⊢ D ⇐ Desc.{l} I;  the same for scofix)
     Γ ⊢ S ⇐ (ω i : I) → Sort (l+1)
     Γ ⊢ step ⇐ (ω i : I) → (ω s : S i) → ⟦D⟧ S i ⊣ U_st     Γ ⊢ i ⇐ I    Γ ⊢ t ⇐ S i ⊣ U_t
     ───────────────────────────────────── coit                                              Check.lean:594–606
     Γ ⊢ coit S step i t ⇒ ν D i ^∞ ⊣ ω·(U_st + U_t)

     Γ ⊢ A ⇐ (ω i : I) → Sort (l+1)
     Γ ⊢ f ⇐ (0 s : Size) → (ω rec : (ω i : I) → A i → ν^s D i) → (ω i : I) → A i → ν^{↑s} D i   ⊣ U_f
     Γ⁰ ⊢ s ⇐ Size    Γ ⊢ i ⇐ I    Γ ⊢ a ⇐ A i ⊣ U_a
     ───────────────────────────────────── scofix                     Check.lean:566–578, scofixFunTy Conv.lean:180
     Γ ⊢ scofix A f s i a ⇒ ν D i ^s ⊣ ω·(U_f + U_a)

     out (cocon xs)               ⟶  xs                                                     vOut, Eval.lean:468–487
     out (coit S step i t)        ⟶  map D S (ν D) (λj s. coit S step j s) i (step i t)
     out (scofix A f s i a)       ⟶  out (f ∞ (λi a. scofix A f ∞ i a) i a)
```

* `coit`, `scofix` are **values** (`Val.coit`, `Val.scofix`): they unfold only under `out`
  (the guard against infinite unfolding). [std: Abel's sized coinduction; the
  "unfold under observation" strategy is standard (unverified which paper exactly)]
* `ν` is contravariant in its size (§11.5): `ν^∞ ≤ ν^s`.
* `out` requires the size to be visibly a successor or `∞`. Inside `f`, `rec` returns
  `ν^s` for the generic `s`, which can't be observed; this is the productivity check.

---

## 11. Definitional equality and subtyping

The conversion algorithm is **type-directed** (`conv ty a b`), on values in whnf.
There is no separate declarative definitional equality: the algorithm *is* the
specification. The rules below describe what it equates. [std: Abel & Coquand 2007's
type-directed algorithmic equality, cited in `Conv.lean:24`; not re-checked]

### 11.1 Unfolding (δ, ζ, β, ι)

* **β**: `(λx. b) a ⟶ b[a/x]` (`vApp`, `Eval.lean:269`); `(a, b).1 ⟶ a`,
  `(a, b).2 ⟶ b`, `let (x, y) := (a, b); u ⟶ u[a, b]` (`vSplit`, `Eval.lean:295`).
* **ζ**: `let x := v; b ⟶ b[v/x]` (`Eval.lean:142`).
* **δ**: a global with a definition unfolds to it, instantiated at the given levels
  (`Eval.lean:131–135`). It is **glued** [impl]: the value keeps the name and its spine
  and unfolds lazily, so `f a ≡ f b` is first tried by comparing the spines
  (`convGlued`, `Conv.lean:358`); if that fails, both sides are unfolded. Axioms (no
  definition) and partial definitions are neutral heads.
* **ι**: the eliminator rules of §7–§10 and the equality computations of §8.

### 11.2 conv at a type

`conv` (`Conv.lean:252–313`), after unfolding glued values and comparing two numerals
directly:

```
1. proof irrelevance    if typeSort?(A) ≡ 0:   a ≡ b                                   263   [std: PT22]
2. regularity           InReg_conv (§8.4): replace a stuck cast A' B' e t · sp with A' ≡ B' and
                        A' or B' inert (any types under --regularity full) by t · sp, on
                        both sides, before comparing; also in convTy            [std: PLT25, restricted]
3. by the type:
   Π   η:  a x ≡ b x  at B x, for a fresh x : A                                         267–269  [std]
   Σ   η:  a.1 ≡ b.1 : A  and  a.2 ≡ b.2 : B a.1                                        270–272  [std]
   Unit_l:  always                                                                       273      [std: η for unit]
   ULift A:  η:  down a ≡ down b : A                                                       [std; Q4]
   Qty:   as polynomials (equivalent under all assignments), else neutral comparison    274–276  [wiz]
   Enum:  same tag index, else neutral comparison                                        277–279
   Size, Size< s:  sizeEq                                                                280      [wiz]
   Desc:  structurally (ret/arg/rec/hrec), else neutral comparison                       281–291
   μ:     con x ≡ con y  if x ≡ y at the payload type; else neutral comparison           292–294
   ν:     cocon/cocon, scofix/scofix, coit/coit componentwise; else neutral comparison   295–303  [wiz]
   Sort:  convTy                                                                         304
   otherwise: neutral comparison (convNe)                                                305
```

`typeSort?` (`Conv.lean`) computes a type's universe from its value (Π/Σ: from the
component sorts written in it, which the kernel checked; neutral: from `inferNe`).

At `ν`, two coinductive values are equal only if they are built the same way. This is
sound (it equates less than bisimilarity) and incomplete.

### 11.3 convTy

`convTy` (`Conv.lean:326–354`) compares types structurally:

```
Sort u ≡ Sort u'                 ⊢ u ≡ u'
Π/Π, Σ/Σ                         same quantity (or the Π/Σ is a proposition: quantities don't matter),
                                 domains ≡, codomains ≡ under a fresh variable
Qty ≡ Qty, Size ≡ Size           always
Size< s ≡ Size< t                sizeEq s t
Enum ls ≡ Enum ls'               |ls| = |ls'|
Desc l I ≡ Desc l' I'            l ≡ l', I ≡ I'
μ/μ, ν/ν                         l ≡ l', sizeEq, I ≡ I', D ≡ D' : Desc, i ≡ i' : I
Unit_u ≡ Unit_u', Empty_u ≡ Empty_u'   u ≡ u'
ULift.{k,u} A ≡ ULift.{k',u'} A'   u ≡ u', k ≡ k', A ≡ A'
two neutrals                     convNe
```

**The component sorts are compared** (Π/Σ: `σ ≡ σ'` componentwise, decision Q6; `subTy` too).
On well-typed types this is redundant (convertible components have equivalent sorts, and
there is no cumulativity), but it makes "convertible types get the same `propSort?`, hence
the same `vEqType`/`vCast`/`inertTy` decision" hold by construction, without relying on
`Level.equiv` being complete.

### 11.4 convNe

Two neutrals are equal when their heads are equal and their spines are pointwise
convertible at the types computed along the spine (`Conv.lean:388–467`). Heads:
the same variable; the same global at equivalent levels; two stuck equations with
convertible parts; two stuck casts with convertible types and arguments (the proofs `e`
are **not** compared); and **any two proof heads** (`refl`, `reflTy`, `transp`) are equal
(proof irrelevance at the head). Eliminations compare their motives and methods at the
types the kernel would give them.

### 11.5 Subtyping

`subTy` (`Conv.lean:474–489`) is conversion plus sizes [std: AVW17 (sizes); wiz in detail]:

```
μ^s D i ≤ μ^t D' i'     if s ≤ t and the rest is convertible       (covariant)
ν^s D i ≤ ν^t D' i'     if t ≤ s and the rest is convertible       (contravariant)
Π: (q x : A₁) → B₁ ≤ (q' x : A₂) → B₂   if q ≡ q' (or the Π is a proposition), A₂ ≤ A₁, B₁ ≤ B₂
Σ: covariant in both parts, quantities equal
Size< s ≤ Size,   Size< s ≤ Size< t if s ≤ t
otherwise convTy
```

Subtyping is used only by the mode switch (§6) and is **not** reflected in
observational equality (`μ^s ≡ μ^t` as types is stuck, §8.3).

---

## 12. Evaluation strategy

`eval` (`Eval.lean:128`) is call-by-value on an environment, with closures for binders.
Lazy places: glued globals and `ind` on numerals (thunks); `coit`/`scofix` values (until
`out`); `ecase` branches (evaluated only when the tag is known); and proofs, which are
never evaluated: the proof positions of `cast` and `transp`, and marked proofs (§8.6,
§8.6a). Ill-typed situations
(applying a non-function) `panic!` and are meant to be unreachable on checked terms. All
functions are `partial` in Lean: **termination of evaluation and of type checking is not
proved**, and the D1 experiment shows checking can loop (Status.md).

---

## 13. Global declarations and universe polymorphism

```
     name ∉ Σ    level parameters ν₁…νₖ distinct    every level parameter used is among them
     · ⊢ T type@_        (value v given ⇒  · ⊢ v ⇐ T)
     (implementation m given ⇒  · ⊢ m ⇐ T  in  Σ, c.{ν…} : T [:= v])
     ────────────────────────────────────────── addDecl                Check.lean (`addDecl`, `checkImpl`)
     Σ ⊢ c.{ν₁…νₖ} : T [:= v]   added

     c.{ν…} : T ∈ Σ     |us| = k
     ────────────────────────────────────── const                       Check.lean:347–352
     Γ ⊢ c.{us} ⇒ T[us/ν] ⊣ 0
```

* Declarations are checked **once, at symbolic levels**; a use instantiates the
  parameters [std: Lean 4]. Constants have no local usage (`⊣ 0`): globals are not
  tracked by QTT.
* **No recursion in the kernel:** a declaration is checked against the environment
  *without* itself, so a value cannot mention its own name.
* **Axioms** (`value = none`) are accepted with any well-formed type, including `False`.
* **Partial definitions** (`addPartialDecl`, `addPartialImpl`): `f` is opaque, and the
  kernel takes it only with a **witness** `w : T` of its type (`Decl.witness`), which it
  checks (erased), so `f` proves nothing `w` doesn't. Its recursive implementation is
  checked against `f`'s type but used only by the compiler; the kernel never unfolds it.
  (Status.md, F3: the elaborator's old inhabitedness check could be fooled.)
* **`builtin` registrations** are not checked against their definitions by the kernel
  (§9.4). Those of the toolchain's `lib/` are trusted (reviewed, Status.md §7); any other
  is an axiom, listed by `#print axioms` (Status.md, F4). The elaborator checks their
  shapes.
* **Implementations for the compiler** (`Decl.impl`): the term compiled code runs
  instead of the value. Three things set one: a structurally recursive definition by
  equations (its value with the recursor's hypotheses replaced by direct calls, so that a
  program computes only the recursive calls it makes), a partial definition (its body,
  above), and
  `attribute [implemented_by g] f` (the constant `g`). The kernel never unfolds an
  implementation, so it proves nothing, but it **checks every one against the declared
  type**, with the definition itself already declared (a recursive one calls it):
  `checkImpl`, from `addDecl` and `setImpl`, as `addPartialImpl` does for a partial
  definition. So an implementation is well typed at `T`, its quantities are respected,
  and the sorts written on its `Π`s and `Σ`s are right (`checkComponentSort`): erasure reads all
  three. A declaration whose implementation does not check is rejected. For a
  structurally recursive definition the kernel also checks that the implementation
  **computes what the value computes** (`checkImplAgrees`): both are stuck on the same
  argument as `ind P M i x` and `ind P M' i x` (through `T.rec` and `T.casesOn`), convertible
  with `M'` replaced by `M`, and for each constructor tag `t` and a fresh payload
  `xs = (t, rest)`, `M j xs H ≡ M' j xs H` with `H` the hypotheses `ind` computes; by
  induction on the scrutinee they agree on every closed argument (Status.md, T1). An
  `implemented_by` constant is not checked this way (trusted, listed by `#print axioms`).
* `Decl.inline` (evaluate eagerly) does not affect what the kernel accepts.

*Kernel.wiz.* There is no global table: a constant term carries its value and type
(`Tm.const`, `Kernel.wiz:118`), and the kernel trusts that this pair was checked
(`Kernel.wiz:2070`). `checkDecl` (`Kernel.wiz:2211`) checks a declaration at symbolic
levels. Data levels (`μ.{l}`, `Desc.{l}`) are closed numerals.

---

## 14. Where the code and the stage docs disagree

Each item says what the code does; the code is what the kernel checks.

1. **Regularity.** Stages 4c/4e ([stages/04-data.md](stages/04-data.md)) describe regularity (`cast A A e t ≡ t`) as it was before
   D1. Since D1 it is off by default in both kernels, except at inert types (§8.4); the
   sections say so.
2. **`absurd`'s usage.** The rule in `Check.lean`'s docstring (`Check.lean:78–80`) gives
   `absurd M t ⊣ U` (the scrutinee's usage). The code returns `⊣ 0` and checks `t` in
   erased mode (`Check.lean:427–433`).
3. **Method scaling.** Stage 4d ([stages/04-data.md](stages/04-data.md)) and the docstring (`Check.lean:116–121`) say methods are
   scaled by ω. The code scaled by the rig's `explicitDefault`, which is ω only for
   `ZeroOneMany`; for the `Nat` rig it is `1`, which under-counts a method that runs once
   per node. **Resolved** in `a986c02`: the code now scales by `QRig.many?` (Q2).
4. **Linear pairs.** Stage 4b ([stages/04-data.md](stages/04-data.md)): "a linear pair is consumed with `let 1 (x, y) := p`". The
   code also lets `p.2` (and `p.1` when the field allows it) consume a linear pair, dropping
   the other component (§7.1).
5. **Missing rules in the docstring.** `Check.lean`'s rules omit the sort annotation on
   Π/Σ, the `sizeLt` check, `sfix`, `scase`, `scofix`, `cocon`, and the `isNeverZero`
   premise of `refl`. Its `eq` rule writes `l ≠ 0`; the code requires `isNeverZero l`
   (nonzero under *every* instantiation), which is stronger.
6. **`Term.lean`'s module comment** (`Term.lean:27`) says "Not in the core yet: μ/ν data and
   Σ-types (stage 4)". Both are in the core.
7. **`Eval.lean`'s module comment** (`Eval.lean:20–22`) says globals are δ-unfolded
   eagerly. They are glued (unfolded lazily) unless marked `inline` or `eager`.
8. **The OTT table in stage 4c** ([stages/04-data.md](stages/04-data.md)) writes funext as `(x : A) → a x = b x`; the code uses
   quantity 0 for `x`. It writes `Type u` equality as "structural equality of types;
   `False` for different formers", but propositions inside types are compared by
   equivalence, and `μ`/`ν`/`Desc` are stuck. (The prose below the table says the first
   part.)
9. **Sort annotations.** Stage 4c ([stages/04-data.md](stages/04-data.md)) says a Π/Σ "carries its sort (the elaborator writes
   it)". At `9717950`, several Π/Σ the elaborator builds carry none
   (the stage docs themselves list them only on an unmerged branch, commit
   `31395a2`). After that branch merges, the remaining unannotated cases are "a Π/Σ under
   a `fun` whose variable's type isn't written down, or one that still mentions a
   metavariable".
10. **Self-hosting stages 14g–14p** ([stages/14-selfhost-kernel.md](stages/14-selfhost-kernel.md)) describe `Kernel.wiz` as mirroring the Lean
    kernel. It differs in the places listed in §15, one of which is unsound.

---

## 15. The self-hosted kernel (`Kernel.wiz`)

`Kernel.wiz` implements the same algorithm for a fragment, and the differential test
(Status.md) compares the two on random and hand-picked terms. Differences:

| topic | Lean kernel | Kernel.wiz |
|---|---|---|
| quantities | any `QRig`, quantity variables, `Qty` | binder quantities are literals `0, 1, ω` only (`Q`, `Kernel.wiz:19`). Since 21w there is `Qty : U 0` with its literals (`qty`, `qlit`), for description fields; a `Qty` variable (a `Desc.elim` method's `q`) is a neutral, and a `Σ` at one (`sigmaQ`, the template `⟦D⟧` at such a field) stays stuck (`ssigq`) where the Lean kernel builds a Σ at a polynomial quantity; it has the rules of a Σ at an unknown quantity (projections erased only, except `snd` at ω; η; a pair's first part counted ω times), only at a bare variable (as `qtyPoly`: a quantity that is another stuck term is rejected). Unlike the Lean kernel's Σ at a polynomial, it is not canonical: `cast`, `eqTy` and `eq` at it stay stuck (incomplete, never unsound) |
| description fields | carry a quantity | the same (21w): `darg q S D`, `drec q j D`, `dhrec q H j D` with `q : Qty` checked as `checkQty` does (a literal or a variable), the methods receive `q`, and `⟦D⟧` puts it on the field's Σ; `vEqDesc`, conversion, cast, `groundEqDesc` compare it as `sameQty`/`qtyApart` do (`qtySame`: two literals by value, the same variable equal, anything else unknown) |
| `scase` at a quantity (K1) | `q` a quantity term | `q` a literal (`Tm.scase l q …`, `Spine.sscase`); the same rule, `U_m + q·U_x`, payload at `q` |
| the unit eliminator `let () := u; b` | `Term.letUnit`, `checkUnit`; erasure evaluates `u` | `Tm.letUnit`, `checkUnit`, the same rule; `Backend.wiz` refuses it (lazy `let`s), the frontend never produces it |
| `split` (`let (x, y)`) | yes | **no**. Projections need an unrestricted pair in both kernels (§7.1, R1), so a pair held at quantity 1 cannot be consumed in Kernel.wiz's fragment, nor at all in the self-hosted language (no `let (x, y)`; its `IO` and `Prod` are at ω): every term that projects one is rejected by both kernels, and terms with `split` are outside the fragment (the differential test's term type `MTm` has no `split`) |
| numerals, `natOp` | yes | no |
| levels of data | `Level` | closed numerals (`descr l`, `mu l`, `ulift l`) |
| `ULift` (Q4) | `ulift k l`/`up`/`down`, `cast` needs a level never `0` and `k ≡ k'` | `ulift k l`/`up`/`down` at closed levels (`vulift`, `vup`, `sdown`); the same rules |
| component sorts (mandatory sorts) | `BinderSorts ⟨dom, cod⟩` on `pi`/`sigma`, `Level`s; a hole is `Level.hole` | `pi q i j`, `sigma q i j` (`Lvl`; `piq`, `sigmaq`, `sorted` are gone); a hole is `Lvl.lhole`. The templates write closed numerals. The frontend fills holes with the sorts pass (`sortsTy`, `sortsClosed`: the marking pass at `TCtx.pm` 4/5, no markers) |
| globals | table, by name; `addDecl` rejects a second declaration of a name | inline `const` terms carrying value and type (trusted). **`convHead`, `tmEq` and `headSame` compare two constants by name alone**, so the kernel *relies* on every name having one value, and it has no table to check that with. The frontend checks it, in one place: `stepCommand` refuses a command that adds a name already in scope, or twice (`newDuplicate`, `Frontend.wiz`; a partial definition's signature followed by its body is the one exception). Before that check (audit 2, Y4), `def T := Nat; def a : Box T := …; def T := Empty; def c : Box T := a` was accepted, a closed term of an empty type: the two `T`s are both still folded under `Box`. Anything else that builds `const` terms for `Kernel.wiz` (the differential test) must keep names unique too |
| a variable out of scope (raw core terms) | a checking error (`infer`, `.var`); `eval` gives a stuck unknown | the same (`infer`; `lookup` past the end). Before audit 2 both went on with `Sort 0` as the variable's type *and* value (a panic's default value in Lean, `lookup`'s default in Wiz): a term `Prop : Prop`, with which Hurkens' paradox checks. No frontend produces such a term |
| **`Size ≡ Size`, `Size< s ≡ Size< t`** | **stuck** (`Eval.lean:572`) | **`False`**: `canonical` includes `vsize`/`vsizeLt` (`Kernel.wiz:552–565`) and `vEqTypeW` has no case for two sizes, so it falls through to "different formers ⇒ False" (`Kernel.wiz:961–963`). **Unsound** (Status.md, O1). |
| regularity in conversion (InReg_conv, §8.4) | `unCast` in `conv` and `convTy`: a stuck cast at an inert type with `convTy A B`; `--inert ground` turns it off, `--regularity full` widens it to every type | `stripCast` in `convNeW`, with a typed re-entry at the neutral's type; `kernelInertConv`, `kernelRegularity` |
| regularity in evaluation | only the fast path `groundEqTy` | the same |
| proofs (P2, §8.6) | never evaluated (`Globals.lazyProofs`, `--eager-proofs` for the old behaviour); `quote` outside the kernel evaluates a suspended proof within a step budget, the kernel's (`quoteErasesProofs`) never | the same (`kernelLazyProofs := .true`); `quote` evaluates (no budget: it is the frontend's), `quoteM .false` (in `sameVal`, `showVal`) erases |
| the proof marker (§8.6a) | `Term.prf`, required and verified; `Globals.strictProofs` for the strict form | `Tm.prf`, the same rules; no strict form |
| a proof under `absurd` in conversion | not compared (§8.6a) | the same. (Before the marker: any two proof heads in the Lean kernel, only two of the same kind in `Kernel.wiz`.) |
| two proof heads with no `absurd`, at a type not seen to be a proposition | equal (`isProof`) | equal only if of the same kind (`convHead`): stricter |
| convTy at Π/Σ propositions | quantities may differ | quantities must be equal (`Kernel.wiz:1598`) |
| proof irrelevance at Π/Σ | asked at the Π/Σ | asked at the codomain/components only (`Kernel.wiz:1537–1541`); equivalent |
| `isProp` | `typeSort? ≡ 0` | Π: codomain is a proposition; Σ: both parts (`Kernel.wiz:1328`) |
| size equality on non-variable bases | equal if the same metavariable | never (`sizeEq`, `Kernel.wiz:1388`) |
| `app` | evaluates the argument | only if the codomain may mention it (`usesVar`) |
| conversion fast path | none | `valSame`: bounded structural equality (`Kernel.wiz:1461`) |
| μ/ν size argument | unchecked | unchecked (`Kernel.wiz:1918, 1967`) |
| equality of descriptions, `μ ≡ μ` (4g, §8.4b) | `vEqDesc`, `vEqType`, `famPayloadEq?` | the same rules (`vEqDesc`, `famEqTy`, `famPayload`; field quantities since 21w); levels are numerals |

**The self-hosted frontend's quantities** (`Frontend.wiz`, stage 21m; finding K10 of audit 2,
now closed). The frontend reads written quantities (`0`, `1`, `ω`) on binders, `fun`
binders and `let`, with the Lean elaborator's defaults (ω explicit, 0 implicit; a
constructor's parameters at 0), and the kernel checks usage. What still differs is below. A linear
variable used once in each branch of a `match` was a difference until stage 21v: the Lean
frontend now compiles such a match to the additive `T.casesOnA`, and both accept it.
Constructor field quantities and implicit constructor fields were differences until 21w:
a field `(q x : A)` is `darg q A …` here too (an implicit field `{n : A}` at 0, inserted at
the call and not named by patterns), a match binds each field at its quantity (`T.casesOn`'s
method does), and a structure's field at 0 has no projection.
Commands: `#eval` is `#reduce` here, and `attribute [inline]` is checked and ignored
(21u); classes and instances, the other attributes and `import_c` are errors.

| program | Lean frontend | self-hosted frontend |
|---|---|---|
| a `match` on a linear scrutinee (`def m2 (1 x : Nat) : Nat := match x with \| .zero => 0 \| .succ k => k`) | accepts (4h): `T.casesOn1`, the case at 1; `k` is an ω field, so it comes out at `1·ω` | **rejects**: the match is the kernel's case at ω, which uses `x` ω times (the Kernel.wiz rule is the same; only the frontend does not emit `scase` at 1) |
| `%t` quantity terms, quantity variables | yes | an error |

**The self-hosted FFI** (stages 21l, 21o–21t) takes the Lean frontend's `extern`,
`foreign_type`, `export`, callbacks, `c_struct`, `link_c`/`link_lib` and `implemented_by`
with the same checks. It differs in: no `import_c` or `glue` (an error, "unsupported
command"); no `Bytes`, so no buffer arguments or byte-array struct fields; a `Nat` is 63
bits at the boundary (21p); `implemented_by mk get` (22d) is an error; under the collector
`wiz_live_objects()` is 0 and `wiz_retain`/`wiz_release` do nothing.

---

## 16. What is not in the core, and who checks what

**Elaborator-only features** (they produce core terms, which the kernel checks):

* metavariables, unification, implicit arguments, type classes and instance resolution,
  level metavariables and defaulting (unconstrained size metavariables default to `∞`);
* `inductive`/`structure`/`coinductive` (they elaborate to descriptions, `μ`/`ν` and
  constructors), Lean-style `T.rec`, `T.casesOn`, `T.scasesOn`, the additive `T.casesOnA` and the linear `T.casesOn1` (built on `ind`, `ecase`, `split`,
  `cast`, `scase`);
* `match`, equations, structural and sized recursion (compiled to `ind`, `sfix`,
  `scase`), copatterns (compiled to `coit`, `cocon`), coconstructors `T.mk`, the
  guardedness check;
* macros, command macros and reflection, tactics, `deriving`, `do` notation;
* writing the component sorts on every Π/Σ and the content's sort on every `ULift`
  (mandatory: eagerly where known, then one total pass, `Decl.withSorts` in `Mark.lean`, fills
  every hole, inside proofs too; the kernel rejects a hole and checks every sort).

**What the kernel re-checks.** Every `def`, `axiom`, constructor, recursor and generated
declaration goes through `addDecl` (`Elab/Command.lean:700–705`), which type-checks it
from scratch; a bug in elaboration, `match` compilation or recursion compilation can only
make the kernel *reject* a declaration. The kernel does not look at binder info, display
hints, or names.

**What the kernel trusts** (each is a place where a bug, or a wrong user declaration,
is not caught by type checking):

1. **Axioms** (`axiom`, and `C.*` functions from imported C headers, `foreign` types).
   The Prelude has one, `castRefl` (§8.4a).
2. **Partial definitions**: no longer trusted: each has a witness the kernel checks.
3. **`builtin` registrations** of the toolchain's `lib/`: numerals' type and native
   arithmetic (any other registration is an axiom, reported by `#print axioms`).
4. **The templates** (`Templates.lean`): never type-checked; their component sorts are
   hand-written (from `l`, `v`).
5. **The method/motive types** the kernel builds itself (`delimMethodTys`,
   `indMethodTy`, `sfixFunTy`, … in `Conv.lean`), and the terms built inside `vEq`,
   `vEqType`, `vCast` (their binders and component sorts).
6. **Code outside the kernel that runs on checked terms**: erasure and the backends.
   Erasure relies on QTT: a 0-quantity value is assumed unneeded. Every term erasure is
   given has been checked by the kernel, a definition's implementation for the compiler
   included (§13).
6a. **That an implementation for the compiler agrees with the definition** (§13): the
   compiled equations of a structurally recursive definition (two elaborations of the
   same clauses; Status.md, T1), and native implementations (`implemented_by`, `repr:`),
   which `#print axioms` lists.
7. **The Lean compiler and runtime** (for the Lean kernel), and Wiz's own backend (for
   `Kernel.wiz`).

---

## 17. References

Checked for this document (title, authors, venue):

* **[Atkey18]** R. Atkey. *Syntax and Semantics of Quantitative Type Theory.* LICS 2018,
  pp. 56–65. doi:10.1145/3209108.3209189. (QTT; dependent tensor with `let`
  elimination; fixes the substitution problem of McBride's system.)
* **[AC20]** A. Abel, T. Coquand. *Failure of Normalization in Impredicative Type Theory
  with Proof-Irrelevant Propositional Equality.* LMCS 16(2), 2020. arXiv:1911.08174.
* **[CDMM10]** J. Chapman, P.-É. Dagand, C. McBride, P. Morris. *The Gentle Art of
  Levitation.* ICFP 2010, pp. 3–14. doi:10.1145/1863543.1863547.
* **[AVW17]** A. Abel, A. Vezzosi, T. Winterhalter. *Normalization by Evaluation for Sized
  Dependent Types.* PACMPL 1 (ICFP), 2017. doi:10.1145/3110277.
* **[PT22]** L. Pujet, N. Tabareau. *Observational Equality: Now for Good.* PACMPL 6
  (POPL), Article 32, 2022. doi:10.1145/3498693. (TTobs.) Checked against the paper: it
  has no definitional regularity, only the proof term `castrefl` (§2.2, Fig. 2); its Π
  domain equation is forwards (Fig. 4).
* **[PT23]** L. Pujet, N. Tabareau. *Impredicative Observational Equality.* PACMPL 7
  (POPL), Article 74, 2023. doi:10.1145/3571739. (CCobs: TTobs with an impredicative
  universe of definitionally proof-irrelevant propositions; decidability of conversion,
  Theorem 3.2, without reducing proofs; undecidability with a proof-relevant impredicative
  universe, Theorem 6.1.)
* **[PLT25]** L. Pujet, Y. Leray, N. Tabareau. *Observational Equality Meets CIC.* ACM
  TOPLAS 47(2), Article 6, 2025. doi:10.1145/3719342. (CICobs: CCobs with the conversion
  rule Cast-Refl, `cast A B e t ≡ t` when `A ≡ B`, and Coq's inductive types by Fordism;
  decidability of conversion for a fragment, Theorem 5.6. Read in full; the comparison
  with Wiz is `wiz-notes/plt-vs-inert.md`. An earlier version appeared at
  ESOP 2024, which we did not obtain.)
* **Agda issue #3026**, "Well-founded induction on Size is inconsistent"
  (github.com/agda/agda/issues/3026).

Cited from the code or from memory, **not re-checked**:

* **[McBride16]** C. McBride. *I Got Plenty o' Nuttin'.* In *A List of Successes That Can
  Change the World*, LNCS 9600, 2016.
* **[AMS07]** T. Altenkirch, C. McBride, W. Swierstra. *Observational Equality, Now!*
  PLPV 2007.
* **[ML84]** P. Martin-Löf. *Intuitionistic Type Theory.* Bibliopolis, 1984.
* A. Abel, T. Coquand. *Untyped Algorithmic Equality for Martin-Löf's Logical Framework
  with Surjective Pairs.* TLCA 2005 / Fundamenta Informaticae 2007 (cited in
  `Conv.lean`).
* G. Gilbert, J. Cockx, M. Sozeau, N. Tabareau. *Definitional Proof-Irrelevance without
  K.* POPL 2019.
* A. Kovács, *elaboration-zoo* (cited in `Value.lean` for the NbE design).
