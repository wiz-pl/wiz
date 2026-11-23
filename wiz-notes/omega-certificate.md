# `omega` as a certificate-producing Cooper/Omega procedure

Status: design + prototype, 2026-11-23. Lane `omega-certificate`, branch
`agent/omega-certificate` off `integration/train12`.
Reads `docs/numerics-trust.md` §R7 (`:192–208`), the current `omega`
(`lib/Prelude.wiz:1771–2079`), the Nat order lemmas (`lib/Nat.wiz`), the tactic/kernel
path (`Wiz/Elab/Tactic.lean`, `Wiz/Elab/Term.lean:4550–4561`,
`Wiz/Elab/Term.lean:4604–4638`, `Wiz/Core/Check.lean`), and the `proof-auto` history of
the P1 skip (`Tests/Groups/Tactic.lean:459–472`).

**One line.** Keep `omega` proof-producing and add no solver axiom; replace the
10,000-node BFS by a decision procedure whose search is untrusted and whose *certificate*
is a derivation in a small calculus of order/divisibility lemmas, every rule of which is
a theorem proved in `lib/`; the kernel infers the resulting proof term at `assign`, and
outside the linear fragment the tactic refuses with a positioned diagnostic.

This note is a plan, not a claim that R7 is finished. §8 says exactly what is proved,
what is prototyped, and what is still missing.

---

## 1. What exists, and what is missing

The current `omega` (`lib/Prelude.wiz:1771–2079`) is a **sound but incomplete** tactic:

* It runs a deterministic BFS over a graph whose nodes are `Nat` terms and whose edges
  are `Nat.le_refl`, `Nat.le_trans`, `Nat.le_succ`, `Nat.le_add_right`,
  `Nat.le_add_left`, `Nat.le_of_eq`, `Nat.le_of_eq_sym`, and `Nat.le_antisymm`
  (`omegaSuccs`, `:1920–1941`). Every reached edge carries a proof term, so a found path
  is a kernel-checked proof. `#print axioms leTrans` is empty
  (`Tests/Groups/Tactic.lean:459–464`).
* It refuses products, division, modulo and powers before searching
  (`:2034–2041`), with the message `omega: non-linear (multiplication/division is
  outside the linear Nat fragment)`.
* It has a node budget of 10,000 (`omegaBFS`, `:1930`), and a direct equality shortcut
  `omegaDirectAdd` (`:1973–1996`).
* It only proves goals whose type is `Nat.Le`, `Nat.Lt` or an `=` (the `eqView` branch
  `:2061–2078`); there is no refutation path and no division/divisibility.

Two concrete gaps are recorded in the test file:

* `omega P1: sum = constant bounds` is **skipped**
  (`Tests/Groups/Tactic.lean:465–466`): `h : a + b = 3 ⊢ a ≤ 3` is linear, true, and
  not found; the skip names "equality-hypothesis transport … raw omega proof terms hit
  instance-argument conversion".
* There is no completeness claim: a goal that needs a *combination* of two hypotheses
  (`a ≤ b`, `c ≤ d ⊢ a + c ≤ b + d`) has no BFS path, because the BFS walks one chain at
  a time.

The replacement has to buy three things the BFS cannot: **a linear-combination rule**
(the FM/Omega step), **integer reasoning** (divisibility/Cooper), and **a refutation
discipline** that fails loudly outside the fragment. All three can be had with no new
trust: each is a lemma in `lib/Nat.wiz` (or a new `lib/Omega.wiz`), and the kernel checks
the proof term built from those lemmas.

**Finding (R7's file attribution).** `docs/numerics-trust.md:194` says R7 "needs
`Wiz/Elab/Tactic.lean`, held by another lane". The *procedure* is not in that file: the
whole `omega` implementation is `lib/Prelude.wiz:1771–2079`, and
`Wiz/Elab/Tactic.lean` only defines the `Tac` request tags (`assign`, `isDefEq`, …) and
the reflection layer that any tactic uses. The design in this note therefore needs
**no change** to `Wiz/Elab/Tactic.lean`: the calculus is `lib/` lemmas, the checker is a
`lib/` function, and the tactic is registered in `lib/` like `ring`
(`lib/RingTactic.wiz:227–251`). If R7's lane ownership was the reason the plan was
deferred, the reason does not apply to this shape. (The one host-side convenience a
production checker might want is `TacticM.inferType` for better intermediate errors;
that request already exists, `Wiz/Elab/Tactic.lean:57`, and needs no edit.)

### 1.1 What "kernel-checked" means in Wiz

`TacticM.assign g e` (`lib/Prelude.wiz:682`) is the host request
`TacTag.assign` (`Wiz/Elab/Tactic.lean:52,74`) implemented at
`Wiz/Elab/Term.lean:4550–4561`:

```lean
if tag == TacTag.assign then
  let t ← zonk lvl (← reify st.handles (fld 1) lvl)
  if t.mvars.isEmpty then
    match (← get).kernelInfer (gl.kernelCtx g) t with
    | .ok ty => unifyAt gl.ctx .missing gl.ty ty
    | .error e => throwAt info s!"assign: {e}" ErrorCode.tacticFailed
  else
    st := { st with unchecked := st.unchecked.push (gl, t) }
  unifyGoal gl t
```

`kernelInfer` is `Wiz.infer` (`Wiz/Elab/Command.lean:1501`) with `proof := true`; i.e.
the **kernel's** `inferCore` (`Wiz/Core/Check.lean:833–900`), not the elaborator's view.
The declaration is then re-checked by `addDeclSorted`/`addDecl`
(`Wiz/Elab/Command.lean:377`; `Wiz/Core/Check.lean:1760`). The `unchecked` path is only
for terms with holes; the certificate checker builds **hole-free** terms, so the `assign`
path is the kernel path. `assignLate` (`Wiz/Elab/Term.lean:4562–4568`) deliberately skips
the immediate kernel inference and must not be used by `omega`.

So "the kernel checks the certificate" is a statement about *this* call, not about the
tactic monad in general. A production implementation should add a unit test that
`assign` and not `assignLate` is used (or, stronger, that a deliberately wrong
certificate fails at `assign`, see §6.3).

---

## 2. The fragment

### 2.1 Terms and atoms

`F_lin(Nat)` is the quantifier-free, additive fragment over `Nat`:

```
t ::= x | c | t + t | Nat.succ t
a ::= t ≤ t | t < t | t = t
H ::= a₁, …, aₙ                 (the local hypotheses)
G ::= a                          (the goal after ∀-introduction)
```

* `x` is a local variable (a de Bruijn index in the goal's context).
* `c` is a numeral; `Nat.succ t` is read as `t + 1` (it is how `<` is represented:
  `Nat.Lt a b` is `Nat.Le (Nat.succ a) b`, `lib/Nat.wiz:34`).
* Any subterm that is not `+`, `succ` or a numeral is an **atom**: a variable, an
  application `f x`, a projection, … . An atom is a `Nat` value; `omega` reasons about it
  as an uninterpreted *linear* variable. This is what makes the fragment robust: `omega`
  never needs to understand `f`'s definition, and a hypothesis about `f x` is used only
  as an atom.
* `Nat.add` may appear as `Nat.add`, `Add.add` (after 2 class arguments) or `HAdd.hAdd`
  (after 4), as `Expr.addPair` already handles
  (`lib/Prelude.wiz:1829–1841`). The reifier reduces those to the same `+`.
* **Refused**: any occurrence of `Nat.mul`/`HMul.hMul`/`Mul.mul`,
  `Nat.div`/`HDiv.hDiv`/`Div.div`, `Nat.mod`/`HMod.hMod`/`Mod.mod`, `Nat.pow`, and
  `Nat.sub` (until the subtraction slice S4). Also refused: an atom whose type is not
  `Nat`'s order/equality (e.g. `Int`, `Q`, `Bool`), a goal that is not one of the
  three relations, and a hypothesis that is not an atom (a `∀`, an implication, an
  `Or`). The refusals are *loud*: a positioned error naming the operation and the
  hypothesis/goal it occurs in.

Why the fragment is additive rather than the usual `Σ aᵢxᵢ + c ≤ 0`: `Nat` has
truncated subtraction, so moving a term from one side to the other is not a theorem
without a side condition. Keeping **both sides additive and every coefficient
nonnegative** means every rule below is an *order* lemma on `Nat` with no truncated
subtraction. Coefficients are repeated occurrences of the same atom (`2*x` is
`x + x`), and scaling a certificate by a numeral is a proof term using
`Nat.mul_le_mul_left` (multiplication is allowed in the *proof*, never in the *input*).
This is the S0 boundary, and S1 keeps it: a surface `*`/`Nat.mul` in a goal or
hypothesis is refused as non-linear, so the `2*a` acceptance case is written in the
fragment's form as `a + a ≤ b + b` (it is the same coefficient-2 system and the same
FM step).

This fragment is still Presburger arithmetic: the coefficients are arbitrary naturals,
and the decision problem is complete only with the division/modulo slice S3. The
restriction to `Nat` and to nonnegative coefficients is a *proof-engineering* choice,
not a weakening of the logic: `2*x ≤ y` is expressible as `x + x ≤ y`.

### 2.2 Normal form

A linear expression `L` is a pair `(atoms, k)`:

* `atoms` is a list of `(atom, coefficient)` pairs, with no duplicate atoms, in a fixed
  order (`Expr.beq` order on the atom term); coefficients are positive naturals;
* `k` is the numeral constant.

`L₁ + L₂` adds coefficients and constants; `scale n L` multiplies every coefficient and
`k` by `n`; `L₁ ≤ L₂` is stored as the pair `(L₁, L₂)`, *not* as `L₁ − L₂`. The
difference form `D = L₁ − L₂, c = k₁ − k₂` is used only by the **search** (it is an
integer vector and constant), never by the certificate: the certificate's conclusion is
always a two-sided `Nat` atom.

The atom order is syntactic. Two definitionally equal but syntactically different atoms
(e.g. `f x` and `f (x)`, or an unreduced instance argument) may become two variables:
that is **incompleteness, not unsoundness** — the certificate is still a valid proof of
whatever it concludes. The tactic normalizes the goal and hypotheses once
(`TacticM.normalize`) at the boundary, and reports "two atoms are definitionally equal
but not syntactically; unfold the definition or state the goal in the same form" rather
than silently dropping one.

### 2.3 The goal wrapper

The procedure decides **unsatisfiability** of `H ∧ ¬G`; a proof of `G` from `H` needs a
constructive elimination of the double negation. All three relations are decidable
Booleans, and the library already has the case lemmas:

| Goal `G` | Decision lemma | Branches |
|---|---|---|
| `a ≤ b` | `Nat.le_or_lt a b` (`lib/Nat.wiz:228`) | `a ≤ b` (done) ∨ `b < a` (refute with `H`) |
| `a < b` | `Nat.le_or_lt b a` | `a < b` (done) ∨ `b ≤ a` (refute with `H`) |
| `a = b` | `Nat.le_cases a b` twice, or `Nat.cmp` trichotomy | `a < b`, `a = b`, `b < a`; the outer two are refuted |

The `a = b` case needs a small trichotomy lemma (`Nat.cmp` plus `cmp_eq`,
`lib/Nat.wiz:165–176`; the `<`/`>` cases still need `cmp` soundness lemmas). That lemma
is part of S2; until then equality goals can be handled by proving both directions
`a ≤ b` and `b ≤ a` directly (the current `omega` does this with `le_antisymm`), which
is the same proof obligation without the trichotomy.

In each refutation branch the procedure returns a certificate whose conclusion is
`False`; the wrapper builds `Nat.le_or_lt`/`Nat.le_cases`, passes the "bad" branch to
the refutation, and closes the good branch with the lemma's proof. The result is a
proof term, not a metalinguistic "the search failed to find a counterexample".

---

## 3. The calculus

The certificate is a derivation tree in the following calculus. Each rule is a theorem
in `lib/` (existing or new), stated with **all arguments explicit** so the checker can
build an application without inserting implicits. The rule's conclusion is a function of
its premises and parameters; the checker computes it, so the certificate never has to be
trusted about what it concludes.

### 3.1 Structural rules

| Rule | Premises | Conclusion | Wiz lemma |
|---|---|---|---|
| `hyp i` | — | `aᵢ` as read from the hypothesis type | `Expr.var i` |
| `refl L` | — | `L ≤ L` | `Nat.le_refl` |
| `trans` | `L₁ ≤ L₂`, `L₂ ≤ L₃` | `L₁ ≤ L₃` | `Nat.le_trans` |
| `add` | `L₁ ≤ L₂`, `L₃ ≤ L₄` | `L₁+L₃ ≤ L₂+L₄` | `Nat.add_le_add` |
| `scale k` | `L₁ ≤ L₂` | `k·L₁ ≤ k·L₂` | `Nat.mul_le_mul_left` |
| `cancelR K` | `L₁+K ≤ L₂+K` | `L₁ ≤ L₂` | `Nat.le_of_add_le_add_right` |
| `cancelL K` | `K+L₁ ≤ K+L₂` | `L₁ ≤ L₂` | `Nat.le_of_add_le_add_left` |
| `eq→le` | `L₁ = L₂` | `L₁ ≤ L₂` | `Nat.le_of_eq` |
| `eq→le-sym` | `L₁ = L₂` | `L₂ ≤ L₁` | `Nat.le_of_eq_sym` |
| `le→eq` | `L₁ ≤ L₂`, `L₂ ≤ L₁` | `L₁ = L₂` | `Nat.le_antisymm` |
| `lt→le` | `L₁ < L₂` | `succ L₁ ≤ L₂` | definitional (`Nat.Lt`) |
| `le→lt` | `succ L₁ ≤ L₂` | `L₁ < L₂` | definitional |
| `eq-add` | `L₁ + K = L₂` | `L₁ ≤ L₂` | `Nat.le_of_eq_add'` |
| `false` | `c + (k+1) ≤ c` | `False` | `Nat.not_add_succ_le` |
| `absurd` | `False` | `G` | `False.elim` |

`Nat.le_of_eq_add'` exists for the common "equality whose left side is a sum"
(`lib/Nat.wiz:310–313`) and is the rule the skipped P1 case needs.

### 3.2 The linear-combination rule (real shadow)

The central new rule is Fourier–Motzkin / Pugh's **real shadow**:

```
A + a·x ≤ B        C ≤ D + b·x          (a, b ≥ 1)
------------------------------------------------
        b·A + a·C ≤ b·B + a·D
```

It is sound over `Nat` for every `a,b ≥ 1` (no side condition): multiply the first
inequality by `b`, the second by `a`, add, and cancel `a·b·x`. The proof is one theorem,
proved once in `lib/Omega.wiz`:

```wiz
/-- `omega`'s real shadow (Fourier–Motzkin step for one variable). -/
def Nat.omegaFM (A B C D a b x : Nat)
    (h₁ : Nat.Le (A + a * x) B) (h₂ : Nat.Le C (D + b * x)) :
    Nat.Le (b * A + a * C) (b * B + a * D)
```

Its proof uses `Nat.mul_le_mul_left`, `Nat.add_le_add`, `Nat.le_of_add_le_add_right`,
`Nat.add_assoc`, `Nat.add_comm`, `Nat.mul_assoc`, `Nat.mul_comm`, `Nat.mul_add` and
`Nat.add_mul` (all in `lib/Nat.wiz`). The coefficient multiplications are `Nat.mul` in
the *proof term*; the kernel checks them, and the input fragment never contains `*`.

The rule eliminates one variable `x` from a lower-bound atom and an upper-bound atom.
Applying it to every pair (lower, upper) and keeping the results is a sound
over-approximation of the projection (the real shadow). Over `ℚ` it is exact; over `ℤ`
it is exact only up to the **dark shadow**, below.

### 3.3 The integer step (dark shadow and gcd)

Over integers, the real shadow is necessary but not sufficient: `2x ≤ 1` and
`2x ≥ 1` have no integer solution though their real shadow is true. Pugh's Omega test
adds two kinds of tightening:

1. **Coefficient gcd / exact bound.** A single inequality `a·x ≤ u` with `a > 0` is
   equivalent over `ℤ` to `x ≤ ⌊u/a⌋`, i.e. to `a·x ≤ a·⌊u/a⌋`. In the two-sided form
   this is a *divisibility* tightening, not an order combination. Its certificate is the
   division algorithm:
   `Nat.div_add_mod : m ≠ 0 → m * (n / m) + n % m = n` and
   `Nat.mod_lt : 0 < m → n % m < m`.
2. **Dark shadow.** Combining a lower and an upper bound with coprime coefficients
   `a`, `b` gives the tightened atom
   `b·A + a·C + (a−1)(b−1) ≤ b·B + a·D`.
   The exact form and its side conditions are Pugh's theorem; the certificate takes the
   side conditions as `rfl`-checked Bool hypotheses (see §5.3), so the checker cannot
   silently use a wrong gcd.

Neither the gcd tightening nor the dark shadow is a source of trust: each is a theorem
with a proof obligation. The **honest position for this lane** is that S1 implements
§3.1–§3.2 plus the refutation wrapper and the `cancel` nodes, which is sound and
complete for *difference logic* (unit coefficients, where the LP relaxation is
integral); full `F_lin` completeness arrives with S3, and until then a detected
integrality gap is a **positioned refusal**, never a "no proof" guess. `lib/Nat.wiz`
currently has **no** `Nat.div_add_mod`, `Nat.mod_lt` or divisibility lemmas; proving
them is part of S3, not an assumption.

### 3.3a Canonical forms are certificates too

The FM rule's premises are in the shape `A + a*x ≤ B` with a **numeral** `a`, but the
input fragment has no `*`: `2*x` is `x + x`. The reifier computes the coefficient `2`
(the tactic's own `Nat` arithmetic), but the proof must not depend on that computation.
So the certificate carries a **canonicalisation step** for each atom:

```
L₁ ≤ L₂        (the atom as written, e.g. x + x + A ≤ B)
    ⇓  Eq (canonical(L₁) = L₁), Eq (canonical(L₂) = L₂)
canonical(L₁) ≤ canonical(L₂)
```

The two equalities are proved by the ring normaliser's soundness theorem
(`NatExpr.prove`, `lib/Ring.wiz`; kernel-checked by computing the normal forms), not by
the tactic's arithmetic. The checker builds the transport with `Eq.mp'`/`Eq.mpr'`. This is
the "arithmetic certificate for each coefficient comparison" of R7: a wrong coefficient
makes the `NatExpr.prove` term fail to typecheck, so the search's arithmetic is not
trusted. `nat_ring!` is a convenient way to write the equality in the library proof; in
the checker the equality is an `Expr` built from `NatExpr.prove` (or a small lemma) and
the kernel checks it.

A certificate therefore has two kinds of leaves: **hypotheses** (terms) and
**arithmetic identities** (ring certificates). Both are kernel-checked; neither is an
axiom.

### 3.3b Size and coefficients

A scaled inequality `k·(L₁ ≤ L₂)` is one `Nat.mul_le_mul_left` application, so a
coefficient `k` does not cost `k` proof nodes. A coefficient vector is stored as a list
of numerals; the kernel computes only the *closed* coefficient arithmetic (`k * c`,
`(a−1)(b−1)`, gcds on numerals) and never reduces a symbolic `k * x` (it is stuck, as
expected). A certificate's size is `O(nodes + coefficient digits)`, independent of the
size of the values the variables take.

### 3.4 Cooper's split (the complete fallback)

For the existential closure of a conjunction of literals, Cooper's algorithm eliminates
a variable `x` by a finite disjunction over residues:

```
∃x. φ(x)  ↔  ⋁_{r=0}^{a−1} φ(a·y + r)  ∨  φ(−∞)
```

where `a` is the lcm of the coefficients that occur in divisibility atoms of `x` (in
`F_lin(Nat)` there are no explicit divisibility atoms; `a` is the lcm of the positive
coefficients of `x` in equalities, and the residue split is justified by the division
algorithm). The `−∞` branch is the "no solution below the bounds" case, discharged by
monotonicity.

For a *certificate* the direction that matters is the refutation direction: a finite
case tree whose leaves are constant contradictions. Each split node is justified by

* `Nat.div_add_mod x a : a * (x / a) + x % a = x` (the substitution `x := a·y + r`),
* `Nat.mod_lt x a : x % a < a` (the finitely many residues),

and each leaf is a derivation in §3.1–§3.3. The disjunction is exhaustive because every
`x` is `a·(x/a) + x%a` with `x%a < a`; the kernel checks the identity and the bound, so
the case tree is a proof, not an appeal to Cooper's theorem. This is the route to
completeness over `F_lin(Nat)` without a solver.

The R7 text also names Cooper for the existential case and Pugh's dark shadow/splice for
the universal one. In this design the two engines share the same rule language; the
procedure picks one by a *fragment test* (are there coefficients > 1 or equalities with
non-unit coefficients?) and by the failure of the previous engine. A detector must never
turn an integrality gap into "no proof": it either produces a certificate or a
positioned "incomplete" message.

---

## 4. The procedure

### 4.1 Pipeline

```
goal type ──► ∀-intro ──► relation/atom check ──► reify goal + hyps
                                                      │
                                                      ▼
                         negation of the goal (wrapper) + hypotheses
                                                      │
                                                      ▼
                        normalize to (L₁, L₂) pairs; scan for non-linear heads
                                                      │
                              ┌───────────────────────┴───────────────────────┐
                              ▼                                               ▼
                    equality elimination (S2)                       FM elimination (S1)
                              └───────────────────────┬───────────────────────┘
                                                      ▼
                          constant contradiction?  ──yes──►  false certificate
                                      │no
                                      ▼
                          integrality gap? ──yes──► Cooper split (S3) or positioned refusal
                                      │no
                                      ▼
                          budget exhausted ──► positioned "budget" refusal
```

### 4.2 Search state (untrusted)

The search carries, for each derived atom, a record:

* the two linear forms `(L₁, L₂)`, coefficients as `Nat` in canonical atom order;
* the proof `Expr` that has already been built for it (or the certificate node);
* a provenance tag `hyp i`, `fm (p, q, x, a, b)`, `cancel K`, `scale k`, `eq→le`, …

The search may use integer difference vectors, gcd, lcm, division and arbitrary
heuristics; **none of that is trusted**. The only thing that matters is the certificate
it emits.

### 4.3 Search rules

1. **Normalize** every hypothesis and the negated goal. An equality becomes two
   inequalities (`eq→le` and `eq→le-sym`) unless equality elimination (S2) substitutes
   it. A `<` becomes `succ` ≤. A `≤` stays.
2. **Constant check**: if an atom has no atoms on either side and the constant on the
   left exceeds the constant on the right, emit `false` (the numerals compute, so the
   checker's `Nat.not_add_succ_le` application has a `rfl` premise or a computed
   numeral inequality).
3. **Equality elimination (S2)**: if an equality has a unit coefficient on one side,
   substitute it (using `Nat.le_of_eq_add'` for the order direction and a transport
   lemma for the general case), and re-normalize. If the equality's coefficients have a
   gcd `g > 1` that does not divide the constant, emit `false` using the divisibility
   rule (S3); otherwise divide the equality by `g` (a `rfl`-checked coefficient
   certificate).
4. **FM elimination (S1)**: pick the atom/variable with the fewest lower×upper pairs;
   for every lower-bound atom containing `x` on the left and every upper-bound atom
   containing `x` on the right, emit `fm`; replace the pair by the combination, dropping
   the atoms that contain `x`. If there are no atoms left, the system is feasible over
   `ℚ`: report a **real-feasible** gap (which over `ℕ` may still be integer-infeasible).
5. **Integrality (S3)**: if the system has coefficients > 1 and the real shadow is
   feasible but no integer point is found by the residue enumeration, run the Cooper
   split on the variable with the smallest lcm and recurse. A gap at a leaf is a
   *contradiction certificate* (constant false) or a loud `omega: incomplete` with the
   leaf's atom set — not a silent "no proof".
6. **Budget**: every loop carries a fuel counter checked against a named limit. S1
   measures the FM search on the cases below and sets `Omega.fmFuel` to **512**
   derived-items (pair attempts); the additive path search keeps `Omega.pathFuel = 64`,
   the S0 measurement, and the unconditional successor edge it used to grow is gone.
   Running out is `omega: incomplete: budget exhausted (512)` with the number, never a
   hang and never a claim of infeasibility; the S0 10,000-node BFS budget is not reused.

The order is deterministic and documented; no random seed, no external process, no
cache of verdicts (R5). A certificate cache is allowed later, keyed by the exact goal
and hypotheses and storing the *proof term*; an entry is re-checked by the kernel on
replay, so a poisoned cache can only fail.

### 4.4 What is decided

* **S1 (FM only)**: sound for all of `F_lin`; complete for the difference-logic
  sub-fragment (every coefficient 0/1 after normalization, i.e. all atoms are
  `x + c ≤ y + d` or `c ≤ y + d` forms). This is the fragment where the rational
  relaxation is integral (network matrices are totally unimodular), so a real-feasible
  system has a natural solution.
* **S3 (+ Cooper)**: complete for `F_lin(Nat)` modulo the fuel bound. This is the
  Presburger decision problem; no claim of efficiency (Oppen 1978: triply exponential
  in the worst case). The practical budget is part of the interface. The case tree is
  exhaustive by `Nat.div_add_mod`/`Nat.mod_lt` (every `x` is `a*(x/a) + x%a` with
  `x%a < a`); the nonnegativity bounds that turn the `Nat` problem into the integer one
  are the theorem `Nat.zero_le`. The exact elimination order and the `−∞`/large-`x`
  branch are implementation details with a proof obligation, to be settled in S3 — not
  assumed here.
* **Int** (`F_lin(Int)`): P1/S5, a separate instantiation with `lib/IntOrder.wiz`'s
  lemmas; the same certificate shape, different rule statements. Do not pretend Nat
  rules prove Int goals.

---

## 5. The certificate format

### 5.1 The datatype

The certificate is a **typed step list** (a derivation tree, serialized as an inductive
value), not an opaque proof term. It is produced by untrusted search; the checker is the
only consumer.

```wiz
inductive Omega.Cert where
  | hyp (i : Nat)
  | refl (a : Expr)
  | leAddRight (a k : Expr)
  | leAddLeft (a k : Expr)
  | trans (a b c : Expr) (p q : Omega.Cert)
  | add (a b c d : Expr) (p q : Omega.Cert)
  | scale (k : Nat) (a b : Expr) (p : Omega.Cert)
  | cancelR (k : Expr) (a b : Expr) (p : Omega.Cert)
  | cancelL (k : Expr) (a b : Expr) (p : Omega.Cert)
  | eqToLe (i : Nat) (dir : Bool)              -- a hypothesis `u = v`
  | eqOfLe (a b : Expr) (p q : Omega.Cert)
  | leOfEqAdd (a c k : Expr) (i : Nat)
  | fm (A B C D a b x : Expr) (p q : Omega.Cert)
  | falseOf (a k : Expr) (p : Omega.Cert)      -- from `a + (k+1) ≤ a`
  | absurd (g : Expr) (p : Omega.Cert)
```

(`leOfEqAdd`'s `i` is the hypothesis index; `eqToLe` reads the hypothesis' sides with
`TacticM.eqView`, so no `Expr` arguments are needed for the equality.)

The S0 prototype in `lib/Omega.wiz` was a subset of this datatype: it omitted `scale`
and `absurd`, added `leSucc` (the `Nat.le_succ` edge), and had the `fm` node in place
but not used by the search. S1 deletes `leSucc` and its unconditional edge, and uses the
real shadow (`fm`) and cancellation (`cancel`) in a separate refutation certificate
(`Omega.RCert`/`Omega.checkR`) rather than retrofitting the additive `Cert`; the additive
certificate keeps its fast path. The full form above remains the target for S2–S3; the
note keeps the target and the implementation separate rather than pretending the
prototype is the whole calculus.

The *typing rules* are exactly §3: each constructor corresponds to one theorem. A
certificate is **well-formed** when each child's computed conclusion matches the parent's
premise pattern (syntactically, `Expr.beq`, after reification). Ill-formed certificates
are rejected by the checker with a message naming the node; if a bug lets one through,
the kernel still rejects the proof term it builds.

### 5.2 The checker

```
check : Nat → List (String × Expr) → Omega.Cert → TacticM (Omega.Conc × Expr)
```

* `Nat` is the goal id; the hypothesis list is `TacticM.goalHyps g` (index `i` is
  `Expr.var i`, `Wiz/Elab/Term.lean:4345–4352`).
* For each node, `check` computes the conclusion it *claims* (the two linear forms, an
  equality, or `False`) and builds the proof `Expr` with `Expr.mkApp`/`Expr.ap*` of
  **all-explicit** library lemmas:
  * `trans`: `Nat.le_trans a b c p q`;
  * `add`: `Nat.add_le_add a b c d p q`;
  * `scale`: `Nat.mul_le_mul_left k a b p`;
  * `cancelR`: `Nat.le_of_add_le_add_right k a b p`;
  * `cancel`: `Omega.cancelSame`/`cancelMoreL`/`cancelMoreR` (the `Nat.add` forms of the
    cancellation lemmas, the S0 instance-argument bridge);
  * `fm`: `Omega.fm A B C D a b x p q`, the `Nat.add`/`Nat.mul` form of `Nat.omegaFM`;
  * `falseOf`: `Nat.not_add_succ_le a k p`;
  * `absurd`: `False.elim g p`.
* **Shape checking vs type checking.** The production checker validates each parent's
  premise pattern against the child's claimed conclusion (`TacticM.isDefEq`, not
  `Expr.beq`, because `Nat.add a k` and the surface `a + k` are definitionally equal but
  not syntactically), so an ill-shaped certificate fails with a message naming the node.
  The S0 prototype's checker builds the term and lets the **kernel** do the type check
  (the `Conc` it returns is a claim, not a verified premise); this is sound but gives a
  coarser error. S1 adds the shape checks; neither layer is trusted for soundness.
* The checker **does not** call `assignLate`; it returns the `Expr` and the tactic does
  `TacticM.assign g e` once, at the root. The kernel infers the whole term then.
* The checker may call `TacticM.inferType` on intermediate nodes as a *debugging* aid
  (better messages); this is optional and not a soundness requirement.

### 5.3 Side conditions as checked arithmetic

Rules with a coefficient side condition (gcd, `0 < m`, `r < a`, `k > 0`) take a
**proof of the side condition** as an argument, built by the checker as `rfl` on the
concrete numerals:

```wiz
-- inside the checker, for the dark-shadow rule:
h := Expr.refl (Expr.app (Expr.app (Expr.const "Nat.beq") (nat a)) (nat b))   -- if the lemma takes a Bool
```

The kernel computes `Nat.beq`/`Nat.gcd`/`Nat.mod` on the numerals; if the search's
coefficient is wrong, the `rfl` does not typecheck and the whole proof is rejected. This
is the "arithmetic certificate for each coefficient comparison" from R7: the comparison
is not trusted to the tactic's `Nat` arithmetic, it is replayed by the kernel.

(If a side condition is a `Prop` with a decidable Boolean view, state the lemma with the
Boolean equality as the hypothesis (`Nat.beq a b = .true`), so `rfl` is the proof; this
is the pattern `Nat.beq_eq`/`Nat.cmp_eq` already uses, `lib/Nat.wiz:141–176`.)

### 5.3a Two worked certificates

**`a ≤ b`, `c ≤ d ⊢ a + c ≤ b + d`.** The certificate is one `add` node:

```
Cert.add a b c d (Cert.hyp i₁) (Cert.hyp i₂)
```

and the checker emits

```wiz
Nat.add_le_add a b c d (Expr.var i₁) (Expr.var i₂)
```

whose type is `Nat.Le (Nat.add a c) (Nat.add b d)`. The kernel's conversion sees the
goal's `a + c` (the surface `HAdd.hAdd` or `Nat.add`) as the same term; the assignment
is `assign`, so the kernel infers the whole application. This is the case no single BFS
chain can prove.

**`h : a + k = c ⊢ a ≤ c`.** The certificate is one `leOfEqAdd` node:

```
Cert.leOfEqAdd a c k i true
```

and the checker emits

```wiz
Nat.le_of_eq_add' a c k (Expr.var i)
```

whose type is `Nat.Le a c` (the theorem is `lib/Nat.wiz:310–313`). The `true` says the
hypothesis is oriented `a + k = c`; the other orientation uses the existing
`Nat.le_of_eq_add` (`lib/Nat.wiz:306–308`). This is exactly the skipped P1 case.

### 5.4 The kernel check, end to end

```
search (untrusted)  ──►  Cert
                           │
                     check (lib/Omega.wiz, untrusted for soundness)
                           │
                           ▼
                  Expr proof term (hole-free)
                           │
                TacticM.assign g e
                           │
                  Wiz.infer (kernel, proof := true)
                           │
             type e  ~~  goal type  (conversion)
                           │
               addDeclSorted re-checks the declaration
```

* **Soundness**: if `assign` succeeds, the kernel says `e : G`. A wrong certificate
  either fails `check` (ill-formed) or produces an `e` whose type is not `G`; the kernel
  rejects it. There is no path from a search bug to a proved false goal.
* **Trust**: the kernel, its `Nat` primitives/GMP (already in the TCB, R2), and the
  library lemmas. **No solver axiom**, no `smt✝`, no `native✝`, no `assignLate`.
* **Axiom audit**: every new lemma is `#print axioms`-clean; the test group asserts it.
  A mechanical scan already exists for `lib/` (`Tests/Groups/Numerics.lean`, R4), and the
  new module must not add a ledger row.
* **Caching**: only the certificate/proof term may be cached, never the verdict (R5).

---

## 6. The checking plan (tests)

### 6.1 The smallest acceptance test

Positive — one linear goal closed by a kernel-checked proof, with witnesses that the
BFS cannot close it:

```wiz
import Nat
-- `h₁` and `h₂` are two independent chains: no single BFS path proves this.
def omegaSum (a b c d : Nat) (h₁ : Nat.Le a b) (h₂ : Nat.Le c d) :
    Nat.Le (a + c) (b + d) := by
  omega
#print axioms omegaSum
```

Expected: `'omegaSum' does not depend on any axioms`.

The P1 goal that is skipped today is the second positive:

```wiz
import Nat
def omegaSumConst (a b : Nat) (h : Nat.add a b = 3) : Nat.Le a 3 := by
  omega
#print axioms omegaSumConst
```

Expected: `'omegaSumConst' does not depend on any axioms`. (If the prototype still hits
the instance-argument conversion, this stays a documented S2 acceptance test and the
note says so in §8 — it is not allowed to become a silent pass.)

Negative — one non-linear goal refused with a positioned message:

```wiz
import Nat
def omegaNonlinear (a b : Nat) : a * b = b * a := by
  omega
```

Expected: exactly one error, at the `omega` token, of the form

```
4:3: error: omega: non-linear: `Nat.mul` occurs in the goal (multiplication is outside
the linear Nat fragment)
```

The test must assert **both** the message fragment and the `line:col` (the test
harness renders `Msg.render` as `line:col: error: …`, `Wiz/Elab/Command.lean:58–61`).
The S0 tests use the explicit `Nat.Le`/`Nat.add` forms (as the existing omega tests
do); `Omega.asLe`/`asLt` also read the class forms `LE.le`/`LT.lt`, but the notation
path is only exercised once the kernel's projection conversion is tested, so it is not
claimed here.
A message without a position is a failing test: a refusal the user cannot locate is the
"silent fallback" in a different costume.

### 6.2 The group

Add the cases to the existing `tactics` group (`Tests/Groups/Tactic.lean:100`) where the
current omega cases already live (`:458–472`), rather than creating a new group: the new
cases are the continuation of the same interface, and the shard selector already exists
(`.github/test-shards.json`, `"tactics"`). If the group grows beyond the shard budget,
split a new `omega` group and add its shard entry; do not leave a group unselected
(`scripts/check-shards.py` is the gate).

### 6.3 Negative controls (the tests that keep it honest)

1. **False goal**: `def bad (n : Nat) : n < n := by omega` must fail with
   `omega: no proof` (or the integrality-gap message), never close.
2. **False consequence of hypotheses**: `h : a < b` ⊢ `b < a` must fail.
3. **Non-linear in a hypothesis**: `h : a * b = 3` ⊢ `a ≤ 3` must fail with the
   non-linear position on the hypothesis, not on the goal.
4. **Corrupted certificate**: expose a test-only `omega_cert_with (c : Cert)` that
   checks a certificate supplied by the test (or a Wiz `#eval` over `check`), and assert
   that a certificate whose `fm` parameters are swapped is rejected by `check`/`assign`.
   This is the regression test for "the checker is a checker, not a proof by assertion".
   If exposing the checker to surface syntax is too invasive, put the test at the Lean
   level: build a wrong `Expr` and assert `kernelInfer` rejects it; the important thing
   is that *some* test would fail if the checker stopped consulting the kernel.
5. **Axiom audit**: `#print axioms` on every positive theorem, plus the existing R4 scan
   that `lib/` contains no `smt`/`native_refl`/`native_decide` use.
6. **Budget**: a goal with many atoms must return `omega: budget exhausted (N)` within a
   bounded time, not hang the test run; a timeout is a failure.
7. **Position**: the LSP diagnostic for the non-linear case has a range at the `omega`
   token (reuse `tacticLsp`, `Tests/Groups/Tactic.lean:511–519`), so the refusal is
   positioned in the language server, not only in the CLI renderer.

### 6.4 Build/run

All builds/tests go through `heavy`: `heavy --rsync -- lake build wiz tests` and
`heavy --sshfs -- lake test -- '=tactics'` (or a single case with
`heavy --sshfs -- .lake/build/bin/tests --run tactics N`). The new module is discovered
by `Tests.loadedModules "lib"`, so no registry edit is needed. Test counts are reported
as `N passed, M failed, K skipped`; a skipped case is not a pass.

The test must run **on the build node**, not on the controller: a `--rsync` build copies
`.lake/build/bin` back, and the binary's ELF interpreter is a store path that exists on
the build node, not on the controller. Running it locally gives
`no such file or directory` at exec, which is the documented copied-back-artifact case
(`AGENTS.md`), not a test failure. A direct exec from the `--sshfs` mount can give
`Permission denied` (the mount is treated as noexec for the executable); the working
recipe is one `--rsync` job that builds and runs on the same node:

```sh
heavy --rsync --timeout 1800 -- sh -c \
  '. /workspace/wiz-env.sh && lake build wiz tests && .lake/build/bin/tests --run tactics N'
```

or a `lake test -- '=tactics'` job with the same transport. A copied-back binary must
not be executed on another node's store either; if a pin is needed for a node-local
store path, say why in the report.

---

## 7. Ordered slices

Each slice lands green on its own, with the previous tests still passing. The order is
chosen so that the *sound* part is complete early and the *complete* part never weakens
the fragment boundary.

### S0 — certificate skeleton and the chain/add prover (this branch, prototype)

* New `lib/Omega.wiz`: `Omega.Cert`, `Omega.Atom`, `Omega.check`, reification
  (`Omega.linearize`), the rule lemmas that already exist (`Nat.le_trans`,
  `Nat.add_le_add`, `Nat.le_add_right/left`, `Nat.le_of_eq*`, `Nat.le_antisymm`,
  `Nat.le_of_eq_add'`), and the tactic `omega_cert` (initially a separate name; the
  existing `omega` is untouched).
* The prover is a bounded DFS for `≤`/`=` with the **add** rule, so the two positive
  acceptance tests above can be attempted.
* Refusals: non-linear (positioned), non-Nat relation, non-atom hypothesis, budget.
* Exit: `#print axioms` clean for the positive cases; the negative case's position
  pinned; the `tactics` group green.

### S1 — FM and the refutation discipline

* Prove `Nat.omegaFM` (`lib/Omega.wiz`), `scale`, `cancelR/L`, and wire the FM rule into
  the search.
* Add the goal wrapper (`Nat.le_or_lt`, the equality trichotomy or two-direction
  antisymmetry) and the refutation path with `Nat.not_add_succ_le`/`False.elim`.
* Completeness claim: difference logic (unit coefficients) only. A system whose real
  shadow is feasible but which has coefficients > 1 is refused with
  `omega: incomplete: integrality gap …` (positioned), not "no proof".
* Acceptance: `h : a + k ≤ b + k ⊢ a ≤ b`; `h₁ : a ≤ b, h₂ : c ≤ d ⊢ a + c ≤ b + d`;
  `h : 2*a ≤ 2*b ⊢ a ≤ b` (needs FM + cancel; in the input fragment the coefficient is
  written `a + a`, §2.1 — the same coefficient-2 system); a false goal refused; a budget
  case.

**Landed on `agent/omega-s1` (2026-11-23).** The search emits `Omega.RCert` and the
checker `Omega.checkR` replays it. `Nat.omegaFM` was already proved in S0; S1 adds the
`cancel` nodes (`Omega.cancelSame`, `Omega.cancelMoreL/R`), the negated-goal wrapper
(`Nat.le_or_lt`/`Or.elim`/`False.elim`), the implicit `0 ≤ x` items
(`Nat.zero_le`), the integrality detector, and the measured FM budget. The
unconditional successor edge is gone from `Omega.allEdges`/`Omega.Cert`; the additive
path search remains the fast path, not a fallback. The status table is §8.1b.

### S2 — equality elimination and substitution

* Add the equality path: `eqView`, `Nat.le_of_eq`/`le_of_eq_sym`, `Nat.le_of_eq_add'`,
  the transport lemma for substituting an equality (built from `Eq.substProp`/`Eq.mp'`
  or `transp`), and the trichotomy lemma for `=`.
* Remove the `omegaDirectAdd` special case by folding it into the general rule.
* Acceptance: the P1 `h : a + b = 3 ⊢ a ≤ 3` (skipped today); `h : a = b ⊢ a + c ≤ b + c`;
  `h : a = b, h' : b = c ⊢ a = c`.
* If the instance-argument conversion still fails, the fix belongs here (use the
  hypothesis' own term and an explicit transport, not a raw `le_trans` with a
  normalized middle); the note's honesty ledger records whether it is fixed.

### S3 — Cooper split and divisibility (completeness for `F_lin(Nat)`)

* Prove in `lib/Nat.wiz` (new, no axiom): `Nat.mod_lt`, `Nat.div_add_mod`,
  `Nat.div_unique`/`Nat.mod_eq` as needed, and the gcd divisibility lemma
  (`Nat.gcd_dvd_left/right`, `Nat.dvd_of_mod_eq_zero` — names to settle).
* Add `Omega.split` to the certificate: a node carrying `x`, the modulus `a`, the residue
  `r`, and the branch certificate; the checker builds the `div_add_mod`/`mod_lt` case
  split and the branch proofs.
* Search: lcm/residue enumeration for the variable with the smallest lcm; exact
  coefficient-gcd contradiction.
* Acceptance: `h : 2*a = 1 ⊢ False`; `h : 2*a = 2 ⊢ a = 1`;
  `h₁ : 2*a ≤ 3, h₂ : 1 ≤ 2*a ⊢ a = 1`; and a case that requires the `−∞` branch.
* Exit: the first **complete** claim for `F_lin(Nat)`, with the fuel bound documented.

### S4 — subtraction and the `Nat` coefficient forms

* Add `Nat.sub` only where a side condition `b ≤ a` is available
  (`Nat.add_sub_of_le`, `lib/Nat.wiz:365–369`), so the input can use `a - b` when the
  hypotheses prove `b ≤ a`. Outside that side condition, refuse.
* Acceptance: `h : b ≤ a ⊢ a - b + b = a`; a goal with `a - b` and no side condition is
  refused, not guessed.

### S5 — `Int`

* A second instantiation of the same calculus over `Int` (`lib/IntOrder.wiz`): sign
  split on `Int.ofNat`/`Int.negSucc`, the order lemmas already present, and the
  certificate's `Atom` parameterized by the carrier. This is where negative coefficients
  become natural; the `Nat` fragment stays the default for `Nat` goals.
* Acceptance: `h : x ≤ y ⊢ x - 1 ≤ y`; `h : x < y ⊢ x + 1 ≤ y`; `h : 2*x = 3 ⊢ False`
  (integer, not rational); a `Q` goal is still refused (not a linear order carrier here).
* Interop: a `Nat` goal must be proved by the Nat engine, not by casting to `Int` and
  back, unless the cast lemmas (`Int.ofNat` injectivity, `Int.ofNat_le`) are proved and
  the final transport is certified.

### S6 — replace `omega`, delete the BFS, update the docs

* Make `omega` the certificate engine; delete `omegaBFS`/`omegaEqEdges`/`omegaDirectAdd`
  and the 10,000-node budget. Keep `omega`'s surface syntax and messages compatible
  where they are tested (`omega: non-linear`, `omega: no proof`) and add the new
  positioned reasons.
* Update `docs/numerics-trust.md` §R7 from "deferred plan" to the implemented design,
  and `Tests/Groups/Numerics.lean`'s "R7 is a plan only" line.
* Acceptance: the whole `tactics` group, the omega cases, the axiom audit, and a
  compatibility case for every old positive; no silent fallback (the BFS is gone, not
  kept behind a flag).

---

## 8. Honesty ledger

| Claim | Status on this branch | Evidence / caveat |
|---|---|---|
| `omega` adds no solver axiom | true today and by design | `#print axioms` on the positive tests; the rules are `lib/` theorems; no `smt✝`/`native✝` |
| Every step is kernel-checked | true for the certificate engine: `assign` calls `kernelInfer` (implicitly, the kernel's `inferCore`) and `addDeclSorted` re-checks | `Wiz/Elab/Term.lean:4550–4561`; the checker builds hole-free terms; no `assignLate` |
| The search is untrusted | true: a wrong search produces a certificate the checker/kernel rejects | §5.4; the negative-control test in §6.3(4) |
| The fragment is linear and refuses the rest | true for the prototype's checks (non-linear heads, non-Nat relations); the exact boundary is §2.1 | positioned refusals; the test asserts `line:col` |
| Sound for all of `F_lin(Nat)` | true for S1's rule set (each rule is a theorem); the *search* may fail to find a proof | §3; no rule assumes integrality |
| The real shadow is a theorem, not a solver step | true: `Nat.omegaFM` and `Omega.cancelSame`/`cancelMoreL`/`cancelMoreR` are proved in `lib/Omega.wiz` | `#print axioms Nat.omegaFM` is empty; the FM/cancel nodes are `lib/` applications |
| S1 is complete for difference logic | **yes modulo the named budget**: unit coefficients, with the implicit `0 ≤ x` (`Nat.zero_le`) bounds; the FM search eliminates to a constant contradiction or reports `incomplete` | cases in §8.1b; no coefficient > 1 is accepted as a verdict |
| An integrality gap is refused, not guessed | true: a feasible real shadow with a coefficient > 1 is `omega: incomplete: integrality gap …` (positioned) | the S1 gap case; `Omega.maxCoeff` is the detector |
| A search budget cut is loud | true: `omega: incomplete: budget exhausted (512)`; the S1 budget case | `Omega.fmFuel = 512`, measured; no "no proof" on exhaustion |
| Complete for `F_lin(Nat)` | **not yet**: S1 is complete only for difference logic; S3 adds Cooper + div/mod lemmas | before S3, an integrality gap is refused as incomplete, never reported as "no proof" or closed by a guess |
| Complete for `Int` | **not yet**: S5 | `Int` is P1 today (`lib/Prelude.wiz:1779–1780`) |
| The old BFS stays until S6 | true on this branch: `omega` is untouched and `omega_cert` is separate | no regression risk while the prototype is incomplete; the switch is atomic and deletes the BFS |
| "Presburger is cheap" | **false**; no efficiency claim | Oppen 1978 (triply exponential); the fuel bound is an interface, and running out is loud |
| Atom identity is syntactic | true; a definitional-but-not-syntactic equality is incompleteness, not unsoundness | §2.2; message asks the user to unfold |
| Coefficient arithmetic is trusted | **no**: side conditions are `rfl`-checked by the kernel | §5.3; a wrong coefficient fails typechecking |
| The P1 skipped case is closed | **check §8.1**: the prototype either closes it (then the test is unskipped) or the note records the exact failure, not a workaround | `Tests/Groups/Tactic.lean:465–466` |
| No external solver / no process | true: no `runSolver`, no Z3, no cache of verdicts | the rule set is all `Nat` lemmas |
| The `Nat` kernel/GMP is trusted | unchanged, as everywhere | R2; `omega` adds no new TCB |
| The certificate is cached as a verdict | **never**: only proof terms may be cached, re-checked on replay | R5; the answer cache is not touched |

### 8.1 Prototype status (this branch)

Verified on the build node (`noobnoob`, `heavy --rsync`, `lake build wiz tests` then
`tests --run tactics N` for one case, and `lake test -- '=tactics'` for the group;
`N` below is the 0-based `--run` index):

| Case | Result |
|---|---|
| `omega_cert: two independent chains close by adding the inequalities` (case 54) | **passed**, `#print axioms omegaSum` empty |
| `omega_cert: an equality with a sum side gives a bound (the P1 goal)` (case 55) | **passed**, `#print axioms omegaSumConst` empty |
| `omega_cert: cancelling a common summand` (case 56) | **passed** after the `Nat.add`-form `Omega.cancelR` wrapper; the raw `Nat.le_of_add_le_add_right` premise failed `assign` with an instance-argument mismatch (expected and inferred both printed `Nat.Le (a + k) (b + k)`) |
| `omega_cert refuses a non-linear goal at the tactic's position` (case 57) | **passed**, error at `3:3` (`3:3: error: omega: non-linear …`) |
| `omega_cert refuses a false linear goal` (case 58) | **passed** (11.5 s in the group run at the 64-expansion budget) |
| `omega_cert: the real-shadow lemma is proved, not assumed` (case 59) | **passed**, `#print axioms Nat.omegaFM` empty |
| `omega_cert does not reverse a hypothesis` (case 60) | **passed** (12.5 s in the group run) |
| `omega_cert refuses a non-linear hypothesis` (case 61) | **passed**, `omega: non-linear` |

The full group was run with `lake test -- '=tactics'` on the build node:
**67 passed, 0 failed, 1 skipped** (449.5 s; the skip is the pre-existing `omega P1`
case, `Tests/Groups/Tactic.lean:465–466`; the new `omega_cert` P1 case is case 55 and
is green). The 64-expansion budget is what made the two failed-search cases 11–13 s
instead of the 19 s seen at 200 and the multi-hour hang seen at 2000.

The two acceptance tests that matter for R7 are the first two rows: a linear goal closed
by a kernel-checked proof that the BFS cannot close, and the previously skipped P1 goal
closed with no axiom. The negative non-linear case is the third row.

**Lesson recorded.** The 2000-node DFS was not a proof search limit but a
*test-runtime* limit: with the growing successor chain and a path-length `seen` list,
each expansion compares longer and longer terms, so a failed search costs far more than
its node count suggests. At 200 expansions a failed search still took 19 s (cases 58 and
60); the S0 budget is now **64** expansions. S1 deletes the unconditional successor edge
(the additive path search can no longer grow a successor chain) and measures the FM
budget separately (`Omega.fmFuel = 512` pair attempts). A budget cut is a loud
`omega: incomplete: budget exhausted (N)` message, never a hang and never "no proof".

### 8.1a What was tried and did not work

* **Raw `Nat.le_of_add_le_add_right` in the cancel rule.** `assign` rejected
  `Nat.le_of_add_le_add_right k a b h` with a type mismatch whose two types printed
  identically (`Nat.Le (a + k) (b + k)`); the difference is the `+` instance argument.
  The fix is the `Omega.cancelR` wrapper stated with explicit `Nat.add`, plus a test
  hypothesis written with `Nat.add`. This is the same instance-argument problem the P1
  skip mentioned; the equality-add rule `Nat.le_of_eq_add'` did **not** hit it (the
  hypothesis was already `Nat.add`-formed).
* **Raw `Nat.omegaFM` in the S1 checker.** The certificate's linear forms are
  `Nat.add`/`Nat.mul` trees, so the FM step goes through `Omega.fm`, a wrapper with the
  arithmetic written explicitly (the `Omega.cancelR` bridge). The cancellation lemmas
  `Omega.cancelSame`/`cancelMoreL`/`cancelMoreR` are stated the same way; the ring
  identities inside them are `NatExpr.prove` terms, not trusted tactic arithmetic.
* **Coefficient `2*a` and surface `*`.** Two attempts to accept a `Nat.mul`/surface-`*`
  coefficient in the input were dropped. The first hit the S0 instance-argument mismatch
  at `assign` (expected and inferred both printed `Nat.Le (2 * a) (2 * b)`); switching
  the checker to `TacticM.inferType` for the hypothesis types did not fix the surface
  `*` instance (the same class as the S0 `Nat.add` cancellation hypothesis). The second,
  an explicit `Nat.mul 2 a` test, exposed that a multiplication scan has to know the
  operation's private prefix count. The final S1 boundary is the note's original one:
  coefficients are repeated occurrences (`a + a`), and any `Nat.mul`/`HMul`/`Mul.mul` in
  the input is refused. The guard is the S0 one: `Expr.hasOp` on the goal and its
  normalized form, plus `omegaHypsBad`/`omegaEqBad`, which normalize **each relation
  side**; that side normalization is what exposes a surface `*` that the whole-type
  scan misses. Subtraction is a separate head list with its own message. The arithmetic,
  the coefficient-2 FM step and the kernel check are identical; the certificate's
  `formExpr`/`Nat.omegaFM` still use `Nat.mul` internally, and that is not an input
  occurrence.
* **`failsLib` for the negative cases.** It uses the default loader, which has no
  `Omega`; the cases need `failsLibs` (the all-lib loader). This is a test-harness
  detail, not a tactic bug.
* **`Expr.ap5` for `Nat.add_le_add`.** It takes six arguments after the head, so the
  checker builds it with `Expr.mkApp`; `ap5` stopped at five.
* **`Omega.nth?`.** `?` is not an identifier character in Wiz; renamed to `Omega.nth`.
* **The initial `Eq.mp'` transport.** A lambda motive without a binder annotation left
  the motive as a metavariable; `Omega.leL`/`leR` with `fun (t : Nat) => …` elaborate.

### 8.1b S1 status (FM and the refutation discipline)

Verified on the build node with `heavy --rsync` for the build and the same job for the
tests (`.lake/build/bin/tests --run-case tactics N`); the group run is
`heavy --rsync -- lake test -- '=tactics'`. Final run, 2026-11-23:
`wiz check lib/Omega.wiz` green; the six S1 cases and the two restored non-linear
refusals (cases 57 and 61) pass individually; the group is **73 passed, 0 failed,
1 skipped** (the skip is the pre-existing `omega P1` case, unchanged).

| Case | Result |
|---|---|
| `omega_cert S1: a difference-logic goal by real-shadow refutation` | **passed**, `#print axioms omegaLtTrans` empty |
| `omega_cert S1: the real shadow proves 2*a ≤ 2*b ⊢ a ≤ b` | **passed**, `#print axioms omegaTwo` empty |
| `omega_cert S1 refuses a false goal` | **passed**, `omega: no proof` |
| `omega_cert S1 reports an integrality gap, not no proof` | **passed**, positioned `omega: incomplete: integrality gap …` |
| `omega_cert refuses subtraction at the tactic's position` | **passed**, positioned `omega: outside the linear Nat fragment` |
| `omega_cert S1 reports budget exhaustion as incomplete` | **passed**, `omega: incomplete: budget exhausted (512)` |

The FM budget is **512** pair attempts (`Omega.fmFuel`): the passing FM cases use fewer
than a dozen pair attempts, and the budget case (25 lower and 25 upper bounds on one
atom, 26×26 pairs) exhausts it in a bounded time and reports incompleteness. The
additive path search keeps the S0 **64**-expansion budget (`Omega.pathFuel`), now without
the unconditional successor edge: a failed path search can no longer grow a successor
chain.

Measured in that group run (harness wall time, including the per-case driver): the six
S1 cases took 13.317, 12.726, 13.583, 13.975, 12.804 and 15.029 s. The no-search
`omega_cert` refusals are 12.7–13.9 s and the base cases 4–5 s; the budget case is
~1.5–2 s above the no-search refusals, so 512 pair attempts is about two seconds and the
passing FM cases are indistinguishable from the no-search ones. That is the measurement
behind `Omega.fmFuel = 512`: a failed refutation is bounded, while the passing cases need
only a handful of pairs. The group total was 591.760 s for 74 cases.

The `2*a` case is written in the source in the fragment's repeated-occurrence form,
`Nat.add a a` and `Nat.add b b` (likewise the integrality-gap case). The coefficient is
2, the FM step is the same and the kernel checks the same certificate; a `Nat.mul` in
the input would be refused as non-linear (§2.1). The note's §7 acceptance is stated
mathematically as `2*a`, and this is that system.

### 8.2 Why this is stronger than the alternatives

* **Bigger BFS**: buys completeness only by search, and still cannot combine two
  hypotheses; the fragment boundary remains implicit. A certificate buys completeness
  with no new trust.
* **SMT call**: adds `smt✝` per use (R4/R5) and makes the toolchain and the solver part
  of the TCB. `omega` must not.
* **A solver axiom / `unsafe` shortcut**: rejected outright; a certificate is the point.
* **Silent fallback to `omegaBFS`**: would make the fragment boundary unpredictable and
  could turn an incomplete case into "proof by search"; the plan deletes the BFS instead.

### 8.3 Wiz implementation notes (from the S0 prototype)

These are compiler-level facts the next slice should not rediscover:

* **Identifiers cannot contain `?`.** `Omega.nth?` is a parse error (`unexpected
  '?'`); the prototype uses `Omega.nth`.
* **`Expr.apN` stops at `ap5`.** `Nat.add_le_add` takes four Nat arguments and two
  proofs (six after the head), so the checker builds it with `Expr.mkApp` and an
  explicit argument list; `ap5` is only enough for `Nat.le_trans`.
* **Leading-dot constructors need an expected type.** A term `.cons x .nil` in an
  unannotated `let` gives `the syntax term.dotIdent has no meaning`; annotate the
  binding (`let succEdge : List (Expr × Omega.Cert) := …`) or write the type ascription.
  The same applies to `.none` in a `let`.
* **`Eq.mp'` with a lambda motive needs the binder annotated**, or the elaborator
  leaves the motive as a metavariable and reports a type mismatch on the proof
  argument. The prototype isolates the transports in `Omega.leL`/`Omega.leR`
  (`Eq.mp' (fun (t : Nat) => …)`), which elaborate.
* **A `partial def` is the safe recursion form** for the checker and the DFS: the
  structural termination checker does not see through a monadic `do` bind, and Wiz's
  `mutual` does not accept `partial` definitions (see `lib/Prelude.wiz:1712–1713`),
  so the DFS uses an explicit stack and one recursive function.
* **Do not run a copied-back binary on the controller.** The ELF interpreter is a
  store path from the build node; `--sshfs` exec can be `Permission denied` (noexec
  mount). Build and run in one `--rsync` job (§6.4).

---

## 9. Open decisions for the coordinator

1. **Where the production code lives.** The calculus is a set of `Nat`/`Int` lemmas and
   a checker, so `lib/Omega.wiz` is the natural home; `Wiz/Elab/Tactic.lean` needs no
   change unless the checker wants a host-side `inferType` aid. R7 says that file is
   held by another lane, and this design keeps it out of the path.
2. **The switch.** Replace `omega` in one commit after S3/S5 pass the full `tactics`
   group, or land `omega_cert` first and alias `omega` to it later? Recommendation: land
   the engine and tests under `omega_cert`, then switch `omega` and delete the BFS in
   one commit (S6), so no user sees a half-complete `omega`.
3. **Equality atoms.** Treat `=` as two `≤` (sound, incomplete for non-unit
   coefficients until S3) or implement substitution first (S2)? The P1 case wants
   substitution/`le_of_eq_add'`; both are in S2, so the order inside S2 is free.
4. **Atom identity.** Syntactic (`Expr.beq`) first. A definitional comparison would need
   `isDefEq` per pair and a canonical representative; it is a completeness improvement,
   not a soundness one. Do not do it before S3.
5. **Test group.** Add to `tactics` (already selected by a shard) or create `omega` and
   add a shard entry? Recommendation: `tactics` until it exceeds the shard budget, then
   a new group; never an unselected group.
6. **Docs.** After S6, rewrite `docs/numerics-trust.md` §R7 from "deferred plan" to the
   implemented calculus, and change `Tests/Groups/Numerics.lean`'s "R7 is a plan only".

---

## 10. References

* W. Pugh, *The Omega Test: a fast and practical integer programming algorithm for
  dependence analysis*, SC '91.
* D. C. Cooper, *Theorem proving in arithmetic without multiplication*, 1972.
* D. C. Oppen, *A 2^2^2^(pn) upper bound on the complexity of Presburger arithmetic*,
  1978.
* Lean 4 `omega` (`Lean/Elab/Tactic/Omega`): a proof-producing implementation over
  `Int`/`Nat` with no solver axiom; the model for "certificate, not oracle".
* `docs/numerics-trust.md` §R7 (`:192–208`); `wiz-notes/sota-numerics.md` §5.7
  (`:292–297`); `lib/Prelude.wiz:1771–2079`; `lib/Nat.wiz`; `Wiz/Core/Check.lean`;
  `Wiz/Elab/Term.lean:4550–4561, 4604–4638`.
