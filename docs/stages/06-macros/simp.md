# `simp`: a simplifier whose algorithm is Wiz

`simp` rewrites the goal with a list of equations until no rule applies, then stops.
The **algorithm** (rule order, direction, fuel, messages) lives in Wiz, in
`lib/Prelude.wiz`; the host (`Wiz/Elab/Tactic.lean`, `Wiz/Elab/Term.lean`) provides one
small request, `Tac.rewriteAt`, that matches a rule and builds the transport. This is
deliberate: `simp` must be runnable by the self-hosted frontend once its `Tac`/`Expr`
layer reaches parity, so the tactic is ordinary Wiz code, not a second engine in Lean
(`wiz-notes/simp-design.md` §4.3, §6.6).

```
def ex (a b : Nat) (h : a = b) (P : Nat → Prop) (pb : P b) : P a := by
  simp [h]            -- ⊢ P b
  exact pb

def ex2 (n : Nat) (h : (k : Nat) → k + 0 = k) : n + 0 = n := by
  simp [h]            -- the rule's k is found by matching: ⊢ n = n
  rfl
```

## Syntax and semantics (S1)

```
simp                          -- the default set; empty today (no [simp] attribute yet)
simp [h, Nat.add_zero]        -- add these equations
simp only [h]                 -- exactly these
simp only []                  -- identity
simp [← h]                    -- use h right to left
```

* A rule is a complete term whose type is a telescope `∀ x₁ … xₙ, lhs = rhs`. The
  telescope variables are **matched** against a subterm of the goal: this is what makes
  `simp [h]` work for `h : (n : Nat) → n + 0 = n`, where `rw h` cannot (it needs `h n`).
* Rules are tried in list order, each in the direction written (`← h` flips it), and a
  rewrite restarts the pass. A pass that changes nothing ends `simp` **successfully**:
  `simp` is not `rw`, so no match is not an error, and the goal is left as it is.
* There is **no automatic closer** in S1. `simp` only rewrites; `rfl`, `exact` or
  `assumption` are written by the user (Wiz keeps computation and closing explicit;
  `simp only []` is the identity, unlike Lean's beta/iota reduction). This is why the
  stage's tests end in `exact`/`rfl`.
* `simp only []` uses no rules and changes nothing.
* A rule that is not an equation after its binders is an error:
  `simp: expected an equation: not an equation`. A bare proposition `h : P` is not
  rewritten to `True` (Wiz has no propositional extensionality).
* **Fuel.** At most `Simp.fuel` (100) rewrites; exhausting it is
  `simp: maximum steps (100) reached: possible loop (…)`, never a silent "normal form".
  A rule that rewrites a term to itself is not a step, so it is skipped. Direction is
  explicit; a rule like `Nat.add_zero` is never run backwards automatically (that would
  grow `n` to `n + 0` forever).

## The host request: `Tac.rewriteAt`

`Tac.rewrite` takes a *complete* equation: `rw (Nat.add_zero n)`. Matching a rule needs
fresh metavariables and unification, and the reflected `Expr` has no metavariable, so
that part stays host-side (the Wiz driver never sees a metavariable):

```wiz
inductive RewriteResult where
  | noMatch
  | rewritten (goal : Nat) (type : Expr)   -- the new goal and its type, reflected
  | error (msg : String)

| rewriteAt (g : Nat) (lemma : Expr) (rtl : Bool) (all : Bool)
    (k : RewriteResult → Tac)
```

What `Tac.rewriteAt` does (`Wiz/Elab/Term.lean`, helpers in `Wiz/Elab/Tactic.lean`):

1. It reads the rule's type **as written** when its head is a constant (`ruleType?`:
   the declaration's type with the term's level parameters and arguments, and a fresh
   metavariable for each remaining binder). This matters: an equation at a data type
   *computes* when evaluated (`b ^ 0` is `1`, so `b ^ 0 = 1` evaluates to `True`), and
   the evaluated type has lost the sides. For a local hypothesis it uses the kernel's
   (evaluated) type. Rules whose pattern *computes to a data value with variables*
   (`List.map f (x :: xs)`, `Option.map f (some a)`) are refused: the goal's value has
   computed those already, so there is nothing left to rewrite (a closed data pattern
   is matched structurally).
2. It strips the `∀` binders (metavariables), then matches the pattern side (`lhs`, or
   `rhs` for `rtl`) against each subterm of the goal type in pre-order (`matchRule`),
   unifying the rule's metavariables. `typeOfUnifying?` then solves what the match left
   (implicit parameters, from the arguments' types); every metavariable must be
   determined.
3. The matched **subterm** is what the transport abstracts (`abstractOccAt`: every
   occurrence, or the first), because the rule's side may equal it only up to
   conversion (`List.append x []` is written `x ++ []` in the lemma).
4. It builds the same `transp`/`cast` proof as `rewrite` and returns the new goal and
   its reflected type. No match changes nothing; the kernel checks the finished term.

The Wiz side then commits the new goal (`replaceMainGoal`), restarts the pass, and reads
the returned type (no extra `goalType` crossing per step). The request is deliberately
the *only* host addition: there is no simplifier, no discharger and no default set on
the host. `Tac.rewrite` is unchanged (it could be expressed as `rewriteAt` with
`all := true`).

## Why not a host-side engine

A whole simplifier in `Wiz/Elab/Simp.lean` would save interpreter crossings (one
request per run instead of one per rule per pass), and matching, occurrence selection
and context transport all need `Term` anyway. It was rejected (user decision,
2026-11-14) because the algorithm would then have to be written a second time for the
self-hosted frontend, and `simp` would stop being a Wiz library tactic: rule order,
`only`, direction, fuel and later `[simp]`/`simp?` policy are exactly the parts that
must stay changeable in Wiz. The accepted costs and their mitigations are in
`wiz-notes/simp-design.md` §4.3 and §9 (host-side scan per rule, the new type in the
answer, no re-reflection per step).

## What remains

* **S2: `[simp]` and the default set.** `lib/SimpLemmas.wiz` is the written set (Nat
  powers, Bool, List, Option/pairs, Int); it needs the attribute, the default-set read
  (`Tac.getSimpLemmas`), `local attribute`, and caching. Until then `simp` with no list
  rewrites with nothing, and `simp [..]` is the way to use the set.
* **S3: conditional lemmas and dischargers.** A rule with a premise before the equation
  currently does not fire (the premise metavariable is not determined); the Wiz
  discharger (`assumption`, `rfl`, recursive `simp`) and premise goals in
  `rewriteAt` are S3.
* **S4: `simp at h`, `simp?`.** Hypothesis surgery (`changeHyp`/`addHyp`/`clearHyp`) and
  used-rule tracking are host/Wiz additions of their own. Goal rewriting only for now.
* **S5: congruence and arithmetic.** Dependent arguments, ordered/AC rewriting, a rule
  index by head name; and matching rules whose pattern computes to a data value (S1
  refuses them: the goal value has already computed, so a usable occurrence needs a
  stuck form).
* **Occurrences.** `rewriteAt` takes `all : Bool` (all occurrences, or the first); an
  `Occurrence` with `nth`/`path` and an `at` syntax are follow-ups.
* **Selfhost parity.** Port `stripRule`/`matchRule`/`abstractOccAt` and the `Tac`
  branch to `selfhost/Kernel.wiz`/`selfhost/Frontend.wiz`, add goal/tactic state and
  `Expr` reflection there, and run the same sources (P1–P5 in the design note).

## Tests

The `tactics` group (`Tests/Groups/Tactic.lean`): a local equation under a context; a
quantified lemma matched (`(n : Nat) → n + 0 = n`); `simp only` order and restriction;
no match / `simp only []`; the step bound on a growing rule; a non-equation argument;
`#print axioms` clean; `rw` then `simp`; `← h`; and rules from `lib/SimpLemmas.wiz`
(`Bool.and_true`, `List.append_nil`).
