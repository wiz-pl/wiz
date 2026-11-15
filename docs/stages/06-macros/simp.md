# `simp`: a simplifier whose algorithm is Wiz

`simp` rewrites the goal with equations until no rule applies, then stops. The
**algorithm** (rule order, direction, fuel, the default set's use, messages) lives in
Wiz, in `lib/Prelude.wiz`; the host (`Wiz/Elab/Tactic.lean`, `Wiz/Elab/Term.lean`)
provides two small requests: `Tac.rewriteAt` matches one rule and builds the transport,
and `Tac.getSimpLemmas` hands the default set to the driver. This is deliberate: `simp`
must be runnable by the self-hosted frontend once its `Tac`/`Expr` layer reaches parity,
so the tactic is ordinary Wiz code, not a second engine in Lean
(`wiz-notes/simp-design.md` §4.3, §6.6).

```
import SimpLemmas

def ex (a b : Nat) (h : a = b) : a + 0 = b := by
  simp [h]            -- h first, then the default Nat.add_zero: ⊢ b = b
  rfl

def ex2 (a : Nat) : a + 0 = a := by
  simp                -- the default set (Nat.add_zero is registered with [simp])
  rfl
```

## Syntax and semantics

```
simp                          -- the default set (the registered [simp] lemmas)
simp [h, Nat.add_zero]        -- the listed equations, then the default set
simp only [h]                 -- exactly these; no default set
simp only []                  -- identity (no rules, no computation)
simp [← h]                    -- use h right to left
attribute [simp] Nat.add_zero -- add a theorem to the default set
attribute [simp 500] myLemma  -- with a priority (higher is tried first)
local attribute [simp] myLemma -- only in this module (dropped by its end)
```

* A rule is a complete term whose type is a telescope `∀ x₁ … xₙ, lhs = rhs`. The
  telescope variables are **matched** against a subterm of the goal: this is what makes
  `simp [h]` work for `h : (n : Nat) → n + 0 = n`, where `rw h` cannot (it needs `h n`).
* **Order.** Explicit arguments are tried first, in the order written, then the default
  set: higher priority first, and within one priority oldest registration first. A
  rewrite restarts the pass. `simp only [r₂, r₁]` therefore overrides registration order.
* **No match is not an error.** A pass that changes nothing ends `simp` successfully and
  leaves the goal as it is; `simp` is not `rw`. A rule that rewrites a term to itself is
  not a step (the host reports no match), so a degenerate rule cannot loop.
* **No automatic closer.** `simp` only rewrites; `rfl`, `exact` or `assumption` are
  written by the user (Wiz keeps computation and closing explicit; `simp only []` is the
  identity, unlike Lean's beta/iota reduction). This is why the tests end in
  `exact`/`rfl`.
* **Fuel.** At most `Simp.fuel` (100) rewrites; exhausting it is
  `simp: maximum steps (100) reached: possible loop (…)`, never a silent "normal form".
  Direction is explicit; a rule like `Nat.add_zero` is never run backwards automatically
  (that would grow `n` to `n + 0` forever).

## The `[simp]` attribute (S2)

`attribute [simp] f` registers an existing declaration. The command checks it and the
default set is data in the elaborator state, not in the kernel environment: `local`
drops it at the end of its module, and an imported module's registrations are replayed
(the command is not cacheable, so a cache hit re-runs it rather than losing the set).

The checks (with stable error codes):

| case | result |
|---|---|
| unknown name | error `unknown-declaration` |
| a constructor | error `simp-lemma-not-equation` ("is a constructor, not an equation") |
| an axiom (no value or witness) | error `simp-lemma-not-equation` ("must be a theorem, not an axiom") |
| not an equation after its `∀` binders | error `simp-lemma-not-equation` |
| a premise before the equation (`… → lhs = rhs`) | error `simp-lemma-conditional` (dischargers are S3) |
| already registered | warning "duplicate `[simp]` registration" (kept once) |
| `lhs = lhs` | warning "does not simplify" |
| the right side contains the left side | warning "possibly looping simp theorem" |

Orientation is not guessed: a lemma is used left to right, and the reverse would have to
be a separate registration. A looping rule still fails with the fuel message if it was
registered before the warning was seen.

**The default set.** Each library registers its own rules at the end of its file, so
importing it is enough: `lib/Nat.wiz` (`Nat.add_zero`, `Nat.mul_one`/`one_mul`/
`mul_zero`), `lib/Int.wiz` (the seven `Int` identities), `lib/Logic.wiz` (the oriented
Boolean algebra: `Bool.not_not`, `Bool.and_true`/`and_false`/`and_self`/`and_absorb`/
`and_not_self`, `Bool.or_false`/`or_true_right`/`or_self`/`or_absorb`/`or_not_self`,
`Bool.not_and`/`not_or`) and `lib/ListLemmas.wiz` (`List.append_nil`, `List.map_id`,
`List.map_map`, `List.map_append`, and the `length`/`reverse`/`filter`/`any`/`all`
normal forms). `lib/SimpLemmas.wiz` is the umbrella: `import SimpLemmas` brings all of
them, and it also keeps the lemmas that are deliberately explicit-only. The set is
deliberately small and confluent where it matters: commutativity, associativity and
distributivity stay out, and rules whose left side computes to a variable or a bare data
value (`0 + n`, `b ^ 0`, `[] ++ l`, `Prod.fst (a, b)`), patterns that compute to a
constructor carrying rule variables (`map f (x :: xs)`), `↔` lemmas and conditional
lemmas are not registered: matching is up to conversion, so such a rule would match
anything or have already computed away in the goal. The same rules remain available
explicitly (`simp only [Nat.zero_add]`), and S5 is where matching computes-away patterns
is revisited. The Boolean rules are stated over `Bool.and`/`Bool.or`/`Bool.not`, which
is the stuck term that `&&`, `||` and `!` elaborate to, so a goal written with the
notation is simplified too.

## The host requests

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
| getSimpLemmas (g : Nat) (k : List (String × Expr) → Tac)
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
4. A step that would leave the type syntactically unchanged is reported as `noMatch`
   (`newT == goalT`), so a degenerate rule is skipped instead of consuming fuel.
5. It builds the same `transp`/`cast` proof as `rewrite` and returns the new goal and
   its reflected type. No match changes nothing; the kernel checks the finished term.

`Tac.getSimpLemmas` returns each registered lemma's name and its reflected constant, in
the order the driver should try them (priority, then registration). The command
elaborator threads the set from `CommandState.simpLemmas` into `ElabState.simpLemmas`;
`local` registrations are recorded by position and dropped by `CommandState.endModule`,
exactly like `local instance`s. The Wiz side then commits the new goal
(`replaceMainGoal`), restarts the pass, and reads the returned type (no extra `goalType`
crossing per step). `Tac.rewrite` is unchanged (it could be expressed as `rewriteAt`
with `all := true`).

## Why not a host-side engine

A whole simplifier in `Wiz/Elab/Simp.lean` would save interpreter crossings (one
request per run instead of one per rule per pass), and matching, occurrence selection
and context transport all need `Term` anyway. It was rejected (user decision,
2026-11-14) because the algorithm would then have to be written a second time for the
self-hosted frontend, and `simp` would stop being a Wiz library tactic: rule order,
`only`, the default set, direction, fuel and later `simp?` policy are exactly the parts
that must stay changeable in Wiz. The accepted costs and their mitigations are in
`wiz-notes/simp-design.md` §4.3 and §9 (host-side scan per rule, the new type in the
answer, no re-reflection per step).

## What remains

* **S3: conditional lemmas and dischargers.** A rule with a premise before the equation
  is rejected by `attribute [simp]` and does not fire from an explicit list (the premise
  metavariable is not determined); the Wiz discharger (`assumption`, `rfl`, recursive
  `simp`) and premise goals in `rewriteAt` are S3.
* **S4: `simp at h`, `simp?`.** Hypothesis surgery (`changeHyp`/`addHyp`/`clearHyp`) and
  used-rule tracking are host/Wiz additions of their own. Goal rewriting only for now.
* **S5: congruence and arithmetic.** Dependent arguments, ordered/AC rewriting, a rule
  index by head name; and matching rules whose pattern computes to a variable or a bare
  data value (today such rules are not in the default set and, from an explicit list,
  either do nothing useful or hit the fuel bound).
* **Occurrences.** `rewriteAt` takes `all : Bool` (all occurrences, or the first); an
  `Occurrence` with `nth`/`path` and an `at` syntax are follow-ups.
* **Selfhost parity.** Port `stripRule`/`matchRule`/`abstractOccAt` and the `Tac`
  branches (including `getSimpLemmas`) to `selfhost/Kernel.wiz`/`selfhost/Frontend.wiz`,
  add goal/tactic state and `Expr` reflection there, and run the same sources (P1–P5 in
  the design note).

## Tests

The `tactics` group (`Tests/Groups/Tactic.lean`), in addition to the S1 cases: the
default set fires (`import SimpLemmas`; `simp` on `a + 0 = a` gives `⊢ a = a`) while
`simp only []` does not; `simp [h]` adds to the default set and `simp only [h]` does
not; the default order is priority first then oldest registration (`getSimpLemmas`);
`[simp]` errors for a constructor, an unknown name and a conditional lemma; warnings for
a duplicate registration and a possibly looping orientation; and a two-module fixture
that checks `local attribute [simp]` works in its module and is gone in the importer,
through both the frontend and the command cache. The library-set case uses the
annotations of `lib/ListLemmas.wiz` and `lib/Logic.wiz` on real goals: a list goal that
needs `List.append_nil`, `List.length_append_eq` and `List.reverse_reverse`, the
`&&`/`!` notation against the `lib/Logic.wiz` Boolean rules, and `simp only
[List.append_nil]` rewriting both occurrences. The S1 cases (explicit list, matched
quantified lemma, `simp only` order, no match / identity, fuel, non-equation argument,
`#print axioms`, `rw` then `simp`, `← h`, `SimpLemmas` rules) are unchanged.
