# Stage 6: macros

## 6a: macros by example

```
infixl:65 " + " => add
notation "two" => Nat.succ (Nat.succ Nat.zero)
syntax "if" term "then" term "else" term : term
macro_rules
  | `(term| if $c then $t else $e) => `(term| match $c with | .true => $t | .false => $e)
```

* Every syntax category has **antiquotations** `$x`, and every category `c` has a
  **quotation** `` `(c| …) `` as a term (`Builtin.addMetaParsers`, also run for
  `declare_syntax_cat`).
* `macro_rules` match syntax structurally and instantiate templates
  (`Elab/Macro.lean`). `notation` and `infixl`/`infixr`/`infix` register a syntax rule
  and a macro rule together. User command syntax expands too.
* **Hygiene** via macro scopes: identifiers a template introduces become `x✝n`. Locals
  must match exactly, and globals are found with the scope stripped.

| #   | Where              | What                                      |
|-----|--------------------|-------------------------------------------|
| 6.1 | `Elab/Macro.lean`  | `matchPattern`, `instantiate` (hygiene)   |

## 6b: the prelude, literals and procedural macros

```
import Prelude
#eval 100 * 100 * 100 - 1          -- 999999, computed natively
def t : 2 + 2 = 4 := refl 4         -- the kernel computes on literals too

syntax (name := twice) "twice!" term : term
def twiceMacro : Macro := fun stx => do
  e ← MacroM.pure (Syntax.getArg stx 1);
  MacroM.pure `(term| let y := $e; Nat.add y y)
attribute [macro term.twice] twiceMacro
#eval twice! 21                     -- 42
```

* `import M` loads `lib/M.wiz` (and the `-I DIR` roots; `import A.B` is `A/B.wiz`). `lib/Prelude.wiz` defines `Bool`,
  `Nat`, `List`, `Option`, `Char`, `String`, `Except`, `Syntax`, `MacroM`, and `do`
  notation (written as macros).
* `builtin key := name` registers prelude definitions with the kernel and the runtime
  (as Agda's `BUILTIN`): `nat` and its constructors and operations, and `string`.
  Registrations in `lib/` are trusted (22f); anywhere else each is an axiom.
* **Literals.** A numeral of the registered `Nat` is a kernel literal `natLit n`. It
  unfolds one step at a time (`0 ↦ zero`, `n+1 ↦ succ (natLit n)`, `vNatView`) when an
  eliminator, `conv`, `unify` or `vEq` looks inside it. Registered operations compute
  natively on literals (`vBuiltin?`, `vNatOp`), and otherwise fall back to their
  definitions. The runtime uses native numbers that look like their unary payloads
  when inspected (`RVal.nat`, `natView`). Strings are `String.mk [Char.mk n, …]`, and
  `#eval` prints numbers and strings as literals.
* **Quotations in terms** build `Syntax` values (`elabQuote`): identifiers are marked
  `x✝`, and `$x` refers to a local `x : Syntax`.
* **Procedural macros** are Wiz functions `Syntax → MacroM Syntax`, where
  `MacroM A := Nat → Except String (A × Nat)` (a supply of fresh scopes, plus failure).
  `attribute [macro k] f` registers `f` for node kind `k`. Expanding a node compiles
  the environment, encodes the node as a runtime value, runs `f` in the interpreter,
  and decodes the result (`Elab/ProcMacro.lean`). The `x✝` marks then get this
  expansion's scope.
* Antiquotations win ties within their category; `$x:term` picks the other reading.
  `match` alternatives must line up (`colGe`), so a nested `match` ends where the
  outer one's next alternative starts.

| #   | Where                  | What                                              |
|-----|------------------------|---------------------------------------------------|
| 6.2 | `Elab/Term.lean`       | `elabQuote`: a quotation as a term building `Syntax` |
| 6.3 | `Elab/ProcMacro.lean`  | `decodeSyntax`: a runtime value back to `Syntax`  |

## 6c: tactics in Wiz

**Infinitary inductives.** Descriptions gain `Desc.hrec q H j D`, a field
`(h : H) → μ D (j h)`: one subtree per `h`, as in W-types. `Desc.elim` takes a fifth
method, `interp`/`All`/`hyps`/`map` have the obvious extra case, and `All` now lives in
`Sort (max (l+1) v)`. `inductive` accepts fields like `(k : Nat → Tree)`, the recursor's
hypothesis for them is `(x : Nat) → motive (k x)`, and structural recursion accepts
`f (k n)`. `Level.equiv` now decides `imax` by splitting on parameters. The tactic monad
needs all of this: it is a free monad, whose continuations are infinitary fields.

If you have already done exercises 4.17–4.21 (the templates, `vDelim`, description
checking and `ctorDesc`), add the `hrec` cases.

**Tactics** (`examples/tactics.wiz`):

```
def ap : (A B : Type) → (A → B) → A → B := by
  intro A; intro B; intro f; intro a
  apply f
  assumption
```

* `by tac₁; tac₂ …` (or one tactic per line) makes a hole of the expected type and runs
  the tactics on it. Leftover goals are reported with their hypotheses.
* A tactic is a **Wiz function** `Syntax → TacticM Unit`, registered for a `tactic`
  syntax kind with `attribute [tactic k] f`. Tactic syntax can also be macros
  (`rfl` is `exact rfl`).
* `TacticM A := (A → Tac) → Tac`, where `Tac` is an inductive type of **requests** to
  the elaborator, each with a continuation (an infinitary field). The elaborator
  interprets them (`runTac`): goals (`getGoals`, `setGoals`, `goalType`, `goalHyps`),
  `intro`, `exact`, `elabInfer`, `assign`, `newGoal`, `isDefEq`, `normalize`,
  `instantiate`, `inferType`, `evalTactic`, and `catch` (which backtracks the elaborator
  state). Tactic code itself stays pure and deterministic. Macros use the same monad
  (`MacroM := TacticM`, requesting only `fresh` and `fail`), so `do` notation serves both.
* Terms are reflected as `Expr` (de Bruijn variables, constants, closed sorts, Π, λ,
  application, numerals). Every other kernel form is an **opaque handle** that
  remembers its depth, and nominal types are shown by name (`Vec A n`).
* The prelude's tactics: `intro`, `exact`, `rfl`, `assumption`, `apply`, `try`,
  `first | t | u`, `( t; u )`, `repeat`, `trace`.
* Macro and tactic code is erased once, on first use, and only what is reachable
  from them (`compileReachable`; `#eval` does the same).

Also fixed along the way: `elabMatch` zonks the expected type, and `checkApp` keeps the
written arguments (not the placeholders' normal forms) and solves placeholders
without quoting.

| #   | Where                 | What                                               |
|-----|-----------------------|----------------------------------------------------|
| 6.4 | `Elab/Tactic.lean`    | `reflect` and `reify`: terms ↔ `Expr` with handles |
| 6.5 | `Elab/Term.lean`      | `runTac`: the request loop                         |
| 6.6 | `lib/Prelude.wiz`     | `TacticM.findHyp`, for `assumption` (in Wiz!)      |

Next: typeclasses with tabled resolution (stage 7), which also make `do` generic.

## 6d: `trace` and `trace_state`

```
def k : Nat → Bool → Nat := by
  intro n
  trace "hello"          -- t.wiz:3:3: info: hello
  trace_state            -- t.wiz:4:3: info: n : Nat
  intro b                --                  ⊢ Bool → Nat
  exact n
```

* `TacticM.trace msg` (the `trace "…"` tactic, or any tactic or macro written in Wiz)
  adds an **info message** at the tactic (for a macro: at the syntax it expands). It goes
  through the same channel as every other message, so `wiz check` prints it, the
  language server publishes it as a diagnostic of severity 3, and it is cached and
  replayed with the declaration's other messages.
* `trace_state` prints the open goals as the "unsolved goals" error does (hypotheses,
  then `⊢ type`; goals separated by a blank line; `no goals`). For tactic authors:
  `TacticM.ppGoal g : TacticM String` and `TacticM.ppExpr g e : TacticM String` print a
  goal and a reflected term in a goal's context, for traces and error messages (no
  hand-written `Expr` printer needed).
* **The infoview.** `wiz/plainGoal` and `wiz/interactiveGoals` answer with a `messages`
  field as well: the texts of the info messages of the tactic the state belongs to, in
  order (`rendered` has them after the goals). The clients show them in a "Messages"
  section under the goals: the terminal and web infoviews (`TacView`,
  `View.ofTacState`, `Infoview.htmlTacState` in `lib/Infoview.wiz`) and the Neovim
  plugin (`editors/nvim/lua/wiz/infoview.lua`).
* **Deterministic.** Traces are recorded in the elaborator's state (as entries of the
  info tree that the command elaborator turns into messages), in the order they were
  made. So a trace in a branch that fails and is caught (`try`, `first`, `catch`) is
  dropped with the rest of that branch, as in Lean, and the traces made before an
  uncaught error are still shown, before the error. Type mismatch errors now carry the
  state they were raised in too (they used to lose the info tree recorded so far).
* Commands that keep no info tree (`#check`, `#eval`, `instance`, …) still show their
  traces (`withTraces`). A macro's traces come back with its result (`runMacroTac`
  returns them also when the macro fails).

## 6e: names for introduced variables

A tactic that introduces variables must call them something. Coq's answer (generated
`H0`, `x1` that proofs then mention) makes proofs break under unrelated edits; Lean's is
hygiene: a name nobody chose is *inaccessible* (`n✝`), and a proof that wants to use
it says so (`rename_i`, `intro n`). Wiz follows Lean, with predictable base names.

```
def k : (n : Nat) → (b : Bool) → Nat → Nat := by
  intros                 -- n✝ : Nat, b✝ : Bool, x✝ : Nat
  rename_i c, m          -- names the last inaccessible hypotheses: b✝ ↦ c, x✝ ↦ m
  exact m
```

* **From the binder.** `TacticM.introFresh g hint : TacticM (String × Nat)` introduces
  under `hint`, or (if `hint` is `""`) the binder's name, or `h` for a proof and `x`
  otherwise when the binder has none. A name already in the context gets the first free
  numeric suffix (`n`, `n1`, `n2`, …): nothing is shadowed. The request **returns the
  name** with the new goal, so a tactic can report or reuse what it introduced.
  `TacticM.intro g x` is unchanged (it takes the name as given, shadowing).
* **Inaccessible.** `TacticM.introInaccessible g hint` marks the name with `✝` (`n✝`,
  then `n✝1`, …). `✝` is not an identifier character, so the name can be read in a goal
  but not written. `intros` introduces every binder of the goal this way (it does not
  unfold definitions to find more; `TacticM.intros g` returns the names), and
  `rename_i a, b` (`TacticM.rename g i x`: hypothesis `i` renamed, a new goal with the
  same hole, since names are not part of terms) gives the most recent ones real names.
* **Binder names survive unification.** A hole solved under a binder used to be
  abstracted over a generated name: `?J x7 := …` became `fun x7 => …`, and a tactic
  that introduced `J`'s variable called it `x7`. The unifier now remembers the names of
  the binders it goes under (`ElabState.binderNames`, by level; `fun n => …` against a
  hole, or two `Π`s) and `solve` uses them: `ap0 g0` elaborates to
  `ap0 (fun k => List Nat) g0`, not `ap0 (fun x0 => List Nat) g0`. Names are not part of
  conversion, so nothing else changes.

## 6f: `unfold`, `whnf`, `change`, `rw`

```
def MList : List Nat → Nat → Pred
  | .nil, p => fun h => p = 0
  | .cons x L, p => ex (fun n => star (cell p x n) (MList L n))

def t (x : Nat) (L : List Nat) (p : Nat) : Ent (MList (.cons x L) p) … := by
  unfold MList     -- ⊢ Ent (ex (fun n => star (cell p x n) (MList L n))) …
```

`normalize` evaluates and quotes, and since values are glued (7a) it hands a definition
back folded: no request showed what a definition unfolds to, and tactics found out by
unifying with every shape they knew. Four requests (and the tactics of the same names):

* `TacticM.unfold g n e` (`unfold f, g`): every application of the definition `n` in `e`,
  unfolded **once**. "Once" is what a person means by it: the definition's body with
  the arguments in place and the `match` on them computed (a definition by cases or
  structural recursion is `fun x => T.rec … x`, so the eliminator at its head is
  unfolded with it, `isRecursor`), but the definitions the body mentions still folded
  (`ex`, `star` above). An application that is stuck (`MList L p`, `L` a variable) stays
  as it is: the request returns the term unchanged, and the `unfold` tactic then fails
  ("nothing to unfold"), as Lean's does. So does a name that is not a definition (a
  constructor, an axiom): the request returns the term unchanged, so a library can try
  it without catching, and the tactic says "`n` is not a definition" (it asks
  `TacticM.isDefinition n` first).
* `TacticM.whnf g e` (`whnf`): the head unfolded until it is not a definition.
* **Recursive calls are folded back.** A structurally recursive definition is an
  eliminator, so what unfolding leaves for `MList L n` is `ind … L n`, with the whole
  definition inlined in it. `foldRec` looks for stuck eliminators in the result and
  replaces each by `f ?a₁ … ?aₖ` when that unifies with it, for the `f`s just unfolded
  (`foldAs?`: the candidate is itself stuck on the hole it recurses on, which is not a
  pattern, so that hole is first solved with what the eliminator is stuck on). What
  cannot be folded is left raw; it is still correct.
* `TacticM.change g ty` (`change t`): the goal restated as a convertible type, checked
  by unification at once (a tactic that assigned a new goal's hole itself got its
  error from the kernel, at the end of the declaration). `unfold` and `whnf` end with it.
* `TacticM.rewrite g h rtl` (`rw h`, `rw ← h`): for `h : a = b`, a complete term, the
  occurrences of `a` in the goal `G[a]` become `b`. The old goal is solved with
  `cast (transp (fun x _ => G[x] = G[a]) (refl G[a]) h) ?new`, as `Eq.substBack` does,
  so it works for goals in any universe. Occurrences are found syntactically in the
  normal form the goal is printed in (no unification: instantiate a quantified
  equation yourself, `rw (h x)`), and the equation must still be one: an equation at a
  data type that has computed (`succ a = succ b` is `a = b`) is rewritten as what it
  computed to.

None of this is trusted: the unfolded or rewritten type is a candidate that `change`
checks by conversion, and the kernel checks the finished term (it does not evaluate the
`transp` proof: nothing here depends on proofs computing).

## 6g: reflection of constructors, and reading terms

```
-- the goal  P (x :: Nat.succ x :: L)  as a tactic reads it (TacticM.goalType):
--   before:  app (const "P") (opaque 0)
--   now:     P (List.cons Nat x (List.cons Nat (Nat.succ x) L))
```

Data types are descriptions (stage 4), and a constructor application, once evaluated,
is `con ('cons, x, L, refl, ())`: a tagged payload that says nothing of its type or the
type's parameters. `reflect` could only hand tactics an opaque handle, so a tactic
could not look inside `x :: L` or tell `Prog.get l k` from `Prog.ret v` except by
unifying with every constructor in turn, and two reflections of the same term were two
different handles.

* **Type-directed reflection** (`reflectT`, `Elab/Tactic.lean`). The payload does not
  say which constructor of which type it is, but its *type* does: a `con` with tag
  `cons` at the nominal type `List A` is `List.cons A x L`. So reflection follows the
  types down the term: the head of an application (a constant, a variable of the goal's
  context) gives the types of its arguments, a `fun` at a `Π` type the type of its
  body, a constructor the types of its fields. A `con` at a known nominal type is
  reflected as `const "T.c"` applied to the type's parameters (read off the type) and
  the fields (read off the payload by the shape of the constructor's own declaration,
  `ctorShape?`, which also undoes the universe lifting of Q4). The kernel's numeric
  operations are reflected by their registered names (`Nat.succ n`).
* **Building terms back needs nothing new**: constructors are globals, so `reify`
  already turns `List.cons A x L` into the term that evaluates to the same `con`. The
  **trusted base is unchanged**. Reflection is only what a tactic reads; whatever it
  builds is elaborated, unified with the goal and checked by the kernel as before.
* **Where it applies.** The goal's type and hypotheses, a goal's hole, the results of
  `elabInfer`, `normalize`, `whnf`, `unfold` and `instantiate` (for these the type is
  computed from the term's head, `RCtx.typeOf?`, which works with holes in the term).
  A `con` whose type is not known (an argument of an unsolved metavariable, the inside
  of another opaque kernel form, a structure's tuple) is still an opaque handle. A
  term without data is reflected exactly as before (`hasData`).
* **Handles are interned**: a term that stays opaque (a quantity, an equation, a raw
  eliminator) gets the handle it got before, so two reflections of a goal are equal
  `Expr`s and `Expr.beq` can compare them.
* **Reading terms** (the prelude; after Lean's `getAppFn`/`getAppArgs` and Ltac2's
  one-level `Constr.Unsafe.kind`): `Expr.view e : ExprView` is the head with all its
  arguments (`const name args`, `var i args`, `pi`, `lam`, `lit`, `sort`, `other`);
  `Expr.getAppFn`, `Expr.getAppArgs`, `Expr.mkApp`, `Expr.headName`, `Expr.appOf n e`
  (the arguments, if `e` is `n` applied to some), `Expr.beq` (syntactic equality, now
  meaningful for data), `Expr.nameEq`.
* **Constructors.** `TacticM.ctorInfo n` says whether the constant `n` is a
  constructor (its type, number of parameters and of fields), `TacticM.ctorApp e` gives
  a constructor application's name and fields, and `TacticM.whnfCtorApp g e` computes
  first: `Prog.swap p q` is read as the `Prog.get p …` it computes to, in one request.
