# FeEval: the self-hosted elaboration-time evaluator (Item 4)

**Status.** Design and skeleton only, 2026-11-23. Lane `agent/feeval-core`, worktree
`/workspace/wt/feeval-core`, branch `agent/feeval-core`, base
`integration/train12` `f489cc876`. The skeleton is `selfhost/FeEval.wiz`; it is **not**
in `Wiz/Selfhost.frontendFiles`, is not called from `Frontend.wiz`, and changes no
existing declaration. No build, test group, or perf run happened in this lane (the
queue was reserved for train11 green). Static checks: the standalone self-hosted
`wiz` (`pure-bins`) checks `Kernel.wiz` clean, and checks `FeEval.wiz` against
`Kernel.wiz` plus a small stub of the `Globals`/`Global`/`IndInfo`/`Ctor` surface it
uses; the full `Frontend.wiz` concatenation is left to E1 because the base's
`Frontend.wiz` does not self-compile (F48) and the installed `wiz` binaries predate the
`namespace` form. Every unverified assumption is in §5.

**Inputs read.** `wiz-notes/extensibility.md` §3.1 B1/B2/B3, §4 Items 2–4 and the
dependency line; `wiz-notes/elab-evaluator-plan.md` §2–§5 (the design this implements);
`wishful/selfhost-deriving.md`; `selfhost/Frontend.wiz` (`runMacroTac`
`11113`, the deriver block `10840-11486`, the dispatch `11495-11517`, `partialCmd`
`9415`, `preludeText` `10151`); `selfhost/Kernel.wiz` (`Tm`/`Val`/`Eval`/`forceSp`
`1423`, the budget `1204-1226`, `instC` `1454`); `lib/Prelude.wiz` (`SyntaxF`
`152-162`, `IndView` `538`, `Tac` `555-644`, `Deriver` `903`); the uncommitted
`agent/ext-term-elab` tree (`TermElab`, `AttrAction.termElab`, `elabTermElab?`); and
`agent/structured-view`, which has no commits past `f489cc876` yet.

---

## 1. What the evaluator is

The kernel already has NbE (`Kernel.wiz`: `eval`, `vapp`, `vfst`/`vsnd`, `whnf`,
`forceSp`, `quote`). FeEval is the **boundary** around it: it turns a host `Syntax`
tree, `String`, `Nat` or `List` into a kernel `Val`; it applies a registered Wiz
metaprogram to that value; it answers the `Tac` requests the program makes; and it
decodes the result. It introduces **no trusted code**: the output of a macro or a
deriver is re-elaborated and kernel-checked like hand-written source, exactly as the
host's `runDeriver` → `elabExpansion` path does.

The two pieces that are not the kernel are:

1. **The data layouts.** Encoders apply the prelude's own constructor values
   (`SyntaxF.node`, `List.cons`, `String.mk`, `Char.mk`, …) looked up in the running
   `Globals`. Tags, `up`-lifted fields and index proofs are then whatever `addCtors`
   made, so the evaluator cannot drift from the frontend's data representation.
2. **Stuck-head repair.** A metaprogram may reach a `partial` function, a native
   (`Nat.toString`, `Array.*`, `StrMap.*`) or an `IO` axiom. `whnfE` repairs the first
   two by replaying the spine and refuses the third (`elab-evaluator-plan.md` §3.4).

The evaluator is explicit and requested: the frontend calls it only from
`deriveClassOn` (E3) and the macro/term-elab hooks (E2/Item 2). It must not inherit the
elaborator's eager `eval` calls (`elab-evaluator-plan.md` §2, #422 lesson).

---

## 2. ABI dependencies

### 2.1 Item 2: `term_elab` (branch `agent/ext-term-elab`, uncommitted)

The host-side ABI on that branch is:

```
TermElab := Syntax → TacticM Unit                 -- lib/Prelude.wiz, next to Tactic
attribute [term_elab k] f                        -- AttrAction.termElab, payload .name
```

`check` dispatches after `expand?` and before the built-in kind switch; `infer`
dispatches with a fresh type metavariable. `elabTermElab?` makes one goal (a fresh meta
of the expected type), runs `f stx` through `TacticM.run` in the interpreter, then
applies `elabBy`'s end checks. The handler is expected to use `TacticM.mainGoal`,
`TacticM.assign`, `TacticM.exact`, `TacticM.elabInfer`, `TacticM.newGoal` and the
`Expr` codec, and it must not re-elaborate its own node.

For the selfhost, FeEval is the runner that replaces the erased-code interpreter. It
therefore needs, in the embedded prelude, the same `TermElab` type and at least the
`Tac` tags a term elaborator uses:

| tag | request | status in `FeEval.wiz` |
|---|---|---|
| 5 | `getGoals` | refused (marked `TODO(Item 2)`) |
| 11 | `exact` | refused (needs a re-entrant `check` from the evaluator) |
| 13 | `assign` | refused (needs an `Expr → Tm` conversion in the goal's context) |
| 12 | `elabInfer` | refused |
| 14 | `newGoal` | refused |

Every refusal is a `MetaR.err` naming the tag and the lane that owns it, never a hang or
a panic. The `Handler` record in the skeleton is where those arms go when Item 2's
request set is settled; the loop itself does not bake goal state in.

### 2.2 Item 3: the structured view (branch `agent/structured-view`)

At this base the branch has **no commits** past `f489cc876`; the view's request tag,
payload and capability list are unsettled. FeEval therefore:

* treats `TacTag` as **append-only**: an unknown tag is reported by number;
* does not add a view request or a view type to `Tac`;
* has one arm to extend when Item 3 appends tag 45+ (`runMeta`'s default arm).

`IndView` *is* settled (`lib/Prelude.wiz:538`, mirrored by the f48 slice): the evaluator
encodes `Globals.view`'s host `IndView` constructor by constructor (`encIndView`). That
is the only reflection the deriver slice needs.

### 2.3 The prelude/meta ABI (SH-2.0a and the f48 slice)

The base's embedded prelude (`Frontend.preludeText`, `10151`) has `SyntaxF`, `Syntax`,
`Syntax.getArg`, `String`, `Char`, `Nat`, `List`, `Option`, `Prod` and **no `Tac`,
`IndView`, `Expr`, `MacroM` or `Deriver`**. `runMacroTac`/`deriveInhabitedV` compile
today only because the *checker* is built with the host's `lib/Prelude.wiz`
(`import Std`); a self-compile of `Frontend.wiz` fails on those names (audit F48).

`agent/f48-selfcompile` `b8db99bb5`/`226487b9b` adds the slice this evaluator can run
today:

```
inductive BinderKind | default | implicit | instImplicit
inductive ParamView | mk (name : String) (kind : BinderKind) (type : Syntax)
inductive FieldView | mk (name : String) (kind : BinderKind) (type : Syntax)
                        (recursive : Bool) (proof : Bool)
inductive CtorView  | mk (name : String) (fields : List FieldView) (indices : List Syntax)
inductive IndView   | mk (name : String) (levelParams : List String)
                         (params : List ParamView) (indices : List ParamView)
                         (ctors : List CtorView) (isStructure : Bool)
inductive Tac where
  | done | result (stx : Syntax) | fail (msg : String)
  | trace (msg : String) (next : Tac)
  | getInductive (n : String) (k : Option IndView → Tac)
def MacroM (A : Type) : Type := (A → Tac) → Tac
def Deriver : Type := String → MacroM (List Syntax)
```

The tag numbers are a subsequence of the host's (`done 0`, `result 1`, `fail 2`,
`trace 3`, `getInductive 21`), so `FeEval`'s loop is written to the host's
`Wiz/Elab/Tactic.lean` `TacTag` and also runs this slice. `fresh` (4) is in the host's
`Tac` but not in the f48 slice; the loop answers it when the type has it, and the
deriver path does not need it.

**Prerequisite, not this lane:** put the full `Tac`/`MacroM`/`Deriver` (and the
`Syntax.mk*` API, SH-2.0a) in the one prelude. Until then the evaluator is host-only.

### 2.4 The Frontend surface FeEval assumes (C-SPLIT)

`FeEval.wiz` names only these existing Frontend declarations, so the split must put
them in or before FeGlobals/FeTerm (the plan places FeEval after FeGlobals and before
FeTerm):

| name | today | use |
|---|---|---|
| `Globals`, `Global`, `IndInfo`, `Ctor`, `CField` | `Frontend.wiz` | the evaluator's state and the constructor table |
| `Globals.all`, `Globals.scope`, `Globals.ind` | `Frontend.wiz` | `feGlobal`, `feCtorRef` |
| `Scope.find` | `Frontend.wiz` | kernel-name lookup |
| `globalKeyOf` | `Frontend.wiz` | a deriver/term-elaborator registration is a source name |
| `lparamLvls` | `Frontend.wiz` | constructing a constructor's `.const` |
| `strEq` | `Parse.wiz` | name comparison |
| `Globals.view` | `Frontend.wiz` | passed into `EvalEnv`, not called by name |
| `Kernel`'s `Tm`/`Val`/`eval`/`whnf`/`vapp`/`vfst`/`vsnd`/`forceSp`/`proof*`/`KNat` | `Kernel.wiz` | everything |

It does **not** call `kids`: the deriver entry returns the `Syntax` and the caller takes
`kids` (the host's `CommandMacro.run` `.args`). That keeps FeEval independent of the
syntax helpers' final home.

### 2.5 `builtin nat` (B1) and numerals

`Kernel.wiz` already has E-K (`Tm.nlit`, `Val.vnat`, native `Nat` operations), but the
selfhost frontend has **no `command.builtin`** and never emits `.nlit`; compare the
comment at `Frontend.wiz:7262`. `NatB` is not reachable from `Globals`. FeEval's
`EvalEnv` therefore carries an `Option NatB`:

* `some nb`: `encNat` emits `Val.vnat (knOfNat n) nb` (O(1) per numeral);
* `none`: `encNat` falls back to the unary `Nat.zero`/`Nat.succ` constructors.

The fallback is correct and the plan's measurement says it is ~500× slower for `✝`
codes (§3.5). Choosing literals is the B1/SH-2.0a decision, not this lane's.

---

## 3. Fuel and error contract

**Fuel.** One budget per invocation:

```
match proofStart N with
| .false => run without owning the budget      -- a read-back is already running; count on it
| .true  => run; then proofEnd 1                -- .false means it ran out
```

* `N` is `EvalEnv.fuel`, default `10_000_000` (`--meta-steps` when wired).
* A **step** is one `instC` instantiation (a β-step or going under a binder), the
  kernel's existing counter. The evaluator's own encoding, decoding, constructor
  lookup and spine replay are not ticked. This is deliberately the same contract as a
  proof read-back: it bounds reductions, not the frontend's bookkeeping.
* `proofEnd` is called after the loop on **every** path, with a non-constant argument
  that depends on the result, so Wiz's laziness cannot order it before the work. The
  outer `match` on the `MetaR` forces it first.
* When a `proofTick` fails, `instC` returns `outOfSteps` =
  `vne (haxiom " out of steps") sp`. `whnfE` recognises that name and reports the
  budget message. `proofEnd .false` reports the same message.
* The message is stable and names the limit:
  `the metaprogram did not finish within N evaluation steps (--meta-steps)`.
  The acceptance test asserts the message, not a timeout or a stack overflow.
* A nested invocation (`proofStart .false`) must not call `proofEnd`; it counts on the
  outer budget, as a read-back inside a macro does.
* Memory is not bounded by the budget (§3.6.6 of the plan); watch peak RSS in E4.

**Errors.** All failures are `MetaR.err` with a message:

| case | message (shape) |
|---|---|
| budget | `… did not finish within N evaluation steps (--meta-steps)` |
| unreached axiom | `a metaprogram reached the axiom <n>` |
| `IO`/unknown native | `the metaprogram reached <n>; … is refused by the self-hosted evaluator` |
| `getType`, no handler | `… needs a Tm → Syntax delaborator (elab-evaluator-plan §3.2; E3)` (a handler answers `Option Syntax`) |
| tactic-only request | `… made a request only tactics can make (<tag>); FeEval answers macros and derivers in this slice` |
| malformed value | `… returned a malformed syntax tree` / `…: not a Tac request` |
| unknown deriver | `unknown deriver <f>` |

Traces are accumulated in order and survive a later failure (the host's `withTraces`
behaviour). With L4/L5 (T lane) they become info messages at the call's syntax; the
skeleton returns them in `MetaR`.

**Stuck heads.** `whnfE` loops:

1. `vglued`/`vnatglue` → unfold the memo (`whnf`'s own rule);
2. `vne (haxiom n)` → if `n = " out of steps"`, budget; else if `n` is in the
   partial table, `forceSp (eval .nil body) sp`; else if `n` is a native, compute and
   `forceSp`; else error;
3. anything else is a whnf.

It needs **no kernel change**. `nativeDecide` stays refused: it would need a trusted
evaluator, which is a separate decision.

---

## 4. Staged plan (and when the four bodies die)

The four hand-written bodies in this base are:

| body | lines (`selfhost/Frontend.wiz`) | library deriver |
|---|---|---|
| `deriveBEq` | `11202-11302` | `lib/Deriving.wiz` `deriveBEq` |
| `deriveDecidableEq` | `11303-11379` | `lib/Deriving.wiz` `deriveDecidableEq` |
| `deriveCompare` | `11380-11445` | **none** (`lib/Compare.wiz` declares the class; `lib/` registers no deriver) |
| `deriveRepr` | `11446-11486` | `lib/Deriving.wiz` `deriveRepr` |

`deriveInhabitedV` (`11270`) is already the library-shaped runner and is not deleted;
it is the template. `deriveCompare` **cannot be deleted** until `lib/Compare.wiz` (or
`lib/Deriving.wiz`) gains a `deriveCompare` and registers it; deleting the body first
would remove the only implementation.

Stages (each is a separate, reviewable PR; none is this lane):

0. **This lane.** Skeleton + note. No wiring, no behaviour change. Check: the
   standalone self-hosted `wiz` on `Kernel.wiz`, and on `Kernel.wiz` + a stub of the
   `Globals` surface + `FeEval.wiz`. A full `Frontend.wiz` concatenation is E1's:
   the base's frontend does not self-compile (F48).
1. **ABI + data layouts.** Put the meta slice (or the full `Tac`) in the embedded
   prelude; add the `NatB` field when B1 lands; record partial bodies in `partialCmd`;
   build `EvalEnv.ctors` from `Globals`. Acceptance: a closed `Syntax` → `Val` →
   `Syntax` round-trip test and a partial-function repair, as `=selfhost` cases; no
   user metaprogram yet.
2. **Run one library deriver.** A test module with `deriving Inhabited`, using only the
   slice's API, registered and run by the selfhost; output text identical to the host.
   This is the plan's smallest acceptance test.
3. **The differential four.** A 6-constructor, 3-field-each type through
   `deriveBEq`/`deriveRepr`/`deriveDecidableEq`/`deriveCompare` (the last needs the
   library deriver first). Compare the emitted instance text to the host's natively
   written derivers, for every shape the frontend supports (0/1/2/3 fields, a recursive
   polymorphic inductive, an after-the-fact instance, a structure).
4. **`lib/Deriving.wiz` libdiff.** Move its cause row from `meta-api`/`diverging` to
   `ok` (or a ratchet step), and the same for `lib/OpticDerive.wiz` `Lens`. Only after
   both 3 and 4 are green:
   * delete **one** body per PR, in this order: `deriveBEq`, `deriveDecidableEq`,
     `deriveRepr`, then `deriveCompare` (after its library deriver exists);
   * keep `deriveInhabitedR`/`runDeriver` as the runner;
   * each PR re-runs the A11 `=selfhost` cases and the differential test.
5. **Item 2 + Item 3.** `TermElab` through `runMeta` with the `Handler` (`assign`,
   `exact`, `mainGoal`, `Expr` codec); the structured-view request when its tag lands.
   The evaluator's shape is unchanged; only `Handler` grows.
6. **Measurement (E4).** `--meta-stats`, the B1–B7 corpus, E-C cache and E-K decision.
   If the thresholds fail, E6 (erased-code interpreter) uses the same `MetaR`/`Handler`
   interface; nothing in this skeleton presumes NbE in the interface.

**What must run later (not in this lane).**

* A host `wiz check` of `Kernel.wiz` + `Frontend.wiz` + `FeEval.wiz` in one synthetic
  module (the file is not in `frontendFiles`, so CI does not see it). This lane's check
  used a stub for the Frontend `Globals` surface, not the real file.
* The `=selfhost` group and the new A11/FeEval cases; the `=selfhost-libdiff` ratchet.
* The 40-element list-literal probe (the plan's ~19 s baseline) before the literals
  decision.
* The self-compile/fixpoint (the F48 resolution bug is independent but blocks any
  self-compile evidence).
* The trust ledger: FeEval adds no trusted row; the `partial`/`native` repairs compute
  in the frontend and are re-checked, and `#print axioms` must not lose a native name.

---

## 5. Open ABI questions

1. **`Tac` in the embedded prelude: slice or full?** f48's five-request slice is
   enough for derivers; term elaborators need tactics. The full `Tac` has
   higher-order recursive fields (`Nat → Tac`) and needs P0-PBLK. Item 2 owns the
   decision.
2. **`getType`.** It needs a `Tm → Syntax` delaborator (~150 lines, plan §3.2). The
   skeleton's `Handler.getType : String → Option (Option Syntax)` separates "no
   handler" (refusal) from "no such declaration" (`Option.none`); `Handler.macro`
   supplies neither. `lib/Deriving.wiz` does not use it.
3. **`Expr` and handles.** The `Tac.assign`/`exact` path needs an `Expr` codec and a
   `Tm → Expr`/`Expr → Tm` conversion in a goal context, including `opaque` handles.
   Item 3 (structured view) and the T lane own the handle table; do not pin it here.
4. **`IndView` field types.** `Globals.view`'s `idxViews` gives every index
   `.missing`, and field/param types are syntax. A deriver that inspects a type
   (`Lens`, `Bundle`) needs real syntax-valued types; that is the host's
   `delab`/`termSyntax` work (plan §3.2), not an encoder bug.
5. **`result` payload.** Host `runMacroTac` returns a `Syntax`; command macros wrap
   their commands in a `null` node and take `.args`. FeEval's `MetaR` returns the
   `Syntax`; the deriver entry takes `kids`. If Item 2 changes `result` to a list,
   only the entry (not the loop) changes.
6. **`fresh` numbering.** Host `runMacroTac` starts at `scope + 1` and returns the next
   scope; the selfhost `runMacroTac` has no `fresh`. FeEval takes `next` from the
   caller; the caller must seed it from the invocation's scope and apply
   `scopeQuoted` to the output (FeMacro/E2). Hygiene is **not** in this skeleton.
7. **Hygiene/ranges.** The selfhost's `SyntaxF` has no hidden range fields; the host's
   output is synthetic at the call's range unless L2 spans land. FeEval preserves
   whatever `Syntax` it is given; it does not invent positions.
8. **`builtin nat`.** Unary fallback vs `Val.vnat` (B1). The `NatB` value must come
   from the frontend's registration table; today there is none. The evaluator's
   interface already takes `Option NatB`.
9. **Partial bodies.** Where `partialCmd` records them: the frontend keeps the
   signature and the body as two `Global`s under one name (`isPartialKey`). The
   evaluator's table should be filled by `partialCmd` (plan E1, ~20 lines) rather than
   guessed from `Globals.all`.
10. **Natives.** Which axioms are computed (`Nat.toString`, `Array.*`, `StrMap.*`) and
    which are refused (`IO.*`, `Process.*`, foreign calls). A native computes in the
    frontend; it is not a kernel axiom, so `#print axioms` must not attribute it to the
    user program. The table is data in `EvalEnv`.
11. **Nested evaluation.** A metaprogram that calls `nativeDecide`/`#eval`/a tactic
    inside itself is refused, not run under a second budget. `proofStart .false`
    already means "count on the outer budget"; a second *entry* is a separate decision.
12. **`EvalEnv` lifetime.** Per command (fresh ctor table) or per run (cache, E-C)?
    The skeleton builds it per invocation; E-C adds a value cache to the same record,
    not a new interface.
13. **Numeral width (C13).** `KNat` is exact and `Nat` (the host/runtime) wraps at 63
    bits; `feDecNatPure` uses `knToNatL`, so a metaprogram's numeral above 2^63-1 would
    decode wrapped. The deriver slice is fine (counters, lengths), but a macro doing
    `BitVec`-scale arithmetic needs either a `KNat`-preserving codec or a refusal.
    Decide with E-K; do not let it wrap silently.
14. **Lifted fields.** A constructor at a level above `Type 0` stores its fields as
    `up x` (`addCtors`' `payloadPL`); the decoder needs the constructor's `lifts` flags
    to peel them. The deriver slice's types are all `Type 0`, so the skeleton does not
    peel (peeling unconditionally would be wrong for a `ULift` field of a `Type 0`
    type). E1 adds the flag to `CtorRef` when a general decoder is needed.

---

## 6. What this lane did not do

* No edits to `selfhost/Frontend.wiz`, `Kernel.wiz`, `lib/`, or `Wiz/Selfhost.lean`.
* No entry in `frontendFiles`; no test group, no build, no `integration/*` push, no PR.
* No deriver body deleted; `deriveCompare`'s missing library deriver is recorded above.
* No `--meta-steps` flag; `EvalEnv.fuel` is a field with the default.
