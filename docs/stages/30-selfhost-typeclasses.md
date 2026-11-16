# Stage 30: type classes in the self-hosted toolchain

`selfhost/Frontend.wiz` has been a bidirectional elaborator with metavariables,
unification and postponed arguments since stage 17; what it lacked, compared with the
Lean frontend, was surface area. This stage starts closing the largest gap in `lib/`:
**type classes** (`wiz-notes/selfhost-parity.md`, row A10). It is a first milestone, not
full parity: instance resolution is deterministic and bounded, and default instances,
`binop` and `outParam` are still missing (below).

## 30a: classes, instances and dictionary passing

The smallest sound design over the existing kernel: **a class is a structure, an
instance is a global of the class's type, a method is a projection, and a dictionary is
the structure value.** No new kernel term, no backend rule, no erasure rule: structures
already compile (stages 18e, 21a), and a class's type parameters are implicit at
quantity 0, so they are erased.

* `class C (ps) where f₁ : A₁ …` is `structure C (ps) where | mk (f₁ : A₁) …` (the same
  `structCmd` path: one inductive with constructor `mk`, then a projection per field),
  plus a registration in `Globals.classes`. The *methods* `C.fᵢ` are the projections
  with an **instance** `self` binder:
  `C.fᵢ {ps} [self : C ps] : Aᵢ`. The class's parameters keep their written kinds in the
  type former `C`, so a class with an instance parameter
  (`class Commute (e₁ e₂) (m) [i : Monad m] …`) inserts that problem at every use of
  `C e₁ e₂ m`, as in Lean.
  Rejected: private fields (a class's fields are its methods), and (by the elaborator's
  ordinary errors) `outParam`, universe-polymorphic classes, `deriving`.
* `instance [priority] [name] {ps} : C a… := v` (or `where f := v …`) is an ordinary
  definition whose type is checked to be a class application (`C` must be a class). For
  `where` the body is `C.mk f₁ … fₙ` in the class's field order; a missing, duplicated
  or unknown field is an error. The instance's name is the written one, or `inst` + the
  class name (with a numeric suffix if that is taken). `(priority := n)` is parsed and
  stored (default 1000). Two instances whose types are definitionally equal are an
  error: this frontend has no way to choose between overlapping candidates yet.
* **Binder kinds.** `Global`'s mask is now a `List BKind` (`dflt`, `impl`, `inst`), not
  a `List Bool`, so an instance binder is distinguishable from `{}`, `()` and a plain
  parameter. `binderNames`/`binderType` read `[x : C A]` (type at 2) and give `[C A]`
  the deterministic name `inst✝`; an instance binder's default quantity is ω.

### Class problems and resolution

A method call (`C.f`, or a use of `C` with instance parameters) makes a metavariable
for each `inst` binder and records a **class problem**: the metavariable, its type (a
class application `C a…`) and the context (`ES.insts`, a `PInst`). Nothing is resolved
at that point: the class's arguments are often not known yet (`def get {A} [Default A] :
A := Default.d` called as `get : Nat` learns `A` from the expected type *after* the
method is elaborated).

`finishElab` (called wherever a command previously called `drain`) alternates `drain`
with resolution and solves every problem before the command is zonked and checked:

1. the problem is **ready** when its type's head is a class constant and no argument of
   it mentions an unsolved metavariable (the class head is inspected without `whnf`: a
   class unfolds to its `μ`); otherwise it is reported as
   `type class problem is stuck: …`, since no later unification is left to fix it;
2. the **candidates** are, in order, the local hypotheses whose type unifies with the
   goal (innermost first: a `[i : C A]` binder, or any hypothesis of that type), then
   the class's registered instances, by priority (descending) and latest declaration
   first;
3. a global instance is applied to fresh metavariables for its leading parameters (its
   explicit and implicit parameters too: the goal or a later parameter fixes them), its
   own `inst` parameters become further problems (subgoals), and its conclusion is
   unified with the goal. The first candidate that applies is **committed to**;
4. a problem with no candidate is an error naming the class application
   (`failed to synthesize an instance of …`), and the search has a step budget (100
   resolutions per command), so a cycle is that error rather than a loop.

The boundary of this milestone, in one list: **no tabling** (a cyclic instance such as
`instance [C A] : C A` fails instead of being shared; two branches that need the same
dictionary each resolve it, which is correct, just not shared), **no backtracking** out
of a committed candidate (with duplicate instances rejected, overlapping candidates
cannot arise; a candidate whose subgoals fail fails the command), **no default
instances** (`attribute [default_instance]` is still an unsupported command), **no
`binop`/`OfNat`** (a numeral at a non-`Nat` type is not a class problem; `import
Prelude` still loads the self-hosted prelude, which has no classes), **no `outParam`**
(the class's parameter types are not rewritten), and **no universe-polymorphic classes**
(that is A15). A class with an instance parameter works, and its instance's own
parameters are solved by ordinary resolution (the `Commute` shape).

### Tests

The `selfhost` group (`Tests/Groups/SelfHost.lean`) gains seven cases (117–123 of 124):

* a class with one method, instances for `Nat` and `Bool`, and a generic function using
  the class (`get : Nat`, `get : Bool`), with the exact checked output of `#check` and
  `#reduce` (117);
* `where` instances, a two-method class and a generic function using both methods, a
  parameterised instance (`Default (List A)` from `Default A`, resolving recursively),
  and a class with instance parameters (the `Commute` shape) (118);
* a missing instance: `failed to synthesize an instance of (Default ?m0)` (119);
* a duplicate instance: an error naming the first one and the type (120);
* verdict parity with the Lean frontend on eight declarations (accept: the core, `where`
  and an instance-parameter class; reject: a private field, missing/extra `where`
  fields, an instance for a non-class, a missing instance) (121);
* pinned differences: a duplicate instance (Lean accepts, this frontend rejects) and
  `outParam` (Lean accepts, this frontend does not) (122);
* the self-hosted *backend* compiles a class program and runs it: dictionary passing
  really passes the structure value (123).

The self-check case (93) is the regression test that matters most: the whole frontend,
with the new code, still checks itself.

### What remains for full parity

* default instances and priorities in the *choice* between overlapping candidates (the
  registration command and the priority field are there; the duplicate check makes the
  choice moot today);
* `outParam`: rewrite an output parameter's type to its argument when the class is
  elaborated, and leave it out of the resolution key;
* numeric classes (`OfNat`, `Add`, …) in the self-hosted prelude, numerals at other
  types, and `binop` operand typing (`docs/stages/07-type-classes.md`, 7e/7f);
* tables for generators/consumers (Lean's tabled resolution), so cyclic instances are
  shared and fail late rather than by budget, and so a dictionary needed in two places
  is searched once;
* `attribute [default_instance]`, `attribute [binop]`, `binop%`;
* dictionary unboxing and projection inlining in the backend (performance, not
  semantics);
* universe-polymorphic classes (`class Repr.{u} …`), which need A15's level parameters
  and U2's symbolic descriptions.

## 30b: `deriving`

Parity row A11 (`wiz-notes/selfhost-parity.md`): `inductive T … deriving C₁, C₂` (also
`structure`), `deriving instance C₁, C₂ for T₁, T₂`, and `deriving` on a member of a
`mutual` block. The self-hosted grammar already had the forms (the parser tables come
from `Builtin.tables`), but there was no handler, so they were "unsupported command".

The Lean toolchain's `deriving` is a **deriver**: a Wiz function
`Deriver := String → MacroM (List Syntax)`, registered with `attribute [deriver C] f`,
which asks the elaborator for the type's shape (`MacroM.getInductive`) and returns the
commands that make the instance. This frontend has no elaboration-time evaluation of Wiz
code and no quotations (`wishful/selfhost-deriving.md`, items 1–3), so a Wiz deriver
cannot be *run* here. It has the host's **table** instead: `Globals.derivers` maps a
class name to a deriver name, `attribute [deriver C] f` records a pair, and `deriving C`
looks `C` up and dispatches on the registered name. The five derivers `lib/Deriving.wiz`
registers in the Lean toolchain are implemented in `Frontend.wiz` under the same names
(`deriveInhabited`, `deriveBEq`, `deriveRepr`, `deriveDecidableEq`, `deriveCompare`) and
are pre-registered for the canonical class names, because the self-hosted prelude has no
classes and no `import Deriving`. A deriver reads the type's shape from the
already-elaborated `IndInfo` (the reflection counterpart) and **emits ordinary
commands** — a `def` by structural recursion and an `instance` — which go through the
same elaborator and kernel as a hand-written instance. The derived instance is a normal
global: no axiom, no new kernel rule, no change to the trust ledger.

* **The table.** Keyed by the class **name** (as `CommandState.derivers` is, not by the
  class's method shape: the host's `Lens` is a `def`, not a class). `attribute [deriver
  C] f` checks that `f` is declared with one argument (the host unifies its type with
  `Deriver`; this frontend checks the Π arity, since `Deriver`/`MacroM` are not in its
  prelude) and records `(C, f)`. A built-in deriver's name needs no declaration, so a
  look-alike class can reuse one: `attribute [deriver Eq2] deriveDecidableEq`. A
  registered name that is not one of the five is accepted and reported as unrunnable
  when `deriving C` uses it: *the deriver f cannot be run (this frontend has no
  elaboration-time evaluator; …)*.
* **Class arity.** A derived instance is `C (T p…)`, so the class must take one type
  parameter; `class Pair (A B : Type)` is rejected with the class's arity in the
  message.
* **Reflection.** `IndInfo` grew the parameter binders as syntax (`params`), the
  self-hosted counterpart of the Lean reflection's `ParamView` (name, kind, type). The
  constructors, their fields, quantities, implicitness and recursion were already there.
  A derived instance is `{p₁ : P₁} → [C p₁] → … → C (T p₁ … pₙ)`: every parameter is an
  implicit binder, and a `Type`/`Type u` parameter gets an instance argument (as
  `Derive.instBinder` in `lib/Deriving.wiz`).
* **What the derivers generate.** Each is a `def T.<kind>✝` by equations whose
  recursive calls the equation compiler turns into the recursor's induction hypotheses
  (`T.rec` in the Lean derivers), then an `instance … where <method> := @T.<kind>✝ …`.
  The helper's name contains `✝`, so no source program can name it. In every deriver a
  constructor's **explicit data fields** are used, except fields at quantity 0 and proof
  fields (a proof of a proposition is unique, has no `BEq`/`Repr` instance, and cannot be
  a `default`; a field is a proof when the kernel's `isProp` says so of its type, the
  question `FieldView.proof` answers in the Lean reflection, evaluated here under dummy
  values for the binders the field type is over).
  * `Inhabited`: the first constructor without recursive or proof fields, applied to
    `Inhabited.default` for each explicit field (`Derive.firstPlain`).
  * `BEq`: `Bool.and` of `BEq.beq` on the fields, or the helper for a recursive field;
    `Bool.false` for two different constructors.
  * `Repr`: `"T.c"`, then each data field through `Repr.reprPrec`/the helper at 1024, an
    explicit proof field as `_`, and parentheses when the precedence is at least 1024.
  * `DecidableEq`: an enumeration (every constructor is a constant) or a
    single-constructor record with no recursive field (`lib/Deriving.wiz`'s rule: a
    recursive field's comparison would need the instance being defined); fields through
    the class's own method, `Bool.false` for a different constructor.
  * `Compare`: lexicographic on the fields of the same constructor, `.lt`/`.gt` by the
    constructors' **declaration order** (the first is least), recursive fields through
    the helper. There is no Lean-host deriver for `Compare` (the class is
    `lib/PMap.wiz`'s, whose `Ordering` comes from `lib/Nat.wiz`, and its instances are
    written by hand), so this one has no differential case; it is tested in the
    self-hosted toolchain only, whose prelude has no `Ordering` (the case declares one),
    and the deriver names its result type `Ordering` as the other derivers name `Bool`
    and `String`.
* **Rejected**, in the host's message shape (`deriving C for T: <reason>`): an indexed
  family (`indexed families are not supported`; the index is a constructor argument the
  equations would have to generalise, and `lib/Deriving.wiz` rejects it for `BEq` too); a
  member of a `mutual` block (`not an inductive type or structure: T`, as the host's
  `MacroM.getInductive` says); an all-recursive type for `Inhabited` (`every constructor
  of T is recursive or has a proof field`); a recursive type for `DecidableEq`
  (`DecidableEq is derived for an enumeration or a single-constructor record only, and
  T`); a class with no entry in the table (`no deriver for C (register one with
  `attribute [deriver C] f`)`, the host's message); a class with the wrong arity; and a
  registered deriver this frontend cannot run. A field with no `BEq` instance is rejected
  through ordinary instance resolution when the generated `BEq.beq` cannot be solved.
  `deriving C` on a `mutual` block itself is refused with the command's span (`deriving C
  for T: a mutual inductive is not supported …`): the host
  derives for the joint family (`A_B t`, an indexed family, so one instance covers every
  member), which this frontend's equation-based derivers do not support; `deriving Repr`
  on a mutual block is therefore a pinned difference (the host accepts it).
* **Positions.** A derivation error is the command's line, so the driver's diagnostics
  position it (`file:line:col`); the checker's own output (`checkFile`) strips the offset
  like every other command's. The host positions the error at the class name inside the
  command (`4:19`); this frontend's diagnostics are command-granular (D6).
* **Structural types meet the duplicate check.** Data types are descriptions, so two
  declarations with the same shape are the same type to the kernel: `inductive D | a |
  b` is `Bool`, and two one-field `Nat` records are each other. Deriving `BEq` for both
  then makes a second instance of the same type, which the duplicate check refuses
  (`duplicate instance: instBEq1 already has the type of this one`). The host accepts
  it. The tests give each derived type a distinct shape (a known difference, not pinned by
  a case).

What a **user deriver** still needs: (1) a way to run Wiz code at elaboration time (an
interpreter over the kernel's terms, or compiling with `Backend.wiz` and loading the
result), which is also what macros and tactics need; (2) quotations in terms and the
`Syntax` constructors (`Syntax.mkApp`/`mkVar`/`mkStr`), since the elaborator's `SyntaxF`
is not visible to a Wiz program; (3) the `Deriver`/`MacroM`/`Syntax` types and the
`Derive.*` toolkit of `lib/Deriving.wiz` in the self-hosted prelude; (4)
`MacroM.getInductive`/`getType` requests over the globals (the `IndInfo` change here is
the data, the request loop is what is missing); (5) `T.rec` as a global (this frontend's
equations compile to it internally, but a deriver written in Wiz would want to apply it
by name). Until then the table registers a user's function but cannot call it, and a
deriver that produces several definitions and laws (`Lens`, `Bundle`) stays out of
reach.

`lib/*.wiz` has `deriving` clauses for six names; this milestone implements the five
that `lib/Deriving.wiz` registers. `Lens` (`lib/OpticDerive.wiz`) and `Bundle`/`BitPack`
(`lib/Hdl/Core.wiz`, `drafts/hdl/`) are user derivers and need the pieces above.

### Tests

The `selfhost` group gains six cases: the original `BEq`/`Repr` case and its negative
case; the **table** case (the five built-ins on an `inductive`, a `structure`, an
after-the-fact instance, several classes and several types in one instance, and a
built-in re-registered for a look-alike class, with every result reduced); the table's
**error** case (no deriver, an indexed family, a recursive field for `DecidableEq`, an
all-recursive type for `Inhabited`, a deriver registered with the wrong arity, an
unrunnable registered deriver, and a `mutual` block), with exact messages pinned; a
**differential** case that checks the Lean host (importing `lib/Deriving.wiz`) and the
self-hosted frontend agree on every form's verdict; and a **span** case through the
self-hosted driver's `check`, pinned as `input.wiz:4:1: error: …`.
