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

Parity row A11 (`wiz-notes/selfhost-parity.md`) is the next command: `inductive T …
deriving C₁, C₂` (also `structure`) and `deriving instance C₁, C₂ for T₁, T₂`. The
self-hosted grammar already had both (the parser tables come from `Builtin.tables`), but
there was no handler, so both were "unsupported command".

The Lean toolchain's `deriving` is a **deriver**: a Wiz function
`Deriver := String → MacroM (List Syntax)`, registered with `attribute [deriver C] f`,
which asks the elaborator for the type's shape (`MacroM.getInductive`) and returns the
commands that make the instance. This frontend has no elaboration-time evaluation of Wiz
code and no quotations (`wishful/selfhost-deriving.md`, items 1–3), so a deriver cannot
be a Wiz value here. Instead the deriver is a function in `Frontend.wiz`, chosen by the
**method shape of the class**, that reads the same shape from the already-elaborated
`IndInfo` and **emits ordinary commands** — a `def` by structural recursion and an
`instance`. Those commands then go through the same elaborator and kernel as a
hand-written instance: the derived instance is a normal global, with no axiom, no new
kernel rule and no change to the trust ledger. The derivation itself is silent (it adds
no output line), as in the Lean toolchain.

* **Class resolution.** `Globals.class` must know the class (it was declared with
  `class`); its method list picks the deriver: exactly `["beq"]` is `BEq`, exactly
  `["reprPrec"]` is `Repr`; anything else is an error naming the class and the type.
* **Reflection.** `IndInfo` grew the parameter binders as syntax (`params`), the
  self-hosted counterpart of the Lean reflection's `ParamView` (name, kind, type). The
  constructors, their fields, quantities, implicitness and recursion were already there.
  A derived instance is `{p₁ : P₁} → [C p₁] → … → C (T p₁ … pₙ)`: every parameter is an
  implicit binder, and a `Type`/`Type u` parameter gets an instance argument (as
  `Derive.instBinder` in `lib/Deriving.wiz`).
* **What `BEq` generates.** The equality is not written as one `match` inside the
  instance: a recursive field's comparison needs the instance being defined. The deriver
  emits a helper definition by equations,
  `def T.beq✝ {p…} [b✝0 : BEq p…] : T p… → T p… → Bool | c a✝… , c b✝… => …`, whose
  recursive calls the equation compiler turns into the recursor's induction hypotheses
  (`T.rec` in the Lean deriver); the constructor's **explicit data fields** are compared
  (`Bool.and` of `BEq.beq a✝i b✝i`, or the helper for a recursive field), and two
  different constructors are `Bool.false`. Proof fields and fields at quantity 0 are not
  compared (a proof of a proposition is unique; it also has no `BEq` instance). The
  helper's name contains `✝`, so no source program can name it. The instance is
  `instance … : BEq (T p…) where beq := @T.beq✝ p… b✝…`.
* **What `Repr` generates.** The same shape: `def T.repr✝ … : T p… → Nat → String` with
  `"T.c"`, then each data field (through `Repr.reprPrec` or the helper at 1024), an
  explicit proof field as `_`, and parentheses when the precedence is at least 1024.
* **Rejected.** Indexed families (the `BEq` deriver in `lib/` rejects them too: the
  index is a constructor argument the equations would have to generalise); a type with
  no constructors; a class with no deriver in this frontend; and, through ordinary
  instance resolution, a field with no `BEq` instance (`structure Bad where f : Nat →
  Nat` is rejected when the generated `BEq.beq f g` cannot be solved). The error is the
  command's line, so the driver's diagnostics position it (`file:line:col`); the
  checker's own output (`checkFile`) strips the offset like every other command's.
  Still missing, and cheap follow-ups: `Inhabited` (the first constructor without
  recursive or proof fields, at `default`), and `Lens` (`lib/OpticDerive.wiz`), whose
  deriver produces several definitions and laws.

`lib/*.wiz` has `deriving` clauses for `Inhabited`, `BEq`, `Repr`
(`lib/Deriving.wiz`) and `Lens` (`lib/OpticDerive.wiz`, registered with
`attribute [deriver Lens]`); this milestone implements `BEq` and `Repr`.

The gap to a general `deriving` is exactly the wishful note's items 1–3 plus two small
ones: (1) a way to run Wiz code at elaboration time (an interpreter over the kernel's
terms, or compile with `Backend.wiz` and load the result); (2) procedural macros and the
`Deriver` registry (`attribute [deriver C] f` is still an unsupported command); (3)
quotations in terms; (4) `MacroM.getInductive`/`getType` requests over the globals (the
`IndInfo` change here is the data, the request loop is what is missing); (5) `T.rec` as
a global (this frontend's equations compile to the recursor internally, but a deriver
written in Wiz would want to apply it by name). Once (1)–(3) exist, the derivers in
`lib/Deriving.wiz` can replace the ones in `Frontend.wiz` unchanged.

### Tests

The `selfhost` group gains two cases: `deriving BEq` on a 0-field inductive, 1-, 2- and
3-field structures, a recursive polymorphic inductive, and an after-the-fact
`deriving instance BEq for Box`, with every comparison reduced; and the negative cases
(`structure Bad` with a `Nat → Nat` field, and a class with no deriver), whose exact
error messages are pinned.
