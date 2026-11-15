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
  ordinary errors) `outParam`, `deriving`. A class at universe parameters
  (`class Repr.{u} (A : Type u)`) works since U2 (30d).
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
* `outParam` rewriting and default instances (above); universe-polymorphic classes
  landed with U2 (30d).

## 30d: symbolic levels in descriptions (U2)

A data type at a universe parameter (`inductive Box.{u} (A : Type u) : Type u`,
`structure Wrap.{u} (A : Type u)`, `class Repr.{u} (A : Type u)`) has no closed
description level. `Tm.descr`, `delim`, `mu`/`mus`, `nu`, `sfix`/`scase`, `scofix`,
`coit`, `ind`, `ulift`, `unit`/`empty` and their `Val` counterparts now carry `Lvl`
instead of `Nat`; the kernel compares them with `lvlEquiv` in `convTy`, `tmEq`,
`ground*` and `subTy`, and the templates (`interpTm`, `allTm`, `hypsTm`, `mapTm`,
`delim*`, `ind*`, `sfix*`, `scase*`, `coit*`) build `lsucc`/`lmax`/`limax` levels.

The frontend (`inductiveCmdL`, `dataLevel`) takes the declaration's universe parameter
(or the largest `Type u` it mentions) as the description level. Above `Type 0` the
description's tag field is lifted (`ULift (Enum k)`, Q4), as in the Lean frontend: the
constructor stores `up tag`, the description eliminates it through `down`, and match
compilation lifts/downs the tag in the method type and the reconstructed constructor.
Level metavariables of a constant's instantiation are unified (`unifyHead`/`unifyLvls`)
so `Box Nat` solves `Box.{?u} ?A` from the expected type. A class's method projections
carry the class's `.{u}` parameters.

Tests (`=selfhost`): a polymorphic `inductive`/`structure`/`class` with `Repr` and
`Inhabited` instances and compiled reductions; verdict parity on level mismatches,
an undeclared universe and a field above the data type's universe; and a positioned
diagnostic for `inductive Bad : Type u`. The fixpoint and `=check`/`=elab`/
`=inductive`/`=sized types` remain the regression evidence.

Not implemented: inferring the result universe of a data type whose *field* is itself a
`Type u` (that needs `u+1`, and is rejected with the kernel's ULift message); a general
level solver; level-polymorphic data types with smaller fields beyond the tag (the
frontend does not synthesize field lifts).
