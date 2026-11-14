# Stage 4: data

Stage 4 has several steps, each committed separately:

1. **Universe polymorphism** (below)
2. **Type-directed conversion, Σ / ⊤ / ⊥ with η** (below)
3. **Observational equality** (below)
4. **Quantity polymorphism** and **indexed descriptions, μ / ν** (below)
5. Surface `inductive` / `structure` (below); dependent `match`, structural and
   well-founded recursion, and copatterns are next

## 4a: universe polymorphism

`Wiz/Core/Level.lean` has Lean-style levels: `Sort 0` is `Prop` (impredicative),
`Type u` is `Sort (u+1)`, and Π lives in `Sort (imax u v)`. Declarations take level
parameters, `def id.{u} {A : Sort u} (x : A) : A := x`, and uses get fresh level
metavariables (`id`) or explicit levels (`id.{1}`). The level normaliser is
provided. Exercise 1.7's `pi` and `sort` cases now produce `imax` and `succ`.

Metavariables are untyped, so the elaborator records "this hole has type `Sort l`"
for implicit type arguments and type holes. After elaboration it asks the kernel for
each solution's type to solve `l` (`solveSortConstraints`).

| #   | Where              | What                                   |
|-----|--------------------|----------------------------------------|
| 4.1 | `Elab/Unify.lean`  | `unifyLevel`                           |
| 4.2 | `Elab/Term.lean`   | `elabLevel`: level syntax → `Level`    |

Optional:
* **4.3** Write your own level normaliser and compare it with `Level.normalize`.
  Can you make `imax` complete?
* **4.4** Postpone level constraints such as `max ?u ?v =?= 1` instead of failing.
* **4.5** Hide inserted implicit arguments when pretty printing (`id Type`, not
  `id (Type 1) Type`). This needs the binder info of the head's type.

## 4b: Σ, Unit, Empty, and type-directed conversion

Structs are Σ types ending in `Unit`, and the Σ binder names are the field names:
`(x : Unit) × (y : Unit) × Unit` supports `p.y`. Pairs have η (`p ≡ (p.1, p.2)`),
and so does `Unit` (`u ≡ ()`).

η for `Unit` can't be decided without types, so **conversion is now type-directed**
(`conv tys A a b`, `convTy`, and `convNe` for neutrals), and neutral spines hold
general eliminations (`Elim`: application, `.1`, `.2`, `let (x, y) := …`, `absurd`).
These changes landed in stage 1's files. Stage 1's exercises keep their numbers, and
the new constructor cases inside them are labelled 4.3–4.8.

Quantities: `(1 x : A) × B` is a pair whose first field is linear. **Projections are
available only on unrestricted pairs**: `p.1` keeps one component and drops the other, so
`p.1` and `p.2` use `p` ω times, whatever the component types, and so does a projection
of an expression (`(act w).1` uses `w` ω times). A pair held at quantity 1 (or at a
quantity variable) is taken apart with the split form, which binds both components:

```
axiom Tok : Type
def swap {A : Type} (1 p : A × Tok) : (1 t : Tok) × A := let 1 (a, t) := p; (t, a)
def bad  {A : Type} (1 p : A × Tok) : A := p.1
-- error: cannot project p.1: a projection needs an unrestricted pair (it keeps one
-- component and drops the other), but this one uses p, which has quantity 1; take the
-- pair apart with `let 1 (x, y) := p; …` instead
```

Write the quantity: `let (x, y) := p` splits at ω and uses `p` ω times too. An erased
field (`(0 n : A) × B`) can't be projected at runtime at all. In erased positions (types,
proofs, arguments to `0` binders, the value of a `let 0`, a `0` field of a pair being
built) every projection is allowed and uses nothing: `g p.1 p` is fine for
`g : (0 a : A) → (1 p : A × Tok) → …`. (CoreSpec §7.1; Status.md, Q1/R1.)

A **structure** is such a Σ, and `s.field` is a projection: so a structure can only be
held unrestricted for now. `(1 g : Guard)` can be passed along, but no field of it can
be read, `match` doesn't take it apart, and a nested `let 1 (x, y)` leaves the
structure's marker tail unconsumed. Use a tuple for linear data, e.g. `Nat × Tok`
instead of `structure Guard where n : Nat; tok : Tok`. (Linear matching is not there
yet: `wiz-notes/wishful/linear-case.md`.)
This includes a one-field wrapper (`structure Coin where value : Nat`, read with
`c.value` at 1), which worked before: write it as `def Coin : Type := Nat`. The planned
form is `let 1 (.mk a b) := s`, compiled to nested splits
(`wiz-notes/linear-case-design.md`). The eliminators follow the same rule:
`ind`, `sfix`, `scase` (and `coit`/`scofix` for their seed) bind what they take apart at
ω, so their scrutinee counts ω times and a value of an inductive type held at 1 can be
passed on but not eliminated; `match` already took its scrutinee at ω. The accepted follow-up is the linear-case plan (`wiz-notes/linear-case-design.md`): K2a (an unused variable may leave its binder when its type is `Unit`, so a linear `Unit` needs no consumer), re-encoding B of structures (the marker in a 0-quantity first component, so a nested `let 1` leaves no marker tail to consume), and a quantity on `scase` (`scase_π`: the scrutinee is used π times and its fields are bound at π·q), which gives structures a destructuring form and linear inductive values an eliminator.

| #   | Where              | What                                                       |
|-----|--------------------|------------------------------------------------------------|
| 4.3 | `Core/Eval.lean`   | `eval` cases for Σ / pairs / Unit / Empty                  |
| 4.4 | `Core/Eval.lean`   | `vSplit`, `vFst`, `vSnd`                                   |
| 4.5 | `Core/Eval.lean`   | `quote` for the new values and eliminations                |
| 4.6 | `Core/Conv.lean`   | η for pairs and Unit; `convTy` and `convNe` cases          |
| 4.7 | `Core/Check.lean`  | typing rules (in the module docstring)                     |
| 4.8 | `Elab/Unify.lean`  | unification cases                                          |
| 4.9 | `Elab/Term.lean`   | `elabFields`: field access by name                         |

`examples/pairs.wiz` shows it all.

## 4c: observational equality

`a = b` is not an inductive type. It is a proposition that **computes** by the type
of `a` and `b` (Pujet & Tabareau, *Observational Equality: Now for Good*):

| at type          | `a = b` computes to                                  | consequence |
|------------------|------------------------------------------------------|-------------|
| `(x : A) → B`    | `(0 x : A) → a x = b x`                              | funext      |
| `(x : A) × B`    | `(e : a.1 = b.1) × cast … a.2 = b.2`                  |             |
| `Unit`, `Empty`  | `True`                                               |             |
| `Prop`           | `(a → b) × (b → a)`                                  | propext     |
| `Type u`         | structural equality of types (propositions inside by equivalence; `μ`, `ν` by their codes, 4g); `False` for different formers | no-confusion |
| a type variable  | stuck                                                 |             |

`cast e t : B` (for `e : A = B`, `t : A`) also computes by the two types.
`transp P p e` transports into propositions, and together they give `J`
(`examples/equality.wiz` derives `subst` and `sym`). Proofs are **definitionally
irrelevant**, so conversion at a proposition always succeeds.

**No regularity (D1).** Regularity, `cast A A e t ≡ t` for *any* proof `e`, would make
`J` compute on `refl` everywhere, but together with an impredicative `Prop` and
irrelevant proofs it makes type checking loop (Abel–Coquand; `Tests/Elab.lean` "D1"). So
it is off (`wiz check --regularity full` turns it back on, for experiments). Instead
`cast` computes on data, constructor by constructor: `cast (μ D i) (μ D' i') e (con x)`
casts each field of `x` along the pieces of `e` (since 4g `μ D i = μ D' i'` compares the
codes) (so a proof field is
cast between propositions, which is a stuck proof: that is what stops the loop).
At **inert** types (first-order data: `Nat`, `Bool`, `List Nat`, … — no `Prop` fields,
functions or type variables) regularity is kept: there a cast between equal types is the
identity. A cast at a type variable (`cast e a` for `e : A = A`) stays stuck, as in
TTobs: `J` computes on `refl` at data types, not at a variable family (docs/CoreSpec.md §8.4).
What regularity said definitionally is available as a proof: the Prelude's axiom
`castRefl : (cast e a : A) = a` (for `e : A = A`). It doesn't compute, it is consistent
(the setoid model), and `#print axioms` shows where it is used.

**Propositions inside types.** Two propositions are equal when equivalent, whatever
their shapes: `True = (True → True)` holds. So equality of types can't compare a
proposition by its shape either, even as the domain of a function type in `Type`:
comparing `(True → Unit) = ((True → True) → Unit)` domain by domain once proved `False`
(`transp` carries the first equation to the second). Type equality first asks each side
whether it is a proposition (`propSort?`): two propositions compare by equivalence, a
proposition and another type are different, and only other types compare by shape. A
`Π` or `Σ` can't tell by itself (`(x : A) → B` is a proposition when `B` is), so it
carries its sort (the elaborator writes it, the kernel checks it); without one, type
equality waits. Surface `Π`/`Σ` get theirs from the levels `checkType` computes; the
ones the elaborator builds itself (a definition's telescope, constructor, recursor and
projection types, a structure's or an index's `Σ`, match motives) get theirs from the
kernel's `typeSort?` in the context they live in (`Sorts` in `Elab/Basic.lean`, applied to
every declaration before the kernel sees it). Only a `Π`/`Σ` under a `fun` whose
variable's type isn't written down, or one that still mentions a metavariable, goes
without. A cast between propositions is itself a proof, so it stays stuck: **proofs are
never evaluated** (the equation of a `cast` and the proofs of a `transp` are kept as
written; `wiz check --eager-proofs` restores the older evaluator that ran them;
docs/CoreSpec.md §8.6).

Stuck equations, casts and proofs are new neutral heads (`Head.eq`, `Head.cast`,
`Head.refl`, …). Some results of the computation rules need new binders. Values can't
contain Lean functions, so those are closures over small term templates (see
`vEq` in `Core/Eval.lean`).

| #    | Where              | What                                                     |
|------|--------------------|----------------------------------------------------------|
| 4.10 | `Core/Eval.lean`   | `eval` cases                                             |
| 4.11 | `Core/Eval.lean`   | `vEq`, `vEqType`, `vCast`: the computation rules         |
| 4.12 | `Core/Eval.lean`   | `quote` for the new heads                                |
| 4.13 | `Core/Conv.lean`   | proof irrelevance, regularity, comparing the new heads   |
| 4.14 | `Core/Check.lean`  | typing rules                                             |

Optional:
* **4.15** Quotient types: `A / R` with `Eq (A / R) [a] [b] ↦ R a b`. This is where
  OTT shines.
* **4.16** Make `rfl` work when the expected equation has already computed (for
  example at function types), by recording the original `a = b` alongside its
  computed form.

## 4d (part 1): quantity polymorphism

Quantities are now **terms** of a primitive type `Qty`. A binder annotation is any
quantity term: a literal (`1`, `ω`), or a variable written `%q`.

```
def app {A B : Type} {q : Qty} (f : (%q x : A) → B) (%q a : A) : B := f a
```

Usage vectors hold **polynomials** over the rig in the quantity variables
(`Core/QPoly.lean`), so `a` above is used `q · 1 = q` times. `used ≤ declared` must
hold for *every* value of the variables. For finite rigs that is decided by trying
all assignments (`QRig.elements?`); for infinite rigs only syntactically equal
polynomials are accepted.

So `def keep {q : Qty} (%q x : A) : A := x` is **rejected**: `q` could be `0`, and an
erased variable can't be returned. (Linear Haskell avoids this by having no `0`
multiplicity.) Bounded quantity variables are an optional exercise.

This is what lets descriptions (next) carry field quantities and still have a
`Desc` eliminator: the eliminator abstracts over a field's quantity like any other
argument.

| #    | Where              | What                                                     |
|------|--------------------|----------------------------------------------------------|
| 4.15 | `Core/QPoly.lean`  | `leSymbolic`: `p ≤ q` for every assignment               |

Stage 1 changed shape slightly: binder quantities are `Term`s / `Val`s, `Usage` holds
`QPoly`s, and `Rig` gained `mul_comm`. The constant case of `QPoly.le` is provided,
so stage 1 still only needs `QRig.le`.

Optional:
* **4.16** Bounded quantity variables: `{q : Qty} [1 ≤ q]`, so that `keep` above is
  accepted, with the constraint checked at use sites.

## 4d (part 2): data as descriptions

Inductive and coinductive types are **anonymous**: `μ D i` and `ν D i` for a
*description* `D : Desc I`. Constructors are tags of a finite `Enum`:

```
def NatD : Desc Unit :=
  Desc.arg 1 (Enum [zero, succ]) (fun t => ecase t [Desc.ret (), Desc.rec 1 () (Desc.ret ())])
def Nat : Type := μ NatD ()
def succ (n : Nat) : Nat := con ('succ, n, (), ())
```

| primitive | meaning |
|---|---|
| `Enum [a, b]`, `'a`, `ecase t [b₀, b₁]` | tags (labels are metadata), case on a tag |
| `Desc I`, `Desc.ret i`, `Desc.arg q S D`, `Desc.rec q j D` | descriptions; fields carry quantities |
| `Desc.elim P mret marg mrec D` | the eliminator of descriptions (generic programming) |
| `μ D i`, `con xs`, `ind P m x` | least fixed point, constructor, induction |
| `ν D i`, `coit S step s`, `out x` | greatest fixed point, unfold, observe |
| `Desc.interp D X i`, `Desc.All D X P i xs` | `⟦D⟧ X i` and the induction hypotheses |

`⟦D⟧`, `All`, the hypotheses and `map` are **not kernel primitives**. They are closed
terms built with `Desc.elim` (`Core/Templates.lean`), so on a neutral description
they get stuck as an ordinary `Desc.elim`. The field quantities are what made the
eliminator need quantity polymorphism: `marg` abstracts over the field's `q : Qty`.

Observational equality extends to data: `con a = con b ↦ a = b`, tags compare by
index, and `Enum`s by size. Equality at ν is stuck (a design decision).

A case uses the **join** of its branches' usages (`0 ⊔ 1 = ω`), so a linear variable
must be used identically in every branch. `ind`'s method is scaled by ω, since it runs
once per node (and so are the methods of `Desc.elim`, `sfix`, `scofix` and `coit`). ω
is the rig's unrestricted quantity (`QRig.many?`); a rig without one, like exact
counting (`Nat`), only lets a method use local variables in erased positions. Erased fields can be projected in erased positions (`Ctx.erased`).

`examples/data.wiz` defines `Bool`, `Nat`, addition by `ind` (with a hand-written
"convoy" to branch on the tag, which `match` will generate in stage 4e), and streams.

| #    | Where                  | What                                                     |
|------|------------------------|----------------------------------------------------------|
| 4.17 | `Core/Templates.lean`  | `allTm` (optional: the others are written for you)       |
| 4.18 | `Core/Eval.lean`       | `eval` cases                                             |
| 4.19 | `Core/Eval.lean`       | `vEcase`, `vDelim`, `vInd`, `vOut`: the computation rules |
| 4.20 | `Core/Check.lean`      | typing rules                                             |

## 4e (part 1): `inductive` and `structure`

```
inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A .zero
  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)

structure Point where
  x : Nat
  y : Nat
```

An `inductive` elaborates to `Vec.desc` (its description), `Vec` (a nominal wrapper
around `μ`, with a *display hint* so it prints as `Vec A n`), and constructors
`Vec.nil`, `Vec.cons`, all checked by the kernel. Constructor fields are elaborated
with `Vec` bound as a local variable: a field of type `Vec A j` becomes `Desc.rec`, the
result type becomes `Desc.ret`. Positivity therefore holds by construction, and any
other occurrence is an error. A `structure` is a Σ ending in `Unit` with constructor
`S.mk`.

Every `inductive` also gets Lean-style eliminators `T.rec` (with induction
hypotheses) and `T.casesOn` (`Elab/Recursor.lean`). They are built on `ind`: a
"convoy" `ecase` on the tag, then a `cast` along the constructor's index equation
(none for a type without indices). Indexed families also get `T.recN` and `T.casesOnN`,
whose motive is a plain type: they need no cast, and `match` uses them when its result
type depends on neither the indices nor the scrutinee. Without regularity (D1) the cast
in `T.rec` computes on a constructor only through the motive's type: at an inert type
(`Vec.length`) it vanishes, at a type variable (`Vec.map : … → Vec B n`) the fields stay
cast (`cons (cast B B _ (f x)) …`).

`.c` (with or without arguments) is a constructor of the expected type. Applications
containing such arguments are elaborated *expected type first* (`checkApp`), so
`.cons .zero .nil : Vec Nat (.succ .zero)` resolves every constructor. Values print
with their constructor names (`.cons .zero .zero .nil`, including erased fields).

| #    | Where                  | What                                        |
|------|------------------------|---------------------------------------------|
| 4.21 | `Elab/Inductive.lean`  | `ctorDesc`: a constructor's description      |

## 4e (part 2): pattern matching and structural recursion

```
def add : Nat → Nat → Nat
  | .zero, n => n
  | .succ m, n => .succ (add m n)

def head {A : Type} {n : Nat} : Vec A (.succ n) → A
  | .cons x _ => x                      -- the `nil` case is impossible, so it's omitted
```

`match` and equation-style definitions compile to case trees over `T.casesOn`
(`compileMatch` in `Elab/Term.lean`). Later match variables are reverted into the
motive. Index *variables* are generalised by the motive, which is Cockx's solution
rule without an equation. Other indices get an equation `idx_c = ξ`, which
observational equality computes. When it contains `False`, the case is closed
automatically with `absurd`. Recursive calls on a recursive field of the first
argument compile through `T.rec`, and the other arguments may change between calls.

The solution rule *with* an equation is supported too (`tail`, `zip`). When the
computed equation contains `y = t` for a constructor field `y`, the later fields are
re-bound with `y := t`, and the branch is transported back along the equation with
`cast`/`transp`.

Coinductive types and **copatterns**:

```
coinductive Stream (A : Type) where
  head : A
  tail : Stream A

def nats (n : Nat) : Stream Nat
  | .head => n
  | .tail => nats (.succ n)
```

A coinductive type is `ν` of a one-constructor description whose fields are the
observations. Each observation `T.f` is a projection of `out`. A copattern definition
compiles to `coit`: the state is the tuple of the definition's explicit arguments
(implicit ones stay fixed), and each recursive observation must be a corecursive call,
whose arguments are the next state. This is the guardedness check.
`(nats .zero).tail.head` uses generalised field notation (`x.f` is `T.f x` for a
nominal type `T`), which also works on inductives.

A copattern definition with **no corecursive observation** is not recursive at all:
it compiles to `cocon`, one cell in front of the values given, and `f` may not occur
on its right-hand sides. That is how a delay is written:

```
def register {A : Type} (init : A) (s : Stream A) : Stream A
  | .head => init
  | .tail => s
```

The same cell as a term is the **coconstructor** `Stream.mk init s` (or `.mk init s`
against a coinductive expected type); `cocon` itself is a data primitive like `con`.
With a sized result type `(Stream Nat)^(↑i)`, the tail is checked at `(Stream Nat)^i`:
`register` is the size bump that guarded feedback needs.
Copatterns keep one syntax for every codata definition (Agda's, and the clause form
Wiz already uses for `match`), so there is no separate `where head := …` notation.
A mix (one recursive observation a corecursive call, another an existing stream) is
still rejected: that needs a state that can be either.

At runtime codata is a lazy cell (`coit`, `scofix`), and the compiled backends
**memoise** observation: `out` on a shared cell overwrites it in place with its payload
(`wiz_lazy_set`, like a forced `memo` thunk), so observing `s.tail` twice computes it
once. A unique cell is about to die, so it is just unfolded; a hoisted constant is not
overwritten. The payload's corecursive fields are always *new* cells built from the
state, never the cell itself, so no cycle forms and reference counting stays exact;
the price is that a stream keeps its observed prefix alive while its root is referenced
(walk it with `s := s.tail` to let the prefix go). A knot is not tied: feedback through
`scofix` (`Signal.fix`) unfolds a new cell per step and stays quadratic. The runtime has
one mutator, as for `memo`; with threads, only shared cells would need a blackhole.
The interpreter (`#eval`) still recomputes. A Mealy machine (`mealy f st i`, state =
its arguments) costs O(1) per step either way.

| #    | Where               | What                                                |
|------|---------------------|-----------------------------------------------------|
| 4.24 | `Elab/Command.lean` | `elabCopatternsCocon`: copatterns without corecursion |

Not yet: course-of-values recursion, and well-founded recursion (`termination_by`).

## 4f: sized types

Well-founded recursion and general corecursion are justified by **sizes** (Abel-style),
your choice over `Acc`/`termination_by` and guarded recursion. `μ` and `ν` carry a size:
`Nat^i` is the naturals below depth `i`, and `Nat` is `Nat^∞`.

* Sizes: `Size`, `∞`, `↑s`, and `Size< s` (sizes below `s`). Comparison uses the
  bounds in the context.
* `∞` is the top size and `↑∞ = ∞`, but `∞` is not below itself. Since every `↑s ≤ ∞`,
  that comparison can't decide `s < ∞` (Agda's `∞ < ∞`, issue #3026, gave `False`). So
  `Size< ∞` holds only sizes built from a bounded variable, `↑ᵏ x` for `x : Size< u`;
  not `∞`, and not a variable of type `Size` (it may stand for `∞`). Running a sized
  function at `∞` is fine: `sfix` takes any `s`, and its recursive calls take sizes below it.
* **Subtyping**: `μ^s ≤ μ^t` when `s ≤ t` (and the reverse for `ν`), applied through Π
  and Σ. The kernel's mode switch checks `inferred ≤ expected` (`subTy`).
* `con xs : μ^{↑s}` for a payload at `μ^s`; `out : ν^{↑s} → ⟦D⟧ (ν^s)`; `cocon` builds ν
  values.
* `sfix P f s i x` is recursion where the recursive call takes any `j : Size< s`. It
  unfolds only on constructors.
* `scase P m s i x` is case analysis on `x : μ^s` whose fields live at some `j : Size< s`.
* `scofix` is sized corecursion that unfolds only under `out`.
* Every inductive also gets `T.scasesOn`.

| #    | Where              | What                                                |
|------|--------------------|-----------------------------------------------------|
| 4.22 | `Core/Eval.lean`   | `vSfix`, `vScase` (and the eval cases)              |
| 4.23 | `Core/Check.lean`  | typing rules for `sfix`, `scofix`, `cocon`, `scase` |

Definitions with a sized signature use all of this automatically:

```
def fib {i : Size} : Nat^i → Nat
  | .zero => .succ .zero
  | .succ .zero => .succ .zero
  | .succ (.succ n) => add (fib n) (fib (.succ n))
```

compiles to `sfix`. Inside, `fib` is a local function that only accepts arguments of
a size below the current one, so the termination check is ordinary type checking.
Matching on a sized value uses `T.scasesOn` (fields at a smaller size). A constructor
checked against a sized type gets size `↑m`, where `m` is the size of its recursive
arguments, so `fib (.succ n)` is accepted because `n` is two levels down. Unconstrained
size metavariables default to `∞`.

Limitations: non-indexed types only, recursion on the first argument, and no
as-patterns (size-preserving functions like `minus` want `x@.zero`).

## 4g: equality of descriptions

```
def refute (e : List Nat = List Bool) : Empty := absurd (((e.2.1.2 'cons).1).2.1.2 'succ)
def ne (e : UIntN 8 = UIntN 16) : Empty := absurd ((e.1.1.2 16).1 (refl 16))
#reduce fun (h : List A = List B) (x y : A) => (cast h [x, y] : List B)   -- [cast _ x, cast _ y]
```

Until now `μ D i = μ D' i'` computed only for one family (the same description,
compared syntactically) and was stuck otherwise, so `List Nat = List Bool` could be
neither proved nor refuted, and neither could `UIntN 8 = UIntN 16`. Now the kernel
compares the **codes** (as in Pujet–Tabareau's universe of codes), in both kernels:

| equation | computes to |
|---|---|
| `μ I D i = μ I' D' i'` | `(I, D, i) = (I', D', i')` (the codes, at `(J : Type) × Desc J × J`): `(e :0 I = I') × ((cast _ D = D') × (cast _ i = i'))` |
| `ret j = ret j'` (at `Desc I`) | `j = j'` |
| `arg q S E = arg q S' E'` | `(e :0 S = S') × ((s :0 S) → E s = E' (cast e s))` |
| `rec q j E = rec q j' E'` | `(j = j') × (E = E')` |
| `hrec q H j E = hrec q H' j' E'` | `((e :0 H = H') × ((h :0 H) → j h = j' (cast e h))) × (E = E')` |
| different constructors, or different quantities | `False` |

A cast between two `μ` (or `ν`) types computes constructor by constructor along the pieces
of the equation, as it did for one family. Proof fields are lifted propositions, which
compare by equivalence. What this costs, and why:

* **`μ D i = μ D i'` is no longer `i = i'`.** It is the general form, whose components
  are `I = I`, `cast _ D = D` and `cast _ i = i'`. Keeping the old answer for one family
  would not be stable under substitution: `List A = List B` becomes one family when
  `B := A`, and its general form would not be convertible to the old one (that needs
  regularity, which is off, 4c). For the same reason nothing is simplified, not even a
  `True` component: so the equations print with `True`s in them.
* So a proof of `n = m` is not a proof of `Vec A n = Vec A m` any more. Use congruence
  (`congrArg (Vec A) h`, or `transp` from `refl`), which is what the elaborator does for
  index equations. `refl (Vec A n)` and `rfl` both prove `Vec A n = Vec A n`: the
  equation's part over the constructor tags, `(t : Enum ls) → …`, is stuck under its
  binder, so `rfl` proves it tag by tag (a case split, wrapped in a `transp` because the
  binder is erased; `rflProof` in `Elab/Term.lean`). One expected limit: if a later
  index of the type depends on a field at a type *variable*, `rfl` is left with a stuck
  cast at that variable and fails; `refl T` still works.
* A `cast e t` with no expected type reads its target off the type of `e`, which works
  only while that equation is stuck. Equations between data types now compute, so write
  `(cast e t : T)` (or use the cast where its type is expected); the error says so.
* `μ` is now injective in its description, a large-into-small map (Hur's paradox has
  this shape). It is the same shape as the injectivity of Π that observational equality
  already has, and a description can't range over its own universe (fields are exactly in
  `Sort (l+1)`), so the model of codes covers it. That is an argument, not a proof:
  docs/CoreSpec.md §8.4b, docs/Status.md E1.

## 4h: linear case analysis

A value of an inductive type held at quantity 1 can be taken apart (linear-case stage 2;
design in `wiz-notes/linear-case-design.md`, K1 and the unit eliminator (K2a withdrawn); rules and soundness argument in
`docs/CoreSpec.md` §10.2 and §10.2a).

* **K1, `scase` at a quantity.** `Term.scase` carries a quantity `q`. The method runs once
  and receives the payload at `q`; the scrutinee is used `q` times (`U_m + q·U_x`). At ω
  this is the old case; at 1 a linear value is taken apart; at 0 the scrutinee is erased
  and the method can't branch on it. Both kernels (`Check.lean`, `Kernel.wiz`).
* **The unit eliminator** `let () := u; b` consumes a `u : Unit` (its usage counts once)
  and is compiled as "evaluate `u`, then `b`". It is the only way a linear `Unit` is
  used up. (K2a, "a unit-shaped binder may go unused", was implemented and withdrawn:
  a closure of a unit-shaped type can hold a resource; `docs/CoreSpec.md` §10.2a lists
  the counterexamples.)
* **`T.casesOn1`**, generated for every inductive next to `T.casesOnA`: the additive case
  with the scrutinee at 1, built on `scase` at 1 and `split`s at 1 (fields come out at
  their declared quantities), ending in `let () := u` for the payload's final `Unit`. `match` uses it when the scrutinee mentions a variable
  bound at 1 (the scrutinee is then bound at 1 too), and a field bound at 1 is linear
  again for a nested match.

```
inductive Res1 (A : Type) where
  | ok (1 a : A)
  | err (e : Nat) (1 back : A)
def rebuild (1 r : Res1 Tok) : Res1 Tok := match r with
  | .ok t => .ok t
  | .err e t => .err e t          -- dropping `t`, or using it twice: a quantity error
```

A field that holds a resource must be declared at 1 (`1 val : S`): an ω field puts its
value in an ω position. A *structure* held at 1 still can't be taken apart (its marker
tail can't be consumed); linear data is a one-constructor `inductive`. Tests: the group `linear-case`, and `linearCaseRule` (both
kernels) in the self-hosted group.
