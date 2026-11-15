import Std.Data.HashMap
import Wiz.Core.Level
import Wiz.Syntax.PPTable

/-!
# Core terms

The kernel language. Variables are **de Bruijn indices**: `var 0` is the nearest
enclosing binder, `var 1` the next one out, and so on. This makes α-equivalence
syntactic equality and keeps substitution out of the kernel entirely (we never
substitute; see `Wiz.Core.Eval` for normalisation by evaluation).

Names on binders (`x`) are kept only for pretty-printing.

The quantity `q` on `pi` and `letE` is the QTT annotation. It is itself a term of
type `Qty`: a literal `qlit r` (`r : R`), or (stage 4d) a quantity variable. Lambdas carry no
quantity or domain: they are only ever *checked* against a `pi`, which supplies both.

`BinderInfo` on `pi` says whether the argument is explicit or implicit. The kernel
ignores it; the elaborator uses it to insert implicit arguments.

`mvar` is a metavariable, a hole the elaborator (stage 3) is still solving. The kernel
evaluates it to a stuck neutral and rejects it in the type checker. Elaborated terms
have all their metavariables replaced before they reach the kernel.

Universe levels are described in `Wiz.Core.Level`.

Stage 4 added Σ-types, observational equality, descriptions with μ/ν data, and sizes.
-/

namespace Wiz

inductive BinderInfo where
  | default
  | implicit
  /-- `[x : C A]`: filled by type class resolution (the kernel treats it as implicit) -/
  | instImplicit
  deriving Repr, BEq, DecidableEq, Inhabited

/-- (Mandatory sorts) The sorts of a `Π`/`Σ`'s two components: the domain (first
component) is in `Sort dom`, the codomain (second component, under the binder) in
`Sort cod`. The `Π` is in `Sort (imax dom cod)` (`piSort`), the `Σ` in
`Sort (max dom cod)` (`sigmaSort`). The kernel checks each against the inferred sort of
its component (rules *pi* and *sigma*, `docs/CoreSpec.md` §6, §7.1) and reads them to
decide whether the type is a proposition (`propSort?`) and whether a cast computes
(`vCast`, D2). A `Level.hole` is a sort the elaborator has not written yet: the sorts
pass fills every one, and the kernel rejects one. -/
structure BinderSorts where
  dom : Level
  cod : Level
  deriving Repr, Inhabited, BEq, Hashable

namespace BinderSorts

/-- Both sorts still to be filled (elaborator only). -/
def hole : BinderSorts := ⟨.hole, .hole⟩

/-- The sort of the `Π`. -/
def piSort (σ : BinderSorts) : Level := .imax σ.dom σ.cod

/-- The sort of the `Σ`. -/
def sigmaSort (σ : BinderSorts) : Level := .max σ.dom σ.cod

def hasHole (σ : BinderSorts) : Bool := σ.dom.hasHole || σ.cod.hasHole

def mapM {m : Type → Type} [Monad m] (f : Level → m Level) (σ : BinderSorts) : m BinderSorts :=
  return ⟨← f σ.dom, ← f σ.cod⟩

/-- Componentwise equivalence (`Level.equiv`). -/
def equiv (σ τ : BinderSorts) : Bool := σ.dom.equiv τ.dom && σ.cod.equiv τ.cod

/-- Fill the holes of `σ` with the sorts `dom?`/`cod?`, where known. -/
def fill (σ : BinderSorts) (dom? cod? : Option Level) : BinderSorts :=
  ⟨if σ.dom.hasHole then dom?.getD σ.dom else σ.dom,
   if σ.cod.hasHole then cod?.getD σ.cod else σ.cod⟩

end BinderSorts

inductive Term (R : Type) where
  /-- de Bruijn index -/
  | var (ix : Nat)
  /-- a global declaration, with its universe level parameters instantiated -/
  | const (name : Name) (levels : List Level)
  /-- `Sort l` (`Prop` is `Sort 0`, `Type u` is `Sort (u+1)`). Non-cumulative:
  `Sort l : Sort (l+1)` only. -/
  | sort (level : Level)
  /-- `(q x : dom) → cod` (or `{q x : dom} → cod`), where `cod` lives under one extra
  binder. `σ` gives the sorts of `dom` and `cod` (mandatory sorts, `BinderSorts`): type
  equality compares propositions by logical equivalence, other types by their parts,
  and needs to know which is which (the kernel checks `σ`, component by component) -/
  | pi (x : Name) (bi : BinderInfo) (q : Term R) (dom cod : Term R) (σ : BinderSorts)
  /-- `λ x. body`, where `body` lives under one extra binder -/
  | lam (x : Name) (body : Term R)
  | app (fn arg : Term R)
  /-- `let x :q ty := val; body`, where `body` lives under one extra binder -/
  | letE (x : Name) (q : Term R) (ty val body : Term R)
  /-- `(tm : ty)`, used to switch from checking to inference -/
  | ann (tm ty : Term R)
  /-- metavariable number `id` (elaborator only) -/
  | mvar (id : Nat)
  -- Stage 4: structural types. `sigma` binder names double as field names.
  /-- `(q x : A) × B`: the first component may be used `q` times; `σ` as for `pi` -/
  | sigma (x : Name) (q : Term R) (fst snd : Term R) (σ : BinderSorts)
  | pair (a b : Term R)
  | fst (t : Term R)
  | snd (t : Term R)
  /-- `let q (x, y) := scrut; body` with motive `fun z => motive` for the result type.
  `motive` is under one binder (`z`), `body` under two (`x`, then `y`). -/
  | split (q : Term R) (scrut : Term R) (z : Name) (motive : Term R) (x y : Name) (body : Term R)
  /-- the unit type in `Sort l`: `True` at level 0, `Unit` at level 1 -/
  | unit (level : Level)
  | tt
  /-- the empty type in `Sort l`: `False` at level 0, `Empty` at level 1 -/
  | empty (level : Level)
  /-- `absurd t : motive`, given `t : empty l` -/
  | absurd (motive t : Term R)
  /-- `let () := u; b`: the unit eliminator (linear logic's 1-elimination, linear-case
  stage 2). `u : Unit_l` is consumed (its usage counts), then `b`. It computes to `b` by
  η (every `u` is `()`), but compiled code evaluates `u` first: a consumer stashed in a
  unit runs. The only way a linear `Unit` is used up. -/
  | letUnit (u b : Term R)
  -- Stage 4c: observational equality.
  /-- `a = b` at type `A : Type u`. A proposition that *computes* by `A`. -/
  | eq (A a b : Term R)
  /-- `A = B` for types (what `eq (Sort l) A B` computes to); no level needed -/
  | eqTy (A B : Term R)
  /-- `refl a : a = a` (`A` is the type of `a`) -/
  | refl (A a : Term R)
  /-- `refl X : X = X` for a type `X` -/
  | reflTy (X : Term R)
  /-- `cast A B e t : B` given `e : A = B` and `t : A`. Computes by `A` and `B`. -/
  | cast (A B e t : Term R)
  /-- `transp A a P p b e : P b e` given `P : (b : A) → a = b → Prop`, `p : P a (refl a)`
  and `e : a = b`. Transport into propositions; with `cast` it gives `J`. -/
  | transp (A a P p b e : Term R)
  -- Stage 4d: quantity polymorphism. Binder quantities are terms of type `Qty`.
  /-- the type of quantities -/
  | qty
  /-- a quantity literal -/
  | qlit (r : R)
  -- Stage 4d: data. Labels are metadata; conversion ignores them.
  /-- a finite enumeration of tags, `Enum [a, b, c]` -/
  | enum (labels : List Name)
  /-- the `i`-th tag of an enumeration -/
  | tag (labels : List Name) (i : Nat)
  /-- `ecase t [b₀, …]` with motive `fun z => motive` -/
  | ecase (z : Name) (motive : Term R) (scrut : Term R) (branches : List (Term R))
  /-- descriptions of indexed inductive types, `Desc.{l} I` -/
  | desc (l : Level) (I : Term R)
  | dret (i : Term R)
  /-- a non-recursive field of quantity `q` and type `S`; `D : S → Desc I` -/
  | darg (q S D : Term R)
  /-- a recursive field of quantity `q` at index `j` -/
  | drec (q j D : Term R)
  /-- an infinitary recursive field `(h : H) → μ D (j h)` of quantity `q`, for
  `j : H → I` (a "higher" recursive field: one subtree per `h`) -/
  | dhrec (q H j D : Term R)
  /-- the eliminator of descriptions, into `P : Desc I → Sort v` -/
  | delim (v : Level) (P mret marg mrec mhrec D : Term R)
  /-- the least fixed point `μ D i`. `hint` is display metadata: the nominal form
  (`Vec A n`) to print instead; conversion ignores it. -/
  | mu (l : Level) (I D i : Term R) (sz : Term R) (hint : Option (Name × List Level × List (Term R)))
  | con (x : Term R)
  /-- induction: `ind P m i x : P i x` for `x : μ D i` -/
  | ind (l : Level) (I D : Term R) (v : Level) (P m i x : Term R)
  /-- the greatest fixed point `ν D i` -/
  | nu (l : Level) (I D i : Term R) (sz : Term R) (hint : Option (Name × List Level × List (Term R)))
  /-- observation: `out x : ⟦D⟧ (ν D) i` -/
  | out (x : Term R)
  -- Sized types: sizes are erased bounds on the depth of μ/ν values.
  /-- the type of sizes -/
  | size
  /-- the infinite size: `μ^∞` is the ordinary inductive type -/
  | szInf
  /-- the successor size `↑s` -/
  | szSuc (s : Term R)
  /-- `Size< s`: the sizes below `s` -/
  | sizeLt (s : Term R)
  /-- sized recursion: `sfix P f s i x : P i x` for `x : μ^s D i`, where
  `f : (s : Size) → ((j : Size< s) → (i : I) → (y : μ^j D i) → P i y) → (i : I) → (x : μ^s D i) → P i x`.
  It unfolds only on a constructor. -/
  | sfix (l : Level) (I D : Term R) (v : Level) (P f s i x : Term R)
  /-- sized case analysis at a quantity: `scase_q P m s i x : P i x` for `x : μ^s D i`, where
  `m : (j : Size< s) → (i : I) → (q xs : ⟦D⟧ (μ^j D) i) → P i (con xs)`: the fields have
  some size below `s`, and the payload is handed over at `q` (K1 of the linear-case
  design: `q = ω` is the ordinary case, `q = 1` takes a linear value apart). `q` is a
  quantity term, as `split`'s. -/
  | scase (l : Level) (q : Term R) (I D : Term R) (v : Level) (P m s i x : Term R)
  /-- a ν constructor: `cocon xs : ν^{↑s} D i` for `xs : ⟦D⟧ (ν^s D) i` -/
  | cocon (x : Term R)
  /-- sized corecursion: `scofix A f s i a : ν^s D i`, where
  `f : (s : Size) → ((i : I) → A i → ν^s D i) → (i : I) → A i → ν^{↑s} D i`.
  It unfolds only when observed with `out`. -/
  | scofix (l : Level) (I D A f s i a : Term R)
  /-- coiteration: unfold a state `s : S i` with `step` -/
  | coit (l : Level) (I D S step i s : Term R)
  /-- a numeral of the `builtin nat` type. It means `succ (… (succ zero))`, and
  unfolds one step at a time when something looks inside it. -/
  | natLit (n : Nat)
  /-- only made by `eval`, inside the closure for a registered operation such as
  `nat.add`: compute natively when the arguments (variables) are literals, else apply
  the definition -/
  | natOp (op : Name) (args : Array (Term R))
  -- Q4: lifting a type to a bigger universe
  /-- `ULift.{l} A : Sort l` for `A : Sort k` with `k ≤ l`: a copy of `A` one or more
  universes up. Description fields must live exactly in `Sort (l+1)`, so the elaborator
  wraps smaller ones (proof fields, and fields of a level-polymorphic type whose level
  is a `max`). A lifted proposition (`l ≠ 0`) is not a proposition: its inhabitants are
  boxed proofs, all equal by η. Erased at run time. `k` is `A`'s sort (mandatory sorts:
  the kernel checks it, and the equation and cast at `ULift` read it). -/
  | ulift (k l : Level) (A : Term R)
  /-- `up a : ULift A` for `a : A` (checked only) -/
  | up (a : Term R)
  /-- `down t : A` for `t : ULift A`; `down (up a) ↦ a`, and `t ≡ up (down t)` (η) -/
  | down (t : Term R)
  /-- (P2) **the proof marker**: `prf.{l} t : T` for `t : T`, where `l` must be the sort
  of `T` (`T : Sort l`; the kernel verifies it). When `l` is `0`, `t` is a proof: the
  evaluator suspends it and never looks at it (`Head.prf`); otherwise it evaluates `t`.
  A level-generic term is marked at its level `u` and becomes a suspended proof at the
  instance `u := 0`. Outside a proof, the kernel requires every term whose sort may be
  `0` to be marked or neutral-shaped (`Check.lean`, "the proof marker"): so it never
  evaluates a proof. The elaborator's marking pass (`Wiz/Elab/Mark.lean`) inserts it. -/
  | prf (l : Level) (t : Term R)
  deriving Repr, Inhabited, BEq

/-- A global declaration. `value = none` is an axiom/postulate. -/
structure Decl (R : Type) where
  name  : Name
  /-- universe level parameters, e.g. `[u]` for `def id.{u} ...` -/
  levelParams : List Name := []
  type  : Term R
  value : Option (Term R)
  /-- unfold eagerly instead of gluing (constructors, so values look like constructor
  applications) -/
  inline : Bool := false
  /-- an implementation for the compiler: the term compiled code runs instead of `value`
  (a structurally recursive definition's value with direct recursion instead of the
  recursor, `deriveImpl`; a partial definition's body; a native implementation's
  constant). The kernel never unfolds it, but checks it against `type` (`checkImpl` in
  `addDecl`/`setImpl`, `addPartialImpl`), so erasure only sees checked terms, and checks
  that a derived one computes what `value` computes (`checkImplAgrees`). -/
  impl : Option (Term R) := none
  /-- a partial definition's witness: a term of its type that the kernel checks
  (`addPartialDecl`). The definition stays opaque (`value = none`) but is not an axiom:
  its type is inhabited, so assuming `f : T` proves nothing that `w : T` doesn't. -/
  witness : Option (Term R) := none
  deriving Repr, Inhabited

/-- The native implementation of a definition (`attribute [implemented_by g] f`): compiled
code runs `g` for `f`, while the kernel keeps `f`'s definition. It is the `impl` that is
just another constant (a recursive definition's `impl` is its own equations, a partial
definition's is its body, which has a witness). -/
def Decl.nativeImpl? {R : Type} (d : Decl R) : Option Name :=
  if d.witness.isSome then none else
  match d.impl with
  | some (.const g _) => if g == d.name then none else some g
  | _ => none

/-- Does compiled code run equations of this definition derived from its value? A
structurally recursive definition's `impl` (its value with direct recursion,
`deriveImpl`): the kernel checks its type and that it agrees with the value
(`checkImplAgrees`). Not a native implementation (`nativeImpl?`, trusted and listed by
`#print axioms`) nor a partial definition's body (it has no value to agree with). -/
def Decl.derivedEquations {R : Type} (d : Decl R) : Bool :=
  d.impl.isSome && d.value.isSome && d.witness.isNone && d.nativeImpl?.isNone

namespace Term

variable {R : Type}

/-- Rebuild a term with `fl` applied to its levels and `f k c` to each immediate
child `c`, where `k` is the number of binders the child is under. Generic traversals
(level instantiation, zonking, free-variable checks) are written with this so they
don't need a case per constructor. -/
@[specialize] def mapChildrenM {m : Type → Type} [Monad m] (fl : Level → m Level)
    (f : Nat → Term R → m (Term R)) : Term R → m (Term R)
  | .pi x bi q a b s => return .pi x bi (← f 0 q) (← f 0 a) (← f 1 b) (← s.mapM fl)
  | .lam x b => return .lam x (← f 1 b)
  | .app a b => return .app (← f 0 a) (← f 0 b)
  | .letE x q t v b => return .letE x (← f 0 q) (← f 0 t) (← f 0 v) (← f 1 b)
  | .ann a b => return .ann (← f 0 a) (← f 0 b)
  | .sort l => return .sort (← fl l)
  | .const n ls => return .const n (← ls.mapM fl)
  | .sigma x q a b s => return .sigma x (← f 0 q) (← f 0 a) (← f 1 b) (← s.mapM fl)
  | .pair a b => return .pair (← f 0 a) (← f 0 b)
  | .fst t => return .fst (← f 0 t)
  | .snd t => return .snd (← f 0 t)
  | .split q s z m x y b => return .split (← f 0 q) (← f 0 s) z (← f 1 m) x y (← f 2 b)
  | .unit l => return .unit (← fl l)
  | .empty l => return .empty (← fl l)
  | .absurd a b => return .absurd (← f 0 a) (← f 0 b)
  | .letUnit u b => return .letUnit (← f 0 u) (← f 0 b)
  | .eq A a b => return .eq (← f 0 A) (← f 0 a) (← f 0 b)
  | .eqTy A B => return .eqTy (← f 0 A) (← f 0 B)
  | .refl A a => return .refl (← f 0 A) (← f 0 a)
  | .reflTy X => return .reflTy (← f 0 X)
  | .cast A B e t => return .cast (← f 0 A) (← f 0 B) (← f 0 e) (← f 0 t)
  | .transp A a P p b e => return .transp (← f 0 A) (← f 0 a) (← f 0 P) (← f 0 p) (← f 0 b) (← f 0 e)
  | .ecase z mo s bs => return .ecase z (← f 1 mo) (← f 0 s) (← bs.mapM (f 0))
  | .desc l I => return .desc (← fl l) (← f 0 I)
  | .dret i => return .dret (← f 0 i)
  | .darg q S D => return .darg (← f 0 q) (← f 0 S) (← f 0 D)
  | .drec q j D => return .drec (← f 0 q) (← f 0 j) (← f 0 D)
  | .dhrec q H j D => return .dhrec (← f 0 q) (← f 0 H) (← f 0 j) (← f 0 D)
  | .delim v P a b c h D => return .delim (← fl v) (← f 0 P) (← f 0 a) (← f 0 b) (← f 0 c) (← f 0 h) (← f 0 D)
  | .mu l I D i s h => return .mu (← fl l) (← f 0 I) (← f 0 D) (← f 0 i) (← f 0 s) (← h.mapM (hintM fl f))
  | .con x => return .con (← f 0 x)
  | .ind l I D v P mt i x =>
    return .ind (← fl l) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 mt) (← f 0 i) (← f 0 x)
  | .nu l I D i s h => return .nu (← fl l) (← f 0 I) (← f 0 D) (← f 0 i) (← f 0 s) (← h.mapM (hintM fl f))
  | .out x => return .out (← f 0 x)
  | .szSuc s => return .szSuc (← f 0 s)
  | .sizeLt s => return .sizeLt (← f 0 s)
  | .sfix l I D v P g s i x =>
    return .sfix (← fl l) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 g) (← f 0 s) (← f 0 i) (← f 0 x)
  | .cocon x => return .cocon (← f 0 x)
  | .scase l q I D v P m s i x =>
    return .scase (← fl l) (← f 0 q) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 m) (← f 0 s) (← f 0 i) (← f 0 x)
  | .scofix l I D A g s i a =>
    return .scofix (← fl l) (← f 0 I) (← f 0 D) (← f 0 A) (← f 0 g) (← f 0 s) (← f 0 i) (← f 0 a)
  | .coit l I D S st i s =>
    return .coit (← fl l) (← f 0 I) (← f 0 D) (← f 0 S) (← f 0 st) (← f 0 i) (← f 0 s)
  | .ulift k l A => return .ulift (← fl k) (← fl l) (← f 0 A)
  | .up a => return .up (← f 0 a)
  | .down t => return .down (← f 0 t)
  | .prf l t => return .prf (← fl l) (← f 0 t)
  -- (the arguments are children like any others: `Val.lvlBound` reads a closure's free
  -- variables through this traversal, and missing them here made `sameVal` identify
  -- `Nat.add x` with `Nat.add y`, which proved `False`; `wiz-notes/soundness-audit.md`, S1)
  | .natOp op args => return .natOp op (← args.mapM (f 0))
  -- the leaves, by name: with a default arm a new constructor would be skipped silently
  -- (S1), and this way it does not compile until it has a case
  | t@(.var _) | t@(.mvar _) | t@.tt | t@.qty | t@(.qlit _) | t@(.enum _) | t@(.tag ..) | t@.size | t@.szInf
  | t@(.natLit _) => pure t
where
  hintM (fl : Level → m Level) (f : Nat → Term R → m (Term R)) :
      Name × List Level × List (Term R) → m (Name × List Level × List (Term R))
    | (n, us, as) => return (n, ← us.mapM fl, ← as.mapM (f 0))

/-- Visit every immediate child (and level), ignoring the rebuilt term. -/
def forChildren {m : Type → Type} [Monad m] (fl : Level → m Unit) (f : Nat → Term R → m Unit)
    (t : Term R) : m Unit := do
  let _ ← t.mapChildrenM (fun l => do fl l; pure l) (fun k c => do f k c; pure c)

/-- Shift the free variables (indices `≥ cut`) up by `k`. -/
partial def lift (k : Nat) (cut : Nat := 0) : Term R → Term R
  | .var i => if i ≥ cut then .var (i + k) else .var i
  | t => Id.run <| t.mapChildrenM pure (fun d c => pure (lift k (cut + d) c))

/-- Abstract every occurrence of `target` (a term in the same context) as a new
variable `var 0`, shifting the other free variables up. This is how the elaborator
generalises a scrutinee in the expected type of a case (Lean's `kabstract`). -/
partial def abstract [BEq R] (t : Term R) (target : Term R) (depth : Nat := 0) : Term R :=
  if t == target.lift depth then .var depth else
  match t with
  | .var i => if i ≥ depth then .var (i + 1) else .var i
  | t => Id.run <| t.mapChildrenM pure (fun d c => pure (abstract c target (depth + d)))

/-- Remove variable `k`, which must not occur, lowering the variables above it. -/
partial def strengthen? (k : Nat) (t : Term R) (depth : Nat := 0) : Option (Term R) :=
  match t with
  | .var i =>
    if i < depth || i < k + depth then some (.var i)
    else if i == k + depth then none
    else some (.var (i - 1))
  | t => t.mapChildrenM (m := Option) some (fun d c => strengthen? k c (depth + d))

/-- Substitute `s` for variable `k`. `s` is a term in the context *without* `k`. -/
partial def instantiateAt (t : Term R) (k : Nat) (s : Term R) (depth : Nat := 0) : Term R :=
  match t with
  | .var i =>
    if i < depth || i < k + depth then .var i
    else if i == k + depth then s.lift depth
    else .var (i - 1)
  | t => Id.run <| t.mapChildrenM pure (fun d c => pure (instantiateAt c k s (depth + d)))

/-- (P2) Remove the proof markers that mark nothing: `prf.{l} t` at a level that is not
`0` is `t` (a level-generic term, at an instance that is not `Prop`). A proof (`l = 0`)
is kept as it is. For the compiler, which looks at the shapes of terms. -/
partial def stripMarks : Term R → Term R
  | .prf l t => if l.isZero then .prf l t else stripMarks t
  | t => Id.run <| t.mapChildrenM pure (fun _ c => pure (stripMarks c))

/-- The head and arguments of an application spine. -/
def spine : Term R → Term R × List (Term R)
  | .app f a => let (h, as) := spine f; (h, as ++ [a])
  | t => (t, [])

/-- Instantiate universe level parameters `ps` with `us`. -/
partial def instLevels (ps : List Name) (us : List Level) (t : Term R) : Term R :=
  -- (no parameters: nothing to replace; the copy cost a traversal of the body at every
  -- unfolding of a global, `wiz-notes/kernel-eval.md`)
  if ps.isEmpty then t else
  Id.run <| t.mapChildrenM (fun l => pure (l.instParams ps us)) (fun _ c => pure (instLevels ps us c))

/-- Does `var ix` occur free in `t`? (Trusted: `Ctx.instArg` in `Check.lean` skips
evaluating an argument when this says the codomain doesn't mention it. It is complete
because `mapChildrenM` visits every child of every constructor.) -/
partial def hasVar (ix : Nat) : Term R → Bool
  | .var i => i == ix
  | t => (t.forChildren (m := StateM Bool) (fun _ => pure ())
      (fun k c => modify (· || c.hasVar (ix + k))) |>.run false).2

/-- (Mandatory sorts) Does the term contain a `Level.hole` (a `Π`/`Σ` or `ULift` sort the
sorts pass has not filled yet)? -/
partial def hasHole (t : Term R) : Bool :=
  (go t |>.run false).2
where
  go (t : Term R) : StateM Bool Unit := do
    if ← get then return
    t.forChildren (fun l => modify (· || l.hasHole)) (fun _ c => go c)

/-- All level parameter names mentioned in a term. -/
partial def levelParamsUsed (t : Term R) : List Name :=
  (go t |>.run []).2
where
  go (t : Term R) : StateM (List Name) Unit :=
    t.forChildren (fun l => modify (l.params ++ ·)) (fun _ c => go c)

end Term

/-- A description that starts with a choice of tag, `Desc.arg q (Enum ls) F`, or, in a
data type above `Type`, `Desc.arg q (ULift (Enum ls)) F` (Q4: the tag is lifted to the
type's universe). Returns the labels, whether the tag is lifted, and `F`. -/
def Term.descTag? {R : Type} : Term R → Option (List Name × Bool × Term R)
  | .darg _ (.enum ls) F => some (ls, false, F)
  | .darg _ (.ulift _ _ (.enum ls)) F => some (ls, true, F)
  | _ => none

/-- The constant of the constructor with tag `c` of the data type `T`: `T.c`. A `mutual`
block's family (`Elab/Command.lean`, `mutualInductive`) holds every member's
constructors under tags qualified by the member (`Ev.s`, `Od.s`: two members may share a
constructor name), and such a constructor is named by its tag alone, so `Ev.s` is the
constant and the family's name stays internal. An ordinary constructor's tag is one
identifier without a dot (`inductive` rejects `| a.b`). -/
def ctorConst (T c : Name) : Name := if c.contains '.' then c else T ++ "." ++ c

/-- A constructor tag as written after a dot (`.s`): a qualified tag's last component. -/
def ctorShort (c : Name) : Name := ((c.splitOn ".").getLast?).getD c

/-- Does the constructor written `.c'` (or `T.c'`, `c'` then the resolved tag) select
the tag `c`? A qualified tag (`Ev.s`) is also selected by its last component. -/
def ctorSelects (c' c : Name) : Bool := c' == c || (c.contains '.' && ctorShort c == c')

/-- The binder name of a **phantom** argument (`Elab/Inductive.lean`): a type whose
parameters no field mentions ends in `(0 phantom✝ : D) → … → Unit` instead of `Unit`,
with `D` mentioning the parameter. Such a function type has one inhabitant up to η,
`fun _ => ()`, so it has no runtime content (`erasable`, which goes by the type's shape,
not by this name: conversion ignores binder names). The name is inaccessible, so only
the elaborator writes it; it uses it to let `()` stand for the tail's value. -/
def phantomName : Name := "phantom✝"

/-- The **structure marker** (stage 22i): a structure with at least one field ends in
`(0 phantom✝ : D) → … → (0 fields✝ : Enum [fields✝]) → Unit` (its phantom tail, 22e, then
the marker), so `structure S where val : A` is `(val : A) × ((0 fields✝ : Enum [fields✝]) → Unit)`.
It is a function into `Unit` with an erased argument, like a phantom tail, so it is a
singleton and has no runtime content. Erasure does **not** recognise it by this label or
by a binder name: conversion ignores both (`Enum` types are compared by length), so a
user's `(0 f : Enum [x]) → Unit` is the same type, and a representation must be the same
for convertible types. `Compiler/Erase.lean` goes by the shape (`erasedFunTy`), and
unboxes the Σ before such a tail only under `--unbox-structs` (`unboxedSigma`). -/
def structTailName : Name := "fields✝"

/-- The marker's domain, `Enum [fields✝]`. -/
def structTailDom {R : Type} : Term R := .enum [structTailName]

/-- The **seal** of a `sealed inductive T` (stage 22k): an axiom `T.seal✝ : Type`, private
to `T`'s module, that `T`'s index tail mentions (`(0 phantom✝ : T.seal✝) → … → Unit`,
like a phantom type parameter, 22e). A constant without a value is compared by name, so
a declaration of the same shape that can't write the name is not convertible to `T`. -/
def sealName (T : Name) : Name := T ++ ".seal✝"

/-- The registration of a seal, `seal:T` (with the seal's name), among the builtins. -/
def sealKey (T : Name) : Name := "seal:" ++ T

/-- A binder name of a phantom tail (`phantomName` or `structTailName`). -/
def isPhantomName (x : Name) : Bool := x == phantomName || x == structTailName

/-- The value of a phantom tail type, `fun _ … _ => ()`. -/
partial def Term.phantomTailVal? {R : Type} : Term R → Option (Term R)
  | .pi x _ _ _ b _ => if isPhantomName x then (phantomTailVal? b).map (.lam x) else none
  | .unit _ => some .tt
  | _ => none

/-! ### The step budget for reading proofs back (P2)

The kernel never evaluates a proof. The elaborator does, when it reads a value that
holds a suspended proof back into a term (`quote` outside the kernel: metavariable
solutions, `#reduce`, hover, messages), and a proof need not have a normal form
(Abel–Coquand). So that evaluation runs within a **budget of steps**, counted, not
timed: the same on every machine and in every run. A step is one instantiation of a
closure (a β-step, or going under a binder to read it back); every loop of the evaluator
takes one. When the budget runs out the evaluator stops computing (a closure's
instantiation is a stuck constant from then on), and the proof reads back as a constant
whose name is the message.

The counter is a mutable cell behind a pure interface (`unsafeBaseIO`). It is made for
one read-back, used only by the evaluation that read-back starts, and dropped with it,
so nothing else can observe it. The kernel's own evaluation never has one
(`Globals.budget = none`): it does not evaluate proofs, so it needs no bound. -/

/-- A step budget: the steps left, plus one (`0`: it ran out). -/
structure Budget where
  ref : IO.Ref Nat

namespace Budget

instance : Nonempty Budget := ⟨⟨Classical.choice inferInstance⟩⟩

@[never_extract, noinline] unsafe def tickImpl (b : Budget) : Bool :=
  unsafeBaseIO do
    let n ← b.ref.get
    if n ≤ 1 then do b.ref.set 0; pure false
    else do b.ref.set (n - 1); pure true

/-- Take one step: `false` when the budget has run out. -/
@[implemented_by tickImpl] opaque tick (b : Budget) : Bool

/-- (An action, so that what comes after it in `runImpl` comes after `x` is computed: the
compiler may move a pure computation, not an action.) -/
@[never_extract, noinline] private def computed {α : Type} (x : α) : BaseIO α := pure x

@[never_extract, noinline] unsafe def runImpl {α : Type} [Inhabited α] (steps : Nat) (f : Budget → α) : α × Nat :=
  unsafeBaseIO do
    let r ← IO.mkRef (steps + 1)
    let x ← computed (f ⟨r⟩)
    let left ← r.get
    -- (the budget is over: a closure that outlived it, in a metavariable's solution, must
    -- not find it exhausted later)
    r.set (1 <<< 62)
    pure (x, steps + 1 - left)

/-- Compute `f` with a fresh budget of `steps` steps. Returns the result and the number of
steps it took; `steps + 1` means the budget ran out. (Afterwards the budget no longer
counts: a value made under it that is forced later computes freely.) -/
@[implemented_by runImpl] opaque run {α : Type} [Inhabited α] (steps : Nat) (f : Budget → α) : α × Nat

/-- What a proof reads back as when its budget ran out: a constant with this name. No
declaration has it, so the kernel rejects a term that contains it, with this text. -/
def message (steps : Nat) : String :=
  s!"‹a proof was not read back: it needs more than {steps} evaluation steps (raise the bound with --proof-steps N)›"

/-- Is this the name of `message`'s constant? -/
def isMessage (n : String) : Bool := n.startsWith "‹a proof was not read back"

/-- The default: far above what any proof in the library needs to be read back (the
largest measured is noted in `wiz-notes/prf-marker.md`), and small enough to answer at once. -/
def defaultSteps : Nat := 1000000

end Budget

/-- Regularity beyond the inert types, for the D1 experiment (`wiz-notes/d1-experiment.md`,
`conv-regularity.md`). `full` is Cast-Refl at **every** type, [PLT25]'s rule: conversion
identifies `cast A B e t` with `t` when `A ≡ B`. It is decided in the conversion checker
only; the evaluator never fires it. Off by default: the published decidability proof
covers Π, ℕ, ⊥, the impredicative `Prop` and ∃, not Wiz's data types. -/
inductive Regularity where
  /-- Cast-Refl at every type, in conversion -/
  | full
  /-- only at inert types (`InertReg`) -/
  | off
  deriving BEq, Repr, Inhabited

/-- Regularity at inert types (InReg, D1/P1). The rule is InReg_conv: `cast A B e t ≡ t`
when `A` is inert and `A ≡ B` (`wiz-notes/conv-regularity.md`). -/
inductive InertReg where
  /-- only the evaluator's fast path: `cast A B e t ↦ t` when `A` and `B` are equal by
  `groundEqTy` (no free variable in a relevant position, so the decision is invariant
  under conversion and stable under substitution). A fragment of the rule; kept as a
  flag to show what the fast path alone rejects -/
  | ground
  /-- (default) the rule: `ground` in the evaluator, and conversion identifies a stuck
  `cast A B e t` with `t` at an inert type when `A ≡ B` (`convTy`) -/
  | conv
  deriving BEq, Repr, Inhabited

/-- The global environment. `order` records insertion order so anything that walks
the environment does so deterministically (never iterate the hash map directly). -/
structure Globals (R : Type) where
  decls : Std.HashMap Name (Decl R) := {}
  order : Array Name := #[]
  /-- each declaration's position in `order` (its definitional height, for lazy delta in
  unification: `Globals.height`) -/
  heights : Std.HashMap Name Nat := {}
  /-- `builtin key := name` registrations, such as `("nat", Nat)` and `("nat.add", Nat.add)` -/
  builtins : List (Name × Name) := []
  /-- the registrations made outside the toolchain's library, which nothing checks: each
  is an axiom of the declarations that depend on it (`#print axioms`) -/
  assumed : List (Name × Name) := []
  /-- unfold every definition eagerly (no gluing), for normal forms -/
  eager : Bool := false
  /-- which casts reduce by regularity (D1: `off`, so that checking terminates) -/
  regularity : Regularity := .off
  /-- P2 (the default; `--eager-proofs` turns it off while the transition lasts): proofs
  are never evaluated. The positions the syntax marks as proofs (`cast`'s equation,
  `transp`'s two proofs) are suspended; a cast between propositions is stuck instead of
  applying the equivalence; `split` on a proof is η. See `docs/CoreSpec.md` and
  `wiz-notes/p2-proofs.md`. -/
  lazyProofs : Bool := true
  /-- (P2, for the later step to relevance marks; off by default) the strict form of the
  marker's requirement: outside a proof, *every* term of a proposition must be `prf t`,
  variables and applications too (by default a neutral-shaped proof needs no marker).
  With it, "this argument is a proof" is readable from the syntax alone. -/
  strictProofs : Bool := false
  /-- (P2) how many evaluation steps reading one suspended proof back may take, outside
  the kernel (`Budget`; `--proof-steps N`) -/
  proofSteps : Nat := Budget.defaultSteps
  /-- (P2, internal) the budget of the read-back in progress. Never set in the kernel. -/
  budget : Option Budget := none
  /-- (P2, `--trace-proof-steps`) print the steps each read-back of a proof took (stderr) -/
  traceProofSteps : Bool := false
  /-- (tests only; off) the checker skips a hole in a `Π`/`Σ`/`ULift` sort instead of
  rejecting it: for the differential tests' pre-check of a raw random term, which must be
  known to be well typed before the sorts pass (which evaluates it) may run on it -/
  sortHolesOk : Bool := false
  /-- (P2, internal) `quote` writes every suspended proof as `()` instead of evaluating
  it: set by the kernel's own comparisons (`sameVal`), which must not run proofs -/
  quoteErasesProofs : Bool := false
  /-- (13n, elaborator) `quote` reads a Σ that `vEq` computed from an equation back as the
  equation (`eqSigmaSides?`), so that a type that is read back and evaluated again (a
  `match` clause's motive, `zonk`) still shows `rfl` the equation it came from. Set by the
  elaborator's `getGlobals`; off in the kernel and for `#reduce` (which prints the
  computed form) -/
  quoteEqs : Bool := false
  /-- (P1) regularity at inert types: decided by conversion (`conv`) by default -/
  inertReg : InertReg := .conv
  /-- a compiler option, not read by the kernel (`--unbox-structs`, stage 22i): erasure
  represents a Σ whose second component is a structure's tail by its first component
  (`unboxedSigma` in `Compiler/Erase.lean`). Off by default: it is not stable under
  substitution. -/
  unboxStructs : Bool := false
  /-- a compiler option, not read by the kernel (on by default; off only to compare
  compiled code in the tests): compiled equations get the direct calls a nested split
  reverted moved into its branches before erasure (`Push.pushCalls`) -/
  pushCalls : Bool := true
  /-- D1 experiment (default off): reject impredicative `Π`s, those into `Prop` whose
  domain is a universe or ends in one (`Prop`, `A → Prop`, `Type`, …) -/
  predicativeProp : Bool := false
  /-- (13b, `wiz --strict-privacy`, off by default) check every declaration a second time
  against the elaborator's view, where another module's types with private parts have no
  definition (`privacyCheck`, `Elab/Command.lean`). The kernel ignores this. -/
  strictPrivacy : Bool := false
  /-- (13b) names private to a module (`private def …`, `private mk ::`), with the
  module: the elaborator rejects them elsewhere. The kernel ignores this. -/
  privates : Std.HashMap Name String := {}
  /-- (13b) structures with a private constructor, with their module: elsewhere the
  elaborator sees them as opaque (`Globals.elabView`). The kernel ignores this. -/
  opaques : Std.HashMap Name String := {}
  /-- (13b) the definitions `elabView` hid (the opaque types of other modules), kept so
  that conversion can compare two *values* of such a type in the full view (`conv`; only
  a Bool comes out, so nothing of the definition is exposed) -/
  hidden : Std.HashMap Name (Decl R) := {}
  /-- the module being elaborated (`""`: the main file), for `privates` and `opaques` -/
  module : String := ""
  /-- (kernel-eval, P3) a universe-polymorphic definition's value instantiated at the
  levels most uses take (every parameter `0`, `1` or `2`: a `casesOn`'s motive in `Prop`,
  `Type`, `Type 1`), computed once (a `Thunk`) instead of copied at every unfolding
  (`Term.instLevels`). Built by `insert` from the value inserted with it; a pure function
  of that value, so it can't change what unfolding gives (`instValue`). -/
  instCache : Std.HashMap Name (List (List Level × Thunk (Term R))) := {}
  /-- (11r) how terms print as notation: unexpanders and the grammar (`Syntax/PPTable.lean`).
  The kernel ignores this. -/
  pp : PPTable := {}
  /-- the library module each declaration was made in (none for the main file's). Read by
  erasure only (a type with a native representation is built and taken apart only in its
  own module, `nativeHome?` in `Compiler/Erase.lean`); the kernel ignores it. -/
  declModule : Std.HashMap Name String := {}

namespace Globals

variable {R : Type}

def find? (g : Globals R) (n : Name) : Option (Decl R) := g.decls[n]?

def contains (g : Globals R) (n : Name) : Bool := g.decls.contains n

/-- The key `n` is registered under (`nat.add`, ...), if any. -/
def builtinKey? (g : Globals R) (n : Name) : Option Name :=
  (g.builtins.find? (·.2 == n)).map (·.1)

/-- `instCache` with the entry of `d` (its value's instantiations, made when needed), or
without one (no value, or no level parameters). -/
def cacheInst (g : Globals R) (d : Decl R) : Std.HashMap Name (List (List Level × Thunk (Term R))) :=
  let ofNat (k : Nat) : Level := (List.range k).foldl (fun l _ => .succ l) .zero
  let inst : List (List Level × Thunk (Term R)) := match d.value with
    | some v => if d.levelParams.isEmpty then [] else [0, 1, 2].map fun k =>
        let us := d.levelParams.map fun _ => ofNat k
        (us, Thunk.mk fun _ => v.instLevels d.levelParams us)
    | none => []
  if inst.isEmpty then g.instCache.erase d.name else g.instCache.insert d.name inst
/-- A declaration's position in `order` (later declarations are higher); 0 if unknown. -/
def height (g : Globals R) (n : Name) : Nat :=
  match g.heights[n]? with
  | some h => h
  | none => if g.heights.isEmpty then (g.order.idxOf? n).getD 0 else 0

/-- Unchecked insertion. Use `Wiz.addDecl` to type check first. -/
def insert (g : Globals R) (d : Decl R) : Globals R :=
  { g with
    decls := g.decls.insert d.name d
    order := if g.decls.contains d.name then g.order else g.order.push d.name
    instCache := g.cacheInst d
    heights := if g.decls.contains d.name then g.heights else g.heights.insert d.name g.order.size
    declModule := if g.module == "" || g.decls.contains d.name then g.declModule
      else g.declModule.insert d.name g.module }

/-- The value `v` of the global `n` (its parameters `ps`) at the levels `us`:
`v.instLevels ps us`, from `instCache` when `insert` computed it. (The cache is keyed by
the name and built from the value `insert` stored; `decls` changes only through `insert`,
by removing a value or a declaration, or by `renamePrivate`, which moves the entries along
with the renamed declarations (`cacheInst`), so an entry belongs to the value found under its
name.) -/
def instValue (g : Globals R) (n : Name) (v : Term R) (ps : List Name) (us : List Level) : Term R :=
  if ps.isEmpty then v else
  match (g.instCache[n]?).bind fun es => es.find? (·.1 == us) with
  | some (_, t) => t.get
  | none => v.instLevels ps us

/-- (13b) The environment as the elaborator sees it in `g.module`: a structure whose
constructor is private to another module has no definition (it doesn't unfold), so
values of it can't be built from a tuple or a look-alike structure; its fields are read
through its projection functions. The kernel still checks against `g` itself. -/
def elabView (g : Globals R) : Globals R :=
  if g.opaques.isEmpty then g else
  g.opaques.fold (init := g) fun g' n m =>
    if m == g.module then g' else
    match g'.decls[n]? with
    | some d => { g' with decls := g'.decls.insert n { d with value := none }, hidden := g'.hidden.insert n d }
    | none => g'

/-- (13b) The environment with the definitions `elabView` hid put back. -/
def fullView (g : Globals R) : Globals R :=
  if g.hidden.isEmpty then g else
  { g with decls := g.hidden.fold (fun m n d => m.insert n d) g.decls, hidden := {} }

/-- (13b) Is `T` opaque here (a structure, inductive or coinductive type with private
constructors, fields or observations, of another module)? Its module, if so. -/
def opaqueTo? (g : Globals R) (T : Name) : Option String :=
  match g.opaques[T]? with
  | some m => if m == g.module then none else some m
  | none => none

/-- (13b) The kernel name of a private declaration `n` of module `m` (not the main file):
`_private.m._0.n`, as Lean does (`_0`, not `0`, so that it parses as an identifier: `mutual` and some derivers print and parse names), so that two modules' private `helper`s are different
constants and never clash (`docs/stages/23-grail.md`, 23b). In `m`, `helper` resolves to
it (`resolve`); messages show `helper` (`privateBase`). -/
def privateName (m n : Name) : Name := "_private." ++ m ++ "._0." ++ n

/-- The source name of a private declaration's kernel name (`privateName`); other names
as they are. -/
def privateBase (n : Name) : Name :=
  if n.startsWith "_private." then
    match n.splitOn "._0." with
    | _ :: rest@(_ :: _) => "._0.".intercalate rest
    | _ => n
  else n

/-- What the name `n`, as written in the module being elaborated, refers to: the
module's own private declaration of that name if it has one, else `n`. -/
def resolve (g : Globals R) (n : Name) : Name :=
  if g.module.isEmpty then n else
  let p := privateName g.module n
  if g.decls.contains p then p else n

/-- (13b) The module `n` is private to, if that is not the one being elaborated. -/
def privateTo? (g : Globals R) (n : Name) : Option String :=
  match g.privates[n]? with
  | some m => if m == g.module then none else some m
  | none => none

end Globals

end Wiz
