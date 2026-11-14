import Wiz.Rig
import Wiz.Core.ErrorCode
import Wiz.Core.Conv
import Wiz.Core.Usage
import Wiz.Core.Pretty

/-!
# Bidirectional QTT type checking

Two mutually recursive judgments, each also producing a **usage vector**:

    Γ ⊢ t ⇐ A  ⊣ U      check : Ctx → Term → VTy → TCM (Usage R)
    Γ ⊢ t ⇒ A  ⊣ U      infer : Ctx → Term → TCM (VTy × Usage R)

`U` says how many times `t` uses each variable of `Γ` (head = innermost).

## Rules (`n = |Γ|`, `0ₙ` = `Usage.zeros n`, `q·U` = `Usage.scale q U`)

    ──────────────────────────────── var
    Γ ⊢ x_ix ⇒ Γ[ix].type ⊣ single n ix

    c.{u₁…uₖ} has k level parameters
    ──────────────────────────────── const
    Γ ⊢ c.{us} ⇒ type(c)[us] ⊣ 0ₙ      (globals are not tracked locally)

    ──────────────────────────────── sort
    Γ ⊢ Sort l ⇒ Sort (l+1) ⊣ 0ₙ

    Γ ⊢ A type@i     Γ, x:A ⊢ B type@j
    ──────────────────────────────── pi        (types are erased: usage 0ₙ)
    Γ ⊢ (x :q A) → B ⇒ Sort (imax i j) ⊣ 0ₙ

    Γ, x :q A ⊢ b ⇐ B ⊣ (u :: U)     le u q
    ──────────────────────────────── lam
    Γ ⊢ λx. b ⇐ (x :q A) → B ⊣ U

    Γ ⊢ f ⇒ (x :q A) → B ⊣ U₁     Γ ⊢ a ⇐ A ⊣ U₂
    ──────────────────────────────── app
    Γ ⊢ f a ⇒ B[a/x] ⊣ U₁ + q·U₂

    Γ ⊢ T type   Γ ⊢ v ⇐ T ⊣ U₁   Γ, x :q T := v ⊢ b ⇐ A ⊣ (u :: U₂)   le u q
    ──────────────────────────────── let     (and the ⇒ version)
    Γ ⊢ let x :q T := v; b ⇐ A ⊣ q·U₁ + U₂

    Γ ⊢ T type    Γ ⊢ t ⇐ T ⊣ U
    ──────────────────────────────── ann
    Γ ⊢ (t : T) ⇒ T ⊣ U

    Γ ⊢ t ⇒ A' ⊣ U     A ≡ A'
    ──────────────────────────────── switch
    Γ ⊢ t ⇐ A ⊣ U

## Structural types (stage 4b)

    Γ ⊢ A type@i     Γ, x:A ⊢ B type@j
    ──────────────────────────────── sigma
    Γ ⊢ (q x : A) × B ⇒ Sort (max i j) ⊣ 0ₙ

    Γ ⊢ a ⇐ A ⊣ U₁     Γ ⊢ b ⇐ B[a/x] ⊣ U₂
    ──────────────────────────────── pair      (check only)
    Γ ⊢ (a, b) ⇐ (q x : A) × B ⊣ q·U₁ + U₂

    Γ ⊢ t ⇒ (q x : A) × B ⊣ U     le 1 q
    ──────────────────────────────── fst       (an erased field can't be projected at runtime)
    Γ ⊢ t.1 ⇒ A ⊣ ω·U

    Γ ⊢ t ⇒ (q x : A) × B ⊣ U
    ──────────────────────────────── snd
    Γ ⊢ t.2 ⇒ B[t.1/x] ⊣ ω·U

    (R1: projections are available only on unrestricted pairs. A projection keeps one
    component and drops the other, so `t` is used ω times, whatever the component types
    and whether `t` is a variable or not (`projUsage`). In an erased position, Γ⁰, both
    rules have no side condition and the usage is `U`: nothing is consumed there.)

    Γ ⊢ s ⇒ (p x : A) × B ⊣ U₁     Γ, z : (p x : A) × B ⊢ M type
    Γ, x :(q·p) A, y :q B ⊢ b ⇐ M[(x, y)/z] ⊣ (u_y :: u_x :: U₂)
    le u_y q     le u_x (q·p)
    ──────────────────────────────── split
    Γ ⊢ let q (x, y) := s; b ⇒ M[s/z] ⊣ q·U₁ + U₂

    Γ ⊢ Unit_l ⇒ Sort l      Γ ⊢ () ⇐ Unit_l      Γ ⊢ Empty_l ⇒ Sort l

    Γ ⊢ u ⇒ Unit_l ⊣ U₁     Γ ⊢ b ⇒ B ⊣ U₂
    ──────────────────────────────── letUnit   (1-elimination; computes to b by η, but
    Γ ⊢ let () := u; b ⇒ B ⊣ U₁ + U₂             compiled code evaluates u first)

    Γ ⊢ M type     Γ⁰ ⊢ t ⇒ Empty_l
    ──────────────────────────────── absurd    (`t` is never evaluated: an erased position)
    Γ ⊢ absurd M t ⇒ M ⊣ 0ₙ

## Observational equality (stage 4c)

    Γ ⊢ A type@l   l ≠ 0 at every level instance (`isNeverZero`)   Γ ⊢ a, b ⇐ A
    ──────────────────────────────── eq            (a proposition)
    Γ ⊢ a = b ⇒ Prop ⊣ 0ₙ

    Γ ⊢ A type@l    Γ ⊢ B type@l
    ──────────────────────────────── eqTy
    Γ ⊢ A = B ⇒ Prop ⊣ 0ₙ

    Γ ⊢ A type@l (isNeverZero l)   Γ ⊢ a ⇐ A
    ──────────────────────────────── refl          Γ ⊢ X type ⇒ Γ ⊢ reflTy X ⇒ (X = X) ⊣ 0ₙ
    Γ ⊢ refl A a ⇒ (a = a) ⊣ 0ₙ

    Γ ⊢ A, B type@l    Γ ⊢ e ⇐ (A = B)    Γ ⊢ t ⇐ A ⊣ U
    ──────────────────────────────── cast
    Γ ⊢ cast A B e t ⇒ B ⊣ U

    Γ ⊢ A type@l (isNeverZero l)   Γ ⊢ a, b ⇐ A    Γ ⊢ P ⇐ (b :0 A) → (_ :0 a = b) → Prop
    Γ ⊢ p ⇐ P a (refl a)    Γ ⊢ e ⇐ (a = b)
    ──────────────────────────────── transp
    Γ ⊢ transp A a P p b e ⇒ P b e ⊣ 0ₙ

Proofs carry no usage: they are erased, and conversion never looks at them.

## Data (stage 4d)

    Γ ⊢ Enum ls ⇒ Type        Γ ⊢ tag ls i ⇒ Enum ls   (i < |ls|)

    Γ ⊢ t ⇒ Enum ls ⊣ U    Γ, z ⊢ M type    Γ ⊢ bₖ ⇐ M[tag k] ⊣ Vₖ
    ──────────────────────────────── ecase     (⊔ = least upper bound in `le`)
    Γ ⊢ ecase t [b…] ⇒ M[t] ⊣ U + (V₀ ⊔ … ⊔ Vₙ)

    Γ ⊢ I type@(l+1) ⇒ Γ ⊢ Desc.{l} I ⇒ Type (l+1); ret/arg/rec/hrec check against it
    Γ ⊢ Desc.elim P mret marg mrec mhrec D ⇒ P D ⊣ ω·(Uₘ + U_D)   (method types: `delimMethodTys`)
    Γ ⊢ μ.{l} I D i ⇒ Type l           Γ ⊢ con x ⇐ μ D i  if  Γ ⊢ x ⇐ ⟦D⟧ (μ D) i
    Γ ⊢ ind P m i x ⇒ P i x ⊣ ω·(Uₘ + Uₓ)                  (`indMotiveTy`, `indMethodTy`)
    Γ ⊢ ν.{l} I D i ⇒ Type l           Γ ⊢ out x ⇒ ⟦D⟧ (ν D) i
    (at a size: Γ ⊢ μ^s.{l} I D i ⇒ Type l and Γ ⊢ ν^s.{l} I D i ⇒ Type l if also Γ⁰ ⊢ s ⇐ Size)
    Γ ⊢ coit S step i s ⇒ ν D i ⊣ ω·(U_step + U_s)

## Sizes (stage 4f)

    Γ ⊢ Size, Size< s ⇒ Type      Γ ⊢ ∞, ↑s ⇒ Size      (s is checked erased: Γ⁰ ⊢ s ⇐ Size)
    Γ⁰ ⊢ t ⇐ Size   t is below s (`sizeBelow`; ∞ is not below itself)  ⇒  Γ ⊢ t ⇐ Size< s ⊣ 0ₙ
    Γ ⊢ con x ⇐ μ^s D i  if  s = ↑s' and Γ ⊢ x ⇐ ⟦D⟧ (μ^s' D) i;  cocon x ⇐ ν^s D i likewise
    Γ ⊢ sfix P f s i x ⇒ P i x ⊣ ω·(U_f + Uₓ)      (`sfixFunTy`; x ⇐ μ^s D i)
    Γ ⊢ scase_q P m s i x ⇒ P i x ⊣ Uₘ + q·Uₓ      (`scaseMethodTy`: the method runs once and
                                                    binds the payload at q; K1)
    Γ ⊢ scofix A f s i a ⇒ ν^s D i ⊣ ω·(U_f + Uₐ)  (`scofixFunTy`)

A `Π`/`Σ` may carry its sort; if it does, the sort must be the one the rule computes
(`checkSortNote`).

The scrutinee `x` (the seed `s`, `a`) of these eliminators is scaled by ω as well: the
methods bind its payload at ω, so they may copy or ignore it.

A method may run once per node, so its usage is scaled by ω (`QRig.many?`, the rig's
unrestricted quantity; a rig without one, like exact counting, rejects methods that use
local variables outside erased positions). Branches of `ecase` are alternatives, so a
case uses the *join* of its branches' usages: with `{0, 1, ω}` a linear variable must be used the same way in
every branch, and an ω variable may be used differently.

`split` is how a pair held at any quantity other than ω is consumed: it accounts for
both components. `fst p` and `snd p` each drop a component, so they use `p` ω times.

A position scaled by a constant 0 (an argument to a 0 binder, the value of a `let` at 0,
the first part of a pair at a 0 field, the scrutinee of a `split` at 0) is never
computed: it is checked as an erased position (`Ctx.erasedAt`).

`Γ ⊢ A type@i` means `A ⇒ Sort i`, with its usage **thrown away**: types live in
the erased (0) fragment, so they may mention 0-quantity variables freely.

## Simplification vs. Atkey

Atkey's system indexes judgments by σ ∈ {0, 1} and, in the σ = 0 fragment, doesn't
check linearity at all. We instead check everything in "σ = 1 mode" and then discard
the usage of type positions. That is sound but rejects a few erased terms that Atkey
would accept (e.g. a non-linear lambda *inside a type*, under a linear binder). Fixing
this is an optional exercise.
-/

namespace Wiz

variable {R : Type}

inductive TypeError where
  | unboundGlobal (name : Name)
  | typeMismatch (expected inferred : String)
  | notAFunction (term type : String)
  | notAType (term type : String)
  | cannotInfer (term : String)
  | quantityMismatch (var : Name) (declared used : String)
  | duplicateDecl (name : Name)
  /-- (P2) a term whose sort may be `0` is neither marked nor neutral-shaped. Its own
  case, so that the elaborator can tell "this term needs its markers" from a type error
  (`addDeclMarked`). -/
  | unmarkedProof (term type sort : String)
  | other (msg : String)
  deriving Repr, BEq, Inhabited

instance : ToString TypeError where
  toString
    | .unboundGlobal n => if Budget.isMessage n then n else s!"unbound global: {n}"
    | .typeMismatch e i => s!"type mismatch\n  expected: {e}\n  inferred: {i}"
    | .notAFunction t ty => s!"not a function: {t}\n  has type: {ty}"
    | .notAType t ty => s!"not a type: {t}\n  has type: {ty}"
    | .cannotInfer t => s!"cannot infer a type for {t}; add an annotation"
    | .quantityMismatch x d u => s!"variable {x} declared with quantity {d} but used {u}" ++
        match d, u with
        | "0", _ => s!"\n  ({x} is erased: only types, proofs and other erased arguments may use it, not the computation)"
        | "1", "ω" => s!"\n  (a linear variable, of quantity 1, must be used exactly once, and {x} is used more than once)"
        | "1", "0" => s!"\n  (a linear variable, of quantity 1, must be used exactly once, and {x} is not used)"
        | _, _ => ""
    | .duplicateDecl n => s!"'{n}' has already been declared"
    | .unmarkedProof t ty l => s!"unmarked proof: {t}\n  has type {ty}, in Sort {l}; the kernel does not evaluate proofs, so it must be marked (prf)"
    | .other m => m

/-- The message for a declaration `name` the kernel rejected with `e`. The elaborator
leaves quantities (usage) to the kernel, so a quantity error is the user's, reported as
it is, like a clash of names; anything else says that the kernel rejected it. -/
def kernelRejected (name : Name) (e : TypeError) : String :=
  match e with
  | .quantityMismatch .. => toString e
  | .duplicateDecl n => s!"'{n}' has already been declared"
  | .other m => if (m.splitOn "quantity").length > 1 then m else s!"kernel rejected {name}: {m}"
  | e => s!"kernel rejected {name}: {e}"

/-- The error code of a kernel error reported with `kernelRejected` (`ErrorCode`). -/
def kernelRejectedCode : TypeError → String
  | .quantityMismatch .. => ErrorCode.quantity
  | .other m => if (m.splitOn "quantity").length > 1 then ErrorCode.quantity else ErrorCode.kernelRejected
  | _ => ErrorCode.kernelRejected

abbrev TCM := Except TypeError

/-- The typing context. All the lists are aligned: index 0 is the innermost binder. -/
structure Ctx (R : Type) where
  globals : Globals R
  /-- values of locals, for evaluating types that mention them -/
  env   : Env R := []
  names : List Name := []
  qtys  : List (QPoly R) := []
  types : List (VTy R) := []
  /-- number of locals in scope = the next fresh de Bruijn level -/
  lvl   : Lvl := 0
  /-- checking an erased position (a type, or an argument to a `0` binder)? There,
  erased fields may be projected. (A light version of Atkey's σ = 0 mode.) -/
  erased : Bool := false
  /-- (P2) checking inside a proof (under a `prf`, or in `cast`'s equation or `transp`'s
  proofs, which are never evaluated)? Outside, in *relevant mode*, a term of a
  proposition must be marked or neutral-shaped (`unmarkedProof`). -/
  proof : Bool := false
  /-- (P2) the term being checked is the one a marker wraps (`prf.{l} t` at a level that
  is not `0`), or the body of such a `fun`: it is exempt from the marker's requirement.
  Reset below it. -/
  marked : Bool := false
  /-- (the elaborator's sorts pass, `Wiz/Elab/Mark.lean`; not read by the kernel) fill
  the holes in the `Π`/`Σ`/`ULift` sorts only, placing no proof markers -/
  sortsOnly : Bool := false

namespace Ctx

variable [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- Go under a binder: the new variable is a fresh neutral. -/
def bind (ctx : Ctx R) (x : Name) (q : QPoly R) (ty : VTy R) : Ctx R :=
  { ctx with
    env := Val.var ctx.lvl :: ctx.env
    names := x :: ctx.names
    qtys := q :: ctx.qtys
    types := ty :: ctx.types
    lvl := ctx.lvl + 1 }

/-- Go under a `let`: the new variable has a known value. -/
def define (ctx : Ctx R) (x : Name) (q : QPoly R) (ty : VTy R) (val : Val R) : Ctx R :=
  { ctx with
    env := val :: ctx.env
    names := x :: ctx.names
    qtys := q :: ctx.qtys
    types := ty :: ctx.types
    lvl := ctx.lvl + 1 }

def eval (ctx : Ctx R) (t : Term R) : Val R := Wiz.eval ctx.globals ctx.env t

/-- `Closure.inst c (ctx.eval a)`, evaluating `a` only if `c`'s body mentions it.
Evaluation is strict, and the codomain of a non-dependent Π (`List.cons : A → List A →
List A`) doesn't need its argument: evaluating it anyway, at every application along a
nested spine (a long list or string literal), would be quadratic in its length. -/
def instArg (ctx : Ctx R) (c : Closure R) (a : Term R) : Val R :=
  match c with
  -- (the placeholder is the stuck unknown, not a well-formed value: if `hasVar` ever
  -- missed an occurrence, the codomain would be stuck on it, not a type that checks)
  | .mk env body => Wiz.eval ctx.globals ((if body.hasVar 0 then ctx.eval a else default) :: env) body

/-- The types of the locals indexed by level, as `conv` wants them. -/
def tys (ctx : Ctx R) : Array (VTy R) := ctx.types.reverse.toArray

variable [QuantitySyntax R] [DecidableEq R]

/-- Render a value for error messages. (P2: without evaluating a suspended proof, which
reads back as `()`; so no path of the kernel, accepting or rejecting, runs a proof.) -/
def showVal (ctx : Ctx R) (v : Val R) : String :=
  elideLong ((quote { ctx.globals with quoteErasesProofs := true } ctx.lvl v).pretty ctx.names (some ctx.globals))

def showTerm (ctx : Ctx R) (t : Term R) : String := elideLong (t.pretty ctx.names (some ctx.globals))

end Ctx

variable [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- A quantity value as a polynomial, or an error if it is something else (e.g. the
result of a stuck computation). -/
def qtyPoly (ctx : Ctx R) (q : Val R) : TCM (QPoly R) :=
  match q.toPoly? with
  | some p => pure p
  | none => throw (.other s!"quantity must be a literal or a quantity variable: {ctx.showVal q}")

/-- **Exercise 1.5.** Leave the scope of a binder `x` declared at quantity `q`:
pop the binder's own usage off the head of the vector and check it is compatible
with `q` (using `QPoly.le`), returning the rest. Throw `quantityMismatch` otherwise. -/
def popUsage (x : Name) (q : QPoly R) : Usage R → TCM (Usage R)
  --<sol
  | used :: rest =>
    if QPoly.le used q then pure rest
    else throw (.quantityMismatch x (toString q) (toString used))
  | [] => throw (.other "internal error: usage vector underflow")
  --|ex
  --| | u => sorry
  --sol>

/-- (Mandatory sorts) A component sort written on a `Π`/`Σ` (or a `ULift`'s content's sort)
must be the sort the component is in: `inferred` is what `checkType` found for it. Type
equality and `cast` trust it to tell propositions from other types, and the cast rules
compare it (D2). Structural: each component on its own, never a combination. A hole (a
sort the elaborator's sorts pass did not fill) is rejected. -/
def checkComponentSort (what : String) (written inferred : Level) (holesOk : Bool := false) : TCM Unit := do
  if written.hasHole then
    if holesOk then return
    throw (.other s!"internal error: a {what} without its sort (the sorts pass did not fill it)")
  unless written == inferred || written.equiv inferred do
    throw (.other s!"internal error: a {what} marked as in Sort {written} is in Sort {inferred}")

/-- The usage of an eliminator's methods (`ind`, `Desc.elim`, `sfix`, `scofix`, `coit`),
which run once per node: any number of times. Also the usage of what these eliminators
(and `scase`) take apart or unfold, the scrutinee or the seed: its payload reaches the
method as an ω variable, so it counts ω times too (charging it once let a method
duplicate or drop the content of a linear scrutinee; a value held at 1 can't be
eliminated by them until there is a case at a quantity). Scaled by the rig's unrestricted quantity
(`QRig.many?`, ω); a rig without one (exact counting) only lets methods use local
variables in erased positions. -/
def methodUsage (ctx : Ctx R) (u : Usage R) : TCM (Usage R) :=
  match QRig.many? (R := R) with
  | some m => pure (QPoly.const m • u)
  | none =>
    match (u.zip ctx.names).find? fun (p, _) => !QPoly.le p (QPoly.const 0) with
    | some (p, x) => throw (.other s!"a method may run any number of times, so it can't use {x} ({p} times): the rig has no unrestricted quantity")
    | none => pure u

/-- For error messages only: is this `Σ` (a suffix of) a structure, i.e. does its chain
of second parts end in a structure's marker tail (`structTailName`)? -/
partial def endsInStructTail (ctx : Ctx R) (ty : Val R) (k : Nat) : Bool :=
  match whnf ty with
  | .sigma _ _ _ B _ => endsInStructTail ctx (Closure.inst ctx.globals B (Val.var (ctx.lvl + k))) (k + 1)
  | .pi x _ _ _ cod _ => k > 0 && (x == structTailName ||
      (isPhantomName x && endsInStructTail ctx (Closure.inst ctx.globals cod (Val.var (ctx.lvl + k))) (k + 1)))
  | _ => false

/-- (R1) The usage of a projection `t.1` / `t.2`, where `t` uses `u`: **projections are
available only on unrestricted pairs**. A projection keeps one component and drops the
other, and the second component of a `Σ` has no quantity of its own to say whether it may
be dropped, so the rule doesn't look at the component types at all: `t` is used ω times
(`QRig.many?`), whether it is a variable or any other expression (`(act w).1` uses `w` ω
times). A pair held at any other quantity is taken apart with `split`
(`let (x, y) := p; …`), which accounts for both components. Erased positions don't come
here: nothing is consumed there.

Every variable `t` uses is checked against its declared quantity right away, so that the
error can say what to write instead; it would otherwise surface as a plain quantity
mismatch at the variable's binder. (Usages only grow on the way out, except where they
are scaled by a constant 0, and those positions are checked erased: `erasedAt`.) -/
def projUsage (ctx : Ctx R) (t : Term R) (ty : Val R) (field : String) (u : Usage R) : TCM (Usage R) :=
  let st := ctx.showTerm t
  let fail {α} (x : Name) (q : String) : TCM α := throw (.other <|
    s!"cannot project {match t with | .var _ => st | _ => s!"({st})"}{field}: a projection needs an unrestricted pair (it keeps one component and drops the other), but this one uses {x}, which has quantity {q}; " ++
    (if endsInStructTail ctx ty 0 then
      s!"this is a field of a structure, and a structure can't be held at a quantity other than ω yet (it has no destructuring form); use a tuple `A × B` instead, taken apart with `let {q} (x, y) := …`, or a one-constructor `inductive` taken apart by `match`"
    else s!"take the pair apart with `let {q} (x, y) := {st}; …` instead"))
  match QRig.many? (R := R) with
  | some m =>
    let u' := QPoly.const m • u
    -- (a variable `t` doesn't use is not this rule's business: 0 ≤ 1 is false)
    match ((u'.zip ctx.qtys).zip ctx.names).find? fun ((p, q), _) => !QPoly.le p (QPoly.const 0) && !QPoly.le p q with
    | some ((_, q), x) => fail x (toString q)
    | none => pure u'
  | none =>
    -- a rig without an unrestricted quantity (exact counting): only pairs that use no
    -- local variable at all can be projected
    match ((u.zip ctx.qtys).zip ctx.names).find? fun ((p, _), _) => !QPoly.le p (QPoly.const 0) with
    | some ((_, q), x) => fail x (toString q)
    | none => pure u

/-- A position whose usage is scaled by `q`: when `q` is the constant 0 it is erased (the
value is never computed), so it is checked as an erased position. The test is
`QPoly.isErased`, the same one erasure uses to drop the position. -/
def Ctx.erasedAt (ctx : Ctx R) (q : QPoly R) : Ctx R :=
  if q.isErased then { ctx with erased := true } else ctx

/-! ### The proof marker (P2)

The evaluator has no types, so it cannot know that the value of a `let`, an argument or
a field is a proof. The checker can. It has two modes: **relevant** (the default) and
**proof** (`Ctx.proof`: under a marker at level `0`, and in the positions the evaluator
suspends by itself). In relevant mode a term whose type is in a sort that may be `0`
(`Sort l` with `l` not `isNeverZero`: `Prop`, or `Sort u` for a level parameter `u`) must be

* **marked**, `prf.{l} t`, with `l` the sort: the evaluator suspends it without looking at
  `t` when `l` is `0` (for a parameter: at the instances where it is `0`); or
* **neutral-shaped**: a variable, a constant or `()`, under applications, projections,
  `down` and type ascriptions; or one of the stuck proofs `refl`, `reflTy`, `transp`.

Anything else there (a `fun`, a pair, a `let`, a cast, `absurd`, a case analysis, …) is
rejected. Then every value the evaluator builds at a proposition is a neutral,
`()`, or a glued constant that unfolds to one: a variable of proposition type is only
ever bound to the value of a term that was checked here, and applying or projecting such
a value only grows a spine. So the kernel never performs a β, projection or ι step inside
a proof (`wiz-notes/prf-marker.md` §3). With `Globals.strictProofs`, only `prf t` is
accepted. With `--eager-proofs` (no `lazyProofs`) nothing is required. -/

/-- The formers that need no marker at a proposition: evaluating them at a proposition
only looks a value up or grows a spine (their subterms are checked in turn). And the
proofs that are stuck heads, `refl`, `reflTy` and `transp`: evaluating one evaluates its
relevant parts (the type and the term of a `refl`; `transp`'s two proofs are suspended)
and gives a neutral, with no step inside a proof. (Without these, nearly every
definition that builds a value of an indexed family needed the marking pass, for the
`refl` that proves its index equation.) -/
def Term.neutralShaped : Term R → Bool
  | .var _ | .const .. | .tt | .app .. | .fst _ | .snd _ | .down _ | .ann .. | .prf .. => true
  | .refl .. | .reflTy _ | .transp .. => true
  | _ => false

/-- The sort of a type (`typeSort?`), read off the head for the common formers without
building the array of the context's types. -/
def Ctx.sortOf? (ctx : Ctx R) (ty : VTy R) : Option Level :=
  match whnf ty with
  | .sort l => some (.succ l)
  | .qty | .enum _ | .size | .sizeLt _ => some 1
  | .desc l _ => some (.succ (.succ l))
  | .mu l .. | .nu l .. => some (.succ l)
  | .unit l | .empty l | .ulift _ l _ => some l
  | .pi _ _ _ _ _ σ => if σ.hasHole then typeSort? ctx.globals ctx.tys ty else some σ.piSort
  | .sigma _ _ _ _ σ => if σ.hasHole then typeSort? ctx.globals ctx.tys ty else some σ.sigmaSort
  | ty => typeSort? ctx.globals ctx.tys ty

/-- The sort of a type the checker is working at. It is computable for a well-typed type;
failing to is an error (and not "no marker required"). -/
def Ctx.sortOf (ctx : Ctx R) (ty : VTy R) : TCM Level :=
  match ctx.sortOf? ty with
  | some l => pure l
  | none => throw (.other s!"internal error: cannot compute the sort of {ctx.showVal ty}")

/-- Is this type a proposition, its sort computed and `0` (whatever the proof mode: the
usage rule "a proof uses nothing")? -/
def Ctx.isPropTy (ctx : Ctx R) (ty : VTy R) : Bool := (ctx.sortOf? ty).any (·.isZero)

/-- Leave a binder of quantity `q` and type `ty`: as `popUsage`, except that a binder
whose type is a proposition takes any usage. Its variable is a proof, erased and never
run (CoreSpec §6), so a linear proof that is used zero times or several times consumes
nothing (prf-review L1: `(1 h : True) → True`, `let 1 (a, h) := p` at `(1 x : A) × P x`). -/
def Ctx.popUsageAt (ctx : Ctx R) (x : Name) (q : QPoly R) (ty : VTy R) (u : Usage R) : TCM (Usage R) :=
  if ctx.isPropTy ty then
    match u with
    | _ :: rest => pure rest
    | [] => throw (.other "internal error: usage vector underflow")
  else popUsage x q u

/-- Is this type a proposition (its sort is computed, and is `0`)? -/
def Ctx.isProofTy (ctx : Ctx R) (ty : VTy R) : Bool :=
  ctx.globals.lazyProofs && (ctx.sortOf? ty).any (·.isZero)

/-- **The mode of a subterm is decided by its type** (I-1). Inside a proof, a subterm whose
type is not a proposition is a relevant term again: it can be evaluated (as the index of
a type the checker computes), so the proofs in it must be marked, as anywhere else. Only
a subterm that is itself a proof stays in proof mode. (A type whose sort cannot be
computed, U5, is left in the mode it is in.) -/
def Ctx.modeAt (ctx : Ctx R) (ty : VTy R) : Ctx R :=
  if !ctx.proof then ctx else
  match ctx.sortOf? ty with
  | some s => if s.isZero then ctx else { ctx with proof := false }
  | none => ctx

/-- **Bind by type** (I-1): the value of `t : ty`, for the checker to bind a variable to
or to instantiate a type with. Inside a proof, a proof is not evaluated: it is suspended.
(Outside, a proof was checked in relevant mode, so evaluating it computes nothing.) So
the checker never evaluates a term that was checked in proof mode. -/
def Ctx.evalAt (ctx : Ctx R) (t : Term R) (ty : VTy R) : Val R :=
  if ctx.proof && ctx.isProofTy ty then suspend ctx.globals ctx.env t else ctx.eval t

/-- `Ctx.instArg` for an argument of type `dom`, bound by type (`evalAt`). -/
def Ctx.instArgAt (ctx : Ctx R) (dom : VTy R) (c : Closure R) (a : Term R) : Val R :=
  match c with
  | .mk env body => Wiz.eval ctx.globals ((if body.hasVar 0 then ctx.evalAt a dom else .unit .zero) :: env) body

/-- Is `t` a term that needs a marker in this mode, if its sort may be `0`? -/
def Ctx.wantsMarker (ctx : Ctx R) (t : Term R) : Bool :=
  !ctx.proof && !ctx.marked && ctx.globals.lazyProofs &&
    !(if ctx.globals.strictProofs then (t matches .prf ..) else t.neutralShaped)

/-- The marker's requirement on `t`, found at the type `ty` in relevant mode. -/
def Ctx.requireMarker (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM Unit := do
  if ctx.wantsMarker t then
    let l ← ctx.sortOf ty
    unless l.isNeverZero do
      throw (.unmarkedProof (ctx.showTerm t) (ctx.showVal ty) l.format)

/-- A marker `prf.{l}` at the type `ty`: `l` must be the sort of `ty`. Returns the context
for the marked term: proof mode when `l` is `0`; otherwise the same mode, with the marked
term itself exempt from the requirement. -/
def Ctx.underMarker (ctx : Ctx R) (l : Level) (ty : VTy R) : TCM (Ctx R) := do
  let s ← ctx.sortOf ty
  unless s.equiv l do
    throw (.other s!"prf.\{{l.format}} marks a term whose type {ctx.showVal ty} is in Sort {s.format}")
  pure (if l.isZero then { ctx with proof := true } else { ctx with marked := true })

/-- (D1 experiment) Is this type a universe, or a function type ending in one? A `Π`
into `Prop` over such a domain is impredicative. -/
partial def largeDomain (ctx : Ctx R) (A : Val R) (l : Nat) : Bool :=
  match whnf A with
  | .sort _ => true
  | .pi _ _ _ _ B _ => largeDomain ctx (Closure.inst ctx.globals B (Val.var l)) (l + 1)
  | _ => false

mutual

/-- **Exercise 1.6.** Check `t` against the type `ty`. Implement the `lam` and `letE`
rules here and fall back to `infer` + `convTy` for everything else. (Stage 4f
replaces `convTy` with `subTy`, sized subtyping: the inferred type must be a subtype
of the expected one.)

**Exercise 4.7a** (stage 4b): the `pair` and `tt` rules. -/
partial def check (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM (Usage R) := do
  -- (given) a proof uses nothing: a term at a proposition is checked in an erased position
  -- and its usage is `0`, at every level of a proof (CoreSpec §6: proofs are erased and
  -- never run, so a variable at quantity `0` may appear in one)
  if ctx.isPropTy ty then
    let _ ← checkU { ctx with erased := true } t ty
    return Usage.zeros ctx.lvl
  checkU ctx t ty

/-- `check` without the rule for proofs. -/
partial def checkU (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM (Usage R) := do
  -- (given) P2: inside a proof, a term that is not a proof is a relevant term again. A
  -- sort that can't be computed is an error here as it is in relevant mode (`requireMarker`),
  -- for a term the requirement would apply to, not a silent "proof mode" (review F4)
  if ctx.proof && ({ ctx with proof := false }).wantsMarker t && (ctx.sortOf? ty).isNone then
    let _ ← ctx.sortOf ty
  let ctx := ctx.modeAt ty
  -- (given) P2: outside a proof, a proof is marked or neutral-shaped
  ctx.requireMarker t ty
  -- (the exemption of a marked term goes on to the body of a marked `fun`: `Sort (imax a l)`
  -- is `0` exactly when `Sort l` is, so where the body's sort is `0` the whole `fun` is a
  -- suspended proof, and the body is never evaluated)
  checkCore (if ctx.marked && !(t matches .lam ..) then { ctx with marked := false } else ctx) t ty

/-- The rules of `check` (which adds the proof marker's requirement). -/
partial def checkCore (ctx : Ctx R) (t : Term R) (ty : VTy R) : TCM (Usage R) :=
  match t, whnf ty with
  -- (given) P2: a marked term. The level must be the sort of the type: at level `0` the
  -- evaluator suspends the term, and conversion takes any two suspended proofs as equal
  | .prf l t, _ => do check (← ctx.underMarker l ty) t ty
  -- (given) Q4
  | .up a, .ulift _ _ A => check ctx a A
  --<sol
  | .lam x body, .pi _ _ q dom cod _ => do
    let q ← qtyPoly ctx q
    let u ← check (ctx.bind x q dom) body (Closure.inst ctx.globals cod (Val.var ctx.lvl))
    ctx.popUsageAt x q dom u
  | .letE x q tty val body, _ => do
    let q ← checkQty ctx q
    let _ ← checkType ctx tty
    let vty := ctx.eval tty
    let uv ← check (ctx.erasedAt q) val vty
    let ub ← check (ctx.define x q vty (ctx.evalAt val vty)) body ty
    let ub ← ctx.popUsageAt x q vty ub
    pure (q • uv + ub)
  | .pair a b, .sigma _ q A B _ => do
    let q ← qtyPoly ctx q
    let ua ← check (ctx.erasedAt q) a A
    let ub ← check ctx b (ctx.instArgAt A B a)
    pure (q • ua + ub)
  | .tt, .unit _ => pure (Usage.zeros ctx.lvl)
  | .letUnit u b, _ => do
    let uu ← checkUnit ctx u
    pure (uu + (← check ctx b ty))
  | t, .sizeLt s => do
    -- a size below `s` (`∞` is not below itself)
    let _ ← check { ctx with erased := true } t .size
    unless sizeBelow ctx.tys (ctx.eval t) s do
      throw (.other s!"the size {ctx.showTerm t} is not below {ctx.showVal s}")
    pure (Usage.zeros ctx.lvl)
  | .dret i, .desc _ I => check ctx i I
  | .darg q S D, .desc l I => do
    let _ ← checkQty ctx q
    let lS ← checkType ctx S
    -- a field lives exactly in `Sort (l+1)`, the universe `Desc.elim`'s `marg` takes it
    -- from (Q4: universes aren't cumulative; the elaborator lifts smaller fields)
    unless lS.equiv (.succ l) do
      throw (.other s!"a description's field type must be in Sort {(Level.succ l).format}, not Sort {lS.format} (lift it with ULift)")
    check ctx D (.pi "s" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval S) (.mk [I] (.desc l (.var 1))) ⟨.succ l, .succ (.succ l)⟩)
  | .drec q j D, .desc l I => do
    let _ ← checkQty ctx q
    let uj ← check ctx j I
    let uD ← check ctx D (.desc l I)
    pure (uj + uD)
  | .dhrec q H j D, .desc l I => do
    -- strict positivity is automatic: `H` can't mention the type being defined
    let _ ← checkQty ctx q
    let lH ← checkType ctx H
    unless lH.equiv (.succ l) do
      throw (.other s!"a description's branching type must be in Sort {(Level.succ l).format}, not Sort {lH.format} (lift it with ULift)")
    let uj ← check ctx j (.pi "h" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval H) (.mk [I] (.var 1)) ⟨.succ l, .succ l⟩)
    let uD ← check ctx D (.desc l I)
    pure (uj + uD)
  | .con x, .mu l I D i s _ => do
    let some s' := sizePred? s
      | throw (.other s!"a constructor builds a value of size ↑s, not {ctx.showVal s}")
    check ctx x (vInterp ctx.globals l I D (muFamilyAt l I D s') i)
  | .cocon x, .nu l I D i s _ => do
    let some s' := sizePred? s
      | throw (.other s!"cocon builds a value of size ↑s, not {ctx.showVal s}")
    check ctx x (vInterp ctx.globals l I D (nuFamilyAt l I D s') i)
  | _, _ => do
    -- (`inferCore`: the marker's requirement was tested above, at the expected type)
    let (ty', u) ← inferCore ctx t
    unless subTy ctx.globals ctx.tys ty' ty do
      throw (.typeMismatch (ctx.showVal ty) (ctx.showVal ty'))
    pure u
  --|ex
  --| | .lam x body, .pi _ _ q dom cod _ => sorry
  --| | .letE x q tty val body, _ => sorry
  --| -- Exercise 4.7a
  --| | .pair a b, .sigma _ q A B _ => sorry
  --| | .tt, .unit _ => sorry
  --| -- Exercise 4.20
  --| | .dret i, .desc _ I => sorry
  --| | .darg q S D, .desc l I => sorry
  --| | .drec q j D, .desc l I => sorry
  --| | .dhrec q H j D, .desc l I => sorry
  --| | .con x, .mu l I D i _ _ => sorry
  --| | _, _ => sorry
  --sol>

/-- **Exercise 1.7.** Infer the type of `t`. See the rules in the module docstring.
`checkType` (below) handles the "`A type@i`" premises.

**Exercise 4.14** (stage 4c): `eq`, `eqTy`, `refl`, `reflTy`, `cast`, `transp`.

**Exercise 4.7b** (stage 4b): `sigma`, `fst`, `snd`, `split`, `unit`, `empty`,
`absurd`. `pair` and `tt` can only be checked. -/
partial def infer (ctx : Ctx R) (t : Term R) : TCM (VTy R × Usage R) := do
  let (ty, u) ← inferCore (if ctx.marked then { ctx with marked := false } else ctx) t
  -- (given) P2: outside a proof, a proof is marked or neutral-shaped
  ctx.requireMarker t ty
  -- (given) a proof uses nothing (as in `check`)
  pure (ty, if ctx.isPropTy ty then Usage.zeros ctx.lvl else u)

/-- The rules of `infer` (which adds the proof marker's requirement). -/
partial def inferCore (ctx : Ctx R) (t : Term R) : TCM (VTy R × Usage R) :=
  match t with
  -- (given) P2: a marked proof
  | .prf l t => do
    -- (the type is not known before `t` is inferred: at level `0` infer it as a proof)
    let (ty, u) ← infer (if l.isZero then { ctx with proof := true } else { ctx with marked := true }) t
    let _ ← ctx.underMarker l ty
    pure (ty, u)
  | .mvar m => throw (.other s!"the kernel does not accept metavariables (?m{m})")
  | .natLit _ =>
    -- a numeral means `succ (… zero)`, so it needs both constructors, as definitions
    let defined (k : Name) := match (ctx.globals.builtins.lookup k).bind ctx.globals.find? with
      | some { value := some _, .. } => true
      | _ => false
    match ctx.globals.builtins.lookup "nat" with
    | some N =>
      if defined "nat.zero" && defined "nat.succ" then pure (ctx.eval (.const N []), Usage.zeros ctx.lvl)
      else throw (.other "numerals need `builtin nat.zero := …` and `builtin nat.succ := …`")
    | none => throw (.other "numerals need `builtin nat := …`")
  | .natOp .. => throw (.cannotInfer (ctx.showTerm t))
  -- (given) Q4: lifting
  | .ulift k' l A => do
    let k ← checkType ctx A
    checkComponentSort "lifted type (ULift)" k' k ctx.globals.sortHolesOk
    unless Level.le k l do
      throw (.other s!"ULift.{l.format} can't lift {ctx.showTerm A}, which is in Sort {k.format}")
    pure (.sort l, Usage.zeros ctx.lvl)
  | .up _ => throw (.cannotInfer (ctx.showTerm t))
  | .down x => do
    let (ty, u) ← infer ctx x
    match whnf ty with
    | .ulift _ _ A => pure (A, u)
    | _ => throw (.typeMismatch "a lifted type (ULift)" (ctx.showVal ty))
  --<sol
  -- (an index beyond the context is an error: `[ix]!` would panic and go on with the
  -- default value `Sort 0`, as the variable's type and as its value: a term `Prop : Prop`)
  | .var ix => match ctx.types[ix]? with
    | some ty => pure (ty, Usage.single ctx.lvl ix)
    | none => throw (.other s!"variable #{ix} is out of scope ({ctx.lvl} in scope)")
  | .const n us => match ctx.globals.find? n with
    | some d => do
      unless d.levelParams.length == us.length do
        throw (TypeError.other s!"{n} expects {d.levelParams.length} universe levels, got {us.length}")
      pure (Wiz.eval ctx.globals [] (d.type.instLevels d.levelParams us), Usage.zeros ctx.lvl)
    | none => throw (.unboundGlobal n)
  | .sort l => pure (.sort (.succ l), Usage.zeros ctx.lvl)
  | .pi x _ q dom cod σ => do
    let q ← checkQty ctx q
    let i ← checkType ctx dom
    checkComponentSort "Π's domain" σ.dom i ctx.globals.sortHolesOk
    let j ← checkType (ctx.bind x q (ctx.eval dom)) cod
    checkComponentSort "Π's codomain" σ.cod j ctx.globals.sortHolesOk
    -- (D1 experiment, off by default) predicative `Prop`: no quantifying over a universe
    -- into `Prop`
    if ctx.globals.predicativeProp && j.equiv 0 && largeDomain ctx (ctx.eval dom) ctx.lvl then
      throw (.other s!"impredicative Π (into Prop over {ctx.showTerm dom}) under predicative Prop")
    pure (.sort (if σ.hasHole then .imax i j else σ.piSort), Usage.zeros ctx.lvl)
  --|ex
  --| | .var ix => sorry
  --| | .const n us => sorry
  --| | .sort l => sorry
  --| | .pi x _ q dom cod s => sorry
  --sol>
  | .lam .. => throw (.cannotInfer (ctx.showTerm t))
  --<sol
  | .app f a => do
    let (fty, uf) ← infer ctx f
    match whnf fty with
    | .pi _ _ q dom cod _ =>
      let q ← qtyPoly ctx q
      -- (inside a proof: the application is a proof exactly when its function is, `Sort
      -- (imax a b)` being `0` when `Sort b` is. If it is not, it can be evaluated, and its
      -- argument with it: the argument is checked as in relevant mode)
      let actx := if ctx.proof && !ctx.isProofTy fty then { ctx with proof := false } else ctx
      let ua ← check (actx.erasedAt q) a dom
      pure (ctx.instArgAt dom cod a, uf + q • ua)
    | _ => throw (.notAFunction (ctx.showTerm f) (ctx.showVal fty))
  | .letE x q tty val body => do
    let q ← checkQty ctx q
    let _ ← checkType ctx tty
    let vty := ctx.eval tty
    if ctx.proof && ctx.isProofTy vty then
      -- inside a proof, a `let`-bound proof: bound suspended, so the body's type is known
      -- before the value is checked. If the `let` is not itself a proof it can be
      -- evaluated, and its value with it: the value is then checked as in relevant mode
      let (bty, ub) ← infer (ctx.define x q vty (suspend ctx.globals ctx.env val)) body
      let uv ← check ((if ctx.isProofTy bty then ctx else { ctx with proof := false }).erasedAt q) val vty
      let ub ← ctx.popUsageAt x q vty ub
      pure (bty, q • uv + ub)
    else
    let uv ← check (ctx.erasedAt q) val vty
    let (bty, ub) ← infer (ctx.define x q vty (ctx.eval val)) body
    let ub ← ctx.popUsageAt x q vty ub
    pure (bty, q • uv + ub)
  | .ann tm tty => do
    let _ ← checkType ctx tty
    let vty := ctx.eval tty
    let u ← check ctx tm vty
    pure (vty, u)
  | .sigma x q a b σ => do
    let q ← checkQty ctx q
    let i ← checkType ctx a
    checkComponentSort "Σ's first component" σ.dom i ctx.globals.sortHolesOk
    let j ← checkType (ctx.bind x q (ctx.eval a)) b
    checkComponentSort "Σ's second component" σ.cod j ctx.globals.sortHolesOk
    pure (.sort (if σ.hasHole then .max i j else σ.sigmaSort), Usage.zeros ctx.lvl)
  | .fst t => do
    let (ty, u) ← infer ctx t
    match whnf ty with
    | .sigma x q A _ _ =>
      -- in an erased position nothing is consumed: any field of any pair may be read; nor
      -- by a projection of a proof (a proof uses nothing)
      if ctx.erased || ctx.isPropTy ty then pure (A, u) else
      let q ← qtyPoly ctx q
      unless QPoly.le (QPoly.const 1) q do
        throw (.other s!"cannot project the field {x}, which has quantity {q}; use let (x, y) := ... instead")
      -- (R1) only an unrestricted pair has projections: `t` counts as used ω times
      pure (A, ← projUsage ctx t ty ".1" u)
    | _ => throw (.other s!"not a pair: {ctx.showTerm t}\n  has type: {ctx.showVal ty}")
  | .snd t => do
    let (pty, u) ← infer ctx t
    match whnf pty with
    | .sigma _ _ _ B _ =>
      let ty := Closure.inst ctx.globals B (vFst (ctx.evalAt t pty))
      if ctx.erased || ctx.isPropTy pty then pure (ty, u) else
      -- (R1) as for `t.1`. The first field's quantity doesn't matter: an unrestricted
      -- pair's field is at ω·q, which may always go unused
      pure (ty, ← projUsage ctx t pty ".2" u)
    | _ => throw (.other s!"not a pair: {ctx.showTerm t}\n  has type: {ctx.showVal pty}")
  | .split q s z m x y b => do
    let q ← checkQty ctx q
    let (sty, us) ← infer (ctx.erasedAt q) s
    match whnf sty with
    | .sigma _ p A B _ =>
      let p ← qtyPoly ctx p
      let j ← checkType (ctx.bind z [] sty) m
      -- (inside a proof, a `split` that is not a proof can be evaluated, and its scrutinee
      -- with it: a scrutinee that is a proof must then be marked or neutral-shaped)
      if ctx.proof && !j.isZero then ({ ctx with proof := false }).requireMarker s sty
      let mc : Closure R := .mk ctx.env m
      let vx : Val R := Val.var ctx.lvl
      let vy : Val R := Val.var (ctx.lvl + 1)
      let ctx₂ := (ctx.bind x (q * p) A).bind y q (Closure.inst ctx.globals B vx)
      let ub ← check ctx₂ b (Closure.inst ctx.globals mc (.pair vx vy))
      let ub ← (ctx.bind x (q * p) A).popUsageAt y q (Closure.inst ctx.globals B vx) ub
      let ub ← ctx.popUsageAt x (q * p) A ub
      pure (Closure.inst ctx.globals mc (ctx.evalAt s sty), q • us + ub)
    | _ => throw (.other s!"not a pair: {ctx.showTerm s}\n  has type: {ctx.showVal sty}")
  | .unit l => pure (.sort l, Usage.zeros ctx.lvl)
  | .empty l => pure (.sort l, Usage.zeros ctx.lvl)
  | .absurd m t => do
    let j ← checkType ctx m
    -- `t` can never be evaluated (nothing inhabits the empty type): an erased position
    -- (inside a proof: if the motive is not a proposition the `absurd` is a relevant term,
    -- which evaluates its argument: the argument is inferred as in relevant mode)
    let (ty, _) ← infer { ctx with erased := true, proof := ctx.proof && j.isZero } t
    match whnf ty with
    | .empty _ => pure (ctx.eval m, Usage.zeros ctx.lvl)
    | _ => throw (.typeMismatch "an empty type" (ctx.showVal ty))
  | .letUnit u b => do
    let uu ← checkUnit ctx u
    let (bty, ub) ← infer ctx b
    pure (bty, uu + ub)
  | .pair .. | .tt => throw (.cannotInfer (ctx.showTerm t))
  | .eq A a b => do
    let l ← checkType ctx A
    unless l.isNeverZero do
      throw (.other s!"equality is for types in Type u, not propositions: {ctx.showTerm A}")
    let vA := ctx.eval A
    let _ ← check ctx a vA
    let _ ← check ctx b vA
    pure (.sort 0, Usage.zeros ctx.lvl)
  | .eqTy A B => do
    let l ← checkType ctx A
    let l' ← checkType ctx B
    unless l.equiv l' do throw (.other "type equality between different universes")
    pure (.sort 0, Usage.zeros ctx.lvl)
  | .refl A a => do
    let l ← checkType ctx A
    unless l.isNeverZero do throw (.other "refl is for terms of types in Type u")
    let _ ← check ctx a (ctx.eval A)
    let va := ctx.eval a
    pure (vEq ctx.globals (ctx.eval A) va va, Usage.zeros ctx.lvl)
  | .reflTy X => do
    let _ ← checkType ctx X
    let vX := ctx.eval X
    pure (vEqType ctx.globals vX vX, Usage.zeros ctx.lvl)
  | .cast A B e t => do
    let l ← checkType ctx A
    let l' ← checkType ctx B
    unless l.equiv l' do throw (.other "cast between different universes")
    let vA := ctx.eval A
    let vB := ctx.eval B
    -- (the equation is never evaluated: checked as a proof)
    let _ ← check { ctx with erased := true, proof := true } e (vEqType ctx.globals vA vB)
    let u ← check ctx t vA
    pure (vB, u)
  | .transp A a P p b e => do
    -- a proof: everything in it is erased
    let ctx := { ctx with erased := true }
    let l ← checkType ctx A
    -- as for `eq` and `refl`: the motive's type and the type of `e` are equations at `A`
    unless l.isNeverZero do
      throw (.other s!"transp is for types in Type u, not propositions: {ctx.showTerm A}")
    let vA := ctx.eval A
    let _ ← check ctx a vA
    let va := ctx.evalAt a vA
    -- (b :0 A) → (_ :0 a = b) → Prop, with env [a, A]
    let motiveTy : Val R := .pi "b" .default (.qlit 0) vA
      (.mk [va, vA] (.pi "_" .default (.qlit 0) (.eq (.var 2) (.var 1) (.var 0)) (.sort 0) ⟨0, 1⟩)) ⟨l, .imax 0 1⟩
    let _ ← check ctx P motiveTy
    let vP := ctx.eval P
    let g := ctx.globals
    -- (`p` and `e` are never evaluated: checked as proofs)
    let _ ← check { ctx with proof := true } p (vApp g (vApp g vP va) (.neutral (.refl vA va) #[]))
    let _ ← check ctx b vA
    let vb := ctx.evalAt b vA
    let _ ← check { ctx with proof := true } e (vEq g vA va vb)
    pure (vApp g (vApp g vP vb) (suspend g ctx.env e), Usage.zeros ctx.lvl)
  | .qty => pure (.sort 1, Usage.zeros ctx.lvl)
  | .qlit _ => pure (.qty, Usage.zeros ctx.lvl)
  | .size => pure (.sort 1, Usage.zeros ctx.lvl)
  | .sizeLt s => do let _ ← check { ctx with erased := true } s .size; pure (.sort 1, Usage.zeros ctx.lvl)
  | .szInf => pure (.size, Usage.zeros ctx.lvl)
  | .szSuc s => do let _ ← check { ctx with erased := true } s .size; pure (.size, Usage.zeros ctx.lvl)
  | .enum _ => pure (.sort 1, Usage.zeros ctx.lvl)
  | .tag ls i => do
    unless i < ls.length do throw (.other s!"tag {i} out of range for {ls.length} labels")
    pure (.enum ls, Usage.zeros ctx.lvl)
  | .ecase z m s bs => do
    let (sty, us) ← infer ctx s
    let .enum ls := whnf sty | throw (.typeMismatch "an enumeration" (ctx.showVal sty))
    unless bs.length == ls.length do throw (.other s!"ecase needs {ls.length} branches, got {bs.length}")
    let _ ← checkType (ctx.bind z [] sty) m
    let mc : Closure R := .mk ctx.env m
    let mut ub : Option (Usage R) := none
    for b in bs, k in [0:bs.length] do
      let u ← check ctx b (Closure.inst ctx.globals mc (.tag ls k))
      match ub with
      | none => ub := some u
      | some u' =>
        let joined := (u.zip u').mapM fun (p, p') => QPoly.join? p p'
        let some j := joined | throw (.other "the branches of a case use variables incompatibly")
        ub := some j
    pure (Closure.inst ctx.globals mc (ctx.eval s), us + ub.getD (Usage.zeros ctx.lvl))
  | .desc l I => do
    let lI ← checkType ctx I
    unless lI.equiv (.succ l) do throw (.other "a description's index type must be in its universe")
    pure (.sort (.succ (.succ l)), Usage.zeros ctx.lvl)
  | .delim v P a b c h D => do
    let (dty, uD) ← infer ctx D
    let .desc l I := whnf dty | throw (.typeMismatch "a description" (ctx.showVal dty))
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx P (delimMotiveTy l v I w)
    let vP := ctx.eval P
    let (ta, tb, tc, th) := delimMethodTys ctx.globals l v I vP w
    let ua ← check ctx a ta
    let ub ← check ctx b tb
    let uc ← check ctx c tc
    let uh ← check ctx h th
    pure (vApp ctx.globals vP (ctx.eval D), ← methodUsage ctx (ua + ub + uc + uh + uD))
  | .mu l I D i s h | .nu l I D i s h => do
    checkHint ctx h
    let _ ← check { ctx with erased := true } s .size
    let lI ← checkType ctx I
    unless lI.equiv (.succ l) do throw (.other "an index type must be in the data type's universe")
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let _ ← check ctx i vI
    pure (.sort (.succ l), Usage.zeros ctx.lvl)
  | .ind l I D v P m i x => do
    checkIndexLevel ctx l I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx P (indMotiveTy ctx.globals l v vI vD w)
    let vP := ctx.eval P
    let um ← check ctx m (indMethodTy ctx.globals l v vI vD vP w)
    let _ ← check ctx i vI
    let vi := ctx.eval i
    let ux ← check ctx x (.mu l vI vD vi .szInf none)
    pure (vApp ctx.globals (vApp ctx.globals vP vi) (ctx.eval x), ← methodUsage ctx (um + ux))
  | .out x => do
    let (ty, u) ← infer ctx x
    let .nu l I D i s _ := whnf ty | throw (.typeMismatch "a coinductive type" (ctx.showVal ty))
    let some s' := sizePred? s
      | throw (.other s!"only a value of size ↑s or ∞ can be observed, not {ctx.showVal s}")
    pure (vInterp ctx.globals l I D (nuFamilyAt l I D s') i, u)
  | .sfix l I D v P f s i x => do
    checkIndexLevel ctx l I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx P (indMotiveTy ctx.globals l v vI vD w)
    let vP := ctx.eval P
    let uf ← check ctx f (sfixFunTy ctx.globals l v vI vD vP w)
    let _ ← check { ctx with erased := true } s .size
    let _ ← check ctx i vI
    let ux ← check ctx x (.mu l vI vD (ctx.eval i) (ctx.eval s) none)
    pure (vApp ctx.globals (vApp ctx.globals vP (ctx.eval i)) (ctx.eval x), ← methodUsage ctx (uf + ux))
  | .scofix l I D A f s i a => do
    checkIndexLevel ctx l I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx A (coitStateTy l vI w)
    let vA := ctx.eval A
    let uf ← check ctx f (scofixFunTy ctx.globals l vI vD vA w)
    let _ ← check { ctx with erased := true } s .size
    let _ ← check ctx i vI
    let ua ← check ctx a (vApp ctx.globals vA (ctx.eval i))
    pure (.nu l vI vD (ctx.eval i) (ctx.eval s) none, ← methodUsage ctx (uf + ua))
  | .scase l q I D v P m s i x => do
    -- (K1) the case at quantity `q`: the method runs once (unscaled) and receives the
    -- payload at `q`, so the scrutinee is used `q` times
    let qp ← checkQty ctx q
    checkIndexLevel ctx l I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx P (indMotiveTy ctx.globals l v vI vD w)
    let vP := ctx.eval P
    let _ ← check { ctx with erased := true } s .size
    let vs := ctx.eval s
    let um ← check ctx m (scaseMethodTy ctx.globals l v vI vD vP vs (ctx.eval q))
    let _ ← check ctx i vI
    let ux ← check (ctx.erasedAt qp) x (.mu l vI vD (ctx.eval i) vs none)
    pure (vApp ctx.globals (vApp ctx.globals vP (ctx.eval i)) (ctx.eval x), um + qp • ux)
  | .cocon _ => throw (.cannotInfer (ctx.showTerm t))
  | .coit l I D S st i s => do
    checkIndexLevel ctx l I
    let vI := ctx.eval I
    let _ ← check ctx D (.desc l vI)
    let vD := ctx.eval D
    let w := QuantitySyntax.explicitDefault
    let _ ← check ctx S (coitStateTy l vI w)
    let vS := ctx.eval S
    let ust ← check ctx st (coitStepTy ctx.globals l vI vD vS w)
    let _ ← check ctx i vI
    let vi := ctx.eval i
    let us ← check ctx s (vApp ctx.globals vS vi)
    pure (.nu l vI vD vi .szInf none, ← methodUsage ctx (ust + us))
  | .dret _ | .darg .. | .drec .. | .dhrec .. | .con _ => throw (.cannotInfer (ctx.showTerm t))
  --|ex
  --| | .app f a => sorry
  --| | .letE x q tty val body => sorry
  --| | .ann tm tty => sorry
  --| -- Exercise 4.7b
  --| | .sigma x q a b s => sorry
  --| | .fst t => sorry
  --| | .snd t => sorry
  --| | .split q s z m x y b => sorry
  --| | .unit l => sorry
  --| | .empty l => sorry
  --| | .absurd m t => sorry
  --| | .pair .. | .tt => throw (.cannotInfer (ctx.showTerm t))
  --| -- Exercise 4.14
  --| | .eq A a b => sorry
  --| | .eqTy A B => sorry
  --| | .refl A a => sorry
  --| | .reflTy X => sorry
  --| | .cast A B e t => sorry
  --| | .transp A a P p b e => sorry
  --| | .qty => pure (.sort 1, Usage.zeros ctx.lvl)
  --| | .qlit _ => pure (.qty, Usage.zeros ctx.lvl)
  --| | .size => pure (.sort 1, Usage.zeros ctx.lvl)
  --| | .sizeLt s => do let _ ← check { ctx with erased := true } s .size; pure (.sort 1, Usage.zeros ctx.lvl)
  --| | .szInf => pure (.size, Usage.zeros ctx.lvl)
  --| | .szSuc s => do let _ ← check { ctx with erased := true } s .size; pure (.size, Usage.zeros ctx.lvl)
  --| -- Exercise 4.20: the data rules (see the module docstring)
  --| | .enum _ => sorry
  --| | .tag ls i => sorry
  --| | .ecase z m s bs => sorry
  --| | .desc l I => sorry
  --| | .delim v P a b c h D => sorry
  --| | .mu l I D i _ _ | .nu l I D i _ _ => sorry
  --| | .ind l I D v P m i x => sorry
  --| | .out x => sorry
  --| | .coit l I D S st i s => sorry
  --| -- Exercise 4.23: the sized rules
  --| | .sfix l I D v P f s i x => sorry
  --| | .scofix l I D A f s i a => sorry
  --| | .scase l q I D v P m s i x => sorry
  --| | .cocon _ => throw (.cannotInfer (ctx.showTerm t))
  --| | .dret _ | .darg .. | .drec .. | .dhrec .. | .con _ => throw (.cannotInfer (ctx.showTerm t))
  --sol>

/-- The hint of a `μ`/`ν` type is its nominal form, `(T, us, args)` for `T.{us} args` (the
elaborator reads it back to find a type's name, constructors and arguments; conversion
ignores it). It is not otherwise constrained, but `eval` evaluates its arguments, so they
must be well typed: an unchecked term there would be run by the evaluator (any of its
`panic!`s, a loop, a constant at the wrong number of levels). If `T` is declared, the
application `T.{us} args` must be well typed. If it is not (the definition of `T` itself,
whose hint lists its own parameters), every argument must have an inferable type. That
the hint *is* the type (`T.{us} args ≡ μ …`) is not checked: nothing in the kernel
depends on it. -/
partial def checkHint (ctx : Ctx R) : Option (Name × List Level × List (Term R)) → TCM Unit
  | none => pure ()
  | some (T, us, args) => do
    let ctx := { ctx with erased := true }
    if (ctx.globals.find? T).isSome then
      let _ ← infer ctx (args.foldl .app (.const T us))
    else
      for a in args do
        let _ ← infer ctx a

/-- The index type of a data type at level `l` lives exactly in `Sort (l+1)`: the premise
`Γ ⊢ I type@k`, `k ≡ l+1` of `μ`/`ν`, repeated by every eliminator that names `I` (`ind`,
`sfix`, `scase`, `coit`, `scofix`). The eliminators need it as much as the type formers:
they check their scrutinee against `μ.{l} I D i` (or return `ν.{l} I D i`) without going
through the type former, so without this premise a term could have a type that is not a
type (soundness audit F3; it is the "index level ≤ family level" condition that injective
type formers need). -/
partial def checkIndexLevel (ctx : Ctx R) (l : Level) (I : Term R) : TCM Unit := do
  let lI ← checkType ctx I
  unless lI.equiv (.succ l) do
    throw (.other s!"an index type must be in the data type's universe: Sort {(Level.succ l).format}, not Sort {lI.format} (lift it with ULift)")

/-- The scrutinee of `let () := u; b` (linear-case stage 2): `u` must have the type
`Unit_l` itself (after `whnf`), never a type that is merely a singleton by η (a function
into `Unit` may be a closure holding a resource: applying it would need its argument). Its
usage is `u`'s own, counted once: the eliminator consumes it. -/
partial def checkUnit (ctx : Ctx R) (u : Term R) : TCM (Usage R) := do
  match u with
  | .tt => pure (Usage.zeros ctx.lvl)
  | _ =>
    let (ty, uu) ← infer ctx u
    match whnf ty with
    | .unit _ => pure uu
    | _ => throw (.typeMismatch "Unit (`let () := u` takes apart a value of the unit type only)" (ctx.showVal ty))

/-- A binder's quantity annotation: a term of type `Qty` (its usage is discarded, as
for types), returned as a polynomial. -/
partial def checkQty (ctx : Ctx R) (q : Term R) : TCM (QPoly R) := do
  let _ ← check ctx q .qty
  qtyPoly ctx (ctx.eval q)

/-- `Γ ⊢ A type@i`: infer `A`, require it to be a `sort`, return the level.
The usage is discarded: type positions are erased. -/
partial def checkType (ctx : Ctx R) (a : Term R) : TCM Level := do
  -- (a type is a relevant term, also inside a proof: it is evaluated)
  let (ty, _) ← infer { ctx with erased := true, proof := false } a
  match whnf ty with
  | .sort l => pure l
  | _ => throw (.notAType (ctx.showTerm a) (ctx.showVal ty))

end

/-- (D1 experiment, `predicativeProp`) Check a declaration's type, but not the
predicativity of its outer `Π`s: a theorem quantifying over types is fine in a predicative
`Prop` too (in a bigger `Prop` or in `Type`; the theorem itself is never used as a proof
of a proposition at level 0). -/
partial def declTypeSpine (ctx : Ctx R) : Term R → TCM Level
  | .pi x _ q dom cod σ => do
    let q ← checkQty ctx q
    let i ← checkType ctx dom
    checkComponentSort "Π's domain" σ.dom i ctx.globals.sortHolesOk
    let j ← declTypeSpine (ctx.bind x q (ctx.eval dom)) cod
    checkComponentSort "Π's codomain" σ.cod j ctx.globals.sortHolesOk
    pure (if σ.hasHole then .imax i j else σ.piSort)
  | t => checkType ctx t

/-- The checks every declaration's header gets: a new name, its level parameters, and
its type is a type. -/
def checkHeader (g : Globals R) (d : Decl R) : TCM Unit := do
  -- (P2) the kernel evaluates no proof, so it has no step budget, and must not be given
  -- one: a budget that ran out inside a conversion would make two different closures the
  -- same stuck constant
  if g.budget.isSome then throw (.other "internal error: the kernel was called inside a proof's read-back (a step budget is set)")
  if g.contains d.name then throw (.duplicateDecl d.name)
  -- (mandatory sorts) **no hole reaches the kernel**: every `Π`/`Σ`/`ULift` of a checked
  -- declaration has its sorts. Formation rejects a hole too, at every `Π`/`Σ`/`ULift` it
  -- checks; this says it once for the whole declaration (its implementation and witness
  -- included), so that `sameSort`'s tolerance of holes (for the elaborator) is never used
  -- on a term the kernel accepted
  if d.type.hasHole || d.value.any (·.hasHole) || d.impl.any (·.hasHole) || d.witness.any (·.hasHole) then
    throw (.other s!"internal error: a Π/Σ/ULift in {d.name} without its sorts (the sorts pass did not fill it)")
  unless d.levelParams.eraseDups.length == d.levelParams.length do
    throw (.other s!"duplicate universe level parameter in {d.name}")
  let used := d.type.levelParamsUsed ++ (d.value.map Term.levelParamsUsed).getD [] ++
    (d.witness.map Term.levelParamsUsed).getD []
  if let some u := used.find? (!d.levelParams.contains ·) then
    throw (.other s!"unknown universe level parameter {u} in {d.name}")
  let ctx : Ctx R := { globals := g }
  if g.predicativeProp then discard <| declTypeSpine ctx d.type
  else discard <| checkType ctx d.type

/-- A definition's **implementation for the compiler** (`Decl.impl`): the term compiled
code runs instead of the value. It may call the definition itself (a structurally
recursive definition's equations with direct recursion), so it is checked against the
declared type in `g`, which already has the definition. The kernel never unfolds it, so it
proves nothing; it is checked because erasure reads it (its types, the sorts noted on its
`Π`s and `Σ`s, its quantities) as it reads a checked term. That a definition's derived
equations compute what its value computes is checked by `checkImplAgrees` (`addDecl`). -/
def checkImpl (g : Globals R) (d : Decl R) (impl : Term R) : TCM Unit := do
  if let some u := impl.levelParamsUsed.find? (!d.levelParams.contains ·) then
    throw (.other s!"unknown universe level parameter {u} in the implementation of {d.name}")
  let ctx : Ctx R := { globals := g }
  match check ctx impl (ctx.eval d.type) with
  | .ok _ => pure ()
  -- (P2) kept as it is, so that the elaborator's marking on demand (`withMarksOnDemand`)
  -- sees that the implementation asks for markers, as a value does
  | .error e@(.unmarkedProof ..) => throw e
  | .error e => throw (.other s!"the implementation of {d.name} (the term compiled code runs) does not check: {e}")

/-- Does the term mention the constant `c`? -/
partial def mentionsConst (c : Name) (t : Term R) : Bool := match t with
  | .const n _ => n == c
  | t => (t.forChildren (m := StateM Bool) (fun _ => pure ()) (fun _ x => modify (· || mentionsConst c x)) |>.run false).2

/-- The constant `c` renamed to `c'` (for tests). -/
partial def replaceConstTo (c c' : Name) (t : Term R) : Term R := match t with
  | .const n us => if n == c then .const c' us else t
  | t => Id.run <| t.mapChildrenM pure (fun _ x => pure (replaceConstTo c c' x))

/-- The constant `c` at the levels `us` replaced by a variable bound outside the term
(`var 0` at the top). At other levels it stays (and `callsOnFields` rejects it). -/
partial def replaceConst (c : Name) (us : List Level) (t : Term R) (depth : Nat := 0) : Term R := match t with
  | .const n us' => if n == c && us' == us then .var depth else t
  | t => Id.run <| t.mapChildrenM pure (fun k x => pure (replaceConst c us x (depth + k)))

/-- **Every call is on a field** (`checkImplAgrees`; termination of compiled code). The
implementation is `[prf.{l}] λ a₀ … a_{k-1}. [let …] K Δ motive m₁ … mₙ ξ x …` for a `T.casesOn`
(or `casesOnN`) `K`, whose scrutinee is the column variable `x` itself (and, in mode A,
whose indices are the index variables `ixL`), and the definition `fn` (at its own levels `us`) occurs only in the
methods, each time as the head of a call whose argument at position `x` (the split's
column) is a field of the method's constructor (`λ fields. …`, a field variable or such a
variable applied to arguments, for an infinitary field). Then every call compiled code
makes is on a strictly smaller value (a field of the scrutinee), so it terminates as the
kernel's recursion does; the conversion check alone cannot see calls at types where every
two values are convertible (`Unit`, propositions). (A `mutual` block's constructors are
named by their member, `Ev.z`, so a case's method binder `m_Ev.z` already names the
constant; otherwise it is the family's `T.c`.) -/
partial def callsOnFields (g : Globals R) (fn : Name) (us : List Level) (k x : Nat) (ixL : Option (List Nat))
    (impl : Term R) : Bool := Id.run do
  let rec peel : Nat → Term R → Option (Term R)
    | 0, t => some t
    | n + 1, .lam _ b => peel n b
    -- (P2: the value and the implementation of a definition whose sort may be `0` get a
    -- top marker, `prf.{u}` at a symbolic level; `lams` counts through it and the binder
    -- indices are unchanged: look through it, as the agreement check does)
    | n + 1, .prf _ b => peel (n + 1) b
    | _, _ => none
  let some body := peel k impl | return false
  let rec skipLets : Term R → Nat → Term R × Nat
    | .letE _ _ ty v b, n => if mentionsConst fn ty || mentionsConst fn v then (.tt, 0) else skipLets b (n + 1)
    | t, n => (t, n)
  let (body, nLets) := skipLets body 0
  let (.const K _, args) := body.spine | return false
  unless K.endsWith ".casesOn" || K.endsWith ".casesOnN" do return false
  let T := String.ofList (K.toList.take (K.length - (if K.endsWith ".casesOnN" then 9 else 8)))
  let (some Td, some descD, some kd) := (g.find? T, g.find? (T ++ ".desc"), g.find? K) | return false
  let rec pis : Term R → Nat
    | .pi _ _ _ _ b _ => pis b + 1
    | _ => 0
  let nΔ := pis descD.type
  let nΞ := pis Td.type - nΔ
  let nc := pis kd.type - nΔ - nΞ - 2
  let rec mbinders : Term R → List Name
    | .pi m _ _ _ b _ => m :: mbinders b
    | _ => []
  let ctors := ((mbinders kd.type).drop (nΔ + 1)).take nc |>.map fun mn => String.ofList (mn.toList.drop 2)
  -- outside the methods: no call at all
  -- the split is the split of the column `x` (a split of anything else, a constructor
  -- applied to `x` say, would make its "fields" `x` itself: t1-review M1c), at the index
  -- variables in mode A
  let ix (ℓ : Nat) : Term R := .var (nLets + k - 1 - ℓ)
  unless args[nΔ + 1 + nc + nΞ]? == some (ix x) do return false
  if let some ls := ixL then
    unless (args.drop (nΔ + 1 + nc)).take nΞ == ls.map ix do return false
  let outside := args.take (nΔ + 1) ++ args.drop (nΔ + 1 + nc)
  if outside.any (mentionsConst fn ·) then return false
  let methods := (args.drop (nΔ + 1)).take nc
  let ok := (ctors.zip methods).all fun (c, m) => Id.run do
    -- (a `mutual` block's constructors are named by their member, `Ev.z`, and so are the
    -- case's method binders, `m_Ev.z`: `c` is then the constant itself; otherwise it is
    -- the family's `T.c`)
    let some cd := (if c.contains '.' then g.find? c else g.find? (T ++ "." ++ c)) | return false
    let F := pis cd.type - nΔ
    let some mb := peel F m | return !mentionsConst fn m
    -- in `mb` under `dd` more binders, field `j` is `var (dd + F - 1 - j)`
    return calls F 0 mb
  return ok
where
  isField (F dd : Nat) (t : Term R) : Bool := match t with
    | .var i => dd ≤ i && i < dd + F
    | .app f _ => isField F dd f
    | _ => false
  calls (F dd : Nat) (t : Term R) : Bool :=
    match t.spine with
    | (.const n us', as) =>
      if n == fn then
        us' == us && as.length > x && isField F dd as[x]! && as.all (calls F dd)
      else as.all (calls F dd)
    | (h, as@(_ :: _)) => calls F dd h && as.all (calls F dd)
    | (t, []) => (t.forChildren (m := StateM Bool) (fun _ => pure ())
        (fun k c => modify (· && calls F (dd + k) c)) |>.run true).2

/-- **The bridge by shape** (`checkImplAgrees`). The value is
`λ a₀ … a_{k-1}. r Δ motive methods ξ x [e] rs` for a recursor `r` (`T.rec`/`T.recN`),
literally (no `let`, the body is this application), where

* `x` and `rs` are variables, the split's columns (levels `x`, `rs`, in this order after
  `ξ`, with one argument between them in mode B: the index equation's proof);
* in mode A, `ξ` is the variables `ixL`; in mode B, `ξ` mentions no column;
* `Δ`, `motive` and `methods` mention no column, nor (mode A) an index variable.

Then for every `j` and `y`, applying the value to the arguments of `hypCall f j y`
(the columns replaced by `y` and the new `rs`, the index variables by `j`'s components,
every other argument the same variable) evaluates `r` on the *same* `Δ`, motive and
methods (they do not mention what changed), at index `j` (mode A) or the split's own
index (mode B) and scrutinee `y`; `r` unfolds to `ind P M j y rs` with the `P` and `M` of
the value's own split. So `hypCall f j y ≡ ind P M j y`: the conversion `checkImplAgrees`
would otherwise do (once) holds by evaluation. A value of another shape returns `false`
and the conversion is done. -/
def bridgeByShape (g : Globals R) (value : Term R) (k x : Nat) (rs ixL : List Nat) (modeA : Bool)
    (nΞ : Nat) : Bool := Id.run do
  let rec peel : Nat → Term R → Option (Term R)
    | 0, t => some t
    | n + 1, .lam _ b => peel n b
    | _, _ => none
  let some body := peel k value | return false
  let (.const r _, targs) := body.spine | return false
  let some rd := g.find? r | return false
  unless r.endsWith ".rec" || r.endsWith ".recN" do return false
  let rec pis : Term R → Nat
    | .pi _ _ _ _ b _ => pis b + 1
    | _ => 0
  let nPre := pis rd.type - nΞ - 1
  -- (level ℓ of the value's λs is de Bruijn index k-1-ℓ in its body)
  let ix (ℓ : Nat) : Nat := k - 1 - ℓ
  let cols := x :: rs
  let forbidden := cols ++ (if modeA then ixL else [])
  let clean (t : Term R) : Bool := forbidden.all fun ℓ => !t.hasVar (ix ℓ)
  unless targs.length ≥ nPre + nΞ + 1 do return false
  unless (targs.take nPre).all clean do return false
  let ξs := (targs.drop nPre).take nΞ
  let okξ := if modeA then ξs == ixL.map fun ℓ => (.var (ix ℓ) : Term R) else ξs.all clean
  unless okξ do return false
  let after := targs.drop (nPre + nΞ)
  let after ← if modeA then pure after else match after with
    | x0 :: _ :: rest => pure (x0 :: rest)
    | _ => return false
  return after == (cols.map fun ℓ => (.var (ix ℓ) : Term R))

/-- **The compiled equations agree with the definition** (docs/Status.md T1): for a
structurally recursive definition whose `impl` is derived from its value, one conversion
per constructor. `g` has the definition (with its value). Applied to fresh variables for
the value's λ-prefix, both must be stuck on the same variable as `ind P M i x …` (the
value through `T.rec`) and `ind P M' i x …` (the implementation through `T.casesOn`, whose
method ignores the hypotheses and calls the definition directly):

* the two stuck terms are convertible with `M'` replaced by `M`;
* for every tag `t` of the description `D = Σ (t : Enum ls). F t`, at a fresh index `j` and
  payload `xs = (t, rest)`, with `H` the hypotheses the kernel computes for `ind`
  (`hyps D (μ D) P (λ j y. ind P M j y) j xs`, as `vIndStep` does):
  `M j xs H ≡ M' j xs H : P j (con xs)`. Where the value uses a hypothesis, `ind P M j' y`
  on a field `y`, the implementation calls the definition, which unfolds once to the same
  stuck `ind` (so the check terminates).

By induction on the scrutinee this gives `value ≡ impl` on every closed argument, with
the implementation's own recursive calls standing for the value (the induction
hypothesis): what compiled code computes is what the kernel computes. An implementation
convertible to the value passes at once; a proposition-valued definition is a proof, whose
value is suspended (P2) and any two of which are convertible (proof irrelevance), so a
well-typed implementation agrees with it. -/
partial def checkImplAgrees (g : Globals R) (d : Decl R) (value impl : Term R) : TCM Unit := do
  let fail {α : Type} (why : String) : TCM α :=
    throw (.other s!"the compiled equations of {d.name} do not agree with its definition: {why}")
  -- A proposition-valued definition is a proof: the evaluator suspends its value (P2), so
  -- there is no split to compare, and conversion takes any two proofs as equal (proofs
  -- are erased and nothing runs them). A well-typed implementation agrees with it.
  let ty0 := eval g [] d.type
  if ((Ctx.sortOf? ({ globals := g } : Ctx R)) ty0).any (·.isZero) then
    if conv g #[] ty0 (eval g [] value) (eval g [] impl) then return
    fail "its value is a proposition, and its implementation is not convertible to it"
  -- An implementation that does not call the definition (a hand-written one, say) agrees
  -- with the value if it is convertible to it. One that calls it is checked below; the
  -- whole-term comparison would compare the two eliminators structurally first, and fail.
  if !mentionsConst d.name impl then
    if conv g #[] ty0 (eval g [] value) (eval g [] impl) then return
    fail "it is not convertible to the value and does not call the definition"
  -- (P2: the conversion goes through the markers too: a level-generic value is
  -- `prf.{l} (fun …)`, with `l` symbolic, which evaluates to its body's value)
  let rec lams : Term R → Nat
    | .lam _ b => lams b + 1
    | .prf _ b => lams b
    | _ => 0
  let k := lams value
  let mut tys : Array (VTy R) := #[]
  let mut ty := ty0
  for i in [0:k] do
    match whnf ty with
    | .pi _ _ _ A B _ => tys := tys.push A; ty := Closure.inst g B (Val.var i)
    | _ => fail "its value has more binders than its type"
  -- The definition, in the implementation, as a variable `F` (level `k`, of its type): its
  -- calls stay calls, compared by their arguments (see the hypotheses below)
  let fL := k
  let fV : Val R := Val.var fL
  tys := tys.push ty0
  let args := (List.range k).map Val.var
  let a := whnf (args.foldl (vApp g) (eval g [] value))
  -- (the implementation with `F` for the definition: everything it says but the calls is
  -- compared with `F` free, which is the more general statement)
  let b := whnf (args.foldl (vApp g) (eval g [fV] (replaceConst d.name (d.levelParams.map Level.param) impl)))
  let (.neutral (.local x) sp, .neutral (.local x') sp') := (a, b)
    | fail "the value or the implementation is not stuck on an argument"
  let (some (Elim.ind l I D v P M i), some (Elim.ind l' I' D' v' P' MF i')) := ((sp[0]? : Option (Elim R)), (sp'[0]? : Option (Elim R)))
    | fail "the value or the implementation is not an induction on an argument"
  let MF? : Option (Val R) := some MF
  unless x == x' && sp.size == sp'.size do fail "they split different arguments"
  -- (the methods are checked below; here both are a fresh variable of the method type, so
  -- that comparing them costs nothing: comparing `M` with itself would go through every
  -- branch of it)
  let mV : Val R := Val.var tys.size
  let tysM := tys.push (indMethodTy g l v I D P QuantitySyntax.explicitDefault)
  let a' : Val R := .neutral (.local x) (sp.set! 0 (.ind l I D v P mV i))
  let b' : Val R := .neutral (.local x') (sp'.set! 0 (.ind l' I' D' v' P' mV i'))
  unless conv g tysM ty a' b' do fail "their motives, indices or other arguments differ"
  -- the methods, constructor by constructor
  let .darg _ S Fd := whnf D | fail "the description does not start with a tag"
  let (ls, lifted) ← match whnf S with
    | .enum ls => pure (ls, false)
    | .ulift _ _ A => match whnf A with
      | .enum ls => pure (ls, true)
      | _ => fail "the description does not start with a tag"
    | _ => fail "the description does not start with a tag"
  let jL := tys.size
  let jv : Val R := Val.var jL
  let X := muFamily l I D
  -- y0 j1 m2 P3 D4 I5 (as in `vIndStep`)
  let fInd : Val R := .lam "j" (.mk [M, P, D, I] (.lam "y" (.ind l (.var 5) (.var 4) v (.var 3) (.var 2) (.var 1) (.var 0))))
  /- **The hypotheses as calls.** The kernel's hypothesis for a field `y` at index `j` is
  `ind P M j y`; a direct call `F … y …` unfolds to an `ind` too, but only after the whole
  definition (and its recursor) is evaluated again, and comparing the two `ind`s compares
  every method: once per call, quadratic in the size of a big family. So, where it
  applies, the hypothesis is replaced by the call it is equal to, `hypCall F j y`: the
  arguments of the value's own split (`a`: `ind … x rs`) with `x := y`, the index
  variables (if the split's index is made of variables) `:= j`, and the other columns
  `rs` abstracted. It is checked once that `hypCall f j y ≡ ind P M j y` for the real
  definition `f` (at a fresh `j`, or at the split's own index when that is not made of
  variables, and then only where `j` is that index). The per-constructor check below
  holds with `F` free, so also for `F := f`; with the bridge it holds for the kernel's
  hypotheses. -/
  let rec comps : Nat → Val R → List (Val R)
    | 0, _ => []
    | n + 1, t => match whnf t with
      | .pair c r => c :: comps n r
      | _ => []
  let iComps := comps 64 i
  let ixL0? : Option (List Nat) := iComps.mapM fun c => match whnf c with
    | .neutral (.local l) #[] => some l
    | _ => none
  -- (an index that is not made of distinct variables: mode B, the split's next argument
  -- is the proof of its index equation, not a column)
  let ixL0? := ixL0?.bind fun ls => if ls.eraseDups.length == ls.length && !ls.contains x then some ls else none
  let rsArgs := (sp.extract 1 sp.size).toList
  let rsArgs := if ixL0?.isSome then rsArgs else rsArgs.drop 1
  let rsL? : Option (List Nat) := rsArgs.mapM fun e => match e with
    | .app (.neutral (.local l) #[]) => some l
    | _ => none
  -- (an index variable that is also a column: no substitution of the index)
  let ixL? := ixL0?.bind fun ls => if (rsL?.getD []).all (!ls.contains ·) then some ls else none
  let modeA := ixL?.isSome
  unless callsOnFields g d.name (d.levelParams.map Level.param) k x ixL? impl do
    fail "a call of the definition is not on a field of the constructor of the split it is in (compiled code could loop)"
  let ixL := ixL?.getD []
  let hypCall (head j y : Val R) (rs : List Nat) (eqArg : Bool) : Val R :=
    let m := rs.length
    let nE := if eqArg then 1 else 0
    let nq := ixL.length
    let unpack (q : Nat) : Val R := vFst ((List.range q).foldl (fun t _ => vSnd t) j)
    -- environment: head, y, the index components, then the levels 0 … k-1
    let env : List (Val R) := [head, y] ++ (List.range nq).map unpack ++ (List.range k).map Val.var
    let ref (e : Nat) : Term R := .var (m + nE + e)
    let argTm (ℓ : Nat) : Term R :=
      if ℓ == x then ref 1
      else match rs.idxOf? ℓ with
        | some p => .var (m - 1 - p)
        | none => match ixL.idxOf? ℓ with
          | some q => ref (2 + q)
          | none => ref (2 + nq + ℓ)
    let call : Term R := ((List.range k).map argTm).foldl .app (ref 0)
    let body := (List.range (m + nE)).foldr (fun _ t => Term.lam "r" t) call
    eval g env body
  -- (the same call as a term at depth `D`, `y` and `j` terms there: for a hypothesis under
  -- the binder of an infinitary field)
  let hypCallTm (D : Nat) (jT yT : Term R) (rs : List Nat) (eqArg : Bool) : Term R :=
    let m := rs.length
    let nE := if eqArg then 1 else 0
    let sh := m + nE
    let lvl (ℓ : Nat) : Term R := .var (D + sh - 1 - ℓ)
    let unpackT (q : Nat) : Term R := .fst ((List.range q).foldl (fun t _ => .snd t) (jT.lift sh))
    let argTm (ℓ : Nat) : Term R :=
      if ℓ == x then yT.lift sh
      else match rs.idxOf? ℓ with
        | some p => .var (m - 1 - p)
        | none => match ixL.idxOf? ℓ with
          | some q => unpackT q
          | none => lvl ℓ
    let call : Term R := ((List.range k).map argTm).foldl .app (lvl fL)
    (List.range sh).foldr (fun _ t => Term.lam "r" t) call
  let fReal : Val R := eval g [] (.const d.name (d.levelParams.map Level.param))
  let replace? : Option (Array (VTy R) → Val R → Bool) := do
    let rs ← rsL?
    -- (mode B needs an index equation; an index of variables that is not mode A: none)
    unless modeA || ixL0?.isNone do none
    let _ ← MF?
    -- mode B: the hypothesis takes the index equation first
    let eqArg := !modeA
    let yTy (j : Val R) : VTy R := .mu l I D j .szInf none
    let bridge (j : Val R) (tys' : Array (VTy R)) : Bool :=
      let yv := Val.var tys'.size
      let tys'' := tys'.push (yTy j)
      conv g tys'' (vApp g (vApp g P j) yv) (hypCall fReal j yv rs eqArg) (vApp g (vApp g fInd j) yv)
    -- The bridge holds by the shape of the value, when it is `λ…. r Δ motive methods ξ x
    -- [e] rs` for the recursor `r` with `x`, `rs` the split's columns, `ξ` (mode A) its
    -- index variables, and `Δ`, the motive and the methods mentioning neither: then the
    -- call evaluates `r` on the same `Δ`, motive and methods, at `(y, rs)` and index `j`,
    -- and `r` unfolds to `ind P M j y rs` with the same `P` and `M`. Otherwise it is
    -- checked by conversion (once, at a fresh field).
    let byShape := bridgeByShape g value k x rs ixL modeA iComps.length
    if modeA then
      if byShape || bridge jv (tys.push I) then some fun _ _ => true else none
    else
      if byShape || bridge i tys then some fun tys' j => conv g tys' I j i else none
  let rs := rsL?.getD []
  -- the tuple of hypotheses, with each `ind P M j y` (at an index where `ok`) replaced
  -- (`none` when a hypothesis is not of that form, an infinitary field's say: then the
  -- constructor is checked with the kernel's hypotheses and the real definition)
  let rec swap (tys' : Array (VTy R)) (ok : Array (VTy R) → Val R → Bool) : Nat → Val R → Option (Val R)
    | 0, _ => none
    | n + 1, h => match whnf h with
      | .pair c r => do
        let c' ← match whnf c with
          | .neutral hd sp => match sp.back? with
            | some (.ind _ _ _ _ _ _ j) =>
              some (if ok tys' j then hypCall fV j (.neutral hd sp.pop) rs (!modeA) else c)
            | _ => none
          -- an infinitary field's: `λ h. ind P M (j h) (k h)` becomes `λ h. F … (k h) …`
          | .lam hn clo =>
            let hl := tys'.size
            match whnf (Closure.inst g clo (Val.var hl)) with
            | .neutral hd sp => match sp.back? with
              | some (.ind _ _ _ _ _ _ j) =>
                if ok tys' j then
                  let jT := quote g (hl + 1) j
                  let yT := quote g (hl + 1) (.neutral hd sp.pop)
                  let env := (List.range hl).reverse.map Val.var
                  some (eval g env (.lam hn (hypCallTm (hl + 1) jT yT rs (!modeA))))
                else some c
              | _ => none
            | _ => none
          | _ => none
        pure (.pair c' (← swap tys' ok n r))
      | h => some h
  -- (at the split's own index `i`, which is general enough: the implementation runs on a
  -- scrutinee at that index, its recursive calls go through the hypotheses. A
  -- constructor whose payload is empty there, one of another sort of a mutual family,
  -- has nothing to check)
  let rec emptyPayload (tys' : Array (VTy R)) : Nat → VTy R → Bool
    | 0, _ => false
    | n + 1, ty => match whnf ty with
      | .empty _ => true
      | .sigma _ _ A B _ =>
        emptyPayload tys' n A || emptyPayload (tys'.push A) n (Closure.inst g B (Val.var tys'.size))
      | _ => false
  for c in [0:ls.length] do
    let t : Val R := if lifted then .up (.tag ls c) else .tag ls c
    let jv := i
    let tysJ := tys
    let restTy := vInterp g l I (vApp g Fd t) X jv
    if emptyPayload tysJ 64 restTy then continue
    let tys' := tysJ.push restTy
    let xs : Val R := .pair t (Val.var tysJ.size)
    let hyps := [I, D, X, P, fInd, jv, xs].foldl (vApp g) (eval g [] (Templates.hypsTm l v))
    -- (the implementation is compared with `F` free, always: so each of its calls must be
    -- one of the hypotheses' calls, on a field. A call on anything else, the scrutinee say,
    -- would make compiled code loop where the kernel's recursion is well founded: such an
    -- implementation is rejected, though it may be convertible to the value)
    let some ok := replace? | fail "its calls could not be matched with the definition's hypotheses"
    let some mF := MF? | fail "its calls could not be matched with the definition's hypotheses"
    let some hyps' := swap tys' ok 1000 hyps
      | fail s!"a hypothesis of constructor {ls[c]!} is not of the form the calls are compared with"
    let (hyps, M') := (hyps', mF)
    let goal := vApp g (vApp g P jv) (.con xs)
    unless conv g tys' goal ([jv, xs, hyps].foldl (vApp g) M) ([jv, xs, hyps].foldl (vApp g) M') do
      fail s!"they differ for constructor {ls[c]!}"

/-- Type check a declaration and add it to the global environment. Its implementation
for the compiler, if it has one, is checked too (`checkImpl`): no term reaches erasure
unchecked. -/
def addDecl (g : Globals R) (d : Decl R) : TCM (Globals R) := do
  -- constants are identified by name: a second declaration of one would change what
  -- everything checked against the first means
  if g.contains d.name then throw (.duplicateDecl d.name)
  if d.witness.isSome then throw (.other s!"{d.name}: only a partial definition has a witness")
  checkHeader g d
  let ctx : Ctx R := { globals := g }
  if let some v := d.value then
    -- usage is the empty vector: a closed term has no locals to misuse
    let _ ← check ctx v (ctx.eval d.type)
  let g' := g.insert d
  if let some impl := d.impl then
    checkImpl g' d impl
    -- compiled equations derived from the value compute what it computes
    if let some v := d.value then
      if d.derivedEquations then checkImplAgrees g' d v impl
  pure g'

/-- Give the declaration `name` another implementation for the compiler
(`attribute [implemented_by g] f` sets the constant `g`), checked like a definition's own
(`checkImpl`): at `name`'s type. The kernel's view of `name` does not change. -/
def setImpl (g : Globals R) (name : Name) (impl : Term R) : TCM (Globals R) := do
  let some d := g.find? name | throw (.other s!"unknown declaration '{name}'")
  checkImpl g d impl
  pure (g.insert { d with impl := some impl })

/-- A partial definition's signature (stage 13): `f : T` is opaque to the kernel, like an
axiom, so the bodies of its group can call it. It must come with a **witness** `w : T`,
which the kernel checks here: then `f` proves nothing `w` doesn't, whatever the bodies do.
The witness is checked erased (quantity 0): it is only evidence that `T` is inhabited,
never run, so it may ignore a linear argument. -/
def addPartialDecl (g : Globals R) (d : Decl R) : TCM (Globals R) := do
  -- constants are identified by name: a second declaration of one would change what
  -- everything checked against the first means
  if g.contains d.name then throw (.duplicateDecl d.name)
  let some w := d.witness
    | throw (.other s!"partial definition {d.name} needs a witness, a term of its type")
  if d.value.isSome then throw (.other s!"partial definition {d.name} can't have a value")
  checkHeader g d
  let ctx : Ctx R := { globals := g, erased := true }
  let _ ← check ctx w (ctx.eval d.type)
  pure (g.insert d)

/-- A partial definition's implementation, which may call `f` and the other definitions
of its group: checked against the type and kept for the compiler. Only a partial
definition (one with a checked witness) takes one. -/
def addPartialImpl (g : Globals R) (name : Name) (impl : Term R) : TCM (Globals R) := do
  let some d := g.find? name | throw (.other s!"unknown declaration '{name}'")
  unless d.witness.isSome && d.value.isNone do
    throw (.other s!"{name} is not a partial definition")
  let ctx : Ctx R := { globals := g }
  let _ ← check ctx impl (ctx.eval d.type)
  pure (g.insert { d with impl := some impl })

/-- The axioms the declaration `n` depends on, through the constants in its type, its
value and (for a partial definition) its witness: the declarations without a value or a
witness (`axiom`s, foreign functions), and the `builtin` registrations made outside the
toolchain's library (`Globals.assumed`), shown as `builtin key := name`. A numeral
depends on the declarations registered as `nat`, `nat.zero` and `nat.succ`. A partial
definition's implementation is not looked at: it is only run, never unfolded in a proof.

Also listed, marked `native`: the **native implementations** the declaration's compiled
code runs, wherever they are registered (the library's too). `native f := g` is
`attribute [implemented_by g] f`, and `native T := mk/get` a native representation of the
type `T` (`attribute [implemented_by mk get] T.mk`, a `repr:` registration). The kernel
never runs them, so they prove nothing: they are trusted to agree with the definitions.
An implementation that is a Wiz definition is walked like a dependency (compiled code runs
it): a chain `f → g → h` lists `native f := g` and `native g := h`, and `h`'s own axioms. A structurally recursive definition's compiled equations are not listed: the kernel
checks that they agree with its value (`checkImplAgrees`).

What compiled code runs is followed through every trusted step (t1-review L2): an
implementation that is a **partial definition** runs its body, so from there on the
bodies of partial definitions are walked too (only on that path: a partial definition
reached through types and values alone still lists nothing for its body). An
implementation that is a foreign function has nothing further to walk. A `native_refl`
proof's value names the implementations its run reached (its `X.native✝` axiom is listed
like any axiom), so they are walked as code that runs. -/
partial def Globals.axiomsOf (g : Globals R) (n : Name) : List String := Id.run do
  let mut seen : Std.HashSet Name := {}
  -- the declarations reached as code that runs (an implementation, or what one runs):
  -- their partial bodies are walked too
  let mut ran : Std.HashSet Name := {}
  let mut todo : List (Name × Bool) := [(n, false)]
  let mut out : Array String := #[]
  let mut reprs : List Name := []
  let numeral := ["nat", "nat.zero", "nat.succ"].filterMap (List.lookup · g.builtins)
  while true do
    match todo with
    | [] => break
    | (c, run) :: rest =>
      todo := rest
      let first := !seen.contains c
      unless first || (run && !ran.contains c) do continue
      seen := seen.insert c
      if run then ran := ran.insert c
      let some d := g.find? c | continue
      if first then
        if d.value.isNone && d.witness.isNone then out := out.push c
        for (k, m) in g.assumed.reverse do
          if m == c then out := out.push s!"builtin {k} := {c}"
        if let some i := d.nativeImpl? then out := out.push s!"native {c} := {i}"
        -- (a `repr:T:mk:get:…` registration is on `T`'s constructor: it concerns whatever
        -- mentions the type or the constructor)
        for (k, m) in g.builtins.reverse do
          if let "repr" :: T :: mkImpl :: getImpl :: _ := k.splitOn ":" then
            if (c == m || c == T) && !reprs.contains T then
              reprs := T :: reprs
              out := out.push s!"native {T} := {mkImpl}/{getImpl}"
      -- a partial definition that runs runs its body
      let body := if run && d.witness.isSome then d.impl.toList else []
      let (cs, lit) := ([d.type] ++ d.value.toList ++ d.witness.toList ++ body).foldl
        (fun (acc : List Name × Bool) t => (consts t acc.1, acc.2 || hasNatLit t)) ([], false)
      -- a registered operation or constructor makes numerals without a literal in the
      -- term (`Nat.zero` is `0`, `Nat.pow 0 0` is `1`), and numerals unfold through the
      -- registered `nat.zero` and `nat.succ`: it depends on them like a literal does
      let lit := lit || g.builtins.any fun (k, m) => m == c && k.startsWith "nat."
      -- (an implementation is walked too, as code that runs: the rest of an
      -- `implemented_by` chain, what it depends on, and a partial one's body; a foreign
      -- function, which has no value, is already named by `native f := g`)
      let impls := match d.nativeImpl? with
        | some i => if (g.find? i).any fun di => di.value.isSome || di.witness.isSome then [(i, true)] else []
        | none => []
      -- (a `native_refl` proof's value: the implementations its run reached, which run)
      let run := run || (d.value.isSome && (g.find? (c ++ ".native✝")).isSome)
      todo := (cs ++ (if lit then numeral else [])).map (·, run) ++ impls ++ todo
  return out.toList
where
  consts (t : Term R) (acc : List Name) : List Name :=
    match t with
    | .const c _ => c :: acc
    | t => (go t |>.run acc).2
  go (t : Term R) : StateM (List Name) Unit :=
    t.forChildren (fun _ => pure ()) fun _ c => match c with
      | .const n _ => modify (n :: ·)
      | c => go c
  hasNatLit (t : Term R) : Bool := match t with
    | .natLit _ => true
    | t => (litGo t |>.run false).2
  litGo (t : Term R) : StateM Bool Unit :=
    t.forChildren (fun _ => pure ()) fun _ c => match c with
      | .natLit _ => set true
      | c => litGo c

/-- Check a list of declarations in order. -/
def addDecls (g : Globals R) (ds : List (Decl R)) : TCM (Globals R) :=
  ds.foldlM addDecl g

end Wiz
