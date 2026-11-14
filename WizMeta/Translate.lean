import Wiz.Core.Term
import Wiz.Rig.Instances
import WizMeta.Syntax

/-!
# From kernel terms to spec terms

`ofTerm` maps a `Wiz.Term ZeroOneMany` to a spec term, and **fails outside the fragment**
(`none`): a binder's quantity that is not a literal, a sized `μ`, `ν` and its operations, sizes,
`split`, numerals, native operations, metavariables, and anything added to `Wiz.Term`
later (the last arm). It is the only file of `WizMeta` that imports the kernel, and it is
not trusted: a wrong translation makes the reference checker vote on another term, which
the differential test would show as a disagreement.

Dropped on the way: names, binder info, the labels of an enumeration (its size is kept)
and the display hint of `μ`.
-/

namespace WizMeta
open Wiz (Term Level ZeroOneMany)

/-- A level; `ps` are the enclosing declaration's level parameters. -/
def ofLevel (ps : List String) : Level → Option Lvl
  | .zero => some .zero
  | .succ l => (ofLevel ps l).map .succ
  | .max a b => do pure (.max (← ofLevel ps a) (← ofLevel ps b))
  | .imax a b => do pure (.imax (← ofLevel ps a) (← ofLevel ps b))
  | .param n => (ps.idxOf? n).map .param
  | .mvar _ | .hole => none

/-- (mandatory sorts) A kernel `Π`/`Σ`'s component sorts as the spec's one sort: `imax`
(resp. `max`) of the two, as the spec's rules relate them (`s ≡ imax i j`). A hole (only
before the elaborator's sorts pass) is no sort. -/
def ofSorts (ps : List String) (σ : Wiz.BinderSorts) (pi : Bool) : Option (Option Lvl) :=
  if σ.hasHole then some none else do
    let s := if pi then σ.piSort else σ.sigmaSort
    pure (some (← ofLevel ps s))

def ofQty : Term ZeroOneMany → Option Q
  | .qlit .zero => some .zero
  | .qlit .one => some .one
  | .qlit .many => some .many
  | _ => none

mutual
def ofTerm (ps : List String) : Term ZeroOneMany → Option Tm
  | .var i => some (.var i)
  | .const c us => do pure (.const c (← us.mapM (ofLevel ps)))
  | .sort l => do pure (.sort (← ofLevel ps l))
  | .pi _ _ q A B σ => do
    let s ← ofSorts ps σ true
    pure (.pi (← ofQty q) s (← ofTerm ps A) (← ofTerm ps B))
  | .lam _ b => do pure (.lam (← ofTerm ps b))
  | .app f a => do pure (.app (← ofTerm ps f) (← ofTerm ps a))
  | .letE _ q A v b => do pure (.letE (← ofQty q) (← ofTerm ps A) (← ofTerm ps v) (← ofTerm ps b))
  | .ann t A => do pure (.ann (← ofTerm ps t) (← ofTerm ps A))
  | .sigma _ q A B σ => do
    let s ← ofSorts ps σ false
    pure (.sigma (← ofQty q) s (← ofTerm ps A) (← ofTerm ps B))
  | .pair a b => do pure (.pair (← ofTerm ps a) (← ofTerm ps b))
  | .fst p => do pure (.fst (← ofTerm ps p))
  | .snd p => do pure (.snd (← ofTerm ps p))
  | .unit l => do pure (.unit (← ofLevel ps l))
  | .tt => some .tt
  | .empty l => do pure (.empty (← ofLevel ps l))
  | .absurd m t => do pure (.absurd (← ofTerm ps m) (← ofTerm ps t))
  | .enum ls => some (.enum ls.length)
  | .tag ls i => some (.tag ls.length i)
  | .ecase _ m s bs => do pure (.ecase (← ofTerm ps m) (← ofTerm ps s) (← ofBranches ps bs))
  | .eq A a b => do pure (.eq (← ofTerm ps A) (← ofTerm ps a) (← ofTerm ps b))
  | .eqTy A B => do pure (.eqTy (← ofTerm ps A) (← ofTerm ps B))
  | .refl A a => do pure (.refl (← ofTerm ps A) (← ofTerm ps a))
  | .reflTy A => do pure (.reflTy (← ofTerm ps A))
  | .cast A B e t => do pure (.cast (← ofTerm ps A) (← ofTerm ps B) (← ofTerm ps e) (← ofTerm ps t))
  | .transp A a P p b e => do
    pure (.transp (← ofTerm ps A) (← ofTerm ps a) (← ofTerm ps P) (← ofTerm ps p) (← ofTerm ps b) (← ofTerm ps e))
  -- (the content's sort `k` is dropped: the spec's rule infers it)
  | .ulift _ l A => do pure (.ulift (← ofLevel ps l) (← ofTerm ps A))
  | .up a => do pure (.up (← ofTerm ps a))
  | .down t => do pure (.down (← ofTerm ps t))
  | .qty => some .qty
  | .qlit .zero => some (.qlit .zero)
  | .qlit .one => some (.qlit .one)
  | .qlit .many => some (.qlit .many)
  | .desc l I => do pure (.desc (← ofLevel ps l) (← ofTerm ps I))
  | .dret i => do pure (.dret (← ofTerm ps i))
  | .darg q S D => do pure (.darg (← ofTerm ps q) (← ofTerm ps S) (← ofTerm ps D))
  | .drec q j D => do pure (.drec (← ofTerm ps q) (← ofTerm ps j) (← ofTerm ps D))
  | .dhrec q H j D => do pure (.dhrec (← ofTerm ps q) (← ofTerm ps H) (← ofTerm ps j) (← ofTerm ps D))
  | .delim v P a b c h D => do
    pure (.delim (← ofLevel ps v) (← ofTerm ps P) (← ofTerm ps a) (← ofTerm ps b) (← ofTerm ps c)
      (← ofTerm ps h) (← ofTerm ps D))
  -- only `μ^∞`: no sizes
  | .mu l I D i .szInf _ => do pure (.mu (← ofLevel ps l) (← ofTerm ps I) (← ofTerm ps D) (← ofTerm ps i))
  | .con x => do pure (.con (← ofTerm ps x))
  | .ind l I D v P m i x => do
    pure (.ind (← ofLevel ps l) (← ofTerm ps I) (← ofTerm ps D) (← ofLevel ps v) (← ofTerm ps P)
      (← ofTerm ps m) (← ofTerm ps i) (← ofTerm ps x))
  -- outside the fragment
  | _ => none

def ofBranches (ps : List String) : List (Term ZeroOneMany) → Option Tm
  | [] => some .bnil
  | b :: bs => do pure (.bcons (← ofTerm ps b) (← ofBranches ps bs))
end

/-- A declaration. Only what the kernel checks is read: the name, the level parameters,
the type and the value (a partial definition's witness and a compiler implementation are
outside the fragment, so such a declaration is refused). -/
def ofDecl (d : Wiz.Decl ZeroOneMany) : Option Decl := do
  if d.witness.isSome || d.impl.isSome then none
  let ty ← ofTerm d.levelParams d.type
  let v ← match d.value with
    | some v => (ofTerm d.levelParams v).map some
    | none => pure none
  pure { name := d.name, nparams := d.levelParams.length, type := ty, value := v }

end WizMeta
