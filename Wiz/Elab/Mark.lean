import Wiz.Core.Check

/-!
# The marking pass (P2)

The kernel never evaluates a proof, and it makes that checkable: outside a proof, a term
whose sort may be `0` must be **marked** (`prf.{l} t`, `l` the sort of its type) or
neutral-shaped (`Check.lean`, "the proof marker"). The elaborator does not write the
markers while it elaborates: metavariables hide types, and terms read back from values or
built by hand (constructors, recursors, match compilation, instances, tactics) carry
none. This pass inserts them, in every declaration, just before the kernel.

It is a typed traversal that mirrors the kernel's `infer` and `check`, without the
checks: it only needs the type of each subterm, to see its sort.

* It is **total**: where it cannot compute a type (an ill-typed term), it leaves the
  term alone, and the kernel reports the real error.
* It is **untrusted**: a missing marker is the kernel's error "unmarked proof", and a
  wrong one is rejected by the kernel's rule for `prf`.
* Inside a proof (a term it marks at level `0`) nothing needs a marker but the proofs in
  a *relevant* subterm (an index, a type), which the kernel may evaluate: the pass goes
  through the proof to find those. A cheaper first attempt marks only the declaration's
  body (`Decl.withTopMarks`); the kernel says whether that was enough.
* It evaluates the terms it has already marked, and binds a proof inside a proof
  suspended, as the kernel does (`Ctx.evalAt`): so it never runs a proof either.
* **The sorts pass** (mandatory sorts). Every `Π`/`Σ` carries its components' sorts and
  every `ULift` its content's (`BinderSorts`); the elaborator writes the ones it knows and
  a `Level.hole` for the others. This traversal fills every hole it passes, from the
  levels of the components it computes, and it passes them all: it goes inside proofs and
  under every `fun` (it knows the types of their variables). It runs on every
  declaration, before the kernel, in a mode that places no markers (`Ctx.sortsOnly`,
  `Decl.withSorts`), and skips the subterms that have no hole. It is total in one step:
  writing some sorts and not others gave two non-convertible equations for one type
  (`wiz-notes/prf-marker.md` §8.1). A hole it could not fill (an ill-typed term) is the
  kernel's error "without its sort"; a wrong sort is the kernel's error too.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

namespace Mark

/-- Does `t`, at the type `ty`, get a marker (and at which level), and is there anything
to mark inside it? Nothing inside a proof (level `0`). -/
def decide (ctx : Ctx R) (t : Term R) (ty : VTy R) : Option Level × Bool :=
  if ctx.sortsOnly then (none, true) else
  if (if ctx.globals.strictProofs then (t matches .prf ..) else t.neutralShaped) then (none, true) else
  match ctx.sortOf? ty with
  | none => (none, true)
  | some s => if s.isNeverZero then (none, true) else (some s, !s.isZero)

private def sortLevel? (ty : Option (VTy R)) : Option Level :=
  match ty.map whnf with
  | some (.sort l) => some l
  | _ => none

/-- The context below a marker `prf.{l}` already in the term, as the kernel's
`Ctx.underMarker`: a proof at level `0`, marked (its `fun`s exempt) otherwise. -/
def underMarker (ctx : Ctx R) (l : Level) : Ctx R :=
  if l.isZero then { ctx with proof := true, marked := false } else { ctx with marked := true }

mutual

/-- Mark `t`, which is checked against `ty`. (`ctx.marked`: `t` is the body of a marked
`fun`, which needs no marker of its own; `ctx.proof`: `t` is inside a proof, where a proof
needs no marker but a relevant subterm is marked as anywhere else; `Check.lean`.) -/
partial def check (ctx : Ctx R) (t : Term R) (ty : VTy R) : Term R :=
  -- (the sorts pass: nothing to fill below)
  if ctx.sortsOnly && !t.hasHole then t else
  match t with
  -- a marker already in the term (from read-back, which writes a proof back as
  -- `prf.{0} …`, or from the user): kept, and gone into as the kernel does (`underMarker`):
  -- since I-1 the kernel checks the relevant subterms of a proof too (review F1)
  | .prf l t' => .prf l (check (underMarker ctx l) t' ty)
  | _ =>
    -- the mode of a subterm is decided by its type
    let ctx := ctx.modeAt ty
    if ctx.proof then checkCore ctx t ty else
    let (w, _) := if ctx.marked then (none, true) else decide ctx t ty
    -- below a marker, and below the `fun`s it wraps, the bodies are exempt; below a marker
    -- at level `0` the term is a proof
    let ctx' := { ctx with marked := (ctx.marked || w.isSome) && (t matches .lam ..),
                           proof := w.any (·.isZero) }
    let t := checkCore ctx' t ty
    match w with
    | some l => .prf l t
    | none => t

partial def checkCore (ctx : Ctx R) (t : Term R) (ty : VTy R) : Term R :=
  let g := ctx.globals
  match t, whnf ty with
  | .lam x body, .pi _ _ _ dom cod _ =>
    -- (`ctx.marked` goes on to the body)
    .lam x (check (ctx.bind x [] dom) body (Closure.inst g cod (Val.var ctx.lvl)))
  | t, ty => checkRest { ctx with marked := false } t ty

partial def checkRest (ctx : Ctx R) (t : Term R) (ty : VTy R) : Term R :=
  let g := ctx.globals
  match t, ty with
  | .up a, .ulift _ _ A => .up (check ctx a A)
  | .letE x q T v b, _ =>
    let (T, _) := type ctx T
    let vT := ctx.eval T
    let v := check ctx v vT
    .letE x q T v (check (ctx.define x [] vT (ctx.evalAt v vT)) b ty)
  | .pair a b, .sigma _ _ A B _ =>
    let a := check ctx a A
    .pair a (check ctx b (ctx.instArgAt A B a))
  | .tt, _ => t
  | _, .sizeLt _ => t
  | .dret i, .desc _ I => .dret (check ctx i I)
  | .darg q S D, .desc l I =>
    let (S, _) := type ctx S
    .darg q S (check ctx D (.pi "s" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval S) (.mk [I] (.desc l (.var 1))) ⟨.succ l, .succ (.succ l)⟩))
  | .drec q j D, .desc l I => .drec q (check ctx j I) (check ctx D (.desc l I))
  | .dhrec q H j D, .desc l I =>
    let (H, _) := type ctx H
    .dhrec q H (check ctx j (.pi "h" .default (.qlit QuantitySyntax.explicitDefault) (ctx.eval H) (.mk [I] (.var 1)) ⟨.succ l, .succ l⟩))
      (check ctx D (.desc l I))
  | .con x, .mu l I D i s _ => match sizePred? s with
    | some s' => .con (check ctx x (vInterp g l I D (muFamilyAt l I D s') i))
    | none => t
  | .cocon x, .nu l I D i s _ => match sizePred? s with
    | some s' => .cocon (check ctx x (vInterp g l I D (nuFamilyAt l I D s') i))
    | none => t
  | _, _ => (inferCore ctx t).1

/-- Mark `t`, and compute its type (`none`: it could not be computed). -/
partial def infer (ctx : Ctx R) (t : Term R) : Term R × Option (VTy R) :=
  match t with
  | .prf l t' =>
    -- (as in `check`; the marker is not added again)
    let (t', ty) := inferCore (underMarker ctx l) t'
    (.prf l t', ty)
  | _ =>
    let (t', ty?) := inferCore ctx t
    -- (inside a proof nothing is wrapped; the relevant subterms were marked on the way)
    if ctx.proof then (t', ty?) else
    match ty? with
    | some ty => match (decide ctx t ty).1 with
      | some l => (.prf l t', ty?)
      | none => (t', ty?)
    | none => (t', none)

/-- Mark a type, and compute its level. -/
partial def type (ctx : Ctx R) (t : Term R) : Term R × Option Level :=
  -- (a type is a relevant term, also inside a proof)
  let (t, ty) := infer { ctx with proof := false } t
  (t, sortLevel? ty)

partial def inferCore (ctx : Ctx R) (t : Term R) : Term R × Option (VTy R) :=
  let g := ctx.globals
  let w : R := QuantitySyntax.explicitDefault
  match t with
  | .var ix => (t, ctx.types[ix]?)
  | .const n us => (t, (g.find? n).bind fun d =>
      if d.levelParams.length == us.length then some (eval g [] (d.type.instLevels d.levelParams us)) else none)
  | .natLit _ => (t, (g.builtins.lookup "nat").map fun N => ctx.eval (.const N []))
  | .sort l => (t, some (.sort (.succ l)))
  -- (the sorts pass: a hole gets the component's level)
  | .pi x bi q A B σ =>
    let (A, lA) := type ctx A
    let (B, lB) := type (ctx.bind x [] (ctx.eval A)) B
    let σ := σ.fill lA lB
    (.pi x bi q A B σ, if σ.hasHole then none else some (.sort σ.piSort))
  | .sigma x q A B σ =>
    let (A, lA) := type ctx A
    let (B, lB) := type (ctx.bind x [] (ctx.eval A)) B
    let σ := σ.fill lA lB
    (.sigma x q A B σ, if σ.hasHole then none else some (.sort σ.sigmaSort))
  | .app f a =>
    let (f, fty) := infer ctx f
    match fty.map whnf with
    | some (.pi _ _ _ dom cod _) =>
      -- (inside a proof, the argument of an application that is not a proof is marked as
      -- in relevant mode: `Check.lean`)
      let actx := if ctx.proof && !(fty.any ctx.isProofTy) then { ctx with proof := false } else ctx
      let a := check actx a dom
      (.app f a, some (ctx.instArgAt dom cod a))
    | _ => (.app f a, none)
  | .letE x q T v b =>
    let (T, _) := type ctx T
    let vT := ctx.eval T
    if ctx.proof && ctx.isProofTy vT then
      -- (inside a proof, a `let`-bound proof: the body first, as in `Check.lean`)
      let (b, bty) := infer (ctx.define x [] vT (suspend g ctx.env v)) b
      let v := check (if bty.any ctx.isProofTy then ctx else { ctx with proof := false }) v vT
      (.letE x q T v b, bty)
    else
    let v := check ctx v vT
    let (b, bty) := infer (ctx.define x [] vT (ctx.eval v)) b
    (.letE x q T v b, bty)
  -- (linear-case stage 2) `let () := u; b`: the unit, then the body
  | .letUnit u b =>
    let (u, _) := infer ctx u
    let (b, bty) := infer ctx b
    (.letUnit u b, bty)
  | .ann tm T =>
    let (T, _) := type ctx T
    let vT := ctx.eval T
    (.ann (check ctx tm vT) T, some vT)
  | .fst p =>
    let (p, ty) := infer ctx p
    match ty.map whnf with
    | some (.sigma _ _ A _ _) => (.fst p, some A)
    | _ => (.fst p, none)
  | .snd p =>
    let (p, ty) := infer ctx p
    match ty.map whnf with
    | some (.sigma _ _ _ B _) => (.snd p, some (Closure.inst g B (vFst (ctx.evalAt p (ty.getD (.unit 1))))))
    | _ => (.snd p, none)
  | .split q s z m x y b =>
    let (s, sty?) := infer ctx s
    match sty?, sty?.map whnf with
    | some sty, some (.sigma _ _ A B _) =>
      let (m, j) := type (ctx.bind z [] sty) m
      -- (inside a proof, the scrutinee of a `split` that is not a proof needs its marker)
      let s := if ctx.proof && !(j.any (·.isZero)) then
          match (decide { ctx with proof := false } s sty).1 with
          | some l => .prf l s
          | none => s
        else s
      let mc : Closure R := .mk ctx.env m
      let vx : Val R := Val.var ctx.lvl
      let vy : Val R := Val.var (ctx.lvl + 1)
      let ctx₂ := (ctx.bind x [] A).bind y [] (Closure.inst g B vx)
      let b := check ctx₂ b (Closure.inst g mc (.pair vx vy))
      (.split q s z m x y b, some (Closure.inst g mc (ctx.evalAt s sty)))
    | _, _ => (.split q s z m x y b, none)
  | .unit l | .empty l => (t, some (.sort l))
  | .absurd m e =>
    let (m, j) := type ctx m
    let (e, _) := infer { ctx with proof := ctx.proof && j.any (·.isZero) } e
    (.absurd m e, some (ctx.eval m))
  | .eq A a b =>
    let (A, _) := type ctx A
    let vA := ctx.eval A
    (.eq A (check ctx a vA) (check ctx b vA), some (.sort 0))
  | .eqTy A B => (.eqTy (type ctx A).1 (type ctx B).1, some (.sort 0))
  | .refl A a =>
    let (A, _) := type ctx A
    let vA := ctx.eval A
    let a := check ctx a vA
    let va := ctx.eval a
    (.refl A a, some (vEq g vA va va))
  | .reflTy X =>
    let (X, _) := type ctx X
    let vX := ctx.eval X
    (.reflTy X, some (vEqType g vX vX))
  | .cast A B e x =>
    -- (the equation is never evaluated, but it is a proof, which may hold relevant
    -- subterms the kernel evaluates (`Check.lean`, I-1): marked in proof mode, as checked)
    let (A, _) := type ctx A
    let (B, _) := type ctx B
    let vA := ctx.eval A
    let vB := ctx.eval B
    let e := check { ctx with proof := true } e (vEqType g vA vB)
    (.cast A B e (check ctx x vA), some vB)
  | .transp A a P p b e =>
    -- (`p` and `e` are never evaluated, but they are proofs, which may hold relevant
    -- subterms: marked in proof mode, as the kernel checks them)
    let (A, lA) := type ctx A
    let vA := ctx.eval A
    let a := check ctx a vA
    let va := ctx.evalAt a vA
    let motiveTy : Val R := .pi "b" .default (.qlit 0) vA
      (.mk [va, vA] (.pi "_" .default (.qlit 0) (.eq (.var 2) (.var 1) (.var 0)) (.sort 0) ⟨0, 1⟩)) ⟨lA.getD .hole, .imax 0 1⟩
    let P := check ctx P motiveTy
    let vP := ctx.eval P
    let p := check { ctx with proof := true } p (vApp g (vApp g vP va) (.neutral (.refl vA va) #[]))
    let b := check ctx b vA
    let vb := ctx.evalAt b vA
    let e := check { ctx with proof := true } e (vEq g vA va vb)
    (.transp A a P p b e, some (vApp g (vApp g vP vb) (suspend g ctx.env e)))
  | .qty | .size | .enum _ => (t, some (.sort 1))
  | .sizeLt _ => (t, some (.sort 1))
  | .qlit _ => (t, some .qty)
  | .szInf | .szSuc _ => (t, some .size)
  | .tag ls _ => (t, some (.enum ls))
  | .ecase z m s bs =>
    let (s, sty?) := infer ctx s
    match sty?, sty?.map whnf with
    | some sty, some (.enum ls) =>
      let (m, _) := type (ctx.bind z [] sty) m
      let mc : Closure R := .mk ctx.env m
      let bs := bs.zipIdx.map fun (b, k) => check ctx b (Closure.inst g mc (.tag ls k))
      (.ecase z m s bs, some (Closure.inst g mc (ctx.eval s)))
    | _, _ => (.ecase z m s bs, none)
  | .desc l I => (.desc l (type ctx I).1, some (.sort (.succ (.succ l))))
  | .delim v P a b c h D =>
    let (D, dty) := infer ctx D
    match dty.map whnf with
    | some (.desc l I) =>
      let P := check ctx P (delimMotiveTy l v I w)
      let vP := ctx.eval P
      let (ta, tb, tc, th) := delimMethodTys g l v I vP w
      (.delim v P (check ctx a ta) (check ctx b tb) (check ctx c tc) (check ctx h th) D, some (vApp g vP (ctx.eval D)))
    | _ => (.delim v P a b c h D, none)
  | .mu l I D i s h =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    (.mu l I (check ctx D (.desc l vI)) (check ctx i vI) s h, some (.sort (.succ l)))
  | .nu l I D i s h =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    (.nu l I (check ctx D (.desc l vI)) (check ctx i vI) s h, some (.sort (.succ l)))
  | .ind l I D v P m i x =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let P := check ctx P (indMotiveTy g l v vI vD w)
    let vP := ctx.eval P
    let m := check ctx m (indMethodTy g l v vI vD vP w)
    let i := check ctx i vI
    let vi := ctx.eval i
    let x := check ctx x (.mu l vI vD vi .szInf none)
    (.ind l I D v P m i x, some (vApp g (vApp g vP vi) (ctx.eval x)))
  | .out x =>
    let (x, ty) := infer ctx x
    match ty.map whnf with
    | some (.nu l I D i s _) => match sizePred? s with
      | some s' => (.out x, some (vInterp g l I D (nuFamilyAt l I D s') i))
      | none => (.out x, none)
    | _ => (.out x, none)
  | .sfix l I D v P f s i x =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let P := check ctx P (indMotiveTy g l v vI vD w)
    let vP := ctx.eval P
    let f := check ctx f (sfixFunTy g l v vI vD vP w)
    let i := check ctx i vI
    let vi := ctx.eval i
    let x := check ctx x (.mu l vI vD vi (ctx.eval s) none)
    (.sfix l I D v P f s i x, some (vApp g (vApp g vP vi) (ctx.eval x)))
  | .scase l q I D v P m s i x =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let P := check ctx P (indMotiveTy g l v vI vD w)
    let vP := ctx.eval P
    let vs := ctx.eval s
    -- (K1) the method's payload is at the case's quantity (quantities are not marked)
    let m := check ctx m (scaseMethodTy g l v vI vD vP vs (ctx.eval q))
    let i := check ctx i vI
    let vi := ctx.eval i
    let x := check ctx x (.mu l vI vD vi vs none)
    (.scase l q I D v P m s i x, some (vApp g (vApp g vP vi) (ctx.eval x)))
  | .scofix l I D A f s i a =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let A := check ctx A (coitStateTy l vI w)
    let vA := ctx.eval A
    let f := check ctx f (scofixFunTy g l vI vD vA w)
    let i := check ctx i vI
    let vi := ctx.eval i
    let a := check ctx a (vApp g vA vi)
    (.scofix l I D A f s i a, some (.nu l vI vD vi (ctx.eval s) none))
  | .coit l I D S st i s =>
    let (I, _) := type ctx I
    let vI := ctx.eval I
    let D := check ctx D (.desc l vI)
    let vD := ctx.eval D
    let S := check ctx S (coitStateTy l vI w)
    let vS := ctx.eval S
    let st := check ctx st (coitStepTy g l vI vD vS w)
    let i := check ctx i vI
    let vi := ctx.eval i
    let s := check ctx s (vApp g vS vi)
    (.coit l I D S st i s, some (.nu l vI vD vi .szInf none))
  | .ulift k l A =>
    let (A, k') := type ctx A
    (.ulift (if k.hasHole then k'.getD k else k) l A, some (.sort l))
  | .down x =>
    let (x, ty) := infer ctx x
    match ty.map whnf with
    | some (.ulift _ _ A) => (.down x, some A)
    | _ => (.down x, none)
  -- checked only (no type to compute), metavariables, and the evaluator's own `natOp`
  | .lam .. | .pair .. | .tt | .up _ | .dret _ | .darg .. | .drec .. | .dhrec .. | .con _ | .cocon _
  | .mvar _ | .natOp .. | .prf .. => (t, none)

end

end Mark

/-- (Mandatory sorts) A declaration with every hole in its `Π`/`Σ`/`ULift` sorts filled
(the sorts pass, `Ctx.sortsOnly`): in the type, the value, the implementation and the
witness. A declaration without holes is returned as it is.

The declared type is **evaluated only when the term's shape needs an expected type** (a
`fun`, a pair, …), or when inference could not type the term: evaluating an equation
computes its sides — the whole of a `refl` proof's computation — and the pass runs on
every declaration (`kernel-eval`). Where the type is not needed the traversal infers the
subterm's type instead (`Mark.infer`). -/
def Decl.withSorts (g : Globals R) (d : Decl R) : Decl R :=
  let has := d.type.hasHole || (d.value.any (·.hasHole)) || (d.impl.any (·.hasHole)) ||
    (d.witness.any (·.hasHole))
  if !has then d else
  let type := (Mark.type { globals := g, sortsOnly := true } d.type).1
  -- (a recursive definition mentions itself, and it is not in the globals yet — its own
  -- check is what adds it. Give the pass the declaration (with its filled type and no
  -- value: a neutral), so that a self-reference has a type and the traversal descends
  -- into its arguments; before, it was an unknown constant and the whole application
  -- was left as it was, holes in it and all.)
  let ctx : Ctx R := { globals := g.insert { d with type, value := none, impl := none, witness := none },
                       sortsOnly := true }
  let ty : Thunk (VTy R) := Thunk.mk fun _ => ctx.eval type
  let fill (t : Term R) : Term R :=
    if !t.hasHole then t else
    -- (the shapes only an expected type can type need it, so it is evaluated; elsewhere
    -- inference fills without it, and the expected type — evaluated — only where
    -- inference does not manage: it returns no type, or leaves a hole. A hole must not
    -- reach the kernel, and the pass is untrusted, so a second strategy costs nothing.)
    let needsType : Bool := match t with
      | .lam .. | .pair .. | .tt | .up .. | .dret .. | .darg .. | .drec .. | .dhrec ..
      | .con .. | .cocon .. => true
      | _ => false
    if needsType then Mark.check ctx t ty.get else
    let byInfer : Term R := match Mark.infer ctx t with
      | (t', some _) => t'
      | (_, none) => t
    if !byInfer.hasHole then byInfer else Mark.check ctx t ty.get
  { d with type := type, value := d.value.map fill, impl := d.impl.map fill, witness := d.witness.map fill }

/-- A declaration with its proof markers (and the `Π`/`Σ` sorts it fills on the way):
what the kernel requires (`Check.lean`, "the proof marker"). -/
def Decl.withMarks (g : Globals R) (d : Decl R) : Decl R :=
  let ctx : Ctx R := { globals := g }
  let type := (Mark.type ctx d.type).1
  let ty := ctx.eval type
  { d with type, value := d.value.map (Mark.check ctx · ty),
           impl := d.impl.map (Mark.check ctx · ty),
           witness := d.witness.map (Mark.check ctx · ty) }

/-- A declaration with a marker on its body only, when the body is a proof (its type's
sort may be `0`) and not neutral-shaped: enough for most theorems, whose proofs hold no
relevant subterm with a proof of its own in it. The kernel answers "unmarked proof" when
it is not enough (`withMarksOnDemand`). -/
def Decl.withTopMarks (g : Globals R) (d : Decl R) : Decl R :=
  let ctx : Ctx R := { globals := g }
  let ty := ctx.eval d.type
  let top (v : Term R) : Term R := match v with
    | .prf .. => v
    | _ => match (Mark.decide ctx v ty).1 with
      | some l => .prf l v
      | none => v
  { d with value := d.value.map top, impl := d.impl.map top, witness := d.witness.map top }

end Wiz
