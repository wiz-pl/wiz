import Wiz.Elab.Term

/-!
# `inductive` and `structure`

```
inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A .zero
  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)
```

elaborates to ordinary declarations, all checked by the kernel:

* `Vec.desc : (A : Type) → Desc ((n : Nat) × Unit)`: the description, with a tag
  per constructor;
* `Vec : (A : Type) → Nat → Type := fun A n => μ (Vec.desc A) (n, ())`: the nominal
  wrapper, with a display hint so that it prints as `Vec A n`;
* `Vec.nil`, `Vec.cons`: constructors, `con ('cons, n, x, xs, refl …, ())`.

Indices are packed into a Σ ending in `Unit`. Constructor fields are elaborated with
the type itself bound as a *local variable* `T : (indices) → Type l`. A field whose
type is `T j` becomes `Desc.rec`, any other field becomes `Desc.arg`, and the return
type `T j` becomes `Desc.ret j`. Since `T` may occur nowhere else, positivity holds
by construction. Later fields may not depend on recursive ones: `Desc.rec` fields are
non-dependent.

`structure S where x : A; y : B` is `(x : A) × (y : B) × Unit`, with constructor
`S.mk`. Field access `p.x` comes from the Σ binder names.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- Elaborate binders into a context, returning the context and the binders as
`(name, binder info, quantity, type)`. -/
def elabTelescope (ctx : LocalCtx R) (bs : List BinderView) :
    ElabM R (LocalCtx R × Array (Name × BinderInfo × Term R × Term R)) := do
  let mut ctx := ctx
  let mut tele := #[]
  for b in bs do
    let ty ← match b.type with
      | some s => pure (← checkType ctx s).1
      | none => freshMeta ctx s!"the type of {b.name}"
    let q ← elabQuantity ctx b.bi b.qty
    tele := tele.push (b.name, b.bi, q, ty)
    let vty ← evalIn ctx ty
    recordBinder ctx b.info b.name vty
    ctx := ctx.bindQ b.name vty (match q with
      | .qlit r => some r
      | _ => none)
  pure (ctx, tele)

/-- `(a₁, (a₂, …, ()))` -/
def tupleTm (as : List (Term R)) : Term R := as.foldr .pair .tt

def lamsTm (xs : List Name) (b : Term R) : Term R := xs.foldr .lam b

/-- `(a₁, (a₂, …, tail))`: an index or structure tuple ending in `tail` (`()`, or the
phantom tail's `fun _ => ()`). -/
def tupleWith (tail : Term R) (as : List (Term R)) : Term R := as.foldr .pair tail

/-- **Phantom parameters.** Types are structural, so a parameter that nothing in the type
mentions would be forgotten: `UIntN 8` and `UIntN 16` would be one type, and `w` could
not be inferred. For each such parameter `p : P` the type's final `Unit` (of an index
type, or of a structure's Σ) becomes `(0 phantom✝ : D) → Unit`, where

* `D := p` if `p` is a type (`P` is a `Sort`), and
* `D := (0 x : P) × (x = p)` otherwise: a type (not a proposition, which would compare by
  equivalence and so forget `p` again) with one inhabitant, mentioning `p`.

The function type has one inhabitant up to η, `fun _ => ()`, so the tail is still a
singleton: constructors fill it in, nothing reads it, and erasure drops it (`erasable`),
so the runtime representation doesn't change. But conversion compares `D`, so `p` now
counts, and unification can solve it. Proof parameters (`p : P` with `P` a proposition)
and sizes or quantities get no phantom; neither does a parameter whose `D` lives above
the type's universe `lvl` (the tail would raise it).

Given `used k` (whether the parameter `var k` of the context `Δ` is mentioned), returns
the tail type and its value in `Δ`, and the names of the phantom parameters. -/
def phantomTail (ctxΔ : LocalCtx R) (Δ : Array (Name × BinderInfo × Term R × Term R))
    (used : Nat → Bool) (lvl : Level) (markTail : Bool := false) (sealAx : Option Name := none) :
    ElabM R (Term R × Term R × List Name) := do
  let g ← getGlobals
  let nΔ := Δ.size
  let tys := ctxΔ.types.reverse.toArray
  -- a sealed type's seal comes first (22k): a closed domain, the axiom itself
  let mut doms : Array (Term R) := match sealAx with
    | some k => #[.const k []]
    | none => #[]
  let mut names : List Name := []
  for (x, _, _, A) in Δ, j in [0:nΔ] do
    let k := nΔ - 1 - j
    if used k then continue
    let P := A.lift (nΔ - j)
    let p : Term R := .var k
    let vP ← force (← evalIn ctxΔ P)
    let D? : Option (Term R) := match vP with
      | .sort _ => some p
      | .qty | .size | .sizeLt _ => none
      | _ => if isProp g tys vP then none
        else some (.sigma "x" (.qlit 0) P (.eq (P.lift 1) (.var 0) (p.lift 1)) none)
    let some D := D? | continue
    let some u := typeSort? g tys (← evalIn ctxΔ D) | continue
    unless u.le lvl do continue
    doms := doms.push D
    names := names ++ [x]
  -- a structure with fields ends in the marker `(0 fields✝ : Enum [fields✝]) → Unit` (22i)
  let nPh := doms.size
  let mark := markTail
  if mark then doms := doms.push (structTailDom : Term R)
  let bname (i : Nat) : Name := if mark && i == nPh then structTailName else phantomName
  let ty := (doms.toList.zipIdx).foldr (fun (D, i) acc => .pi (bname i) .default (.qlit 0) (D.lift i) acc none)
    (Term.unit lvl : Term R)
  let val := (doms.toList.zipIdx).foldr (fun (_, i) acc => .lam (bname i) acc) (Term.tt : Term R)
  pure (ty, val, names)

/-! ### Lifted fields (Q4)

A description field must live exactly in `Sort (l+1)`, where `Desc.elim`'s `marg` takes
it from (universes aren't cumulative). A field in a smaller universe is wrapped in
`ULift.{l+1}`: a proof field of a datatype in `Type`, or a field `A : Type u` of a type in
`Type (max u v)`; so is the domain `H` of an infinitary field, and the tag of a type
above `Type`. The wrapping is invisible: constructors take the field itself (and put
`up x` in the payload), recursors and patterns hand out `down x`, and the printer hides
`up`/`down`. At run time `ULift` is erased. -/

/-- How a field sits in the payload. -/
inductive FieldLift where
  /-- as itself -/
  | none
  /-- an `arg` field, lifted: `up x` -/
  | arg
  /-- an infinitary field with a lifted domain: `fun h => f (down h)` -/
  | hrec
  deriving BEq, Inhabited, Repr

/-- Replace `var 0` by `down (var 0)`: the body of an `arg` whose field is now lifted. -/
def downVar0 (t : Term R) : Term R := (t.lift 1 1).instantiateAt 0 (.down (.var 0))

/-- The fields of one constructor's description, and how each sits in the payload. -/
partial def descFieldLifts : Term R → List FieldLift
  | .darg _ S (.lam _ D) => (if S matches .ulift .. then .arg else .none) :: descFieldLifts D
  | .drec _ _ D => .none :: descFieldLifts D
  | .dhrec _ H _ D => (if H matches .ulift .. then .hrec else .none) :: descFieldLifts D
  | _ => []

/-- A field's value as a payload component. -/
def FieldLift.wrap : FieldLift → Term R → Term R
  | .none, t => t
  | .arg, t => .up t
  | .hrec, t => .lam "h" (.app (t.lift 1) (.down (.var 0)))

/-- A payload component as the field's value. -/
def FieldLift.unwrap : FieldLift → Term R → Term R
  | .none, t => t
  | .arg, t => .down t
  | .hrec, t => .lam "h" (.app (t.lift 1) (.up (.var 0)))

/-- The levels of constructor fields, for `ctorDesc`: for the field of type `A` (in the
context of `ctx` and the fields before it), `A`'s level and, if `A` is a function type,
its domain's. -/
def fieldLevels (ctx : LocalCtx R) (base : Nat) (fs : List (Term R)) : ElabM R (List (Option Level × Option Level)) := do
  let g ← getGlobals
  let allTys := ctx.types.reverse.toArray
  fs.zipIdx.mapM fun (A, k) => do
    let n := base + k
    let tys := allTys.extract 0 n
    let env : Env R := (List.range n).reverse.map Val.var
    let lA := typeSort? g tys (eval g env A)
    let lH := match A with
      | .pi _ _ _ H _ _ => typeSort? g tys (eval g env H)
      | _ => none
    pure (lA, lH)

/-- `T`'s arguments at a position where `T` is `var k`: the first `nΔ` must be the
parameters themselves (`var (k + nΔ - j)` for the `j`-th); returns the rest. -/
def paramArgs? (nΔ k : Nat) (args : List (Term R)) : Option (List (Term R)) :=
  if (args.take nΔ) == (List.range nΔ).map (fun j => .var (k + nΔ - j)) then some (args.drop nΔ)
  else none

/-- **Exercise 4.21.** The description of one constructor.

`fields[k] = (name, quantity, type)`, where the type lives in the context
`[f_{k-1}, …, f₀, T, Δ…]` (innermost first, so `T` is `var k`). `target` is the list
of index arguments of the return type, in the context `[f_{n-1}, …, f₀, T, Δ…]`.
Inside its declaration, `T` is applied to the `nΔ` parameters first (`Vec A n`), and
those must be exactly the parameter variables: use `paramArgs? k args` to strip them.
Build the description from the end:

* start with `Desc.ret (tupleTm target)`, in the context with all fields;
* for field `k` (from last to first) with type `F`:
  - if `F` is `T` applied to arguments (`Term.spine` with head `.var k`), strip the
    parameters and produce `Desc.rec q (tupleTm indices) D`. `D` was built *under*
    `f_k`, so remove it with `strengthen? 0`. If that fails, a later field depends on a
    recursive one: error;
  - if `F` is `(h : H) → T …` (an *infinitary* recursive field), check that `H` doesn't
    mention `T` and produce `Desc.hrec q H (fun h => tupleTm indices) D`, where the
    indices live under `h` (so `T` is `var (k + 1)` there);
  - otherwise produce `Desc.arg q F (.lam name D)`.
* Finally remove `T` itself (`strengthen? 0`). If it still occurs, it was used in a
  non-recursive position: error.

The result lives in the parameter context `Δ`. Index tuples end in `tail` (a term in
`Δ`: `()`, or the phantom tail's value, see `phantomTail`) instead of `()`: lift it to
the context it is used in.

(Q4) `levels[k]` is the level of field `k`'s type, and of its domain if it is a function
type (`fieldLevels`). An `arg` field not in `Sort (l+1)` is lifted with `liftArg`, the
domain of an infinitary field with `liftHrec`. -/
def ctorDesc (nΔ : Nat) (fields : List (Name × Term R × Term R)) (target : List (Term R))
    (tail : Term R := .tt) (l : Level := .zero) (levels : List (Option Level × Option Level) := []) :
    Except String (Term R) := do
  let small (lv : Option Level) : Bool := match lv with
    | some k => !k.equiv (.succ l)
    | none => false
  let mkArg (k : Nat) (q F : Term R) (name : Name) (D : Term R) : Term R :=
    if small (levels[k]?.bind (·.1)) then .darg q (.ulift (.succ l) F) (.lam name (downVar0 D))
    else .darg q F (.lam name D)
  let mkHrec (k : Nat) (q H : Term R) (h : Name) (js D : Term R) : Term R :=
    if small (levels[k]?.bind (·.2)) then .dhrec q (.ulift (.succ l) H) (.lam h (downVar0 js)) D
    else .dhrec q H (.lam h js) D
  --<sol
  let n := fields.length
  let mut D : Term R := .dret (tupleWith (tail.lift (n + 1)) target)
  for (name, q, F) in fields.reverse, k in (List.range n).reverse do
    match F.spine with
    | (.var i, args) =>
      if i == k then
        let some D' := D.strengthen? 0
          | throw s!"a field may not depend on the recursive field {name}"
        let some js := paramArgs? nΔ k args
          | throw s!"the recursive field {name} must use the same parameters"
        D := .drec q (tupleWith (tail.lift (k + 1)) js) D'
      else D := mkArg k q F name D
    | (.pi h _ _ H B _, []) =>
      match B.spine with
      | (.var i, args) =>
        if i == k + 1 then
          let some D' := D.strengthen? 0
            | throw s!"a field may not depend on the recursive field {name}"
          if (H.strengthen? k).isNone then
            throw s!"the type being defined may not occur in the domain of {name}"
          let some js := paramArgs? nΔ (k + 1) args
            | throw s!"the recursive field {name} must use the same parameters"
          D := mkHrec k q H h (tupleWith (tail.lift (k + 2)) js) D'
        else D := mkArg k q F name D
      | _ => D := mkArg k q F name D
    | _ => D := mkArg k q F name D
  match D.strengthen? 0 with
  | some D' => pure D'
  | none => throw "the type being defined may only occur as the type of a field or the result"
  --|ex
  --| sorry
  --sol>

/-- Peel a type signature `(ξ₁ : X₁) → … → Type l` into indices and `l`. -/
def peelSignature : Term R → Except String (List (Name × BinderInfo × Term R × Term R) × Level)
  | .pi x bi q X B _ => do
    let (xs, l) ← peelSignature B
    pure ((x, bi, q, X) :: xs, l)
  | .sort l => match l with
    | .succ l => pure ([], l)
    | l => match l.toNat? with
      | some (n + 1) => pure ([], Level.ofNat n)
      | some 0 => throw "inductive propositions are not supported yet (declare it in Type)"
      | _ => throw s!"the type of an inductive must end in Type u, not Sort {l}"
  | _ => throw "the type of an inductive must be a sequence of arrows ending in Type u"

private def pisTm (bs : List (Name × BinderInfo × Term R × Term R)) (b : Term R) : Term R :=
  bs.foldr (fun (x, bi, q, A) acc => .pi x bi q A acc none) b

/-- The variables of an `n`-binder telescope, outermost first, seen from `extra` binders deeper. -/
private def telescopeVars (n extra : Nat) : List (Term R) :=
  (List.range n).map fun j => .var (extra + n - 1 - j)

/-- Elaborate an `inductive` command to its declarations. -/
def elabInductive (cmd : Syntax) (levelParams : List Name) : ElabM R (List (Decl R)) := do
  let T := ((cmd.child "name").getId?).getD "_"
  let us := levelParams.map Level.param
  let fail {α} (stx : Syntax) (msg : String) : ElabM R α := throwAt stx.info msg
  -- parameters
  let (ctxΔ, Δ) ← elabTelescope {} ((cmd.child "binders").args.flatMap binderViews).toList
  let nΔ := Δ.size
  -- signature
  let sig ← match (cmd.child "sig").args[1]? with
    | some s => pure (← checkType ctxΔ s).1
    | none => do
      -- no signature: the smallest `Type l` that holds every field (`Type` unless a field
      -- is bigger, as `x : A` with `A : Type u`). The fields are elaborated once to find
      -- their levels (with `T : Δ → Type`; a recursive field doesn't raise `l`), then
      -- again below.
      let ctxT0 := ctxΔ.bind T (eval (← getGlobals) [] (pisTm Δ.toList (.sort 1)))
      let saved ← get
      let mut l : Level := .zero
      for c in (cmd.child "ctors").args do
        let (ctxF, fs) ← elabTelescope ctxT0 ((c.child "binders").args.flatMap binderViews).toList
        let mut tys := #[]
        for (_, _, _, A) in fs, k in [0:fs.size] do tys := tys.push (← zonk (ctxT0.lvl + k) A)
        for (lA, _) in ← fieldLevels ctxF ctxT0.lvl tys.toList do
          if let some k := lA then
            -- a field in `Sort (k+1)` needs `l ≥ k`; one in `Sort u` needs `l ≥ u`
            unless k.hasMVar do l := l.join k.predBound
      set saved
      pure (.sort (.succ l))
  finishInstances
  let sig ← zonk ctxΔ.lvl sig
  let (Ξ, l) ← match peelSignature sig with
    | .ok r => pure r
    | .error e => fail (cmd.child "sig") e
  let nΞ := Ξ.length
  -- the index type: (ξ₁ : X₁) × … × Unit
  let I : Term R := Ξ.foldr (fun (x, _, q, X) acc => .sigma x q X acc none) (.unit (.succ l))
  -- constructors, elaborated with `T` bound locally
  -- inside the declaration `T` takes the parameters too: `T : Δ → Ξ → Type l`
  let ctxT := ctxΔ.bind T (eval (← getGlobals) [] (pisTm Δ.toList sig))
  let ctors := (cmd.child "ctors").args
  let mut names : List Name := []
  let mut descs : List (Term R) := []
  let mut ctorInfo : List (Name × List (Name × BinderInfo × Term R × Term R) × List (Term R)) := []
  let mut ctorLevels : List (List (Option Level × Option Level)) := []
  for c in ctors do
    let cname := ((c.child "name").getId?).getD "_"
    if names.contains cname then
      throwAt (c.child "name").info s!"the constructor {cname} is declared twice in {T}" ErrorCode.duplicateConstructor
    let (ctxF, fs) ← elabTelescope ctxT ((c.child "binders").args.flatMap binderViews).toList
    let n := fs.size
    let target ← match (c.child "sig").args[1]? with
      | some s => pure (← checkType ctxF s).1
      -- no result type: `T` applied to the parameters
      | none => pure ((telescopeVars nΔ (n + 1)).foldl .app (.var n))
    -- (HD9) the instance problems of the types (`Vec A (n + 1)`), solved first
    finishInstances
    -- zonk the fields and the target in their contexts
    let mut fs' := #[]
    for (x, bi, q, A) in fs, k in [0:n] do
      fs' := fs'.push (x, bi, ← zonk (ctxT.lvl + k) q, ← zonk (ctxT.lvl + k) A)
    let target ← zonk ctxF.lvl target
    for (_, _, q, A) in fs' do ensureNoMVars q c.info; ensureNoMVars A c.info
    ensureNoMVars target c.info
    let (head, args) := target.spine
    let some js := paramArgs? nΔ n args
      | fail c s!"constructor {cname} must return {T} applied to its parameters and {nΞ} indices"
    unless head == .var n && js.length == nΞ do
      fail c s!"constructor {cname} must return {T} applied to its parameters and {nΞ} indices"
    let lvs ← fieldLevels ctxF ctxT.lvl (fs'.toList.map (·.2.2.2))
    let D ← match ctorDesc nΔ (fs'.toList.map fun (x, _, q, A) => (x, q, A)) js .tt l lvs with
      | .ok D => pure D
      | .error e => fail c s!"constructor {cname}: {e}"
    ctorLevels := ctorLevels ++ [lvs]
    names := names ++ [cname]
    descs := descs ++ [D]
    ctorInfo := ctorInfo ++ [(cname, fs'.toList, js)]
  -- phantom parameters: those that neither a constructor nor an index type mentions
  -- (a `sealed inductive`: the seal was declared just before, `command.sealed`)
  let sealAx := if (← getGlobals).contains (sealName T) then some (sealName T) else none
  let (tailTy, tailV, _) ← phantomTail ctxΔ Δ (fun k => descs.any (·.hasVar k) || I.hasVar k) (.succ l)
    (sealAx := sealAx)
  let I : Term R := Ξ.foldr (fun (x, _, q, X) acc => .sigma x q X acc none) (tailTy.lift nΞ)
  if !(tailV matches .tt) then
    descs ← (ctorInfo.zip ctorLevels).mapM fun ((cname, fs, js), lvs) => match ctorDesc nΔ (fs.map fun (x, _, q, A) => (x, q, A)) js tailV l lvs with
      | .ok D => pure D
      | .error e => fail cmd s!"constructor {cname}: {e}"
  -- the whole description: a tag, then the constructor's description
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  -- (Q4) the tag is in `Type`: lifted when the type is in a bigger universe
  let tagLifted := !(Level.succ l).equiv (Level.ofNat 1)
  let desc : Term R := .darg w (if tagLifted then .ulift (.succ l) (.enum names) else .enum names)
    (.lam "t" (.ecase "z" ((Term.desc l I).lift 2) (if tagLifted then .down (.var 0) else .var 0)
      (descs.map (·.lift 1))))
  let ΔNames := Δ.toList.map (·.1)
  let ΔBinders := Δ.toList
  let descName := T ++ ".desc"
  let descDecl : Decl R :=
    { name := descName, levelParams := levelParams,
      type := pisTm ΔBinders (.desc l I), value := some (lamsTm ΔNames desc) }
  -- the nominal type
  let ξNames := Ξ.map (·.1)
  let Δvars := telescopeVars nΔ nΞ
  let ξvars := telescopeVars nΞ 0
  let muTm : Term R := .mu l (I.lift nΞ) ((Δvars.foldl .app (.const descName us)))
    (tupleWith (tailV.lift nΞ) ξvars) .szInf (some (T, us, Δvars ++ ξvars))
  let typeDecl : Decl R :=
    { name := T, levelParams := levelParams,
      type := pisTm ΔBinders sig, value := some (lamsTm (ΔNames ++ ξNames) muTm) }
  -- constructors
  let implicitΔ := ΔBinders.map fun (x, _, _, A) => (x, BinderInfo.implicit, (.qlit 0 : Term R), A)
  let mut ctorDecls := []
  for (cname, fs, js) in ctorInfo, tagIx in [0:ctorInfo.length], D in descs do
    let n := fs.length
    let lifts := descFieldLifts D
    -- occurrences of the local `T` (already applied to the parameters) become the global
    let Tc : Term R := .const T us
    let fsTy := fs.zipIdx.map fun ((x, bi, q, A), k) => (x, bi, q.instantiateAt k Tc, A.instantiateAt k Tc)
    let resTy := js.foldl (fun acc j => .app acc (j.instantiateAt n Tc)) ((telescopeVars nΔ n).foldl .app Tc)
    let some js' := js.mapM (·.strengthen? n)
      | fail cmd s!"constructor {cname}: its indices may not mention {T}"
    let fieldVars := telescopeVars n 0
    let tag : Term R := if tagLifted then .up (.tag names tagIx) else .tag names tagIx
    let fieldVals := fieldVars.zipIdx.map fun (f, k) => (lifts[k]?.getD .none).wrap f
    let payload := Term.pair tag
      (fieldVals.foldr .pair (.pair (.refl (I.lift n) (tupleWith (tailV.lift n) js')) .tt))
    let d : Decl R :=
      { name := ctorConst T cname, levelParams := levelParams,
        type := pisTm implicitΔ (pisTm fsTy resTy),
        value := some (lamsTm ΔNames (lamsTm (fs.map (·.1)) (.con payload))), inline := true }
    ctorDecls := ctorDecls ++ [d]
  pure ([descDecl, typeDecl] ++ ctorDecls)

/-- Elaborate a `coinductive` command: one "constructor" whose fields are the
observations. `T.desc`, `T := ν (T.desc Δ) ()`, and an observation function per field
(`out x` projected), and the coconstructor `T.mk` (a `cocon`). Returns the declarations and the observation names, with
whether each is recursive. Fields may depend on the parameters only. -/
def elabCoinductive (cmd : Syntax) (levelParams : List Name) :
    ElabM R (List (Decl R) × List (Name × Bool)) := do
  let T := ((cmd.child "name").getId?).getD "_"
  let us := levelParams.map Level.param
  let (ctxΔ, Δ) ← elabTelescope {} ((cmd.child "binders").args.flatMap binderViews).toList
  let nΔ := Δ.size
  let sig ← match (cmd.child "sig").args[1]? with
    | some s => pure (← checkType ctxΔ s).1
    | none => pure (.sort 1)
  finishInstances
  let sig ← zonk ctxΔ.lvl sig
  let l ← match peelSignature sig with
    | .ok ([], l) => pure l
    | .ok _ => throwAt (cmd.child "sig").info "a coinductive type has no indices (yet)"
    | .error e => throwAt (cmd.child "sig").info e
  let ctxT := ctxΔ.bind T (eval (← getGlobals) [] (pisTm Δ.toList sig))
  let views : List BinderView := (cmd.child "fields").args.toList.map fun f =>
    { name := ((f.child "name").getId?).getD "_", info := f.info, bi := .default,
      qty := (f.child "quantity").args[0]?, type := some (f.child "type") }
  let (ctxF, fs) ← elabTelescope ctxT views
  finishInstances
  let mut fs' := #[]
  for (x, bi, q, A) in fs, k in [0:fs.size] do
    let q ← zonk (ctxT.lvl + k) q
    let A ← zonk (ctxT.lvl + k) A
    ensureNoMVars q cmd.info; ensureNoMVars A cmd.info
    fs' := fs'.push (x, bi, q, A)
  let lvs ← fieldLevels ctxF ctxT.lvl (fs'.toList.map (·.2.2.2))
  let D ← match ctorDesc nΔ (fs'.toList.map fun (x, _, q, A) => (x, q, A)) [] .tt l lvs with
    | .ok D => pure D
    | .error e => throwAt cmd.info e
  -- phantom parameters (see `phantomTail`): the index type is the tail
  let (I, tailV, _) ← phantomTail ctxΔ Δ (fun k => D.hasVar k) (.succ l)
  let D ← if tailV matches .tt then pure D else
    match ctorDesc nΔ (fs'.toList.map fun (x, _, q, A) => (x, q, A)) [] tailV l lvs with
    | .ok D => pure D
    | .error e => throwAt cmd.info e
  let ΔNames := Δ.toList.map (·.1)
  let descDecl : Decl R :=
    { name := T ++ ".desc", levelParams := levelParams,
      type := pisTm Δ.toList (.desc l I), value := some (lamsTm ΔNames D) }
  let Δvars := telescopeVars nΔ 0
  let nuTm : Term R := .nu l I (Δvars.foldl .app (.const (T ++ ".desc") us)) tailV .szInf (some (T, us, Δvars))
  let typeDecl : Decl R :=
    { name := T, levelParams := levelParams, type := pisTm Δ.toList sig, value := some (lamsTm ΔNames nuTm) }
  -- observations: T.f : {Δ} → T Δ → F, with F not depending on earlier fields
  let implicitΔ := Δ.toList.map fun (x, _, _, A) => (x, BinderInfo.implicit, (.qlit 0 : Term R), A)
  let mut decls := [descDecl, typeDecl]
  let mut obs := []
  let mut fieldTys : List (Name × Term R) := []
  let lifts := descFieldLifts D
  for (x, _, _, A) in fs'.toList, k in [0:fs'.size] do
    -- `A` lives in [f_{k-1} … f₀, T, Δ]: drop the fields, then replace `T`
    let mut A' := A
    for _ in [0:k] do
      match A'.strengthen? 0 with
      | some a => A' := a
      | none => throwAt cmd.info s!"the observation {x} may not depend on earlier observations"
    let isRec := match (Term.spine A').1 with
      | .var 0 => true
      | _ => false
    let F := A'.instantiateAt 0 (.const T us)
    let Tapp : Term R := (telescopeVars nΔ 0).foldl .app (.const T us)
    -- (out x).2…2.1 in context [x, Δ]
    let proj : Term R := (lifts[k]?.getD .none).unwrap (.fst ((List.range k).foldl (fun t _ => .snd t) (.out (.var 0))))
    let d : Decl R :=
      { name := T ++ "." ++ x, levelParams := levelParams,
        type := pisTm implicitΔ (.pi "x" .default (.qlit QuantitySyntax.explicitDefault) Tapp (F.lift 1) none),
        value := some (lamsTm ΔNames (.lam "x" proj)), inline := true }
    decls := decls ++ [d]
    obs := obs ++ [(x, isRec)]
    fieldTys := fieldTys ++ [(x, F)]
  -- the coconstructor `T.mk : {Δ} → F₁ → … → Fₙ → T Δ`, a `cocon` of the fields
  -- (an existing tail is not unfolded: `T.mk h t` is one cell in front of `t`)
  unless fieldTys.any (·.1 == "mk") do
    let n := fieldTys.length
    let w : Term R := .qlit QuantitySyntax.explicitDefault
    let fsTy := fieldTys.zipIdx.map fun ((x, F), k) => (x, BinderInfo.default, w, F.lift k)
    let resTy := ((telescopeVars nΔ 0).foldl Term.app (Term.const T us)).lift n
    let e : Term R := if tailV matches .tt then .tt else .refl (I.lift n) tailV
    let payload : Term R := ((telescopeVars n 0).zipIdx.map fun (f, k) => (lifts[k]?.getD .none).wrap f).foldr .pair (.pair e .tt)
    let mk : Decl R :=
      { name := T ++ ".mk", levelParams := levelParams,
        type := pisTm implicitΔ (pisTm fsTy resTy),
        value := some (lamsTm ΔNames (lamsTm (fieldTys.map Prod.fst) (.cocon payload))), inline := true }
    decls := decls ++ [mk]
  pure (decls, obs)

/-- Elaborate a `structure` command to the Σ type and its constructor `S.mk`. -/
def elabStructure (cmd : Syntax) (levelParams : List Name) : ElabM R (List (Decl R)) := do
  let S := ((cmd.child "name").getId?).getD "_"
  let us := levelParams.map Level.param
  let (ctxΔ, Δ) ← elabTelescope {} ((cmd.child "binders").args.flatMap binderViews).toList
  let views : List BinderView := (cmd.child "fields").args.toList.map fun f =>
    { name := ((f.child "name").getId?).getD "_", info := f.info, bi := .default,
      qty := (f.child "quantity").args[0]?, type := some (f.child "type") }
  let (ctxF, fs) ← elabTelescope ctxΔ views
  finishInstances
  let mut fs' := #[]
  for (x, bi, q, A) in fs, k in [0:fs.size] do
    let q ← zonk (ctxΔ.lvl + k) q
    let A ← zonk (ctxΔ.lvl + k) A
    ensureNoMVars q cmd.info; ensureNoMVars A cmd.info
    fs' := fs'.push (x, bi, q, A)
  -- the parameters' types may have level metavariables (`outParam.{?u} Type`)
  let mut Δz := #[]
  for (x, bi, q, A) in Δ, k in [0:Δ.size] do
    Δz := Δz.push (x, bi, ← zonk k q, ← zonk k A)
  let Δ := Δz
  -- the universe: as given, or else big enough for every field (`Type u` for a field
  -- `x : A` with `A : Type u`)
  let sig ← match (cmd.child "sig").args[1]? with
    | some s => pure (← checkType ctxΔ s).1
    | none =>
      let g ← getGlobals
      let tys := ctxF.types.reverse.toArray
      let mut l : Level := 0
      for (_, _, _, A) in fs', k in [0:fs'.size] do
        let env := (List.range (ctxΔ.lvl + k)).reverse.map Val.var
        match typeSort? g (tys.extract 0 (ctxΔ.lvl + k)) (eval g env A) with
        | some s => unless s.hasMVar do l := l.join s.predBound
        | none => pure ()
      pure (.sort (.succ l))
  finishInstances
  let sig ← zonk ctxΔ.lvl sig
  let l ← match peelSignature sig with
    | .ok ([], l) => pure l
    | .ok _ => throwAt (cmd.child "sig").info "a structure has no indices"
    | .error e => throwAt (cmd.child "sig").info e
  let body : Term R := fs'.toList.foldr (fun (x, _, q, A) acc => .sigma x q A acc none) (.unit (.succ l))
  -- phantom parameters (see `phantomTail`): the final `Unit` becomes the phantom tail
  -- (a structure with fields marks its tail, so that erasure unboxes the last field, 22i)
  let (tailTy, tailV, _) ← phantomTail ctxΔ Δ (fun k => body.hasVar k) (.succ l)
    (markTail := !fs'.isEmpty)
  let body : Term R := fs'.toList.foldr (fun (x, _, q, A) acc => .sigma x q A acc none) (tailTy.lift fs'.size)
  let ΔNames := Δ.toList.map (·.1)
  let n := fs'.size
  let Sapp : Term R := (telescopeVars Δ.size n).foldl .app (.const S us)
  let implicitΔ := Δ.toList.map fun (x, _, _, A) => (x, BinderInfo.implicit, (.qlit 0 : Term R), A)
  let sDecl : Decl R :=
    { name := S, levelParams := levelParams, type := pisTm Δ.toList sig,
      value := some (lamsTm ΔNames body) }
  let mkDecl : Decl R :=
    { name := S ++ ".mk", levelParams := levelParams, type := pisTm implicitΔ (pisTm fs'.toList Sapp),
      value := some (lamsTm ΔNames (lamsTm (fs'.toList.map (·.1)) (tupleWith tailV (telescopeVars n 0)))), inline := true }
  pure [sDecl, mkDecl]

end Wiz.Elab
