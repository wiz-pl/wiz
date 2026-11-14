import Wiz.Core.Eval

/-!
# Conversion (definitional equality), type-directed

`conv tys A a b` decides whether `a` and `b`, both of type `A`, are definitionally
equal. `tys` holds the types of the local variables **indexed by level**, so
`tys.size` is the size of the context.

Conversion is **type-directed**: the type is inspected first. That makes the η-rules
easy and complete:

* at a Π type, apply both sides to a fresh variable (η for functions);
* at a Σ type, compare the projections (η for pairs);
* at the unit type, **everything is equal** (η for unit). Without the type you
  couldn't tell that a variable `u : Unit` equals `()`.

Stage 4's observational equality adds one more: at a proposition, all proofs are equal.

Types themselves are compared structurally by `convTy`. Two neutrals are compared by
`convNe`, which walks both spines and **computes the type** as it goes, since the
arguments of an application must be compared at the domain's type.

Reference: Abel & Coquand, *Untyped Algorithmic Equality for Martin-Löf's Logical
Framework with Surjective Pairs* (2007), and the "typed" variant in Abel's habilitation.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- The type of a neutral's head: a local's type from `tys`, a global's declared type
with its level parameters instantiated, or (stage 4c) the type of a stuck
observational construct. -/
def headType (g : Globals R) (tys : Array (VTy R)) : Head R → Option (VTy R)
  | .local x => tys[x]?
  | .global n us => (g.find? n).map fun d => eval g [] (d.type.instLevels d.levelParams us)
  | .mvar _ => none
  | .eq .. | .eqTy .. => some (.sort 0)
  | .cast _ B _ _ => some B
  | .refl A a => some (vEq g A a a)
  | .reflTy X => some (vEqType g X X)
  | .transp _ _ P _ b e => some (vApp g (vApp g P b) e)
  -- (a suspended proof carries no type: see `inferNe` and `convNe`)
  | .prf .. => none

/-! ### Types of the data eliminators' arguments (stage 4d)

Built as terms in a small environment and evaluated, like the templates. `w` is the
quantity to put on the binders: the kernel uses the rig's default, and conversion
(which only needs the types to direct η) passes anything. -/

private def tv (i : Nat) : Term R := .var i
private def tapps (f : Term R) (as : List (Term R)) : Term R := as.foldl .app f

/-- `P : Desc I → Sort v` -/
def delimMotiveTy (l v : Level) (I : Val R) (w : R) : VTy R :=
  .pi "D" .default (.qlit w) (.desc l I) (.mk [] (.sort v)) none

/-- The types of `mret`, `marg`, `mrec`, `mhrec` for `Desc.elim` with motive `P`. -/
def delimMethodTys (g : Globals R) (l : Level) (I P : Val R) (w : R) : VTy R × VTy R × VTy R × VTy R :=
  let pi (x : Name) (a b : Term R) : Term R := .pi x .default (.qlit w) a b none
  let env := [P, I]
  -- i0 P1 I2
  let mret := pi "i" (tv 1) (.app (tv 1) (.dret (tv 0)))
  -- q0 P1 I2 ; S0 q1 P2 I3 ; E0 S1 q2 P3 I4 ; ih0 E1 S2 q3 P4 I5
  let marg := pi "q" .qty (pi "S" (.sort (.succ l)) (pi "E" (pi "s" (tv 0) (.desc l (tv 4)))
    (pi "ih" (pi "s" (tv 1) (.app (tv 4) (.app (tv 1) (tv 0)))) (.app (tv 4) (.darg (tv 3) (tv 2) (tv 1))))))
  -- q0 P1 I2 ; j0 q1 P2 I3 ; E0 j1 q2 P3 I4 ; ih0 E1 j2 q3 P4 I5
  let mrec := pi "q" .qty (pi "j" (tv 2) (pi "E" (.desc l (tv 3))
    (pi "ih" (.app (tv 3) (tv 0)) (.app (tv 4) (.drec (tv 3) (tv 2) (tv 1))))))
  -- q0 P1 I2 ; H0 q1 P2 I3 ; j0 H1 q2 P3 I4 ; E0 j1 H2 q3 P4 I5 ; ih0 E1 j2 H3 q4 P5 I6
  let mhrec := pi "q" .qty (pi "H" (.sort (.succ l)) (pi "j" (pi "h" (tv 0) (tv 4)) (pi "E" (.desc l (tv 4))
    (pi "ih" (.app (tv 4) (tv 0)) (.app (tv 5) (.dhrec (tv 4) (tv 3) (tv 2) (tv 1)))))))
  (eval g env mret, eval g env marg, eval g env mrec, eval g env mhrec)

/-- `P : (i : I) → μ D i → Sort v` -/
def indMotiveTy (g : Globals R) (l v : Level) (I D : Val R) (w : R) : VTy R :=
  eval g [D, I] (.pi "i" .default (.qlit w) (tv 1)
    (.pi "_" .default (.qlit w) (.mu l (tv 2) (tv 1) (tv 0) .szInf none) (.sort v) none) none)

/-- `m : (0 i : I) → (xs : ⟦D⟧ (μ D) i) → (ih : All D (μ D) P i xs) → P i (con xs)` -/
def indMethodTy (g : Globals R) (l v : Level) (I D P : Val R) (w : R) : VTy R :=
  -- i0 P1 D2 I3 ; xs0 i1 P2 D3 I4 ; ih0 xs1 i2 P3 D4 I5
  let X₁ : Term R := .lam "j" (.mu l (tv 4) (tv 3) (tv 0) .szInf none)
  let X₂ : Term R := .lam "j" (.mu l (tv 5) (tv 4) (tv 0) .szInf none)
  eval g [P, D, I] (.pi "i" .default (.qlit 0) (tv 2)
    (.pi "xs" .default (.qlit w) (tapps (Templates.interpTm l) [tv 3, tv 2, X₁, tv 0])
      (.pi "ih" .default (.qlit w) (tapps (Templates.allTm l v) [tv 4, tv 3, X₂, tv 2, tv 1, tv 0])
        (tapps (tv 3) [tv 2, .con (tv 1)]) none) none) none)

/-- `S : I → Type l` -/
def coitStateTy (l : Level) (I : Val R) (w : R) : VTy R :=
  .pi "i" .default (.qlit w) I (.mk [] (.sort (.succ l))) none

/-- `step : (i : I) → S i → ⟦D⟧ S i` -/
def coitStepTy (g : Globals R) (l : Level) (I D S : Val R) (w : R) : VTy R :=
  -- i0 S1 D2 I3 ; s0 i1 S2 D3 I4
  eval g [S, D, I] (.pi "i" .default (.qlit w) (tv 2)
    (.pi "s" .default (.qlit w) (.app (tv 1) (tv 0)) (tapps (Templates.interpTm l) [tv 4, tv 3, tv 2, tv 1]) none) none)

/-! ### Sizes

A size is `∞`, or a size variable (any neutral) plus a number of `↑`s. -/

/-- `(base, k)` for `↑ᵏ base`; `none` as the base means `∞`. -/
partial def sizeView : Val R → Option (Val R) × Nat
  | .unfold _ _ _ v => sizeView v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => sizeView v.get
  | .szInf => (none, 0)
  | .szSuc s => let (b, k) := sizeView s; (b, k + 1)
  | v => (some v, 0)

private def sameBase : Val R → Val R → Bool
  | .neutral (.local a) #[], .neutral (.local b) #[] => a == b
  | .neutral (.mvar a) #[], .neutral (.mvar b) #[] => a == b
  | _, _ => false

def sizeEq (a b : Val R) : Bool :=
  match sizeView a, sizeView b with
  | (none, _), (none, _) => true
  | (some x, k), (some y, m) => k == m && sameBase x y
  | _, _ => false

/-- `a ≤ b` for sizes: anything is below `∞`; `↑ᵏ x ≤ ↑ᵐ x` when `k ≤ m`; and a
variable `x : Size< u` (from `tys`) satisfies `↑ᵏ x ≤ b` when `↑ᵏ⁻¹ u ≤ b`
(`x < u`, so `x + 1 ≤ u`), or when `u ≤ b` for `k = 0`. -/
partial def sizeLe (tys : Array (VTy R)) (a b : Val R) : Bool :=
  match sizeView a, sizeView b with
  | _, (none, _) => true
  | (none, _), (some _, _) => false
  | (some x, k), (some y, m) =>
    (k ≤ m && sameBase x y) ||
    match x with
    | .neutral (.local lx) #[] => match tys[lx]? with
      | some (.sizeLt u) => sizeLe tys ((List.range (k - 1)).foldl (fun s _ => .szSuc s) u) b
      | _ => false
    | _ => false

/-- `a < b` for sizes (decision D2): `↑a ≤ b`, except at `∞`. Since `↑∞ = ∞`, `↑a ≤ ∞`
holds for every `a`, including `∞` itself, so it can't say `a < ∞` (Agda's `∞ < ∞`,
issue #3026). Below `∞` are only the sizes built from a variable with a bound,
`↑ᵏ x` for `x : Size< u` (`x < u ≤ ∞`, and `∞` is a limit). A variable of type `Size`
is not: it may stand for `∞`. -/
partial def sizeBelow (tys : Array (VTy R)) (a b : Val R) : Bool :=
  match sizeView b with
  | (none, _) => match sizeView a with
    | (some (.neutral (.local x) #[]), _) => match tys[x]?.map whnf with
      | some (.sizeLt _) => true
      | _ => false
    | _ => false
  | _ => sizeLe tys (.szSuc a) b

/-- `f : (s : Size) → ((j : Size< s) → (i : I) → (y : μ^j D i) → P i y) → (i : I) → (x : μ^s D i) → P i x` -/
def sfixFunTy (g : Globals R) (l : Level) (I D P : Val R) (w : R) : VTy R :=
  let pi (x : Name) (a b : Term R) : Term R := .pi x .default (.qlit w) a b none
  -- s0 P1 D2 I3 ; j0 s1 P2 D3 I4 ; i0 j1 s2 P3 D4 I5 ; y0 i1 j2 s3 P4
  -- rec0 s1 P2 D3 I4 ; i0 rec1 s2 P3 D4 I5 ; x0 i1 rec2 s3 P4
  eval g [P, D, I] (.pi "s" .default (.qlit 0) .size
    (pi "rec" (.pi "j" .default (.qlit 0) (.sizeLt (tv 0))
        (pi "i" (tv 4) (pi "y" (.mu l (tv 5) (tv 4) (tv 0) (tv 1) none) (tapps (tv 4) [tv 1, tv 0]))) none)
      (pi "i" (tv 4) (pi "x" (.mu l (tv 5) (tv 4) (tv 0) (tv 2) none) (tapps (tv 4) [tv 1, tv 0])))) none)

/-- `m : (0 j : Size< s) → (0 i : I) → (q xs : ⟦D⟧ (μ^j D) i) → P i (con xs)`: the method
of `scase` at quantity `q` (K1) receives the payload at `q`. -/
def scaseMethodTy (g : Globals R) (l : Level) (I D P s q : Val R) : VTy R :=
  -- j0 s1 P2 D3 I4 q5 ; i0 j1 s2 P3 D4 I5 q6 ; xs0 i1 j2 s3 P4 D5 I6
  eval g [s, P, D, I, q] (.pi "j" .default (.qlit 0) (.sizeLt (tv 0)) (.pi "i" .default (.qlit 0) (tv 4)
    (.pi "xs" .default (tv 6)
      (tapps (Templates.interpTm l) [tv 5, tv 4, .lam "j'" (.mu l (tv 6) (tv 5) (tv 0) (tv 2) none), tv 0])
      (tapps (tv 4) [tv 1, .con (tv 0)]) none) none) none)

/-- `f : (s : Size) → ((i : I) → A i → ν^s D i) → (i : I) → A i → ν^{↑s} D i` -/
def scofixFunTy (g : Globals R) (l : Level) (I D A : Val R) (w : R) : VTy R :=
  let pi (x : Name) (a b : Term R) : Term R := .pi x .default (.qlit w) a b none
  -- s0 A1 D2 I3 ; i0 s1 A2 D3 I4 ; a0 i1 s2 A3 D4 I5 ; rec0 s1 A2 D3 I4 ; i0 rec1 s2 A3 D4 I5 ; a0 i1 rec2 s3 A4 D5 I6
  eval g [A, D, I] (.pi "s" .default (.qlit 0) .size
    (pi "rec" (pi "i" (tv 3) (pi "a" (.app (tv 2) (tv 0)) (.nu l (tv 5) (tv 4) (tv 1) (tv 2) none)))
      (pi "i" (tv 4) (pi "a" (.app (tv 3) (tv 0)) (.nu l (tv 6) (tv 5) (tv 1) (.szSuc (tv 3)) none)))) none)

/-- The type of a neutral, computed by walking its spine from the head's type. -/
partial def inferNe (g : Globals R) (tys : Array (VTy R)) : Val R → Option (VTy R)
  | .unfold n us sp _ => inferNe g tys (.neutral (.global n us) sp)
  | .lazyInd _ _ _ _ _ _ _ _ _ v => inferNe g tys v.get
  | .neutral h sp => do
    -- (P2) a suspended proof has no type of its own; what follows its last `absurd` is
    -- typed by the motive (a neutral that is a *type* and starts at a proof has one)
    let (start, ty₀) ← match headType g tys h with
      | some ty => pure (0, ty)
      | none => match lastAbsurd? sp with
        | some k => match sp[k]? with
          | some (.absurd m) => pure (k + 1, m)
          | _ => none
        | none => none
    let mut ty := ty₀
    let mut acc : Val R := .neutral h (sp.extract 0 start)
    for e in sp.extract start sp.size do
      match e, whnf ty with
      | .app x, .pi _ _ _ _ cod _ => ty := Closure.inst g cod x; acc := vApp g acc x
      | .fst, .sigma _ _ A _ _ => ty := A; acc := vFst acc
      | .snd, .sigma _ _ _ B _ => ty := Closure.inst g B (vFst acc); acc := vSnd acc
      | .split q z m x y b, _ => ty := Closure.inst g m acc; acc := vSplit g q acc z m x y b
      | .absurd m, _ => ty := m; acc := vAbsurd m acc
      | .ecase z m env bs, _ => ty := Closure.inst g m acc; acc := vEcase g z m acc env bs
      | .delim v P a b c h, _ => ty := vApp g P acc; acc := vDelim g v P a b c h acc
      | .ind l I D v P m i, _ => ty := vApp g (vApp g P i) acc; acc := vInd g l I D v P m i acc
      | .out, .nu l I D i s _ =>
        ty := vInterp g l I D (nuFamilyAt l I D ((sizePred? s).getD .szInf)) i; acc := vOut g acc
      | .sfix l I D v P f s i, _ => ty := vApp g (vApp g P i) acc; acc := vSfix g l I D v P f s i acc
      | .scase l q I D v P m s i, _ => ty := vApp g (vApp g P i) acc; acc := vScase g l q I D v P m s i acc
      | .down, .ulift _ A => ty := A; acc := vDown acc
      | _, _ => none
    pure ty
  | _ => none

/-- The universe level of a type, if it can be computed. -/
partial def typeSort? (g : Globals R) (tys : Array (VTy R)) : VTy R → Option Level
  | .unfold _ _ _ v => typeSort? g tys v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => typeSort? g tys v.get
  | .sort l => some (.succ l)
  | .pi _ _ _ A B _ => do
    return .imax (← typeSort? g tys A) (← typeSort? g (tys.push A) (Closure.inst g B (Val.var tys.size)))
  | .sigma _ _ A B _ => do
    return .max (← typeSort? g tys A) (← typeSort? g (tys.push A) (Closure.inst g B (Val.var tys.size)))
  | .unit l | .empty l | .ulift l _ => some l
  | .qty | .enum _ | .size | .sizeLt _ => some 1
  | .desc l _ => some (.succ (.succ l))
  | .mu l .. | .nu l .. => some (.succ l)
  | v@(.neutral ..) => do
    match whnf (← inferNe g tys v) with
    | .sort l => some l
    | _ => none
  | _ => none

/-- Is this type a proposition? Then all its inhabitants are equal. -/
def isProp (g : Globals R) (tys : Array (VTy R)) (ty : VTy R) : Bool :=
  match typeSort? g tys ty with
  | some l => l.equiv 0
  | none => false

/-- (P2) Is the neutral `h · sp[0..k)` a proof of `False`? Either it starts at a proof
head and has passed through no `absurd` (then it is a proof, and it is being given to an
`absurd`), or its type is computed. -/
def falsePrefix (g : Globals R) (tys : Array (VTy R)) (h : Head R) (sp : Array (Elim R)) (k : Nat) : Bool :=
  let pre := sp.extract 0 k
  (proofHead h && (lastAbsurd? pre).isNone) ||
  match inferNe g tys (.neutral h pre) with
  | some ty => match whnf ty with
    | .empty l => l.isZero
    | _ => false
  | none => false

mutual

/-- **Exercise 1.4.** Definitional equality of `a` and `b` at type `ty`.

* At a `pi` type: η. Apply both sides to `Val.var tys.size` (with `vApp`) and compare at
  the codomain, with the domain pushed onto `tys`.
* At a `sort`: they are types, so use `convTy`.
* At any other type: both must be neutrals, compared by `convNe`.

**Exercise 4.6** (stage 4b): at a `sigma` type compare the `vFst`s and then the
`vSnd`s (η for pairs); at a `unit` type, always `true`.

**Exercise 4.13** (stage 4c): first, **proof irrelevance**: if `isProp ty`, return
`true`. Then **regularity**: a stuck `cast A B e t` with an empty spine and
`convTy A B` is replaced by `t` (on either side) before comparing. -/
partial def conv (g : Globals R) (tys : Array (VTy R)) (ty : VTy R) (a b : Val R) : Bool :=
  -- (P2, `lazyProofs`) proof irrelevance first, so that a glued proof is never unfolded
  if g.lazyProofs && isProp g tys ty then true else
  -- glued values with the same head: compare the spines first, unfold if that fails
  if let some r := convGlued g tys a b then r || conv g tys ty (whnf a) (whnf b) else
  let a := whnf a
  let b := whnf b
  -- numerals: compare two directly, or else look one step inside (`vNatView`)
  if let (.natLit n, .natLit m) := (a, b) then n == m else
  let a := vNatView g a
  let b := vNatView g b
  let ty := whnf ty
  -- (given) Q4: η at `ULift A` (a lifted proposition has one inhabitant)
  if let .ulift l A := ty then l.equiv 0 || conv g tys A (vDown a) (vDown b) else
  --<sol
  if isProp g tys ty then true else
  -- regularity (InReg_conv): a stuck cast between convertible types is its argument
  let a := unCast g tys a
  let b := unCast g tys b
  let neutralsAgree (_ : Unit) : Bool :=
    (a matches .neutral ..) && (b matches .neutral ..) && (convNe g tys a b).isSome
  match ty with
  -- (η at a Π or a Σ, after the neutral comparison: `wiz-notes/wishful/conv-sigma-eta-neutral.md`)
  -- two neutrals are first compared as they are. `convNe` answers "equal" only for the same
  -- head and convertible spines, which η would find too (it compares the same spines, each
  -- extended by the same elimination), so this adds no answer; it saves η-splitting a stuck
  -- record into its fields, each of which compares the whole stuck value again. If it
  -- fails, η as before.
  | .pi _ _ _ dom cod _ =>
    neutralsAgree () ||
    let v := Val.var tys.size
    conv g (tys.push dom) (Closure.inst g cod v) (vApp g a v) (vApp g b v)
  | .sigma _ _ A B _ =>
    neutralsAgree () ||
    let a₁ := vFst a
    conv g tys A a₁ (vFst b) && conv g tys (Closure.inst g B a₁) (vSnd a) (vSnd b)
  | .unit _ => true
  | .qty => match sameQty a b with
    | some r => r
    | none => (convNe g tys a b).isSome
  | .enum _ => match a, b with
    | .tag _ i, .tag _ j => i == j
    | _, _ => (convNe g tys a b).isSome
  | .size | .sizeLt _ => sizeEq a b
  | .desc l I => match a, b with
    | .dret i, .dret j => conv g tys I i j
    | .darg q S E, .darg q' S' E' =>
      conv g tys .qty q q' && convTy g tys S S' &&
        conv g tys (.pi "s" .default (.qlit 1) S (.mk [I] (.desc l (.var 1))) none) E E'
    | .drec q j E, .drec q' j' E' =>
      conv g tys .qty q q' && conv g tys I j j' && conv g tys (.desc l I) E E'
    | .dhrec q H j E, .dhrec q' H' j' E' =>
      conv g tys .qty q q' && convTy g tys H H' &&
        conv g tys (.pi "h" .default (.qlit 1) H (.mk [I] (.var 1)) none) j j' && conv g tys (.desc l I) E E'
    | _, _ => (convNe g tys a b).isSome
  | .mu l I D i _ _ => match a, b with
    | .con x, .con y => conv g tys (vInterp g l I D (muFamily l I D) i) x y
    | _, _ => (convNe g tys a b).isSome
  | .nu l I D i _ _ => match a, b with
    | .cocon x, .cocon y => conv g tys (vInterp g l I D (nuFamily l I D) i) x y
    | .scofix _ _ _ A f _ j x, .scofix _ _ _ A' f' _ j' x' =>
      conv g tys (coitStateTy l I 1) A A' && conv g tys (scofixFunTy g l I D A 1) f f' &&
        conv g tys I j j' && conv g tys (vApp g A j) x x'
    | .coit _ _ _ S st j s, .coit _ _ _ S' st' j' s' =>
      conv g tys (coitStateTy l I 1) S S' && conv g tys (coitStepTy g l I D S 1) st st' &&
        conv g tys I j j' && conv g tys (vApp g S j) s s'
    | _, _ => (convNe g tys a b).isSome
  | .sort _ => convTy g tys a b
  -- (13b) a type that is opaque here (another module's, with private parts: `elabView`
  -- hid its definition): two values of it are compared at its real definition, so that
  -- η and proof irrelevance apply to its fields (two `P.mk 4 h` with different proofs
  -- `h` are equal), as the kernel, which sees the definition, decides
  | .neutral (.global T us) sp => (convNe g tys a b).isSome ||
    match g.hidden[T]? with
    | some { value := some v, levelParams, .. } =>
      let full := g.fullView
      conv full tys (vElims full (eval full [] (v.instLevels levelParams us)) sp) a b
    | _ => false
  | _ => (convNe g tys a b).isSome
  --|ex
  --| sorry
  --sol>

/-- **Exercise 1.4b.** Equality of two types.

* `sort`/`sort`: `Level.equiv`.
* `pi`/`pi`: equal quantities (binder info is irrelevant), convertible domains, and
  convertible codomains under a fresh variable of the domain type. (Stage 4c: when
  the type is a proposition, quantities don't matter, since proofs are erased.)
* Two neutrals: `convNe`.
* Otherwise `false`.

**Exercise 4.6b** (stage 4b): `sigma`/`sigma` like `pi`; `unit`/`unit` and
`empty`/`empty` by `Level.equiv`. -/
partial def convTy (g : Globals R) (tys : Array (VTy R)) (a b : VTy R) : Bool :=
  if let some r := convGlued g tys a b then r || convTy g tys (whnf a) (whnf b) else
  let a := whnf a
  let b := whnf b
  -- (given) regularity (InReg_conv), for a type that is stuck on a cast (`P (cast …)` by
  -- an eliminator: the neutral is the cast, with the elimination in its spine)
  let a := unCast g tys a
  let b := unCast g tys b
  -- (given) Q4
  if let (.ulift l A, .ulift l' A') := (a, b) then l.equiv l' && convTy g tys A A' else
  --<sol
  -- **Cast-Refl at every type, while deciding equality of two propositions.**
  -- The two sides are propositions (truth values in the model): their truth values
  -- are what matters, and the model validates `cast`-regularity at every type. Use the
  -- evaluator's proposition test (`propSort?`), not `isProp`/`typeSort?`: the latter
  -- recomputes a Π/Σ sort from its parts and misses an annotated proposition whose tail
  -- is a Π over a data domain (`vEq`'s equation at a product is exactly that).
  -- This is what lets two proofs whose propositional types differ only in a `cast`
  -- (outside vs inside a projection, a `transp` motive) compare. An equation between two
  -- data *types* still uses the inert-only rule; the flag does reach the equation's two
  -- *sides*, i.e. Cast-Refl for equation proofs (wiz-notes/conv-proof-field.md §8).
  let g := if propSort? a == some true && propSort? b == some true then { g with regularity := .full } else g
  let v := Val.var tys.size
  match a, b with
  | .sort u, .sort u' => u.equiv u'
  | .pi _ _ q A B _, .pi _ _ q' A' B' _ =>
    (convQty q q' || isProp g tys a) && convTy g tys A A' &&
      convTy g (tys.push A) (Closure.inst g B v) (Closure.inst g B' v)
  | .sigma _ q A B _, .sigma _ q' A' B' _ =>
    (convQty q q' || isProp g tys a) && convTy g tys A A' &&
      convTy g (tys.push A) (Closure.inst g B v) (Closure.inst g B' v)
  | .qty, .qty | .size, .size => true
  | .sizeLt s, .sizeLt t => sizeEq s t
  | .enum ls, .enum ls' => ls.length == ls'.length
  | .desc l I, .desc l' I' => l.equiv l' && convTy g tys I I'
  | .mu l I D i s _, .mu l' I' D' i' s' _ | .nu l I D i s _, .nu l' I' D' i' s' _ =>
    l.equiv l' && sizeEq s s' && convTy g tys I I' && conv g tys (.desc l I) D D' && conv g tys I i i'
  | .unit u, .unit u' => u.equiv u'
  | .empty u, .empty u' => u.equiv u'
  | .neutral .., .neutral .. => (convNe g tys a b).isSome
  | _, _ => false
where
  convQty (q q' : Val R) : Bool := conv g tys .qty q q'
  --|ex
  --| sorry
  --sol>

/-- **Regularity, decided by conversion** (InReg_conv; `wiz-notes/conv-regularity.md`).

    A inert     A ≡ B
    ───────────────────────
    cast A B e t ≡ t

[PLT25]'s Cast-Refl, restricted to inert types. It is a rule of conversion, not of
evaluation: a cast on a canonical value takes a structural rule in `vCast`, and a cast
that stays *stuck* is removed here, on either side of a comparison, when its two types
are convertible. The neutral may carry eliminations (`ind … (cast …)`): they are applied
to the argument. The evaluator's `groundEqTy` decides a fragment of the same rule
without conversion.

* "Inert" is asked of either endpoint: `inertTy` reads a `Σ`'s sort annotation, which is
  optional, so of two convertible types one can be inert and the other not.
* Termination: `convTy A B` is a comparison of two components of the neutral, as the
  congruence rule for two casts already makes; each step removes one cast.
* `--regularity full` (an experiment) is the rule at every type.

The value comes back in weak head normal form. -/
partial def unCast (g : Globals R) (tys : Array (VTy R)) (v : Val R) : Val R :=
  match v with
  | .neutral (.cast A B _ t) sp =>
    let applies := g.regularity == .full ||
      (g.inertReg == .conv && (inertTy g 0 A || inertTy g 0 B))
    if applies && convTy g tys A B then unCast g tys (whnf (vElims g t sp)) else v
  | v => v

/-- Two glued values (`Val.unfold`) with the same global head: are their spines
convertible? `none` unless both are glued with the same head. -/
partial def convGlued (g : Globals R) (tys : Array (VTy R)) (a b : Val R) : Option Bool :=
  match a, b with
  | .unfold n us sp _, .unfold n' us' sp' _ =>
    if n == n' && us.length == us'.length && (us.zip us').all (fun (u, u') => u.equiv u') then
      some (convNe g tys (.neutral (.global n us) sp) (.neutral (.global n' us') sp')).isSome
    else none
  -- the same induction on a numeral: compare the folded forms
  | a@(.lazyInd _ _ _ _ _ _ _ x _ _), b@(.lazyInd _ _ _ _ _ _ _ y _ _) =>
    -- (on a constructor, `ind` is lazy for speed alone: compared by what it computes)
    if (whnf x matches .con _) || (whnf y matches .con _) then none else
    -- (P2: the kernel's comparisons don't evaluate proofs)
    let g := { g with quoteErasesProofs := true }
    some (quote g tys.size a == quote g tys.size b)
  | _, _ => none

/-- **Exercise 1.4c.** Compare two neutrals. On success return their (common) type.

Heads must be `Head.equiv` and spines the same length. Start from the head's type
(`headType`) and walk both spines together, keeping the current type and the value
of the neutral so far:

* `app a`, `app b` at type `(x : A) → B`: `conv` the arguments at `A`; the new type is
  `B` instantiated with `a`.

**Exercise 4.13b** (stage 4c): heads that contain values. `eq`: compare the types with
`convTy` and the sides with `conv`; `eqTy`: `convTy` both; `cast`: the types and the
casted terms; two proof heads (`refl`, `reflTy`, `transp`) are always equal.

**Exercise 4.6c** (stage 4b):
* `fst` at `(x : A) × B`: type `A`. `snd`: type `B` instantiated with the first
  projection of the neutral so far.
* `split` at `(x : A) × B`: equal quantities, motives `convTy` under a binder of
  the Σ type, and bodies `conv` under binders `x : A` and `y : B x` at the
  motive instantiated with `(x, y)`. The result type is the motive at the neutral.
* `absurd m`: motives `convTy`; the result type is `m`. -/
partial def convNe (g : Globals R) (tys : Array (VTy R)) (a b : Val R) : Option (VTy R) := do
  --<sol
  let .neutral h sp := a | none
  let .neutral h' sp' := b | none
  let isProof : Head R → Bool
    | .refl .. | .reflTy _ | .transp .. | .prf .. => true
    | _ => false
  -- (P2) **a proof under `absurd` is irrelevant**: the argument of `absurd` at `False` is a
  -- proof, which is never compared (it may be a suspended proof on one side and a
  -- hypothesis on the other). So if the two neutrals pass through an `absurd` on a proof
  -- of `False` at the same distance from their ends, they are compared from there on:
  -- the motives, then the eliminations that follow, typed by the motive.
  let cut : Option (Nat × Nat × VTy R × VTy R) := (List.range (min sp.size sp'.size)).findSome? fun d =>
    let i := sp.size - 1 - d
    let j := sp'.size - 1 - d
    match sp[i]?, sp'[j]? with
    | some (.absurd m), some (.absurd m') =>
      if falsePrefix g tys h sp i && falsePrefix g tys h' sp' j then some (i + 1, j + 1, m, m') else none
    | _, _ => none
  let (start, start', ty₀) ← match cut with
    | some (i, j, m, m') => if convTy g tys m m' then pure (i, j, m) else none
    | none =>
      let headsEq := match h, h' with
        | .eq A x y, .eq A' x' y' => convTy g tys A A' && conv g tys A x x' && conv g tys A y y'
        | .eqTy A B, .eqTy A' B' => convTy g tys A A' && convTy g tys B B'
        | .cast A B _ t, .cast A' B' _ t' => convTy g tys A A' && convTy g tys B B' && conv g tys A t t'
        | _, _ => (isProof h && isProof h') || h.equiv h'
      if !headsEq then none else
      -- two proofs with only applications and projections after them (their type was not
      -- seen to be a proposition, or `conv` would have answered): equal, with nothing to
      -- compare. (The type returned is not used.)
      let onProofs (sp : Array (Elim R)) : Bool := sp.all fun
        | .app _ | .fst | .snd | .down => true
        | _ => false
      if isProof h && isProof h' && onProofs sp && onProofs sp' then return .unit 0 else
      match headType g tys h with
      | some ty => pure (0, 0, ty)
      | none => none
  unless sp.size - start == sp'.size - start' do none
  let mut ty := ty₀
  let mut acc : Val R := .neutral h (sp.extract 0 start)
  for e in sp.extract start sp.size, e' in sp'.extract start' sp'.size do
    match e, e', whnf ty with
    | .app x, .app y, .pi _ _ _ dom cod _ =>
      unless conv g tys dom x y do none
      ty := Closure.inst g cod x
      acc := vApp g acc x
    | .fst, .fst, .sigma _ _ A _ _ =>
      ty := A
      acc := vFst acc
    | .snd, .snd, .sigma _ _ _ B _ =>
      ty := Closure.inst g B (vFst acc)
      acc := vSnd acc
    | .split q _ m _ _ body, .split q' _ m' _ _ body', sty@(.sigma _ _ A B _) =>
      unless conv g tys .qty q q' do none
      let l := tys.size
      unless convTy g (tys.push sty) (Closure.inst g m (Val.var l)) (Closure.inst g m' (Val.var l)) do none
      let x : Val R := Val.var l
      let y : Val R := Val.var (l + 1)
      let bodyTy := Closure.inst g m (.pair x y)
      let tys₂ := (tys.push A).push (Closure.inst g B x)
      unless conv g tys₂ bodyTy (Closure.inst2 g body x y) (Closure.inst2 g body' x y) do none
      ty := Closure.inst g m acc
      acc := vSplit g q acc "z" m "x" "y" body
    | .absurd m, .absurd m', _ =>
      unless convTy g tys m m' do none
      ty := m
      acc := vAbsurd m acc
    | .ecase z m env bs, .ecase _ m' env' bs', ety@(.enum ls) =>
      let l := tys.size
      unless convTy g (tys.push ety) (Closure.inst g m (Val.var l)) (Closure.inst g m' (Val.var l)) do none
      unless bs.length == bs'.length do none
      for b in bs, b' in bs', k in [0:bs.length] do
        unless conv g tys (Closure.inst g m (.tag ls k)) (eval g env b) (eval g env' b') do none
      ty := Closure.inst g m acc
      acc := vEcase g z m acc env bs
    | .delim v P a b c h, .delim v' P' a' b' c' h', .desc l I =>
      unless v.equiv v' && conv g tys (delimMotiveTy l v I 1) P P' do none
      let (ta, tb, tc, th) := delimMethodTys g l I P 1
      unless conv g tys ta a a' && conv g tys tb b b' && conv g tys tc c c' && conv g tys th h h' do none
      ty := vApp g P acc
      acc := vDelim g v P a b c h acc
    | .ind l I D v P m i, .ind _ _ _ v' P' m' i', _ =>
      unless v.equiv v' && conv g tys (indMotiveTy g l v I D 1) P P' do none
      unless conv g tys (indMethodTy g l v I D P 1) m m' && conv g tys I i i' do none
      ty := vApp g (vApp g P i) acc
      acc := vInd g l I D v P m i acc
    | .scase l q I D v P m s i, .scase _ q' _ _ v' P' m' s' i', _ =>
      -- (K1) the quantity is compared too, though computation ignores it, as `split`'s
      unless conv g tys .qty q q' && v.equiv v' && conv g tys (indMotiveTy g l v I D 1) P P' do none
      unless conv g tys (scaseMethodTy g l I D P s q) m m' && sizeEq s s' && conv g tys I i i' do none
      ty := vApp g (vApp g P i) acc
      acc := vScase g l q I D v P m s i acc
    | .sfix l I D v P f s i, .sfix _ _ _ v' P' f' s' i', _ =>
      unless v.equiv v' && conv g tys (indMotiveTy g l v I D 1) P P' do none
      unless conv g tys (sfixFunTy g l I D P 1) f f' && sizeEq s s' && conv g tys I i i' do none
      ty := vApp g (vApp g P i) acc
      acc := vSfix g l I D v P f s i acc
    | .out, .out, .nu l I D i s _ =>
      ty := vInterp g l I D (nuFamilyAt l I D ((sizePred? s).getD .szInf)) i
      acc := vOut g acc
    | .down, .down, .ulift _ A =>
      ty := A
      acc := vDown acc
    | _, _, _ => none
  pure ty
  --|ex
  --| sorry
  --sol>

end

/-- **Subtyping** (stage 4f): `A ≤ B`. Sized inductive types are covariant in their size
(`μ^s ≤ μ^t` when `s ≤ t`), coinductive ones contravariant, functions contravariant in
the domain, and everything else is conversion. -/
partial def subTy (g : Globals R) (tys : Array (VTy R)) (A B : VTy R) : Bool :=
  let v := Val.var tys.size
  match whnf A, whnf B with
  | .mu l I D i s _, .mu l' I' D' i' s' _ =>
    l.equiv l' && sizeLe tys s s' && convTy g tys I I' && conv g tys (.desc l I) D D' && conv g tys I i i'
  | .nu l I D i s _, .nu l' I' D' i' s' _ =>
    l.equiv l' && sizeLe tys s' s && convTy g tys I I' && conv g tys (.desc l I) D D' && conv g tys I i i'
  | .pi _ _ q A₁ B₁ _, .pi _ _ q' A₂ B₂ _ =>
    (conv g tys .qty q q' || isProp g tys A) && subTy g tys A₂ A₁ &&
      subTy g (tys.push A₂) (Closure.inst g B₁ v) (Closure.inst g B₂ v)
  | .sigma _ q A₁ B₁ _, .sigma _ q' A₂ B₂ _ =>
    conv g tys .qty q q' && subTy g tys A₁ A₂ &&
      subTy g (tys.push A₁) (Closure.inst g B₁ v) (Closure.inst g B₂ v)
  | .sizeLt _, .size => true
  | .sizeLt s, .sizeLt t => sizeLe tys s t
  | _, _ => convTy g tys A B

end Wiz
