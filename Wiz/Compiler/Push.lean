import Wiz.Core.Check

/-!
# Direct calls out of reverted arguments (compiled equations)

A structurally recursive definition's compiled equations (`Decl.impl`, derived from its
value by `deriveImpl` in `Elab/Command.lean`) are its value with each induction hypothesis
replaced by the direct call it stands for. The kernel checks that they agree with the
value, one conversion per constructor (`checkImplAgrees`). A nested split reverts the
hypotheses (their types mention the field it splits), so in the derived term a call can
be an argument of an inner `casesOn`, and compiled code would compute it before the case,
whether the branch taken uses it or not. `pushCalls` moves such arguments into the
branches of the inner split, before erasure (`eraseDecl`): a rewrite of the compiler's,
like erasure, done on the checked term. Its result is type-checked again (it must have
the declared type, or the unrewritten term is compiled), but not checked to agree with the
checked term: that it does is by construction (an argument moved into the branches of a
case, at the value of the scrutinee there), and trusted like erasure. In branch `c` the
call is on `c fields` where its type needs the scrutinee, otherwise on the scrutinee
itself.
-/

namespace Wiz.Push

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

def piInfos : Term R → List (Name × BinderInfo × Term R)
  | .pi x bi _ A b _ => (x, bi, A) :: piInfos b
  | _ => []

def peel : Nat → Term R → Option (List Name × Term R)
  | 0, t => some ([], t)
  | k + 1, .lam x b => do let (xs, r) ← peel k b; pure (x :: xs, r)
  | _, _ => none

/-- The rewrite gives up (`fn` and the reason are for debugging). -/
def pbail {α : Type} (_fn _why : String) : Option α := none

/-- Under `k` binders (`Π`s if `pis`, else `λ`s), apply `f`. -/
def underBinders (pis : Bool) : Nat → (Term R → Option (Term R)) → Term R → Option (Term R)
  | 0, f, t => f t
  | k + 1, f, .pi x bi q A b sn => if pis then do pure (.pi x bi q A (← underBinders pis k f b) sn) else none
  | k + 1, f, .lam x b => if !pis then do pure (.lam x (← underBinders pis k f b)) else none
  | _, _, _ => none

/-- The next `m` binders (`Π`s if `pis`, else `λ`s): the first `keep` stay, each later one,
number `p`, is instantiated with `call p` (a term in the context of the kept ones). -/
partial def instBinders (pis : Bool) (m keep : Nat) (call : Nat → Term R) (t : Term R) : Option (Term R) :=
  go 0 t
where
  go (p : Nat) (t : Term R) : Option (Term R) :=
    if p == m then some t else
    match t, pis with
    | .pi x bi q A b sn, true =>
      if p < keep then do pure (.pi x bi q A (← go (p + 1) b) sn) else go (p + 1) (b.instantiateAt 0 (call p))
    | .lam x b, false =>
      if p < keep then do pure (.lam x (← go (p + 1) b)) else go (p + 1) (b.instantiateAt 0 (call p))
    | _, _ => none

/-- Does `t` mention the definition `fn`, or a recursor (a hypothesis the derivation left
as the recursor)? -/
partial def mentions (fn : Name) (t : Term R) : Bool := match t with
  | .const c _ => c == fn || c.endsWith ".rec" || c.endsWith ".recN"
  | t => (t.forChildren (m := StateM Bool) (fun _ => pure ()) (fun _ c => modify (· || mentions fn c)) |>.run false).2

/-- `(λ rs. f …) a…`, a hypothesis that was applied: β-reduced (each `r` occurs once in
the call, so nothing is computed twice). The kernel can't infer an applied `λ`. -/
partial def betaCalls (fn : Name) (t : Term R) : Term R :=
  let t := Id.run <| t.mapChildrenM pure (fun _ c => pure (betaCalls fn c))
  match t with
  -- `let ih := λ rs. f …` (a hypothesis given its index equation's proof, `rewriteRecCalls`):
  -- substituted, so that each use is a call, not a closure
  | .letE _ _ _ v@(.lam ..) b => if mentions fn v then betaCalls fn (b.instantiateAt 0 v) else t
  | _ =>
  match t.spine with
  | (h@(.lam ..), args@(_ :: _)) =>
    if mentions fn h then
      let rec red : Term R → List (Term R) → Term R
        | .lam _ b, a :: as => red (b.instantiateAt 0 a) as
        | b, as => as.foldl .app b
      betaCalls fn (red h args)
    else t
  | _ => t

partial def pushHere (g : Globals R) (fn : Name) (t : Term R) : Option (Term R) := do
  let (.const K us', args) := t.spine | pure t
  if !K.endsWith ".casesOn" then return t
  let T' := String.ofList (K.toList.take (K.length - 8))
  let some Td := g.find? T' | pure t
  let some descD := g.find? (T' ++ ".desc") | pure t
  let some kd := g.find? K | pure t
  let a := (piInfos kd.type).length
  let extras := args.drop a
  let nPush := (extras.reverse.takeWhile (mentions fn)).length
  if nPush == 0 then return t
  let nΔ := (piInfos descD.type).length
  let nΞ := (piInfos Td.type).length - nΔ
  -- mode B (index unification): the index equation's proof comes first
  -- (its motive starts with the equation: `λ ξ x. Π (e : … = …). …`)
  let rec motiveHasEq : Nat → Term R → Bool
    | 0, .pi _ _ _ (.eq ..) _ _ => true
    | k + 1, .lam _ b => motiveHasEq k b
    | _, _ => false
  let modeB := nΞ > 0 && !K.endsWith ".casesOnN" && motiveHasEq (nΞ + 1) args[nΔ]! && !extras.isEmpty
  let eqArg := if modeB then extras.take 1 else []
  let extras := if modeB then extras.drop 1 else extras
  unless (extras.take (extras.length - nPush)).all (!mentions fn ·) do pbail fn "not trailing"
  let m := extras.length
  let keep := m - nPush
  let pushed := extras.drop keep
  let nc := a - nΔ - 2 - nΞ
  let y := args[a - 1]!
  let Δargs := args.take nΔ
  let us := us'.dropLast
  let nE := if modeB then 1 else 0
  -- the motive `λ ξ x. [Π e.] Π r₁ … rₘ. G` (`casesOnN`: no `λ`s): the last `nPush`
  -- binders get the calls
  let nondep := K.endsWith ".casesOnN"
  let nL := if nondep then 0 else nΞ + 1
  let (mxs, mb0) ← peel nL args[nΔ]!
  let (eBinder, mb) ← if modeB then match mb0 with
      | .pi x bi q A b sn => pure (some (x, bi, q, A, sn), b)
      | _ => pbail fn "motive eq"
    else pure (none, mb0)
  -- (when the hypothesis' type does not mention the scrutinee, as for a non-dependent
  -- result type, the call stays on the scrutinee itself: no object is rebuilt)
  let rec domains : Nat → Nat → Term R → Option (List Bool)
    | 0, _, _ => some []
    | k + 1, p, .pi _ _ _ A b _ => do
      let rest ← domains k (p + 1) b
      -- (the domain mentions the scrutinee, its indices or the equation)
      pure (if p < keep then rest else (List.range (nL + nE)).any (fun i => A.hasVar (p + i)) :: rest)
    | _, _, _ => pbail fn "pis"
  let dep ← domains m 0 mb
  if dep.any id && (nΞ > 0 || modeB || nondep) then pbail fn "dependent indexed"
  -- each call over the scrutinee and the arguments kept reverted (the inner split
  -- re-binds them, at the types refined by the constructor): in the context
  -- `…, ŷ, r̂₀ … r̂_{keep-1}`
  let kept := extras.take keep
  unless kept.all (· matches .var _) do pbail fn "kept not var"
  let close (c : Term R) : Term R :=
    kept.zipIdx.foldl (fun acc (r, j) => acc.abstract (r.lift (1 + j))) (c.abstract y)
  let rec instPis : Nat → Nat → Term R → Option (Term R)
    | 0, _, b => some b
    | k + 1, p, .pi x bi q A b sn =>
      if p < keep then do pure (.pi x bi q A (← instPis k (p + 1) b) sn)
      else
        -- `…, ŷ, r̂…` to `…, ξ, x, [e], r…`: ŷ is `x` (`casesOnN`: no `x`; the call
        -- does not depend on it, dep = false)
        let c := close pushed[p - keep]!
        let c := if nondep then c.instantiateAt keep (y.lift keep)
          else (c.lift nΞ (keep + 1))
        -- (the binders of the calls before it are gone: it sits right after the kept ones)
        instPis k (p + 1) (b.instantiateAt 0 (c.lift nE keep))
    | _, _, _ => pbail fn "pis2"
  let mb' ← instPis m 0 mb
  let mb' := match eBinder with
    | some (x, bi, q, A, sn) => Term.pi x bi q A mb' sn
    | none => mb'
  let motive' : Term R := mxs.foldr .lam mb'
  let ctors := ((piInfos kd.type).drop (nΔ + 1)).take nc |>.map fun (mn, _, _) => String.ofList (mn.toList.drop 2)
  let mut methods' : List (Term R) := []
  for c in ctors, mt in (args.drop (nΔ + 1)).take nc do
    let some cd := g.find? (ctorConst T' c) | pbail fn "ctor"
    let F := (piInfos cd.type).length - nΔ
    let (fns, mb1) ← peel (F + nE) mt
    let mb := mb1
    let ctorTm : Term R := ((Δargs.map fun (a : Term R) => a.lift F) ++ (List.range F).reverse.map Term.var).foldl .app
      (.const (ctorConst T' c) us)
    -- the call for pushed argument `p`, right after the kept binders, with `nDeps` binders
    -- (the solution rule's re-bound fields) between the equation and them
    let callAt (nDeps p : Nat) : Term R :=
      let yHere : Term R := if dep[p - keep]! then ctorTm else y.lift F
      (((close pushed[p - keep]!).lift F (keep + 1)).instantiateAt keep (yHere.lift keep)).lift (nE + nDeps) keep
    let body' ← match instBinders false m keep (callAt 0) mb with
      | some b => pure b
      | none =>
        -- the solution rule: `cast (Π deps. Π rs. M) (Π deps'. Π rs. M') e (λ deps. λ rs. b) deps…`
        match mb with
        -- an impossible case: `absurd (Π rs. M) e`
        | .absurd ty prf => do pure (.absurd (← instBinders true m keep (callAt 0) ty) prf)
        | _ =>
          -- another shape (the solution rule's cast, whose proof mentions the reverted
          -- telescope too): apply it to the kept arguments and the calls, so the calls are
          -- computed in this branch only. `λ r₀ … r_{keep-1}. mb r₀ … calls…`
          let applied : Term R := (List.range m).foldl (fun acc p =>
              .app acc (if p < keep then .var (keep - 1 - p) else callAt 0 p))
            (mb.lift keep)
          pure ((List.range keep).foldr (fun _ b => .lam "r" b) applied)
    methods' := methods' ++ [fns.foldr .lam body']
  pure ((Δargs ++ [motive'] ++ methods' ++ (args.drop (nΔ + 1 + nc)).take (a - nΔ - 1 - nc) ++
    eqArg ++ extras.take keep).foldl .app (.const K us'))

/-- A nested split reverts the hypotheses (their types mention the field it splits), so
in the derived term a direct call can be an argument of an inner `casesOn`, which compiled
code would compute before the case (whether the branch taken uses it or not). Move such
trailing arguments into the inner split's branches: in the motive the call is on the
motive's variable, in branch `c` on `c fields` (the value of the scrutinee there). Only
for a scrutinee type without indices; otherwise `none`. -/
partial def pushCalls (g : Globals R) (fn : Name) (t : Term R) : Option (Term R) := do
  -- (a split this can't see through, a cast of the solution rule say, keeps its
  -- arguments: the call is then computed before that split)
  let t := (pushHere g fn t).getD t
  t.mapChildrenM pure (fun _ c => pushCalls g fn c)

/-- In branch `c` of a split on a variable `y` (of a type without indices), the
constructor rebuilt from the branch's fields, `T.c Δ f₁ … fₙ`, is `y` itself. A
derived implementation has such terms where the value's catch-all or variable pattern
names the scrutinee (the recursor's method sees only the fields); compiled code would
rebuild the object. Only for `casesOn`; the result is checked again in `eraseDecl`
(for an indexed family the constructor's index must be the scrutinee's). -/
partial def reuseScrutinee (g : Globals R) (depth : Nat) (t : Term R) : Term R :=
  let t := Id.run <| t.mapChildrenM pure (fun k c => pure (reuseScrutinee g (depth + k) c))
  match t.spine with
  | (.const K us', args) =>
    if !K.endsWith ".casesOn" then t else
    let T' := String.ofList (K.toList.take (K.length - 8))
    match g.find? T', g.find? (T' ++ ".desc"), g.find? K with
    | some Td, some descD, some kd =>
      let nΔ := (piInfos descD.type).length
      let a := (piInfos kd.type).length
      -- (an indexed family: the kernel's check in `eraseDecl` decides whether the
      -- constructor's index is the scrutinee's)
      let _ := Td
      if args.length < a then t else
      let nc := a - nΔ - 2
      let y := args[a - 1]!
      if !(y matches .var _) then t else
      let Δargs := args.take nΔ
      let us := us'.dropLast
      let ctors := ((piInfos kd.type).drop (nΔ + 1)).take nc |>.map fun (mn, _, _) => String.ofList (mn.toList.drop 2)
      let methods := ctors.zip ((args.drop (nΔ + 1)).take nc) |>.map fun (c, mt) =>
        match g.find? (ctorConst T' c) with
        | some cd =>
          let F := (piInfos cd.type).length - nΔ
          match peel F mt with
          | some (fns, b) =>
            let ctorTm : Term R := ((Δargs.map fun (a : Term R) => a.lift F) ++ (List.range F).reverse.map Term.var).foldl .app
              (.const (ctorConst T' c) us)
            -- (as the value has it: constructors unfold, `con (tag, fields…)`)
            let D := depth + F
            let env : Env R := (List.range D).reverse.map Val.var
            let ctorNf := quote g D (eval g env ctorTm)
            fns.foldr .lam (replace ctorNf (y.lift F) 0 (replace ctorTm (y.lift F) 0 b))
          | none => mt
        | none => mt
      (Δargs ++ [args[nΔ]!] ++ methods ++ args.drop (nΔ + 1 + nc)).foldl .app (.const K us')
    | _, _, _ => t
  | _ => t
where
  /-- `b` with `old` (a term at depth 0) replaced by `new` -/
  replace (old new : Term R) (depth : Nat) (b : Term R) : Term R :=
    if b == old.lift depth then new.lift depth
    else Id.run <| b.mapChildrenM pure (fun k c => pure (replace old new (depth + k) c))

end Wiz.Push
