import Wiz.Elab.Basic

/-!
# Pattern unification

`unify l t u` makes two values equal by solving metavariables, or fails.

The core case is a **flex** value, a neutral headed by an unsolved meta:

    ?m x₁ … xₙ  =?=  rhs

Miller's *pattern* fragment requires the spine `x₁ … xₙ` to be **distinct bound
variables**. Then the unique solution is `?m := fun x₁ … xₙ => rhs`, provided that

* `rhs` only mentions variables among `x₁ … xₙ` (a **scope check**), and
* `rhs` doesn't mention `?m` itself (an **occurs check**).

Both checks happen while **renaming** `rhs` from the current context (`cod`, `l`
variables) into the context of the solution (`dom`, `n` variables) with a *partial
renaming* that maps each `xᵢ` to its new position.

Reference: elaboration-zoo `03-holes`, which this follows closely.

## When unification approximates

Outside the pattern fragment a problem has no most general solution, and any answer
is a guess: the **first-order approximation** `?m a₁ … aₖ =?= f b₁ … bₙ` ↦
`?m := f b₁ … bₙ₋ₖ`, `aᵢ =?= bₙ₋ₖ₊ᵢ` (`unifyFirstOrder`), and `?e.op =?= e.op` ↦
`?e =?= e`. A guess is right when nothing else will determine the hole, and wrong when
something still to be elaborated would: the rule is to guess only when no more
information is coming. `ElabState.approx` (`Approx`) says which guesses are allowed.

| problem | example | Wiz | Lean 4 |
|---|---|---|---|
| pattern (distinct variables) | `?m x =?= x + 1` | solve exactly (`solve`) | the same (`processAssignment`) |
| variables, one repeated | `?m Γ i' =?= r i'` (`i'` in `Γ`) | solve without the repeated variable if the right side doesn't use it (pruning); else the first-order guess from the repeated variable on (`.default`) | not a pattern (`isDefEqPattern` wants distinct variables): first-order approximation, else postponed |
| flex-rigid, not a pattern | `?m ?A =?= M Nat` (`do`) | first-order guess (`.default`) | `isDefEq` with `foApprox` (the elaborator's configuration): the same guess |
| the same, in the "expected type first" pass of an application whose result type mentions placeholders of its explicit arguments | `?p ?k =?= ok (base + k)`, `?p`, `?k` the arguments `p`, `k` | no guess (`.none`): the speculative pass fails and is undone, the arguments decide, the result type is unified after them | the expected type is not propagated when the result type depends on explicit arguments (`propagateExpectedType`) |
| flex-flex, both holes over variables applied to the same number of other arguments without holes | `?r Γ (.bits 1) =?= ?r' Γ' x (.bits 1)` (`let x := if c then Hw.lit 1 1 else Hw.lit 1 0`) | the other arguments pairwise, then `?r Γ =?= ?r' Γ' x` (`.default`) | first-order (`isDefEqApp`) |
| flex-flex, both not patterns, different holes | `?r (.bits ?m) =?= ?r' (.bits 1)` (`Hw.cat (Hw.lit 1 1) d`) | postponed: the argument waits behind a placeholder for the other arguments (`inferApp`); still stuck after them, the first-order guess `?r := ?r'` as the last resort (`.last`) | postponed; postponed problems are retried at the end, with approximations |
| flex-flex, one side a pattern | `?a (f y) =?= ?b x` | solve the pattern side (either orientation) | the same |
| a structure-valued hole under projections, applied | `(?C).2.2.1 ?f ?g =?= C.2.2.1 f g` (`C.comp`) | `?C =?= C`, then the eliminations pairwise (`.default`; a guess: another structure with an equal field would do too) | `Category.comp ?C ?f ?g` is a constant applied: first-order (`isDefEqApp`) |
| the same hole on both sides | `?m a =?= ?m b` | unify the arguments (a guess too: `?m` may ignore them) | first-order (`isDefEqApp`), else postponed |

Wiz has no global queue of postponed problems: postponement is per application (an
argument whose check fails outside the pattern fragment, error code `non-pattern`, is
checked again after the others). Regression tests: group *elabfix*, "approximation: …"
and B4.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- (Given) `vElims`, but an elimination that doesn't fit the value (applying a number,
projecting a function) is an elaboration error, not a panic in the evaluator. Heuristic
solutions (the first-order approximation, which is untyped) can be ill-typed:
`?P 3 =?= Ex ?A ?Q` guesses `?Q := 3`, and `?Q 3` comes later. -/
def elimsChecked (m : Nat) (sol : Val R) (sp : Array (Elim R)) : ElabM R (Val R) := do
  let g ← getGlobals
  let mut v := sol
  for e in sp do
    -- (a glued value fits as what it unfolds to: `S T.El`, a structure type, applied to
    -- something is ill-typed, and the evaluator would panic on it)
    let shape ← match v, e with
      | .unfold .., .app _ | .unfold .., .fst | .unfold .., .snd
      | .lazyInd .., .app _ | .lazyInd .., .fst | .lazyInd .., .snd => pure (whnf v)
      | _, _ => pure v
    -- (on a constructor, `ind` is lazy for speed alone: what it computes must fit)
    let fits : Bool := match unlazyCon shape, e with
      | .neutral .., _ | .unfold .., _ | .lazyInd .., _ => true
      | .lam .., .app _ => true
      | .pair .., .fst | .pair .., .snd => true
      | _, .app _ | _, .fst | _, .snd => false
      | _, _ => true
    -- a failure of a guessed solution is never final (`unifySawMeta`, see `unifyGlued`)
    unless fits do
      modify fun s => { s with unifySawMeta := true }
      throwAt {} s!"the solution found for the hole ?m{m} is ill-typed (a guess that didn't fit)"
    v := vElims g v #[e]
  pure v

/-- **Exercise 3.1.** Unfold solved metavariables at the head of a value, repeatedly.
A neutral `?m sp` whose meta has a solution `v` becomes `v` with the eliminations of
`sp` applied (`vElims`). Anything else is returned unchanged. -/
partial def forceMeta (v : Val R) : ElabM R (Val R) := do
  --<sol
  match v with
  | .neutral (.mvar m) sp =>
    match (← lookupMeta m).solution with
    | some sol => forceMeta (← elimsChecked m sol sp)
    | none => pure v
  | _ => pure v
  --|ex
  --| sorry
  --sol>

/-- Unfold solved metavariables and glued definitions at the head: the value's shape,
ready to match on. (`forceMeta` keeps glued heads, for unification.) -/
partial def force (v : Val R) : ElabM R (Val R) := do
  match ← forceMeta v with
  | .unfold _ _ _ v => force v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => force v.get
  | v => pure v

/-- An equation stuck on a metavariable (its type or a side) computes once the
metavariable is solved: recompute it (`none` if nothing changed). -/
def recomputeEq? (v : Val R) : ElabM R (Option (Val R)) := do
  let .neutral (.eq A a b) sp := v | return none
  let solved (v : Val R) : ElabM R Bool := do
    match v with
    | .neutral (.mvar m) _ => return (← lookupMeta m).solution.isSome
    | _ => return false
  if (← solved A) || (← solved a) || (← solved b) then
    let g ← getGlobals
    return some (vElims g (vEq g (← forceMeta A) (← forceMeta a) (← forceMeta b)) sp)
  else return none

/-- A partial renaming from context `cod` (size `cod`) to context `dom` (size `dom`):
`ren` maps the levels of variables in the spine to their new levels; `downs` maps the
variables that occur in the spine lowered, as `down x` (see `invert`). -/
structure PRen where
  dom : Lvl
  cod : Lvl
  ren : Std.HashMap Lvl Lvl
  downs : Std.HashMap Lvl Lvl := {}

/-- Go under a binder on both sides. -/
def PRen.lift (p : PRen) : PRen :=
  { p with dom := p.dom + 1, cod := p.cod + 1, ren := p.ren.insert p.cod p.dom }

/-- **Exercise 3.2.** Invert a spine into a partial renaming. `gamma` is the size of the
current context. Every spine entry must be an application (`Elim.app v`) whose
argument forces to a bound variable with an empty spine (`.neutral (.local x) #[]`),
and a variable that occurs twice is left out of the renaming (the solution may not use
it). Otherwise throw (at `{}`), saying the problem is outside the pattern fragment.
The i-th spine variable maps to level i.

(Given) A lowered variable `down x` (`x : ULift A`) counts as a variable too: the
solution's i-th parameter `y` stands for `down x`, and `x` itself for `up y` (η for
`ULift`). Constructor fields with a lifted domain (`k : A → Proto` with `A : Type` in a
`Type 1` inductive) are stored as `fun h => k (down h)`, so unifying two such fields
meets `?k … (down h)`. -/
def invert (gamma : Lvl) (sp : Array (Elim R)) : ElabM R PRen := do
  --<sol
  let mut ren : Std.HashMap Lvl Lvl := {}
  let mut downs : Std.HashMap Lvl Lvl := {}
  let mut repeated : Array Lvl := #[]
  let mut dom := 0
  for e in sp do
    let .app v := e | throwAt {} "unification problem is outside the pattern fragment" "non-pattern"
    match ← force v with
    | .neutral (.local x) #[] =>
      -- a repeated variable can't be used by the solution (which occurrence?)
      if ren.contains x || downs.contains x then repeated := repeated.push x
      ren := ren.insert x dom
      dom := dom + 1
    | .neutral (.local x) #[.down] =>
      if ren.contains x || downs.contains x then repeated := repeated.push x
      downs := downs.insert x dom
      dom := dom + 1
    | _ => throwAt {} "unification problem is outside the pattern fragment" "non-pattern"
  pure { dom, cod := gamma, ren := repeated.foldl (·.erase ·) ren,
         downs := repeated.foldl (·.erase ·) downs }
  --|ex
  --| sorry
  --sol>

/-- **Exercise 3.3.** Rename a value into a term in the solution's context, checking
scope and occurs.

* A local `x` must be in `p.ren`; it becomes `.var (p.dom - ren[x] - 1)`. Otherwise
  throw a scope error.
* A meta `?m'` with `m' == m` fails the occurs check. Otherwise it is kept.
* Spines are renamed elimination by elimination. Binders go under `p.lift` with a
  fresh variable `Val.var p.cod` (twice for a `split` body). Force first!

(The structural types of stage 4b are already handled in the solution's style. Add
them when you get there.) -/
partial def rename (m : Nat) (p : PRen) (v : Val R) : ElabM R (Term R) := do
  -- (given) a glued value keeps its name in the solution
  if let .unfold n us sp _ ← forceMeta v then return ← rename m p (.neutral (.global n us) sp)
  -- (given) and glued induction on a numeral keeps its folded form
  if let .lazyInd lv I D w P mt i x sp val ← forceMeta v then
    -- (on a constructor, `ind` is lazy for speed alone: renamed as what it computes)
    if (whnf x matches .con _) then return ← rename m p val.get
    let t := Term.ind lv (← rename m p I) (← rename m p D) w (← rename m p P) (← rename m p mt) (← rename m p i) (← rename m p x)
    return ← sp.foldlM (fun t e => match e with
      | .app a => return .app t (← rename m p a)
      | .fst => pure (.fst t)
      | .snd => pure (.snd t)
      | .down => pure (.down t)
      | _ => pure t) t
  if let .natLit n ← force v then return .natLit n
  --<sol
  let goSp (h : Term R) (sp : Array (Elim R)) : ElabM R (Term R) :=
    sp.foldlM (init := h) fun acc e => match e with
      | .app a => return .app acc (← rename m p a)
      | .fst => pure (.fst acc)
      | .snd => pure (.snd acc)
      | .split q z mo x y b => do
        let mo' ← rename m p.lift (← instM mo (Val.var p.cod))
        let g ← getGlobals
        let b' ← rename m p.lift.lift (Closure.inst2 g b (Val.var p.cod) (Val.var (p.cod + 1)))
        pure (.split (← rename m p q) acc z mo' x y b')
      | .absurd mo => return .absurd (← rename m p mo) acc
      | .ecase z mo env bs => do
        let mo' ← rename m p.lift (← instM mo (Val.var p.cod))
        let g ← getGlobals
        let bs' ← bs.mapM fun b => rename m p (eval g env b)
        pure (.ecase z mo' acc bs')
      | .delim v P a b c h =>
        return .delim v (← rename m p P) (← rename m p a) (← rename m p b) (← rename m p c) (← rename m p h) acc
      | .ind l I D v P mt i =>
        return .ind l (← rename m p I) (← rename m p D) v (← rename m p P) (← rename m p mt) (← rename m p i) acc
      | .out => pure (.out acc)
      | .down => pure (.down acc)
      | .scase l q I D v P mt s i =>
        return .scase l (← rename m p q) (← rename m p I) (← rename m p D) v (← rename m p P) (← rename m p mt) (← rename m p s) (← rename m p i) acc
      | .sfix l I D v P f s i =>
        return .sfix l (← rename m p I) (← rename m p D) v (← rename m p P) (← rename m p f) (← rename m p s) (← rename m p i) acc
  match ← force v with
  | .neutral (.local x) sp =>
    match p.ren[x]? with
    | some x' => goSp (.var (p.dom - x' - 1)) sp
    | none => match p.downs[x]? with
      -- (given) `down x` is the parameter `y`; a bare `x` is `up y`
      | some x' =>
        let y : Term R := .var (p.dom - x' - 1)
        if sp[0]? matches some Elim.down then goSp y (sp.extract 1 sp.size) else goSp (.up y) sp
      | none => throwAt {} "a variable escapes the scope of the hole being solved (the hole was made outside a binder that its solution would mention; a type annotation on that binder may help)"
  | .neutral (.global n us) sp => goSp (.const n us) sp
  | .neutral (.eq A a b) sp => do goSp (.eq (← rename m p A) (← rename m p a) (← rename m p b)) sp
  | .neutral (.eqTy A B) sp => do goSp (.eqTy (← rename m p A) (← rename m p B)) sp
  | .neutral (.cast A B e t) sp => do
    goSp (.cast (← rename m p A) (← rename m p B) (← rename m p e) (← rename m p t)) sp
  | .neutral (.refl A a) sp => do goSp (.refl (← rename m p A) (← rename m p a)) sp
  | .neutral (.reflTy X) sp => do goSp (.reflTy (← rename m p X)) sp
  | .neutral (.transp A a P q b e) sp => do
    goSp (.transp (← rename m p A) (← rename m p a) (← rename m p P) (← rename m p q)
      (← rename m p b) (← rename m p e)) sp
  -- (P2) a suspended proof is evaluated for a solution (a normal form, which the kernel
  -- can check)
  -- within a step budget (`Budget`): a proof need not have one
  | .neutral (.prf env t) sp => do
    let g ← getGlobals
    match g.budget with
    | some _ => rename m p (vElims g (eval g env t) sp)
    | none =>
      -- (the monadic read-back is a pure function of the state: it runs inside the budget)
      let st ← get
      let (r, used) := Budget.run g.proofSteps fun b =>
        let g' := { g with budget := some b }
        match (rename m p (vElims g' (eval g' env t) sp)).run { st with globals := g' } with
        | .ok (tm, st') => (some tm, some st', none)
        | .error e => (none, none, some e)
      if used > g.proofSteps then throwAt {} (Budget.message g.proofSteps)
      match r with
      | (some tm, some st', _) => set { st' with globals := g }; pure tm
      | (_, _, some e) => throw e
      | _ => throwAt {} "internal error: read-back of a proof"
  | .neutral (.mvar m') sp =>
    if m == m' then throwAt {} s!"occurs check: the hole ?m{m} would have to contain itself (the type would be infinite, as when a function is applied to itself)"
    else
      -- **pruning**: another hole applied to distinct variables, some of them out of the
      -- solution's scope (`?A n x` in a `match` branch, solving `?T n`): it can't depend
      -- on those, so it becomes a new hole over the others
      match ← pruneArgs? p sp with
      | some keep =>
        let m'' := (← get).metas.size
        let e' ← lookupMeta m'
        -- (its arity: the kept arguments among the ones for the context's variables)
        let arity := (keep.filter (· < e'.arity)).size
        modify fun s => { s with metas := s.metas.push { info := e'.info, desc := "a pruned hole", arity } }
        let n := sp.size
        let body : Term R := keep.foldl (fun t i => .app t (.var (n - i - 1))) (.mvar m'')
        let sol := (List.range n).foldl (fun t i => Term.lam s!"x{n - i - 1}" t) body
        solveMeta m' (eval (← getGlobals) [] sol)
        goSp (.mvar m'') (keep.filterMap fun i => sp[i]?)
      | none => goSp (.mvar m') sp
  | .sort l => pure (.sort l)
  | .pi x bi q a b s =>
    return .pi x bi (← rename m p q) (← rename m p a) (← rename m p.lift (← instM b (Val.var p.cod))) s
  | .lam x b => return .lam x (← rename m p.lift (← instM b (Val.var p.cod)))
  | .sigma x q a b s =>
    return .sigma x (← rename m p q) (← rename m p a) (← rename m p.lift (← instM b (Val.var p.cod))) s
  | .pair a b => return .pair (← rename m p a) (← rename m p b)
  | .unit l => pure (.unit l)
  | .tt => pure .tt
  | .empty l => pure (.empty l)
  | .qty => pure .qty
  | .qlit r => pure (.qlit r)
  | .size => pure .size
  | .sizeLt s => return .sizeLt (← rename m p s)
  | .szInf => pure .szInf
  | .szSuc s => return .szSuc (← rename m p s)
  | .cocon x => return .cocon (← rename m p x)
  | .scofix l I D A f s i a =>
    return .scofix l (← rename m p I) (← rename m p D) (← rename m p A) (← rename m p f) (← rename m p s) (← rename m p i) (← rename m p a)
  | .enum ls => pure (.enum ls)
  | .tag ls i => pure (.tag ls i)
  | .desc l I => return .desc l (← rename m p I)
  | .dret i => return .dret (← rename m p i)
  | .darg q S D => return .darg (← rename m p q) (← rename m p S) (← rename m p D)
  | .drec q j D => return .drec (← rename m p q) (← rename m p j) (← rename m p D)
  | .dhrec q H j D => return .dhrec (← rename m p q) (← rename m p H) (← rename m p j) (← rename m p D)
  | .mu l I D i s h => return .mu l (← rename m p I) (← rename m p D) (← rename m p i) (← rename m p s) (← renameHint h)
  | .nu l I D i s h => return .nu l (← rename m p I) (← rename m p D) (← rename m p i) (← rename m p s) (← renameHint h)
  | .con x => return .con (← rename m p x)
  | .ulift k l A => return .ulift k l (← rename m p A)
  | .up a => return .up (← rename m p a)
  | .natLit n => return .natLit n
  | .unfold n us sp _ => goSp (.const n us) sp
  | .lazyInd _ _ _ _ _ _ _ _ _ v => rename m p v.get
  | .coit l I D S st i s =>
    return .coit l (← rename m p I) (← rename m p D) (← rename m p S) (← rename m p st) (← rename m p i) (← rename m p s)
where
  /-- For a spine of applications whose variable arguments are distinct, some of them out
  of `p`'s scope: the positions of the other arguments. `none` if nothing is to be pruned
  (or it isn't such a spine). -/
  pruneArgs? (p : PRen) (sp : Array (Elim R)) : ElabM R (Option (Array Nat)) := do
    let mut keep : Array Nat := #[]
    let mut seen : Std.HashSet Lvl := {}
    for e in sp, i in [0:sp.size] do
      let .app a := e | return none
      match ← force a with
      | .neutral (.local x) #[] =>
        if seen.contains x then return none
        seen := seen.insert x
        if p.ren.contains x || p.downs.contains x then keep := keep.push i
      -- another argument stays (renaming checks it; `?r Γ x (.bits 1)`, the implicit
      -- signal type of `Hw.lit 1 0` in a branch, loses the branch's `x`)
      | _ => keep := keep.push i
    if keep.size == sp.size then return none
    return some keep
  renameHint : Option (Name × List Level × List (Val R)) → ElabM R (Option (Name × List Level × List (Term R)))
    | some (n, us, as) => return some (n, us, ← as.mapM (rename m p))
    | none => pure none
  --|ex
  --| sorry
  --sol>

/-- **Exercise 3.4.** Solve `?m sp =?= rhs` in a context of size `gamma`: invert the
spine, rename `rhs`, wrap the result in `sp.size` lambdas, and evaluate it in the
empty environment to get the solution. Record it with `solveMeta`. -/
def solve (gamma : Lvl) (m : Nat) (sp : Array (Elim R)) (rhs : Val R) : ElabM R Unit := do
  --<sol
  let p ← invert gamma sp
  let body ← rename m p rhs
  -- a spine variable that is a binder unification went under keeps that binder's name
  let hints := (← get).binderNames
  let nameOf (j : Nat) : Name := match sp[j]? with
    | some (.app (.neutral (.local lv) #[])) => match hints.find? (·.1 == lv) with
      | some (_, x) => x
      | none => s!"x{j}"
    | _ => s!"x{j}"
  let sol := (List.range sp.size).foldl (fun t i => Term.lam (nameOf (sp.size - i - 1)) t) body
  solveMeta m (eval (← getGlobals) [] sol)
  --|ex
  --| sorry
  --sol>

/-- After a failed attempt at unification (the state is back to what it was before it, as
`ElabM` undoes a failed computation's state), keep what unification learnt meanwhile:
whether it met a metavariable, and the failures it recorded. They are true whatever the
attempt did. They come with the error (`throwAt` records the state where it threw); an
error without a state may have met anything. -/
def keepLearnt (e : ElabError R) : ElabM R Unit :=
  modify fun cur => match e.state? with
    | some s => { cur with unifySawMeta := cur.unifySawMeta || s.unifySawMeta,
                           unifyFails := s.unifyFails, unifyFailCount := s.unifyFailCount }
    | none => { cur with unifySawMeta := true }

/-- Did the failed computation that threw `e` meet a metavariable? -/
def ElabError.sawMeta (e : ElabError R) : Bool := (e.state?.map (·.unifySawMeta)).getD true

/-- Unification met an unsolved metavariable. -/
def noteMeta : ElabM R Unit := modify fun s => { s with unifySawMeta := true }

/-- Run `x` with a fresh "met a metavariable" flag: its result, and whether `x` met one
(merged back into the flag afterwards). On failure, the error and the flag; the state is
the one before `x`, with what it learnt (`keepLearnt`). -/
def trackMeta {α : Type} (x : ElabM R α) : ElabM R (Except (ElabError R) α × Bool) := do
  let saw := (← get).unifySawMeta
  modify fun s => { s with unifySawMeta := false }
  let (r, here) ← tryCatch (do let a ← x; pure (.ok a, (← get).unifySawMeta))
    (fun e => do keepLearnt e; pure (.error e, e.sawMeta))
  modify fun s => { s with unifySawMeta := saw || here }
  pure (r, here)

/-- The term with its solved metavariables (term and level) replaced by their solutions;
`none` if it mentions an unsolved one. -/
partial def Term.instSolved (t : Term R) : ElabM R (Option (Term R)) := (go t).run
where
  go (t : Term R) : OptionT (ElabM R) (Term R) := do
    match t with
    | .mvar m =>
      let some v := (← OptionT.lift (lookupMeta m)).solution | failure
      go (quote (← OptionT.lift getGlobals) 0 v)
    | t => t.mapChildrenM (fun l => do
        let l ← OptionT.lift (instLevel l)
        if l.hasMVar then failure else pure l) (fun _ c => go c)

/-- Two quoted values (in a context of size `l`) with their free variables renamed in the
order they first occur (as `var (k + 2⁴⁰ + j)` under `k` binders, for the `j`-th). Unifying
values without metavariables is untyped and only asks which variables are equal, so a
renaming of the free variables doesn't change whether it succeeds; this way the same
comparison in another context gives the same key: say under the fresh variables of the
body of a Church-encoded `Ex`, which unfolding it compares once more. -/
partial def canonKey (l : Lvl) (t u : Term R) : Term R × Term R :=
  let go2 := do let t' ← go 0 t; let u' ← go 0 u; pure (t', u')
  (go2.run {}).1
where
  go (k : Nat) : Term R → StateM (Std.HashMap Nat Nat) (Term R)
    | .var i => do
      if i < k then return .var i
      let x := l + k - 1 - i
      let m ← get
      let j ← match m[x]? with
        | some j => pure j
        | none => do set (m.insert x m.size); pure m.size
      pure (.var (k + (1 <<< 40) + j))
    | t => t.mapChildrenM pure (fun k' c => go (k + k') c)

/-- The failure cache (see `ElabState.unifyFails`): two glued applications of the same
definition `n` in a context of size `l`, quoted (`canonKey`), with solved metavariables
replaced by their solutions, when neither mentions an unsolved one. -/
def failKey? (l : Lvl) (n : Name) (t u : Val R) : ElabM R (Option (UInt64 × Term R × Term R)) := do
  let g ← getGlobals
  let some qt ← (quote g l t).instSolved | return none
  let some qu ← (quote g l u).instSolved | return none
  let (kt, ku) := canonKey l qt qu
  pure (some (hash n, kt, ku))

def lookupFail (key : UInt64 × Term R × Term R) : ElabM R (Option String) := do
  let (h, qt, qu) := key
  let some es := (← get).unifyFails[h]? | return none
  pure ((es.find? (fun (t', u', _) => t' == qt && u' == qu)).map (·.2.2))

def recordFail (key : UInt64 × Term R × Term R) (msg : String) : ElabM R Unit :=
  modify fun s =>
    let (h, qt, qu) := key
    -- (bounded: start afresh now and then)
    let (fails, count) := if s.unifyFailCount ≥ 4096 then ({}, 0) else (s.unifyFails, s.unifyFailCount)
    { s with unifyFails := fails.insert h ((qt, qu, msg) :: (fails.getD h [])), unifyFailCount := count + 1 }

/-- Run `k` under a binder named `x` at level `l` (see `ElabState.binderNames`). -/
def withBinderName (l : Lvl) (x : Name) (k : ElabM R α) : ElabM R α := do
  if x == "_" || x.isEmpty then return ← k
  let saved := (← get).binderNames
  modify fun s => { s with binderNames := (l, x) :: saved }
  let a ← k
  modify fun s => { s with binderNames := saved }
  pure a

/-- Does level metavariable `m` occur in `l`? -/
def Level.occurs (m : Nat) : Level → Bool
  | .mvar m' => m == m'
  | .succ l => Level.occurs m l
  | .max a b | .imax a b => Level.occurs m a || Level.occurs m b
  | _ => false

/-- **Exercise 4.1.** Unify two universe levels. Instantiate solved metas first
(`instLevel`). Then:

* if the levels are already equivalent (`Level.equiv`), succeed;
* a lone metavariable `?u` against any level not containing it: assign it;
* `a+1 =?= b+1`: unify `a` and `b`;
* otherwise fail with a "universe level mismatch" error.

This is deliberately incomplete. `max ?u ?v =?= 1` has several solutions, and Lean
postpones such constraints instead of failing (see the optional exercises). -/
partial def unifyLevel (a b : Level) : ElabM R Unit := do
  -- (given) a failure that met a metavariable may not be final (see `unifyGlued`)
  if (← instLevel a).hasMVar || (← instLevel b).hasMVar then noteMeta
  --<sol
  let a ← instLevel a
  let b ← instLevel b
  if a.equiv b then return
  match a, b with
  | .mvar m, l | l, .mvar m =>
    if Level.occurs m l then throwAt {} s!"universe level mismatch: {a} vs {b}"
    modify fun s => { s with levelMetas := s.levelMetas.set! m (some l) }
  | .succ a', .succ b' => unifyLevel a' b'
  | _, _ => throwAt {} s!"universe level mismatch: {a} vs {b}"
  --|ex
  --| sorry
  --sol>


/-- `v` evaluated again with the holes solved since (as `zonk` does, then `eval`): a
cast computed while a hole in its types was unsolved is stuck, and may compute now, as
the kernel will compute it. `none` if nothing changed. -/
partial def reevalStale? (l : Lvl) (v : Val R) : ElabM R (Option (Val R)) := do
  let g ← getGlobals
  let env : Env R := ((List.range l).map fun i => Val.var i).reverse
  let rec inst (k : Lvl) (t : Term R) : ElabM R (Term R) := do
    let rec spine : Term R → Array (Term R) → Term R × Array (Term R)
      | .app f a, acc => spine f (#[a] ++ acc)
      | t, acc => (t, acc)
    let (h, args) := spine t #[]
    match h with
    | .mvar m =>
      match (← lookupMeta m).solution with
      | some sol =>
        let envk : Env R := ((List.range k).map fun i => Val.var i).reverse
        inst k (quote g k (args.foldl (fun f a => vApp g f (eval g envk a)) sol))
      | none => return (← args.mapM (inst k)).foldl .app (.mvar m)
    | _ =>
      let h' ← h.mapChildrenM instLevel (fun d c => inst (k + d) c)
      return (← args.mapM (inst k)).foldl .app h'
  let q := quote g l v
  let v' := eval g env (← inst l q)
  if quote g l v' == q then return none
  return some v'

/-- η for a projected hole: `?m x… .1` (or `.2`) means `?m x…` is a pair, so it is one:
solve `?m := fun x… => (?a x…, ?b x…)` with two new holes (exact, not a guess; Agda
η-expands holes of record type the same way). Then `?m x… .1` is `?a x…`, a pattern
again: `?q.1 =?= y` (from an equation at a product type computed to its components)
solves `?a := y`. `false` if the spine isn't applications followed by a projection. -/
def etaProjected (m : Nat) (sp : Array (Elim R)) : ElabM R Bool := do
  let k := (sp.toList.takeWhile (· matches .app _)).length
  let isProj : Bool := match sp[k]? with
    | some .fst | some .snd => true
    | _ => false
  unless isProj do return false
  unless (← lookupMeta m).solution.isNone do return false
  let info := (← lookupMeta m).info
  let fresh (desc : String) : ElabM R Nat := do
    let id := (← get).metas.size
    modify fun s => { s with metas := s.metas.push { info, desc, arity := k } }
    pure id
  let a ← fresh "a component of a pair"
  let b ← fresh "a component of a pair"
  let args (h : Nat) : Term R := (List.range k).foldl (fun t i => .app t (.var (k - i - 1))) (.mvar h)
  let sol := (List.range k).foldl (fun t i => Term.lam s!"x{k - i - 1}" t) (Term.pair (args a) (args b))
  solveMeta m (eval (← getGlobals) [] sol)
  pure true

mutual

/-- **Exercise 3.5.** Unify two values in a context of `l` variables, throwing on
failure. Force both sides first, then:

* `sort`/`sort`: `unifyLevel`.
* `pi`/`pi`: equal binder info and quantities, unify domains and codomains.
* `lam`/`lam`, and η: `lam`/anything and anything/`lam`, as in `conv`.
* Two rigid neutrals with the same head: unify the spines. For globals, "the same
  head" means the same name, with the levels unified pairwise.
* Two flex neutrals with the same meta: unify the spines (a simple approximation).
* A flex neutral against anything: `solve`.
* Anything else fails.

**Exercise 4.8** (stage 4b): `sigma`, `pair` (with η: `(a, b) =?= t` unifies `a` with
`t.1` and `b` with `t.2`), `unit`, `tt`, `empty`; and the other eliminations in
`unifySpine`. -/
partial def unify (l : Lvl) (t u : Val R) : ElabM R Unit := do
  -- (kernel-eval: `ind` on a constructor is lazy for speed alone; the elaborator sees what
  -- it computes, which may be glued: `K.beq (.cons x xs) (.cons y ys)` against
  -- `Bool.and ?a ?b` compares the two `Bool.and`s, as before `ind` was lazy there)
  if ← unifyGlued l (unlazyCon (← forceMeta t)) (unlazyCon (← forceMeta u)) then return ()
  -- numerals: compare two directly, or else look one step inside (`vNatView`)
  let g ← getGlobals
  let (t, u) ← match ← force t, ← force u with
    | .natLit n, .natLit m => if n == m then return () else throwAt {} s!"{n} ≠ {m}"
    -- only against a constructor: a metavariable is solved with the numeral itself (as
    -- a constructor view it isn't a literal, and native arithmetic on it falls back to
    -- the unary definitions)
    | t@(.natLit _), u@(.con _) => pure (vNatView g t, u)
    | t@(.con _), u@(.natLit _) => pure (t, vNatView g u)
    | t, u => pure (t, u)
  -- an equation against something that isn't one: it may compute further
  let isEq (v : Val R) : Bool := v matches .neutral (.eq ..) _
  if isEq t != isEq u then
    if let some t' ← recomputeEq? t then return ← unify l t' u
    if let some u' ← recomputeEq? u then return ← unify l t u'
  -- a stuck `cast A B e x` (computed while a hole in `A` or `B` was unsolved) against
  -- something else: if `A` and `B` are now the same (equal without solving anything),
  -- it is `x` (regularity; evaluated again, it would compute to `x`)
  let isCast (v : Val R) : Bool := v matches .neutral (.cast ..) #[]
  if isCast (← force t) != isCast (← force u) then
    if isCast (← force t) then
      if let some t' ← reevalStale? l (← force t) then return ← unify l t' u
    else
      if let some u' ← reevalStale? l (← force u) then return ← unify l t u'
  -- a failure that met a metavariable may not be final (see `unifyGlued`)
  if (← force t) matches .neutral (.mvar _) _ || (← force u) matches .neutral (.mvar _) _ then noteMeta
  --<sol
  match ← force t, ← force u with
  | .sort a, .sort b => unifyLevel a b
  | .pi x bi q a b _, .pi x' bi' q' a' b' _ =>
    unless bi == bi' do throwAt {} "implicit vs explicit binder mismatch"
    unify l q q'
    unify l a a'
    withBinderName l (if x == "_" then x' else x) do
      unify (l + 1) (← instM b (Val.var l)) (← instM b' (Val.var l))
  | .sigma _ q a b _, .sigma _ q' a' b' _ =>
    unify l q q'
    unify l a a'
    unify (l + 1) (← instM b (Val.var l)) (← instM b' (Val.var l))
  | .pair a b, .pair a' b' => unify l a a'; unify l b b'
  | .pair a b, t'@(.neutral ..) => unify l a (vFst t'); unify l b (vSnd t')
  | t'@(.neutral ..), .pair a b => unify l (vFst t') a; unify l (vSnd t') b
  | .unit u, .unit u' | .empty u, .empty u' => unifyLevel u u'
  | .tt, .tt | .qty, .qty | .size, .size | .szInf, .szInf => pure ()
  | .szSuc a, .szSuc b | .cocon a, .cocon b | .sizeLt a, .sizeLt b => unify l a b
  | .scofix u I D A f s i a, .scofix u' I' D' A' f' s' i' a' =>
    unifyLevel u u'
    for (x, y) in [(I, I'), (D, D'), (A, A'), (f, f'), (s, s'), (i, i'), (a, a')] do unify l x y
  | .qlit a, .qlit b => unless a == b do throwAt {} "quantity mismatch"
  | .enum ls, .enum ls' => unless ls.length == ls'.length do throwAt {} "enumeration size mismatch"
  | .tag _ i, .tag _ j => unless i == j do throwAt {} "tag mismatch"
  | .desc u I, .desc u' I' => unifyLevel u u'; unify l I I'
  | .dret i, .dret j => unify l i j
  | .darg q S D, .darg q' S' D' | .drec q S D, .drec q' S' D' => unify l q q'; unify l S S'; unify l D D'
  | .dhrec q H j D, .dhrec q' H' j' D' => unify l q q'; unify l H H'; unify l j j'; unify l D D'
  | .mu u I D i s _, .mu u' I' D' i' s' _ | .nu u I D i s _, .nu u' I' D' i' s' _ =>
    unifyLevel u u'; unify l I I'; unify l D D'; unify l i i'; unify l s s'
  | .con x, .con y => unify l x y
  | .ulift _ u A, .ulift _ u' A' => unifyLevel u u'; unify l A A'
  | .up a, .up b => unify l a b
  | .up a, t'@(.neutral ..) => unify l a (vDown t')
  | t'@(.neutral ..), .up a => unify l (vDown t') a
  | .coit u I D S st i s, .coit u' I' D' S' st' i' s' =>
    unifyLevel u u'
    for (a, b) in [(I, I'), (D, D'), (S, S'), (st, st'), (i, i'), (s, s')] do unify l a b
  | .lam x b, .lam x' b' =>
    withBinderName l (if x == "_" then x' else x) do unify (l + 1) (← instM b (Val.var l)) (← instM b' (Val.var l))
  | .lam x b, t' => withBinderName l x do unify (l + 1) (← instM b (Val.var l)) (← vAppM t' (Val.var l))
  | t', .lam x b => withBinderName l x do unify (l + 1) (← vAppM t' (Val.var l)) (← instM b (Val.var l))
  | .neutral (.mvar m) sp, .neutral (.mvar m') sp' =>
    if m == m' then unifySpine l sp sp' else
    if ← etaProjected m sp then return ← unify l t u
    if ← etaProjected m' sp' then return ← unify l t u
    -- (if the left spine isn't a pattern, the right one may be)
    tryCatch (solve l m sp (.neutral (.mvar m') sp')) fun e => do
      if e.code != "non-pattern" then throw e
      tryCatch (solve l m' sp' (.neutral (.mvar m) sp)) fun e' => do
        if e'.code != "non-pattern" then throw e'
        -- neither is a pattern: two holes over variables, applied to the same number of
        -- other arguments (`?r Γ (.bits 1) =?= ?r' Γ' x (.bits 1)`, a family of types at an
        -- index): those pairwise, and the holes over the variables (a guess, as Lean's
        -- first-order approximation; not in the speculative pass)
        if (← get).approx == .none then throw e'
        let varPrefix (sp : Array (Elim R)) : ElabM R Nat := do
          let mut k := 0
          for el in sp do
            match el with
            | .app a => match ← forceMeta a with
              | .neutral (.local _) #[] => k := k + 1
              | _ => break
            | _ => break
          pure k
        let k ← varPrefix sp
        let k' ← varPrefix sp'
        let rest := sp.extract k sp.size
        let rest' := sp'.extract k' sp'.size
        unless !rest.isEmpty && rest.size == rest'.size && rest.all (· matches .app _) && rest'.all (· matches .app _) do
          throw e'
        -- (before the last resort, only at indices without holes: `?r (.bits ?m) =?= ?r' (.bits 1)`
        -- waits for the other arguments, which may fix `?r`; see "When unification approximates")
        let g ← getGlobals
        let closed (sp : Array (Elim R)) : ElabM R Bool := sp.allM fun el => match el with
          | .app a => return (← (quote g l a).instSolved).isSome
          | _ => pure false
        unless (← get).approx == .last || ((← closed rest) && (← closed rest')) do throw e'
        let s ← get
        try
          unifySpine l rest rest'
          unify l (.neutral (.mvar m) (sp.extract 0 k)) (.neutral (.mvar m') (sp'.extract 0 k'))
        catch _ => set s; throw e'
  | .neutral (.mvar m) sp, t' =>
    if ← etaProjected m sp then unify l t u else solve l m sp t'
  | t', .neutral (.mvar m) sp =>
    if ← etaProjected m sp then unify l t u else solve l m sp t'
  | .neutral h sp, .neutral h' sp' =>
    -- (P2) two proofs with only applications and projections after them are equal, with
    -- nothing to compare (as in `convNe`): their spines need not agree (a suspended
    -- proof on one side, a `transp` applied to a phantom tail's argument on the other).
    -- This is what makes two values that differ only in an erased proof field equal
    -- where the type isn't seen (an opaque type, 13b), e.g. two closed words.
    let lazy := (← getGlobals).lazyProofs
    let isProof : Head R → Bool
      | .refl .. | .reflTy _ | .transp .. | .prf .. => true
      | h => lazy && proofHead h
    let onProofs (sp : Array (Elim R)) : Bool := sp.all fun
      | .app _ | .fst | .snd | .down => true
      | _ => false
    if isProof h && isProof h' && onProofs sp && onProofs sp' then pure () else
    unifyHead l h h'; unifySpine l sp sp'
  | _, _ => throwAt {} "rigid mismatch"
  --|ex
  --| sorry
  --sol>

/-- Glued values (given). Returns `true` if it solved the problem:

* the same global head on both sides: unify the spines (on failure, undo and let the
  caller unfold);
* an unsolved meta against a glued value: solve it with the value as it is, so the
  solution keeps the definition's name; outside the pattern fragment, try the
  **first-order approximation** `?m a₁ … aₖ =?= f b₁ … bₙ` ↦ `aᵢ =?= bₙ₋ₖ₊ᵢ` and
  `?m =?= f b₁ … bₙ₋ₖ` (for the trailing non-variable `aᵢ`; this is how `?M ?A` meets
  `TacticM Nat`). -/
partial def unifyGlued (l : Lvl) (t u : Val R) : ElabM R Bool := do
  let attempt (x : ElabM R Unit) : ElabM R Bool := do
    let s ← get
    try x; pure true catch e => set s; keepLearnt e; pure false
  match t, u with
  | .lazyInd _ _ _ _ _ _ _ x _ _, .lazyInd _ _ _ _ _ _ _ y _ _ =>
    -- (on a constructor, `ind` is lazy for speed alone: compared by what it computes)
    if (whnf x matches .con _) || (whnf y matches .con _) then return false
    let g ← getGlobals
    pure (quote g l t == quote g l u)
  | .unfold n us sp v, .unfold n' us' sp' v' =>
    let same := n == n' && us.length == us'.length && sp.size == sp'.size
    if same then
      if ← attempt (do for a in us, b in us' do unifyLevel a b
                       unifySpine l sp sp') then return true
    -- (the same comparison, without metavariables, failed before: it fails again)
    let key? ← if same then failKey? l n t u else pure none
    if let some key := key? then
      if let some msg ← lookupFail key then throwAt {} msg
    -- lazy delta: unfold the later definition by one step (both, if they are the same),
    -- and compare again
    let g ← getGlobals
    -- (recursors compute: unfold them first; otherwise the later definition)
    let isRec (x : Name) : Bool := x.endsWith ".rec" || x.endsWith ".casesOn" || x.endsWith ".casesOnA" || x.endsWith ".scasesOn"
    let first := isRec n || (!isRec n' && g.height n ≥ g.height n')
    let step := if n == n' then unify l v.get v'.get
      else if first then unify l v.get u else unify l t v'.get
    match ← trackMeta step with
    | (.ok (), _) => return true
    | (.error err, sawMeta) =>
      -- The failure is final: no other order of unfolding is tried. Unfolding is
      -- confluent, so unfolding the other side first meets the same normal forms; trying
      -- both orders at every glued layer is exponential in the number of layers (a wrong
      -- proof about `⋆`, each four definitions deep, took minutes to be rejected; a
      -- wrong proof about `Int.ofPair`, a `Nat.sub` five layers deep, 17 s, wiz-reals S1).
      -- (Trying the other order once per path, when the failure met a metavariable, made
      -- no file of lib/, examples/, selfhost/ or two dogfooding projects check that
      -- doesn't check without it, and was slower.) A failure that met no metavariable is
      -- also remembered (`recordFail`).
      unless sawMeta do
        if let some key := key? then recordFail key err.msg
      -- (with the state as it is now, which has what was learnt)
      throw { err with state? := some (← get) }
  | .neutral (.mvar m) sp, v@(.unfold ..) | v@(.unfold ..), .neutral (.mvar m) sp =>
    noteMeta
    if ← attempt (solve l m sp v) then return true
    if (← get).approx == .none then return false
    unifyFirstOrder l m sp v
  -- a hole against a rigid neutral, outside the pattern fragment:
  -- * the same projection on both sides (`?e.op =?= e.op`): unify what is projected;
  -- * applications (`?M ?A =?= m A`): the first-order approximation.
  -- (Heuristics like Lean's, tried only when pattern unification fails.)
  | .neutral (.mvar m) sp, v@(.neutral h' sp') | v@(.neutral h' sp'), .neutral (.mvar m) sp =>
    noteMeta
    -- (flex-flex: only as the last resort, see "When unification approximates")
    if let .mvar m' := h' then
      if m' == m || (← get).approx != .last then return false
    if ← isPattern sp then return false
    -- a non-linear spine of variables (`?m Γ x` with `x` in `Γ`): solve it pruning the
    -- repeated variable if the right-hand side doesn't need it; else it is a guess
    if ← isVarSpine sp then
      if ← attempt (solve l m sp v) then return true
    if (← get).approx == .none then return false
    -- the same eliminations after the hole's own arguments, projections among them
    -- (`(?C).2.2.2.1 ?f ?g =?= C.2.2.2.1 f g`, a field of a structure-valued hole applied
    -- to arguments): unify what is projected, `?C =?= C`, and then the eliminations
    match sp.findIdx? (!· matches .app _) with
    | some k =>
      let rest := sp.extract k sp.size
      if rest.size > sp'.size then return false
      let rest' := sp'.extract (sp'.size - rest.size) sp'.size
      let sameKind : Elim R × Elim R → Bool
        | (.app _, .app _) | (.fst, .fst) | (.snd, .snd) => true
        | _ => false
      unless (rest.zip rest').all sameKind do return false
      attempt do
        unify l (.neutral (.mvar m) (sp.extract 0 k)) (.neutral h' (sp'.extract 0 (sp'.size - rest.size)))
        unifySpine l rest rest'
    | none =>
      if !sp'.isEmpty && sp'.all (· matches .app _) then
        unifyFirstOrder l m sp v
      else pure false
  | _, _ => pure false
where
  -- distinct variables (Miller's patterns)
  isPattern (sp : Array (Elim R)) : ElabM R Bool := do
    let mut seen : Std.HashSet Lvl := {}
    for e in sp do
      match e with
      | .app a => match ← forceMeta a with
        | .neutral (.local x) #[] | .neutral (.local x) #[.down] =>
          if seen.contains x then return false
          seen := seen.insert x
        | _ => return false
      | _ => return false
    pure true
  -- variables, possibly repeated
  isVarSpine (sp : Array (Elim R)) : ElabM R Bool := do
    for e in sp do
      match e with
      | .app a => match ← forceMeta a with
        | .neutral (.local _) #[] | .neutral (.local _) #[.down] => pure ()
        | _ => return false
      | _ => return false
    pure true

/-- The first-order approximation (see `unifyGlued`). -/
partial def unifyFirstOrder (l : Lvl) (m : Nat) (sp : Array (Elim R)) (v : Val R) : ElabM R Bool := do
  -- the rigid side: a glued definition, or a variable (or other head) applied to arguments
  let (rebuild, sp') : (Array (Elim R) → ElabM R (Val R)) × Array (Elim R) ← match v with
    | .unfold n us sp' _ => pure ((fun pre => do
        let g ← getGlobals
        pure (pre.foldl (fun acc e => match e with
          | .app b => vApp g acc b
          | _ => acc) (eval g [] (.const n us)))), sp')
    | .neutral h sp' => pure ((fun pre => pure (.neutral h pre)), sp')
    | _ => return false
  let appArg : Elim R → Option (Val R)
    | .app a => some a
    | _ => none
  let some args := sp.mapM appArg | pure false
  let some args' := sp'.mapM appArg | pure false
  -- the arguments after the longest prefix of distinct bound variables (a repeated
  -- variable starts the arguments to match: `?m Γ x =?= r x` with `x` in `Γ`)
  let mut k := 0
  let mut seen : Std.HashSet Lvl := {}
  for a in args do
    match ← forceMeta a with
    | .neutral (.local x) #[] =>
      if seen.contains x then break
      seen := seen.insert x
      k := k + 1
    | _ => break
  let j := args.size - k
  if j == 0 || j > args'.size then return false
  let s ← get
  try
    for a in args.extract k args.size, b in args'.extract (args'.size - j) args'.size do
      unify l a b
    let head ← rebuild (sp'.extract 0 (sp'.size - j))
    solve l m (sp.extract 0 k) head
    pure true
  catch e =>
    set s; keepLearnt e
    pure false

/-- Rigid heads: the same variable, the same global (levels unified), or the same
stuck observational construct (components unified). Any two proofs are equal. -/
partial def unifyHead (l : Lvl) (h h' : Head R) : ElabM R Unit := do
  let lazy := (← getGlobals).lazyProofs
  let isProof : Head R → Bool
    | .refl .. | .reflTy _ | .transp .. | .prf .. => true
    -- (P2) with `lazyProofs`, a stuck cast between propositions is a proof too
    | h => lazy && proofHead h
  match h, h' with
  | .global n us, .global n' us' =>
    unless n == n' && us.length == us'.length do throwAt {} "rigid mismatch"
    for a in us, b in us' do unifyLevel a b
  | .eq A a b, .eq A' a' b' =>
    unify l A A'
    let s ← get
    try unify l a a'; unify l b b'
    catch err =>
      -- an equation that was stuck on a metavariable (its type, say) may compute now:
      -- `succ ?a = succ ?b` at a solved `Nat` is `?a = ?b`. Compare the computed forms,
      -- if either changed.
      set s; keepLearnt err
      let g ← getGlobals
      let v := vEq g (← force A) a b
      let v' := vEq g (← force A') a' b'
      let same (w : Val R) (A a b : Val R) : Bool :=
        quote g l w == quote g l (.neutral (.eq A a b) #[])
      if same v A a b && same v' A' a' b' then throw err
      unify l v v'
  | .eqTy A B, .eqTy A' B' => unify l A A'; unify l B B'
  | .cast A B _ t, .cast A' B' _ t' => unify l A A'; unify l B B'; unify l t t'
  | _, _ =>
    unless (isProof h && isProof h') || h.equiv h' do throwAt {} "rigid mismatch"

partial def unifySpine (l : Lvl) (sp sp' : Array (Elim R)) : ElabM R Unit := do
  unless sp.size == sp'.size do throwAt {} "spine length mismatch"
  let g ← getGlobals
  for e in sp, e' in sp' do
    match e, e' with
    | .app a, .app b => unify l a b
    | .fst, .fst | .snd, .snd => pure ()
    | .split q _ m _ _ b, .split q' _ m' _ _ b' =>
      unify l q q'
      unify (l + 1) (← instM m (Val.var l)) (← instM m' (Val.var l))
      unify (l + 2) (Closure.inst2 g b (Val.var l) (Val.var (l + 1)))
        (Closure.inst2 g b' (Val.var l) (Val.var (l + 1)))
    | .absurd m, .absurd m' => unify l m m'
    | .ecase _ m env bs, .ecase _ m' env' bs' =>
      unify (l + 1) (← instM m (Val.var l)) (← instM m' (Val.var l))
      unless bs.length == bs'.length do throwAt {} "spine mismatch"
      for b in bs, b' in bs' do unify l (eval g env b) (eval g env' b')
    | .delim v P a b c h, .delim v' P' a' b' c' h' =>
      unifyLevel v v'
      for (x, y) in [(P, P'), (a, a'), (b, b'), (c, c'), (h, h')] do unify l x y
    | .ind u I D v P mt i, .ind u' I' D' v' P' mt' i' =>
      unifyLevel u u'; unifyLevel v v'
      for (x, y) in [(I, I'), (D, D'), (P, P'), (mt, mt'), (i, i')] do unify l x y
    | .out, .out | .down, .down => pure ()
    | .scase u q I D v P f s i, .scase u' q' I' D' v' P' f' s' i' =>
      unifyLevel u u'; unifyLevel v v'
      for (x, y) in [(q, q'), (I, I'), (D, D'), (P, P'), (f, f'), (s, s'), (i, i')] do unify l x y
    | .sfix u I D v P f s i, .sfix u' I' D' v' P' f' s' i' =>
      unifyLevel u u'; unifyLevel v v'
      for (x, y) in [(I, I'), (D, D'), (P, P'), (f, f'), (s, s'), (i, i')] do unify l x y
    | _, _ => throwAt {} "spine mismatch"

end

end Wiz
