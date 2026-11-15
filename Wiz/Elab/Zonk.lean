import Wiz.Elab.Unify

/-!
# Zonking

Before a declaration goes to the kernel, every solved metavariable is replaced by its
solution ("zonking", a GHC term). A solved meta applied to arguments,
`?m a₁ … aₙ`, is evaluated and quoted back, which β-reduces the solution's lambdas
away. That matters: the kernel can't infer a type for `(fun x => …) a`.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- The metavariables still occurring in a term. -/
partial def Term.mvars (t : Term R) : Array Nat :=
  (go t |>.run #[]).2
where
  go : Term R → StateM (Array Nat) Unit
    | .mvar m => modify (·.push m)
    | t => t.forChildren (fun _ => pure ()) (fun _ c => go c)

/-- **Exercise 3.6.** Replace solved metas in `t`, a term in a context of `l` variables.

Split `t` into a head and arguments. If the head is a *solved* meta, evaluate
`solution a₁ … aₙ` (arguments evaluated in the environment of variables
`[Val.var (l-1), …, Val.var 0]`), quote the result back at `l`, and zonk *that*, since
solutions can mention metas solved later. Otherwise rebuild the term, zonking every
subterm (under binders at `l + 1`) and instantiating level metas in `sort` and
`const` (`instLevel`). Unsolved metas stay. -/
partial def zonk (l : Lvl) (t : Term R) : ElabM R (Term R) := do
  --<sol
  let (h, args) := spine t #[]
  match h with
  | .mvar m =>
    match (← lookupMeta m).solution with
    | some sol =>
      let g ← getGlobals
      let env : Env R := (List.range l).map fun i => Val.var i
      let env := env.reverse
      let v := args.foldl (fun f a => vApp g f (eval g env a)) sol
      zonk l (quote g l v)
    | none => return (← args.mapM (zonk l)).foldl .app (.mvar m)
  | .const "OfNat.ofNat" _ =>
    let args ← args.mapM (zonk l)
    let h ← h.mapChildrenM instLevel (fun _ c => pure c)
    -- (7f) a numeral whose type turned out to be the `builtin nat` type (it was elaborated
    -- at a hole: `@OfNat.ofNat ?T n ?i`) is the literal again, as if it had been written
    -- at `Nat`: kernel terms, native arithmetic, `rfl` and erasure see what they always did
    if let #[A, .natLit n, i] := args then
      if i.mvars.isEmpty then
        if let some N := (← getGlobals).builtins.lookup "nat" then
          let g ← getGlobals
          let env : Env R := ((List.range l).map fun i => Val.var i).reverse
          let isNat := match A with
            | .const c _ => c == N
            | _ => match whnf (eval g env A) with
              | .mu _ _ _ _ _ (some (T, _, _)) => T == N
              | _ => false
          if isNat then
            match whnf (eval g env (args.foldl .app h)) with
            | .natLit m => if m == n then return .natLit n
            | _ => pure ()
    return args.foldl .app h
  | _ =>
    let h' ← h.mapChildrenM instLevel (fun k c => zonk (l + k) c)
    -- a `Π`/`Σ`'s (or a `ULift`'s) sort that stays unknown becomes a hole, which the sorts
    -- pass fills before the kernel (`Decl.withSorts`)
    let unknown (k : Level) : Level := if k.hasMVar then .hole else k
    let h' := match h' with
      | .pi x bi q a b σ => .pi x bi q a b ⟨unknown σ.dom, unknown σ.cod⟩
      | .sigma x q a b σ => .sigma x q a b ⟨unknown σ.dom, unknown σ.cod⟩
      | .ulift k l a => .ulift (unknown k) l a
      | _ => h'
    return (← args.mapM (zonk l)).foldl .app h'
where
  spine : Term R → Array (Term R) → Term R × Array (Term R)
    | .app f a, acc => spine f (#[a] ++ acc)
    | t, acc => (t, acc)
  --|ex
  --| sorry
  --sol>

/-- (7e) Replace only the solved *instance* holes in `t` (`MetaEntry.isInst`), leaving
every other hole as it is. The declared type of a `def` gets this before its body is
checked: the kernel's native arithmetic can't see through a solved instance hole, while
zonking the rest (the implicit arguments, say `Lens.GetPut ?S ?A l`) would let the
type's equation compute further than as written (to a Σ of field equations at a
structure), and `rfl` would then be proved field by field instead of as `refl` of its
sides. -/
partial def zonkInsts (l : Lvl) (t : Term R) : ElabM R (Term R) := do
  let (h, args) := spine t #[]
  match h with
  | .mvar m =>
    let e ← lookupMeta m
    match e.solution, e.isInst with
    | some sol, true =>
      let g ← getGlobals
      let env : Env R := ((List.range l).map fun i => Val.var i).reverse
      let v := args.foldl (fun f a => vApp g f (eval g env a)) sol
      zonkInsts l (quote g l v)
    | _, _ => return (← args.mapM (zonkInsts l)).foldl .app (.mvar m)
  | _ =>
    let h' ← h.mapChildrenM pure (fun k c => zonkInsts (l + k) c)
    return (← args.mapM (zonkInsts l)).foldl .app h'
where
  spine : Term R → Array (Term R) → Term R × Array (Term R)
    | .app f a, acc => spine f (#[a] ++ acc)
    | t, acc => (t, acc)

/-- Does the term mention a level metavariable? -/
partial def Term.hasLevelMVar (t : Term R) : Bool :=
  (go t |>.run false).2
where
  go (t : Term R) : StateM Bool Unit :=
    t.forChildren (fun l => modify (· || l.hasMVar)) (fun _ c => go c)

/-- The level metavariables occurring in a term (after `zonk`, the unsolved ones). -/
partial def Term.levelMVars (t : Term R) : Array Nat :=
  (go t |>.run #[]).2
where
  goL : Level → StateM (Array Nat) Unit
    | .mvar m => modify (·.push m)
    | .succ l => goL l
    | .max a b | .imax a b => do goL a; goL b
    | _ => pure ()
  go (t : Term R) : StateM (Array Nat) Unit :=
    t.forChildren goL (fun _ c => go c)

/-- Fail if `t` still contains unsolved metas, pointing at the first one's hole. -/
def ensureNoMVars (t : Term R) (info : SourceInfo := {}) : ElabM R Unit := do
  if let some m := t.mvars[0]? then
    let e ← lookupMeta m
    let hint :=
      if e.desc == "_" then ": nothing determines this hole; write the term, or give more type information"
      else if e.desc.startsWith "the type of " && !e.desc.startsWith "the type of this" &&
          !e.desc.startsWith "the type of a" then
        s!"; annotate it, as in ({e.desc.drop 12} : T)"
      else if e.desc.startsWith "implicit argument " then
        s!"; give it by name, as in f ({e.desc.drop 18} := …), or add a type ascription"
      else ""
    throwAt e.info s!"could not infer {e.desc}{hint}" ErrorCode.unsolvedHole
  if t.hasLevelMVar then
    -- point at the constant whose universe parameter it is, if known
    let ls := (← get).levelMetas
    let infos := (← get).levelMetaInfo
    let mut first : Option Nat := none
    for m in t.levelMVars do
      if (ls[m]?.join).isNone then first := some m; break
    if let some m := first then
      if let some (i, desc) := infos[m]? then
        if desc != "" && i.stop != 0 then
          throwAt i s!"could not infer {desc}; add a universe parameter or annotation" ErrorCode.unsolvedLevel
    throwAt info "could not infer a universe level; add a universe parameter or annotation" ErrorCode.unsolvedLevel

end Wiz
