import Wiz.Elab.Zonk

/-!
# Finishing the info tree

During elaboration the info tree holds values and local contexts (`RawInfo`): recording
costs nothing then. At the end of a declaration, when the metavariables are as solved as
they will get, every entry is quoted and zonked into `Info`, whose terms no longer depend
on the elaborator's state (they can be memoised, cached, and printed later).
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-- The goal `ctx ⊢ ty`, quoted and zonked. -/
def goalView (ctx : LocalCtx R) (ty : VTy R) (userName : Option Name := none) : ElabM R (GoalView R) := do
  let g ← getGlobals
  let mut hyps : Array (Name × Term R × Option (Term R)) := #[]
  for l in [0:ctx.lvl] do
    let i := ctx.lvl - 1 - l
    let hty ← zonk l (quote g l ctx.types[i]!)
    let val ← if ctx.bound[i]! then pure none else some <$> zonk l (quote g l ctx.env[i]!)
    hyps := hyps.push (ctx.names[i]!, hty, val)
  pure { hyps, target := ← zonk ctx.lvl (quote g ctx.lvl ty), userName }

def RawInfo.finish : RawInfo R → ElabM R (Info R)
  | .ident i n isLocal ctx ty => do
    pure (.ident i n isLocal ctx.names (← zonk ctx.lvl (quote (← getGlobals) ctx.lvl ty)))
  | .term i ctx ty hole user => do pure (.term i (← goalView ctx ty user) hole)
  | .tactic i blk before after => do
    let views (gs : Array (LocalCtx R × VTy R)) := gs.mapM fun (c, t) => goalView c t
    pure (.tactic i blk (← views before) (← views after))
  | .decl i n ctx ty ann at_ => do pure (.decl i n ctx.names (← zonk ctx.lvl ty) ann at_)
  | .inst i ctx ty t => do
    pure (.inst i ctx.names (← zonk ctx.lvl (quote (← getGlobals) ctx.lvl ty)) (← zonk ctx.lvl t))
  | .done i => pure i

/-- The finished info tree of an elaborator state (dropping entries that fail to quote). -/
def finishInfos (st : ElabState R) : Array (Info R) :=
  let go : ElabM R (Array (Info R)) := st.infos.filterMapM fun r =>
    tryCatch (some <$> r.finish) (fun _ => pure none)
  match go.run' st with
  | .ok is => is
  | .error _ => #[]

/-- A goal as text: one hypothesis per line (`x : T`, `x : T := v`), then `⊢ T`. -/
def GoalView.show (g : GoalView R) (env : Option (Globals R) := none) : String := Id.run do
  let mut lines : Array String := #[]
  let mut names : List Name := []
  for (x, ty, v) in g.hyps do
    let val := match v with
      | some v => s!" := {v.pretty names env}"
      | none => ""
    lines := lines.push s!"{x} : {ty.pretty names env}{val}"
    names := x :: names
  lines := lines.push s!"⊢ {goalTarget (g.target.pretty names env)}"
  "\n".intercalate lines.toList

end Wiz
