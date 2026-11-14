import Wiz.Elab.Zonk

/-!
# Type classes: tabled instance resolution

A class is a structure registered with `class`; an instance is a global registered
with `instance`, whose type is `{Δ} → [C₁ …] → … → C args`. An instance-implicit
argument `[x : C A]` becomes a hole and an **instance problem**, solved as soon as
its type is known enough, or at the end of the command.

Resolution follows Selsam, Ullrich & de Moura, *Tabled Typeclass Resolution* (2020),
the algorithm of Lean 4, in a simplified form:

* a **generator** node holds a goal and the instances still to try on it;
* applying an instance leaves its instance arguments as subgoals; a **consumer** node
  holds the subgoals still to solve, with the elaborator state of its partial solution;
* each goal, normalised to a **key** (metavariables numbered in order), has a table
  entry with its answers so far and the consumers waiting for them. A subgoal that
  is already in the table is not solved again: the consumer waits for the existing
  generator's answers, including future ones. That is what makes resolution
  terminate on cycles (`Coe A B → Coe B A → …`) and share work on diamonds.

Answers must be complete terms (no holes). Output parameters (`outParam`) are replaced
by fresh holes before resolution, so they are not part of the key, and are unified
with the answer afterwards. Instances are tried in order: local instances, then by
priority, then latest first.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

structure Answer (R : Type) where
  val : Term R
  ty : Term R

structure Consumer (R : Type) where
  /-- the key of the goal this consumer will produce answers for -/
  key : String
  goal : Term R
  goalTy : VTy R
  /-- the subgoals left: holes and their types -/
  subgoals : List (Term R × VTy R)
  state : ElabState R

structure Generator (R : Type) where
  key : String
  goal : Term R
  goalTy : VTy R
  state : ElabState R
  /-- instances to try (a term and its type), in order -/
  candidates : Array (Term R × VTy R)
  next : Nat := 0

inductive Waiter (R : Type) where
  | root
  | consumer (c : Consumer R)

structure Entry (R : Type) where
  waiters : Array (Waiter R) := #[]
  answers : Array (Answer R) := #[]

structure SynthState (R : Type) where
  gens : Array (Generator R) := #[]
  resume : Array (Consumer R × Answer R) := #[]
  table : Std.HashMap String (Entry R) := {}
  result : Option (Answer R) := none
  steps : Nat := 0

/-- A type, with solved holes filled in, for messages. -/
def showType (ctx : LocalCtx R) (ty : VTy R) : ElabM R String := do
  let g ← getGlobals
  pure ((← zonk ctx.lvl (quote g ctx.lvl ty)).pretty ctx.names (some g))

/-- The class of a type, if it is an application of one (kept by glued evaluation). -/
def classOf? (ty : VTy R) : ElabM R (Option (ClassInfo × List Level × Array (Val R))) := do
  let .unfold n us sp _ ← forceMeta ty | return none
  let some info := (← get).classes.find? (·.name == n) | return none
  let args := sp.filterMap fun | .app a => some a | _ => none
  return some (info, us, args)

/-- Number the metavariables of a term in order of occurrence. -/
partial def canonMVars (t : Term R) : StateM (Array Nat) (Term R) := do
  match t with
  | .mvar m =>
    let ms ← get
    match ms.idxOf? m with
    | some i => pure (.mvar (1000000000 + i))
    | none => set (ms.push m); pure (.mvar (1000000000 + ms.size))
  | t => t.mapChildrenM pure (fun _ c => canonMVars c)

/-- The table key of a goal type. -/
def goalKey (ctx : LocalCtx R) (ty : VTy R) : ElabM R String := do
  let t ← zonk ctx.lvl (quote (← getGlobals) ctx.lvl ty)
  let t' : Term R := (canonMVars t).run' #[] |>.run
  pure (t'.pretty [])

/-- The instances to try on a goal of class `cls`: local instances, then global ones by
priority, latest first. -/
def candidates (ctx : LocalCtx R) (cls : Name) : ElabM R (Array (Term R × VTy R)) := do
  let mut out := #[]
  -- local instances: hypotheses whose type is an application of the class
  for j in [0:ctx.lvl] do
    if let some (info, _, _) ← classOf? ctx.types[j]! then
      if info.name == cls then out := out.push (.var j, ctx.types[j]!)
  let s ← get
  let insts := (s.instances.toList.zipIdx.filter fun (i, _) => i.cls == cls && !i.isDefault).toArray
  let sorted := insts.qsort fun (a, i) (b, j) => a.priority > b.priority || (a.priority == b.priority && i > j)
  for (inst, _) in sorted do
    if let some d := s.globals.find? inst.name then
      let us ← d.levelParams.mapM fun _ => freshLevelMeta
      out := out.push (.const inst.name us, eval s.globals [] (d.type.instLevels d.levelParams us))
  pure out

def mkGenerator (ctx : LocalCtx R) (key : String) (goal : Term R) (goalTy : VTy R) : ElabM R (Generator R) := do
  let cands ← match ← classOf? goalTy with
    | some (info, _, _) => candidates ctx info.name
    | none => pure #[]
  pure { key, goal, goalTy, state := ← get, candidates := cands }

/-- (Given) Does each complete solution of an instance's non-instance argument have the
type the instance's binder gives it? Unification is untyped, so matching the instance's
conclusion can pick an ill-kinded solution: `ShareLet (r a) (r b)` against `S T.El`
(first order: `r := S`, `a := T.El`) although `r : T → Type` and `S : (T → Type) → Type`.
Such an instance doesn't apply. Only a definite mismatch counts: arguments still holes
(or whose types are), and arguments whose type the kernel can't infer, are left to the
rest of elaboration and the kernel. -/
def instArgsWellTyped (ctx : LocalCtx R) (args : Array (Term R × VTy R)) : ElabM R (Option String) := do
  let g ← getGlobals
  let mut checks : Array (Term R × Term R) := #[]
  for (m, dom) in args do
    let t ← zonk ctx.lvl m
    if !t.mvars.isEmpty || t.hasLevelMVar then continue
    let A ← zonk ctx.lvl (quote g ctx.lvl (← forceMeta dom))
    if !A.mvars.isEmpty || A.hasLevelMVar then continue
    checks := checks.push (t, A)
  if checks.isEmpty then return none
  -- the variables' types with the holes solved since they were bound
  let mut tys : Array (VTy R) := #[]
  for v in ctx.types.reverse do
    let j := tys.size
    let t ← zonk j (quote g j (← forceMeta v))
    tys := tys.push (eval g (ctx.env.drop (ctx.lvl - j)) t)
  let kctx : Ctx R := { globals := g, env := ctx.env, names := ctx.names,
                        qtys := ctx.names.map fun _ => QPoly.const QuantitySyntax.explicitDefault,
                        types := tys.toList.reverse, lvl := ctx.lvl }
  let infer := (← get).kernelInfer
  for (t, A) in checks do
    match infer kctx t with
    | .ok ty => unless convTy g tys (eval g ctx.env A) ty do
        return some s!"{t} : {quote g ctx.lvl ty}, expected {A}"
    -- (no answer: a term only checkable, such as a constructor `.bits 8`, or no kernel to
    -- ask outside a command; left to the kernel's check of the whole declaration)
    | .error _ => pure ()
  return none

/-- **Exercise 7.1.** Apply an instance (`e : ty`) to the goal: fill each of its leading
Π binders with a fresh hole (the instance-implicit ones are the subgoals, in order),
then unify the conclusion with the goal type and the goal with the application.
Stop at the conclusion without unfolding it (match on `forceMeta`, not `force`).
Throws if it doesn't apply. -/
partial def applyInstance (ctx : LocalCtx R) (goal : Term R) (goalTy : VTy R) (e : Term R) (ty : VTy R) :
    ElabM R (List (Term R × VTy R)) := do
  --<sol
  let mut t := e
  let mut ty := ty
  let mut subgoals := #[]
  let mut args := #[]
  repeat
    match ← forceMeta ty with
    | .pi x bi _ dom cod _ =>
      let m ← freshMeta ctx s!"instance argument {x}"
      if bi == .instImplicit then subgoals := subgoals.push (m, dom) else args := args.push (m, dom)
      t := .app t m
      ty ← instM cod (← evalIn ctx m)
    | _ => break
  unify ctx.lvl goalTy ty
  if let some why ← instArgsWellTyped ctx args then
    throwAt {} s!"instance does not apply: an ill-typed argument ({why})"
  unify ctx.lvl (← evalIn ctx goal) (← evalIn ctx t)
  pure subgoals.toList
  --|ex
  --| sorry
  --sol>

/-- Tabled resolution of `ty` in `ctx`: a complete term of that type, or `none`. -/
partial def synthInstance (ctx : LocalCtx R) (ty : VTy R) : ElabM R (Option (Term R)) := do
  let some (info, us, args) ← classOf? ty | return none
  -- output parameters become fresh holes
  let mut args' := #[]
  for a in args, out in info.outParams ++ List.replicate args.size false do
    if out then args' := args'.push (← evalIn ctx (← freshMeta ctx "an output parameter"))
    else args' := args'.push a
  let g ← getGlobals
  let goalTy := args'.foldl (vApp g) (eval g [] (.const info.name us))
  let goal ← freshMeta ctx "an instance"
  let key ← goalKey ctx goalTy
  let saved ← get
  let mut ss : SynthState R := { table := ({} : Std.HashMap String (Entry R)).insert key { waiters := #[.root] } }
  ss := { ss with gens := #[← mkGenerator ctx key goal goalTy] }
  while ss.result.isNone do
    ss := { ss with steps := ss.steps + 1 }
    if ss.steps > 4000 then
      set saved
      throwAt ctx.info s!"instance problem is too big: {← showType ctx ty}"
    if let some (c, a) := ss.resume.back? then
      ss := { ss with resume := ss.resume.pop }
      set c.state
      match c.subgoals with
      | (h, hty) :: rest =>
        let ok ← try
            unify ctx.lvl hty (← evalIn ctx a.ty)
            unify ctx.lvl (← evalIn ctx h) (← evalIn ctx a.val)
            pure true
          catch _ => pure false
        if ok then ss ← consume ctx ss { c with subgoals := rest, state := ← get }
      | [] => pure ()
    else if let some gen := ss.gens.back? then
      if h : gen.next < gen.candidates.size then
        let (e, ety) := gen.candidates[gen.next]
        ss := { ss with gens := ss.gens.set! (ss.gens.size - 1) { gen with next := gen.next + 1 } }
        set gen.state
        let applied ← try some <$> applyInstance ctx gen.goal gen.goalTy e ety catch _ => pure none
        if let some subgoals := applied then
          ss ← consume ctx ss { key := gen.key, goal := gen.goal, goalTy := gen.goalTy, subgoals, state := ← get }
      else
        ss := { ss with gens := ss.gens.pop }
    else break
  set saved
  match ss.result with
  | none => return none
  | some a =>
    -- the answer also determines the output parameters
    unify ctx.lvl ty (← evalIn ctx a.ty)
    return some a.val
where
  /-- A consumer with no subgoals left is an answer for its goal; otherwise it waits for
  the answers to its first subgoal (making a generator if the subgoal is new). -/
  consume (ctx : LocalCtx R) (ss : SynthState R) (c : Consumer R) : ElabM R (SynthState R) := do
    set c.state
    match c.subgoals with
    | [] =>
      let val ← zonk ctx.lvl c.goal
      let ty ← zonk ctx.lvl (quote (← getGlobals) ctx.lvl c.goalTy)
      unless val.mvars.isEmpty && ty.mvars.isEmpty do return ss
      let entry := ss.table.getD c.key {}
      if entry.answers.any (fun a => a.val == val && a.ty == ty) then return ss
      let a : Answer R := { val, ty }
      let mut ss := { ss with table := ss.table.insert c.key { entry with answers := entry.answers.push a } }
      for w in entry.waiters do
        match w with
        | .root => ss := { ss with result := some a }
        | .consumer c' => ss := { ss with resume := ss.resume.push (c', a) }
      return ss
    | (h, hty) :: _ =>
      let key ← goalKey ctx hty
      match ss.table.get? key with
      | some entry =>
        let mut ss := { ss with table := ss.table.insert key { entry with waiters := entry.waiters.push (.consumer c) } }
        for a in entry.answers do ss := { ss with resume := ss.resume.push (c, a) }
        return ss
      | none =>
        let gen ← mkGenerator ctx key h hty
        return { ss with table := ss.table.insert key { waiters := #[.consumer c] }, gens := ss.gens.push gen }

/-- The unsolved holes an instance problem waits for: those in its non-output class
arguments (all of its type's, if it isn't a class application yet). It can be attempted
when there are none. -/
def instBlockers (ctx : LocalCtx R) (ty : VTy R) : ElabM R (Array Nat) := do
  let g ← getGlobals
  let some (info, _, args) ← classOf? ty | return (← zonk ctx.lvl (quote g ctx.lvl ty)).mvars
  let mut bs := #[]
  for (a, out) in args.toList.zip (info.outParams ++ List.replicate args.size false) do
    unless out do bs := bs ++ (← zonk ctx.lvl (quote g ctx.lvl a)).mvars
  return bs

/-- Can the problem be attempted? Its non-output arguments must have no unsolved holes. -/
def instReady (ctx : LocalCtx R) (ty : VTy R) : ElabM R Bool := do
  let some _ ← classOf? ty | return false
  return (← instBlockers ctx ty).isEmpty

/-- (7f) Park problem `id`: it waits for the holes `bs` (`instWaiters`); solving one puts it
back on the worklist (`solveMeta`). -/
def parkInst (id : Nat) (p : PendingInst R) (bs : Array Nat) : ElabM R Unit :=
  modify fun s =>
    let w := bs.foldl (fun (w : Std.HashMap Nat (Array Nat)) b => w.insert b ((w.getD b #[]).push id)) s.instWaiters
    { s with pendingInsts := s.pendingInsts.insert id { p with blockers := bs }, instWaiters := w }

/-- Try one pending problem (`force`: even if it isn't ready). Returns whether it was
solved; fails if it is ready and has no instance. -/
def trySynthOne (force : Bool) (id : Nat) (p : PendingInst R) : ElabM R Bool := do
  let ctx := p.ctx
  if (← zonk ctx.lvl p.hole).mvars.isEmpty then
    modify fun s => { s with pendingInsts := s.pendingInsts.erase id }
    return true
  let bs ← instBlockers ctx p.ty
  let ready := bs.isEmpty && (← classOf? p.ty).isSome
  if !ready && !force then parkInst id p bs; return false
  match ← synthInstance ctx p.ty with
  | some t =>
    modify fun s => { s with pendingInsts := s.pendingInsts.erase id }
    unify ctx.lvl (← evalIn ctx p.hole) (← evalIn ctx t)
    -- (11q) which instance, for the infoview (at the application that needed it)
    if ctx.info.stop > 0 then pushInfo (.inst ctx.info ctx p.ty t)
    return true
  | none =>
    if ready then
      throwAt ctx.info s!"failed to synthesize an instance of {← showType ctx p.ty}{← whyNot ctx p}"
    parkInst id p bs
    return false
where
  /-- (7f) Why a problem has no instance, when its default instance applies but one of the
  instance arguments it needs has none (`"a" + 1`: `HAdd String String ?C` through
  `instHAdd`, which needs `Add String`). -/
  whyNot (ctx : LocalCtx R) (p : PendingInst R) : ElabM R String := do
    let s ← get
    let some (info, _, _) ← classOf? p.ty | return ""
    let mut msg := ""
    for d in s.instances do
      unless d.isDefault && d.cls == info.name do continue
      let some decl := s.globals.find? d.name | continue
      let us ← decl.levelParams.mapM fun _ => freshLevelMeta
      let ety := eval s.globals [] (decl.type.instLevels decl.levelParams us)
      if let some subgoals ← (try some <$> applyInstance ctx p.hole p.ty (.const d.name us) ety catch _ => pure none) then
        for (_, hty) in subgoals do
          if (← instReady ctx hty) && (← synthInstance ctx hty).isNone then
            msg := s!" (it needs an instance of {← showType ctx hty}, through {d.name})"
            break
      set s
      unless msg.isEmpty do break
    return msg

/-- Try the pending instance problems that may have become solvable: the new ones, and
those one of whose holes was solved since they were last tried (the worklist, 7f: a
problem that waits is not looked at again until then). `force` tries every pending
problem, also those that aren't ready. Returns whether any was solved. Fails if a
problem has no instance. -/
partial def synthPending (force : Bool := false) : ElabM R Bool := do
  let mut progress := false
  if force then
    modify fun s => { s with instReadyQ := #[] }
    for (id, p) in (← get).pendingInsts.toArray do
      -- (an earlier one's solution may have solved this one too)
      unless (← get).pendingInsts.contains id do continue
      if ← trySynthOne true id p then progress := true
  repeat
    let q := (← get).instReadyQ
    if q.isEmpty then break
    modify fun s => { s with instReadyQ := #[] }
    let mut seen : Std.HashSet Nat := {}
    for id in q.qsort (· < ·) do
      if seen.contains id then continue
      seen := seen.insert id
      let some p := (← get).pendingInsts[id]? | continue
      if ← trySynthOne false id p then progress := true
  pure progress

/-- Record an instance problem; `now`: try it right away. -/
def addInstProblem (ctx : LocalCtx R) (m : Term R) (ty : VTy R) (now : Bool := true) : ElabM R Unit := do
  modify fun s => { s with pendingInsts := s.pendingInsts.insert s.nextInst { ctx, hole := m, ty },
                           instReadyQ := s.instReadyQ.push s.nextInst, nextInst := s.nextInst + 1 }
  if let .mvar k := m.spine.1 then
    modify fun s => { s with metas := s.metas.modify k ({ · with isInst := true }) }
  if now then let _ ← synthPending

/-- (7f) **Default instances.** When no pending problem can make progress, the default
instances (`attribute [default_instance p] i`) of the stuck ones are tried, highest
priority first, then the problems in the order they were made (`from`: only those numbered
from it on): the first default instance that applies to a stuck problem is committed to,
its instance arguments become new problems, and `true` is returned. That is the only place
a default applies (as in Lean: `instHAdd : HAdd A A A` makes `x + 1` homogeneous, `OfNat
Nat n` makes an unconstrained numeral a `Nat`), so there is no backtracking. -/
def applyDefaultInstance («from» : Nat := 0) : ElabM R Bool := do
  let s ← get
  let defaults := (s.instances.toList.zipIdx.filter (·.1.isDefault)).toArray.qsort
    fun (a, i) (b, j) => a.priority > b.priority || (a.priority == b.priority && i > j)
  if defaults.isEmpty then return false
  let stuck := s.pendingInsts.toArray.filter (·.1 ≥ «from»)
  if stuck.isEmpty then return false
  -- the class of each stuck problem
  let mut classes : Array (Nat × PendingInst R × Name) := #[]
  for (id, p) in stuck do
    if let some (info, _, _) ← classOf? p.ty then classes := classes.push (id, p, info.name)
  for (d, _) in defaults do
    let some decl := s.globals.find? d.name | continue
    for (id, p, cls) in classes do
      unless cls == d.cls do continue
      let saved ← get
      let us ← decl.levelParams.mapM fun _ => freshLevelMeta
      let ety := eval s.globals [] (decl.type.instLevels decl.levelParams us)
      match ← (try some <$> applyInstance p.ctx p.hole p.ty (.const d.name us) ety catch _ => pure none) with
      | some subgoals =>
        modify fun s => { s with pendingInsts := s.pendingInsts.erase id }
        for (h, hty) in subgoals do addInstProblem p.ctx h hty (now := false)
        if p.ctx.info.stop > 0 then
          pushInfo (.inst p.ctx.info p.ctx p.ty (← zonk p.ctx.lvl p.hole))
        return true
      | none => set saved
  return false

/-- (7f) Solve what can be solved, using default instances when stuck, for the problems
numbered from `from` on (`withDefaults`: those made while elaborating a type). -/
partial def synthDefaults («from» : Nat := 0) : ElabM R Unit := do
  let _ ← synthPending
  let mut n := 0
  while n < 1000 && (← applyDefaultInstance «from») do
    n := n + 1
    let _ ← synthPending

/-- At the end of a command: solve what can be solved (with default instances when
stuck), then report what is stuck. -/
partial def finishInstances : ElabM R Unit := do
  synthDefaults
  while ← synthPending (force := true) do synthDefaults
  if let some (_, p) := (← get).pendingInsts.toArray[0]? then
    throwAt p.ctx.info s!"type class problem is stuck (holes in its arguments): {← showType p.ctx p.ty}"

end Wiz.Elab
