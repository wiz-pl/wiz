import Wiz.Elab.ProcMacro
import Wiz.Elab.Zonk

/-!
# Tactics: the host side

A tactic is a Wiz function `Syntax → TacticM Unit`, where (in the prelude)

    inductive Tac where | done | fail (msg : String) | getGoals (k : List Nat → Tac) | …
    def TacticM (A : Type) : Type := (A → Tac) → Tac

So running a tactic produces a `Tac` value: a **request** to the elaborator together
with a continuation for the answer (a free monad, in continuation-passing style).
The elaborator interprets the requests one by one (`runTac`, in `Elab/Term.lean`,
since `exact` needs the term elaborator) and applies the continuation to the
answer, encoded as a runtime value. Tactic code itself stays pure.

**Goals** are numbered: `TacState.goals` holds every goal made so far, each a hole
(a metavariable applied to its context's variables) with a context and a type.
`TacState.open` is the current goal list, which tactics read and replace.

**Terms** are reflected as the prelude's `Expr`: variables (de Bruijn indices in the
goal's context), constants, closed sorts, Π (with binder info and quantity), λ,
application, and numerals. Every other kernel form becomes an `opaque` handle into
`TacState.handles`, remembering how many variables were in scope where it was made;
when it is used deeper inside binders, it is lifted. Nominal inductive types (`μ`
with a display hint) are reflected as their names applied to their arguments, so
tactics see `Vec A n`; and constructor applications, which evaluate to tagged payloads,
are reflected by name too, `Vec.cons A n x xs`, by following the types
("Typed reflection" below).
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

-- The constructor numbers of the prelude's `Tac`.
namespace TacTag
def done := 0
def result := 1
def fail := 2
def trace := 3
def fresh := 4
def getGoals := 5
def setGoals := 6
def goalType := 7
def goalExpr := 8
def goalHyps := 9
def intro := 10
def exact := 11
def elabInfer := 12
def assign := 13
def newGoal := 14
def normalize := 15
def instantiate := 16
def isDefEq := 17
def inferType := 18
def evalTactic := 19
def catch_ := 20
-- (HD8) reflection, for macros (`Elab/Reflect.lean`)
def getInductive := 21
def getType := 22
-- the tactic framework's requests (a block of their own in the prelude's `Tac`)
def ppGoal := 23
def ppExpr := 24
def introFresh := 25
def rename := 26
def change := 27
def whnf := 28
def unfold := 29
def rewrite := 30
def ctorInfo := 31
def isDefinition := 32
-- (stage 28) solvers
def satSolve := 33
def eqView := 34
def smt := 35
def define := 36
def assignLate := 37
def nativeDecide := 38
-- (stage 6h) match a lemma's `∀` telescope, rewrite an occurrence, one request
def rewriteAt := 39
-- (stage 6h S2) the registered `[simp]` lemmas, for the default set
def getSimpLemmas := 40
-- (D6) the constructor names of a type, for `constructor`
def ctorNames := 41
-- (6j) a case split on a Boolean expression
def byCases := 42
-- (P0) the `[hint]` database, for `auto`
def getHints := 43
end TacTag

structure Goal (R : Type) where
  ctx : LocalCtx R
  ty : VTy R
  /-- the hole: a metavariable applied to the bound variables of `ctx` -/
  tm : Term R

structure TacState (R : Type) where
  goals : Array (Goal R) := #[]
  «open» : List Nat := []
  /-- opaque terms, with the number of variables in scope where they were reflected -/
  handles : Array (Term R × Nat) := #[]
  /-- (13b) terms given to `assign` while they still had holes, with their goals: their
  types are checked against the goals at the end of the block (`elabBy`), in the
  elaborator's view. The kernel would check them too, but by shape. -/
  unchecked : Array (Goal R × Term R) := #[]

/-! ## Encoding answers -/

def encodeNat (n : Nat) : RVal := .nat n
def encodeBool (b : Bool) : RVal := mkCon (if b then 1 else 0) []
def encodeList (xs : List RVal) : RVal := xs.foldr (fun x t => mkCon 1 [x, t]) (mkCon 0 [])
def encodePair (a b : RVal) : RVal := .obj 0 #[a, b]

/-- The elements of a runtime `List`. -/
partial def decodeList (v : RVal) : Option (List RVal) :=
  match v.tag? with
  | some 0 => some []
  | some 1 => do return v.conField 0 :: (← decodeList (v.conField 1))
  | _ => none

def decodeBool (v : RVal) : Option Bool := v.tag?.map (· == 1)

/-! ## Reflection -/

/-- The handle for the opaque term `t` at `depth`: the one it already has, if it was
reflected before (among the last 256 handles), so that two reflections of a term are
the same `Expr` and tactics can compare them syntactically. -/
def internHandle (hs : Array (Term R × Nat)) (t : Term R) (depth : Nat) : Array (Term R × Nat) × Nat :=
  let n := min hs.size 256
  match (List.range n).find? fun k => let (t', d) := hs[hs.size - 1 - k]!; d == depth && t' == t with
  | some k => (hs, hs.size - 1 - k)
  | none => (hs.push (t, depth), hs.size)

/-- **Exercise 6.4a.** Reflect a term (with `depth` variables in scope) as an `Expr`
value (constructors, in order: `var i`, `const n`, `sort u`, `pi x implicit q dom body`,
`lam x body`, `app f a`, `lit n`, `opaque id`; use `mkCon`, `encodeString`,
`encodeBool`). Levels are dropped from constants (`reify` makes fresh ones), a sort
is reflected only if its level is a numeral, and a `μ`/`ν` with a display hint
`(T, us, args)` becomes `T` applied to `args`. Anything else is `opaque`: its handle is
the index `internHandle` gives `(t, depth)` among the handles. -/
partial def reflect (t : Term R) (depth : Nat) : StateM (Array (Term R × Nat)) RVal := do
  --<sol
  match t with
  | .var i => pure (mkCon 0 [.nat i])
  | .const n _ => pure (mkCon 1 [encodeString n])
  | .sort l => match l.toNat? with
    | some n => pure (mkCon 2 [.nat n])
    | none => mkOpaque
  | .pi x bi q A B _ =>
    pure (mkCon 3 [encodeString x, encodeBool (bi == .implicit), ← reflect q depth, ← reflect A depth,
      ← reflect B (depth + 1)])
  | .lam x b => pure (mkCon 4 [encodeString x, ← reflect b (depth + 1)])
  | .app f a => pure (mkCon 5 [← reflect f depth, ← reflect a depth])
  | .natLit n => pure (mkCon 6 [.nat n])
  | .mu _ _ _ _ .szInf (some (T, _, args)) _ | .nu _ _ _ _ .szInf (some (T, _, args)) =>
    args.foldlM (fun acc a => do pure (mkCon 5 [acc, ← reflect a depth])) (mkCon 1 [encodeString T])
  | _ => mkOpaque
where
  mkOpaque : StateM (Array (Term R × Nat)) RVal := do
    let (hs, i) := internHandle (← get) t depth
    set hs
    pure (mkCon 7 [.nat i])
  --|ex
  --| sorry
  --sol>

/-- **Exercise 6.4b.** The inverse of `reflect`, at `depth` variables in scope. A
constant gets fresh level metavariables for its universe parameters (it must exist).
An `opaque` handle made at depth `d` is lifted by `depth - d` (or strengthened, if
`depth < d`, failing if that is impossible). Binders take the rig's default quantity
only through `q`, which is reflected like any other term. -/
partial def reify (handles : Array (Term R × Nat)) (v : RVal) (depth : Nat) : ElabM R (Term R) := do
  --<sol
  let str (v : RVal) : ElabM R String := match v.toString? with
    | some s => pure s
    | none => throwAt {} "tactic: malformed string"
  let nat (v : RVal) : ElabM R Nat := match v.toNat? with
    | some n => pure n
    | none => throwAt {} "tactic: malformed number"
  match v.tag? with
  | some 0 => return .var (← nat (v.conField 0))
  | some 1 =>
    let n ← str (v.conField 0)
    let some d := (← getGlobals).find? n | throwAt {} s!"tactic: unknown constant {n}"
    return .const n (← d.levelParams.mapM fun _ => freshLevelMeta)
  | some 2 => return .sort (Level.ofNat (← nat (v.conField 0)))
  | some 3 =>
    let bi : BinderInfo := if decodeBool (v.conField 1) == some true then .implicit else .default
    return .pi (← str (v.conField 0)) bi (← reify handles (v.conField 2) depth)
      (← reify handles (v.conField 3) depth) (← reify handles (v.conField 4) (depth + 1)) .hole
  | some 4 => return .lam (← str (v.conField 0)) (← reify handles (v.conField 1) (depth + 1))
  | some 5 => return .app (← reify handles (v.conField 0) depth) (← reify handles (v.conField 1) depth)
  | some 6 => return .natLit (← nat (v.conField 0))
  | some 7 =>
    let some (t, d) := handles[← nat (v.conField 0)]? | throwAt {} "tactic: unknown handle"
    if depth ≥ d then return t.lift (depth - d)
    let some t' := (List.range (d - depth)).foldlM (fun t _ => t.strengthen? 0) t
      | throwAt {} "tactic: a term was used outside the binders it refers to"
    return t'
  | _ => throwAt {} "tactic: malformed Expr"
  --|ex
  --| sorry
  --sol>

/-! ## Typed reflection: constructors by name (stage 6g)

Data types are descriptions, and a constructor application `List.cons A x L` is, once
evaluated, `con ('cons, x, L, refl, ())`: a tagged payload with no trace of the type or
its parameters. `reflect` alone can only make that an opaque handle. But the **type**
tells: a `con` whose type is the nominal `List A` with tag `cons` is `List.cons A x L`.
So reflection is type-directed where it matters: `reflectT` follows the types down a
term (the head of an application gives the types of its arguments, a `fun` checked
against a `Π` the type of its body) and shows a `con` at a known nominal type as its
constructor applied to the type's parameters and the fields, which is exactly what
`reify` turns back into that `con` (constructors are globals). A registered operation
on numbers (`Nat.succ n`, the kernel's `natOp`) is shown as its global, too.

Nothing here is trusted: a reflected term is only what a tactic *reads*; what it builds
from it is elaborated and checked as before. Where the type is not known (an argument of
a metavariable, the inside of another opaque form) a `con` stays an opaque handle. -/

/-- How a constructor's declaration places a field in the payload (`Elab/Inductive.lean`,
Q4): as itself, lifted (`up x`), or an infinitary field with a lifted domain. -/
inductive FieldPos where
  | plain | up | hrec
  deriving BEq, Inhabited

/-- A constructor declaration's shape: the number of parameters, and its fields. -/
structure CtorShape where
  nParams : Nat
  fields : List FieldPos

private def lamsBody : Term R → Nat × Term R
  | .lam _ b => let (n, t) := lamsBody b; (n + 1, t)
  | t => (0, t)

private def tupleParts : Term R → List (Term R)
  | .pair a b => a :: tupleParts b
  | t => [t]

/-- The tag of a payload: its labels and index (the tag is lifted above `Type`). -/
def payloadTag? : Term R → Option (List Name × Nat)
  | .tag ls i | .up (.tag ls i) => some (ls, i)
  | _ => none

/-- Read a constructor's shape off its declaration,
`fun Δ fields => con (tag, field₁, …, fieldₙ, refl …, ())`. -/
def ctorShape? (d : Decl R) : Option CtorShape := do
  guard d.inline
  let (n, body) := lamsBody (← d.value)
  let .con (.pair tag rest) := body | none
  let _ ← payloadTag? tag
  let parts := tupleParts rest
  guard (parts.length ≥ 2)
  let comps := parts.take (parts.length - 2)
  let nF := comps.length
  guard (nF ≤ n)
  let fields ← comps.zipIdx.mapM fun (c, k) =>
    let j := nF - 1 - k
    match c with
    | .var i => if i == j then some FieldPos.plain else none
    | .up (.var i) => if i == j then some FieldPos.up else none
    | .lam _ (.app (.var i) (.down (.var 0))) => if i == j + 1 then some FieldPos.hrec else none
    | _ => none
  pure { nParams := n - nF, fields }

/-- A payload component as the field the constructor was given. -/
def FieldPos.field : FieldPos → Term R → Term R
  | .plain, c => c
  | .up, .up a => a
  | .up, c => .down c
  | .hrec, c =>
    let eta : Term R := .lam "h" (.app (c.lift 1) (.up (.var 0)))
    match c with
    | .lam _ (.app f (.down (.var 0))) => (f.strengthen? 0).getD eta
    | _ => eta

/-- Does a term contain data that only typed reflection shows (a `con`, a `natOp`)? -/
partial def hasData (t : Term R) : Bool :=
  match t with
  | .con _ | .natOp .. => true
  | t => (Id.run <| (t.mapChildrenM (m := StateM Bool) pure fun _ c => do
      if !(← get) && hasData c then set true
      pure c).run false).2

/-- What typed reflection knows about the variables in scope (innermost first). -/
structure RCtx (R : Type) where
  env : Env R
  types : List (Option (VTy R))
  lvl : Nat

def RCtx.ofLocal (ctx : LocalCtx R) : RCtx R :=
  { env := ctx.env, types := ctx.types.map some, lvl := ctx.lvl }

def RCtx.bind (rc : RCtx R) (ty : Option (VTy R)) : RCtx R :=
  { env := Val.var rc.lvl :: rc.env, types := ty :: rc.types, lvl := rc.lvl + 1 }

abbrev ReflM (R : Type) := StateT (Array (Term R × Nat)) (ElabM R)

def forceR (v : Val R) : ReflM R (Val R) := fun s => do pure (← force v, s)
def globalsR : ReflM R (Globals R) := fun s => do pure (← getGlobals, s)
def zonkR (l : Lvl) (t : Term R) : ReflM R (Term R) := fun s => do pure (← zonk l t, s)

/-- The type of a function's result at the argument `a`, evaluating `a` only if the
type depends on it. -/
def RCtx.instArg (rc : RCtx R) (g : Globals R) (c : Closure R) (a : Term R) : VTy R :=
  match c with
  | .mk env body => eval g ((if body.hasVar 0 then eval g rc.env a else .unit .zero) :: env) body

/-- The type of a constant or a variable (the head of an application). -/
def RCtx.headType? (rc : RCtx R) (g : Globals R) : Term R → Option (VTy R)
  | .const n us => (g.find? n).map fun d => eval g [] (d.type.instLevels d.levelParams us)
  | .var i => (rc.types[i]?).join
  | _ => none

/-- The type of an application of a constant or a variable, without the kernel (it may
have holes): for the terms a request is handed, whose type nobody states. -/
def RCtx.typeOf? (rc : RCtx R) (t : Term R) : ElabM R (Option (VTy R)) := do
  let g ← getGlobals
  let (h, args) := Term.spine t
  let mut ty? := rc.headType? g h
  for a in args do
    let some ty := ty? | return none
    match ← force ty with
    | .pi _ _ _ _ cod _ => ty? := some (rc.instArg g cod a)
    | _ => return none
  pure ty?

/-- `typeOf?`, unifying each argument's type (when it has one this way) with the
function's domain on the way. Reflected constants come back with fresh universe levels
(`reify`), and this is what solves them: `F.map_comp f g` reified is `Fun.map_comp.{?a, …}
F f g`, and only the types of `F`, `f` and `g` fix `?a`, … (wiz-cats B6). A mismatch is
left for the kernel to report. -/
partial def RCtx.typeOfUnifying? (rc : RCtx R) (t : Term R) : ElabM R (Option (VTy R)) := do
  let g ← getGlobals
  let (h, args) := Term.spine t
  -- (a field of a structure: the type of what is projected, projected)
  let mut ty? ← match h with
    | .fst p => do
      let some pty ← rc.typeOfUnifying? p | pure none
      match ← force pty with
      | .sigma _ _ A _ _ => pure (some A)
      | _ => pure none
    | .snd p => do
      let some pty ← rc.typeOfUnifying? p | pure none
      match ← force pty with
      | .sigma _ _ _ B _ => pure (some (← instM B (vFst (eval g rc.env p))))
      | _ => pure none
    | h => pure (rc.headType? g h)
  for a in args do
    -- (the arguments' own constants, whatever this application's type)
    let aty ← rc.typeOfUnifying? a
    let some ty := ty? | continue
    match ← force ty with
    | .pi _ _ _ dom cod _ =>
      if let some aty := aty then
        let s ← get
        try unify rc.lvl dom aty catch _ => set s
      ty? := some (rc.instArg g cod a)
    | _ => ty? := none
  pure ty?

mutual

/-- Reflect `t` of type `ty?` (when it is known). As `reflect`, but type-directed. -/
partial def reflectT (rc : RCtx R) (t : Term R) (ty? : Option (VTy R)) : ReflM R RVal := do
  let mkOpq : ReflM R RVal := do
    let (hs, i) := internHandle (← get) t rc.lvl
    set hs
    pure (mkCon 7 [.nat i])
  match t with
  | .var i => pure (mkCon 0 [.nat i])
  | .const n _ => pure (mkCon 1 [encodeString n])
  | .sort l => match l.toNat? with
    | some n => pure (mkCon 2 [.nat n])
    | none => mkOpq
  | .natLit n => pure (mkCon 6 [.nat n])
  | .pi x bi q A B _ =>
    let g ← globalsR
    pure (mkCon 3 [encodeString x, encodeBool (bi == .implicit), ← reflectT rc q none, ← reflectT rc A none,
      ← reflectT (rc.bind (some (eval g rc.env A))) B none])
  | .lam x b =>
    let pi? ← match ty? with
      | some ty => (match ← forceR ty with
        | .pi _ _ _ dom cod _ => pure (some (dom, cod))
        | _ => pure none)
      | none => pure none
    match pi? with
    | some (dom, cod) =>
      pure (mkCon 4 [encodeString x, ← reflectT (rc.bind (some dom)) b (some (Closure.inst (← globalsR) cod (Val.var rc.lvl)))])
    | none => pure (mkCon 4 [encodeString x, ← reflectT (rc.bind none) b none])
  | .app .. =>
    let (h, args) := Term.spine t
    let g ← globalsR
    let rh ← match h with
      | .app .. => mkOpq  -- (not reached: `spine` strips every application)
      | h => reflectT rc h none
    reflectArgs rc rh (rc.headType? g h) args
  | .mu _ _ _ _ .szInf (some (T, us, args)) _ | .nu _ _ _ _ .szInf (some (T, us, args)) =>
    reflectArgs rc (mkCon 1 [encodeString T]) (rc.headType? (← globalsR) (.const T us)) args
  | .natOp op args =>
    let g ← globalsR
    match g.builtinOf? op with
    | some n => reflectArgs rc (mkCon 1 [encodeString n]) (rc.headType? g (.const n [])) args.toList
    | none => mkOpq
  | .con (.pair tag rest) =>
    match ← reflectCtor rc tag rest ty? with
    | some r => pure r
    | none => mkOpq
  | _ => mkOpq

/-- Reflect the arguments of an application whose head (reflected as `acc`) has type `ty?`. -/
partial def reflectArgs (rc : RCtx R) (acc : RVal) (ty? : Option (VTy R)) : List (Term R) → ReflM R RVal
  | [] => pure acc
  | a :: as => do
    let pi? ← match ty? with
      | some ty => (match ← forceR ty with
        | .pi _ _ _ dom cod _ => pure (some (dom, cod))
        | _ => pure none)
      | none => pure none
    let ra ← reflectT rc a (pi?.map (·.1))
    let g ← globalsR
    reflectArgs rc (mkCon 5 [acc, ra]) (pi?.map fun (_, cod) => rc.instArg g cod a) as

/-- A payload at the nominal type `T Δ ξ`: `T.c Δ fields`. -/
partial def reflectCtor (rc : RCtx R) (tag rest : Term R) (ty? : Option (VTy R)) : ReflM R (Option RVal) := do
  let some ty := ty? | return none
  let some (ls, i) := payloadTag? tag | return none
  let (T, us, targs) ← match ← forceR ty with
    | .mu _ _ _ _ _ (some h) _ => pure h
    | _ => return none
  let some c := ls[i]? | return none
  let g ← globalsR
  let cname := ctorConst T c
  let some d := g.find? cname | return none
  let some sh := ctorShape? d | return none
  let parts := tupleParts rest
  unless parts.length == sh.fields.length + 2 && targs.length ≥ sh.nParams do return none
  let fields := ((parts.take sh.fields.length).zip sh.fields).map fun ((c : Term R), (pos : FieldPos)) => pos.field c
  -- the parameters come from the type; they give the fields their types
  let mut acc := mkCon 1 [encodeString cname]
  let mut cty := eval g [] (d.type.instLevels d.levelParams us)
  for p in targs.take sh.nParams do
    let .pi _ _ _ dom cod _ ← forceR cty | return none
    acc := mkCon 5 [acc, ← reflectT rc (← zonkR rc.lvl (quote g rc.lvl p)) (some dom)]
    cty := Closure.inst g cod p
  some <$> reflectArgs rc acc (some cty) fields

end

/-- A constructor's type, number of parameters and number of fields, for tactics
(`TacticM.ctorInfo`): `none` if `n` is not a constructor of an inductive type. -/
def ctorInfo? (g : Globals R) (n : Name) : Option (Name × Nat × Nat) := do
  let d ← g.find? n
  let sh ← ctorShape? d
  let T := ".".intercalate ((n.splitOn ".").dropLast)
  guard (g.contains (T ++ ".desc"))
  pure (T, sh.nParams, sh.fields.length)

/-! ## Names for introduced variables

A tactic that introduces a variable without being given a name takes the binder's
(`intro` on `(n : Nat) → …` gives `n`). The name is then made **fresh**: either
accessible, with the first free numeric suffix (`n`, `n1`, `n2`, …), or
**inaccessible**, marked with `✝` (`n✝`, `n✝1`, …), which is not an identifier
character: the user cannot refer to it by accident, and a proof cannot come to depend
on a generated name. `rename_i` gives inaccessible names a real one. -/

/-- The mark of an inaccessible name. -/
def inaccessibleMark : String := "✝"

def Name.isInaccessible (x : Name) : Bool := (x.splitOn inaccessibleMark).length > 1

/-- The name for a variable introduced from a binder `binder`, given the names in scope:
`hint` if it is not empty, else the binder's name, else `h` for a proof and `x` for
anything else; then made fresh (see above). -/
def introName (taken : List Name) (hint binder : Name) (isProof inaccessible : Bool) : Name :=
  let binder := (binder.splitOn inaccessibleMark).headD ""
  let base := if !hint.isEmpty then hint
    else if !binder.isEmpty && binder != "_" then binder
    else if isProof then "h" else "x"
  let base := if inaccessible then base ++ inaccessibleMark else base
  if !taken.contains base then base else
  match (List.range (taken.length + 1)).find? fun i => !taken.contains s!"{base}{i + 1}" with
  | some i => s!"{base}{i + 1}"
  | none => base

/-! ## Goals -/

/-- The kernel context for a goal, for inferring the types of complete terms. -/
def Goal.kernelCtx (gl : Goal R) (g : Globals R) : Ctx R :=
  { globals := g, env := gl.ctx.env,
    names := gl.ctx.names.reverse.toArray,
    qtys := (gl.ctx.names.map fun _ => QPoly.const QuantitySyntax.explicitDefault).reverse.toArray,
    types := gl.ctx.types.reverse.toArray, lvl := gl.ctx.lvl, erased := true }

/-- Is the goal's hole still unsolved? -/
def Goal.isOpen (gl : Goal R) : ElabM R Bool := do
  let t ← zonk gl.ctx.lvl gl.tm
  pure !(t.mvars.isEmpty)

/-- Show a goal: its hypotheses, then `⊢ type`. -/
def Goal.show (gl : Goal R) : ElabM R String := do
  let mut lines : Array String := #[]
  let ctx := gl.ctx
  for i in [0:ctx.lvl] do
    let j := ctx.lvl - 1 - i
    -- the type of the `j`th local lives in the context below it
    let k := j + 1
    let sub : LocalCtx R :=
      { ctx with env := ctx.env.drop k, names := ctx.names.drop k, types := ctx.types.drop k,
                 bound := ctx.bound.drop k, lvl := ctx.lvl - k }
    lines := lines.push s!"{ctx.names[j]!} : {← showTermM sub (← zonk sub.lvl (quote (← getGlobals) sub.lvl ctx.types[j]!))}"
  lines := lines.push s!"⊢ {goalTarget (← showTermM ctx (← zonk ctx.lvl (quote (← getGlobals) ctx.lvl gl.ty)))}"
  pure ("\n".intercalate lines.toList)

/-! ## Unfolding (stage 6f)

`normalize` evaluates and quotes, but definitions are glued (`Val.unfold` keeps the
name), so it never shows what a definition unfolds to. Two requests do:

* `unfold n e` replaces every application of the constant `n` in `e` by its unfolding,
  **once**: the definition's body with the arguments in place and the `match` on them
  computed, but the definitions it mentions still folded.
* `whnf e` unfolds the head of `e` until it is not a definition (a constructor, a
  binder, a variable, …).

A structurally recursive definition is an eliminator, so what unfolding leaves for its
recursive calls is a raw `ind … L n`, which nobody wrote. `foldRec` finds these stuck
eliminators and folds each back into `f a₁ … aₙ` when that unifies with it (for the `f`s
that were unfolded): the user sees `MList L n` again. The result is only ever a
*candidate*: the elaborator checks it against what it replaces by conversion
(`change`), and the kernel checks the finished proof. -/

private def stripLams : Term R → Nat × Term R
  | .lam _ b => let (n, t) := stripLams b; (n + 1, t)
  | t => (0, t)

/-- `ctx` under `k` more binders (of types the caller doesn't know or need). -/
def bindAnon (ctx : LocalCtx R) : Nat → LocalCtx R
  | 0 => ctx
  | k + 1 => bindAnon (ctx.bind "x" (.unit .zero)) k

/-- `t` as an application of the definition `n`, if `n ?a₁ … ?aₖ` (`k` its number of
`fun`s) unifies with it and that solves every `?aᵢ`. -/
def foldAs? (ctx : LocalCtx R) (n : Name) (t : Term R) : ElabM R (Option (Term R)) := do
  let some d := (← getGlobals).find? n | return none
  let some v := d.value | return none
  let arity := (stripLams v).1
  if arity == 0 then return none
  try
    let us ← d.levelParams.mapM fun _ => freshLevelMeta
    let mut cand : Term R := .const n us
    -- (13b) each hole typed by the definition's parameter (`MetaEntry.type?`)
    let g ← getGlobals
    let mut ty? : Option (VTy R) := some (eval g [] (d.type.instLevels d.levelParams us))
    for _ in [0:arity] do
      let dom? ← match ty? with
        | some ty => do match ← force ty with
          | .pi _ _ _ dom cod _ => pure (some (dom, cod))
          | _ => pure none
        | none => pure none
      let m ← freshMeta ctx "fold" (dom?.map (·.1))
      ty? ← match dom? with
        | some (_, cod) => pure (some (← instM cod (← evalIn ctx m)))
        | none => pure none
      cand := .app cand m
    let cv ← evalIn ctx cand
    let tv ← force (← evalIn ctx t)
    -- `n ?a₁ … ?aₖ` is itself stuck, on the hole it recurses on: `?aᵢ` followed by the
    -- eliminator and the rest. That is no pattern for the unifier, so first solve the
    -- hole with what `t`'s eliminator is stuck on (once per nested `match`)
    for _ in [0:arity] do
      match ← force cv, tv with
      | .neutral (.mvar a) sp, .neutral h' sp' =>
        let some j := sp.findIdx? (fun e => !(e matches .app _)) | break
        let rest := sp.size - j
        if sp'.size < rest then throwAt {} "no match"
        unify ctx.lvl (.neutral (.mvar a) (sp.extract 0 j)) (.neutral h' (sp'.extract 0 (sp'.size - rest)))
      | _, _ => break
    unify ctx.lvl cv tv
    let t' ← zonk ctx.lvl cand
    if t'.mvars.isEmpty then return some t'
    throwAt {} "not determined"
  catch _ => return none

/-- Fold the stuck eliminators in `t` back into applications of the definitions `names`
(see above). An eliminator applied to more arguments than the definition takes, or to
fewer, is tried at each prefix of its arguments. -/
partial def foldRec (ctx : LocalCtx R) (names : List Name) (t : Term R) : ElabM R (Term R) := do
  if names.isEmpty then return t
  if (Term.spine t).1 matches .ind .. then
    for n in names do
      if let some t' ← foldAs? ctx n t then return t'
  t.mapChildrenM pure fun k c => foldRec (bindAnon ctx k) names c

/-- Is `n` an eliminator of an inductive type (`T.rec`, `T.casesOn`, …)? A definition by
cases or by structural recursion is `fun x => T.rec … x`: unfolding it means unfolding the recursor too (which
is where the `match` computes), and nobody wants a recursive call folded into `T.rec`. -/
def isRecursor (g : Globals R) (n : Name) : Bool :=
  match (n.splitOn ".").reverse with
  | e :: rest => ["rec", "recN", "casesOn", "casesOnN", "casesOnA", "scasesOn", "scasesOnN"].contains e &&
      !rest.isEmpty && g.contains (".".intercalate rest.reverse ++ ".desc")
  | _ => false

/-- Unfold the recursors at the head of a value, and compute a lazy eliminator (a `match`
on a numeral or a constructor that evaluation postponed): otherwise `unfold` would show
the raw `ind … L n` of a definition by cases applied to a numeral. -/
partial def forceRecursors (v : Val R) : ElabM R (Val R) := do
  match ← forceMeta v with
  | .unfold n us sp w => if isRecursor (← getGlobals) n then forceRecursors w.get else pure (.unfold n us sp w)
  | .lazyInd _ _ _ _ _ _ _ _ _ _ w => forceRecursors w.get
  | v => pure v

/-- Unfold the head of a value until it is not a definition; also the definitions
unfolded on the way, innermost last. -/
partial def forceNames (v : Val R) (names : List Name := []) : ElabM R (Val R × List Name) := do
  match ← forceMeta v with
  | .unfold n _ _ v =>
    forceNames v.get (if names.contains n || isRecursor (← getGlobals) n then names else names ++ [n])
  | .lazyInd _ _ _ _ _ _ _ _ _ _ v => forceNames v.get names
  | v => pure (v, names)

/-- The weak head normal form of `t`, with recursive calls folded back. -/
def whnfTerm (ctx : LocalCtx R) (t : Term R) : ElabM R (Term R) := do
  let (v, names) ← forceNames (← evalIn ctx t)
  foldRec ctx names.reverse (← zonk ctx.lvl (quote (← getGlobals) ctx.lvl v))

/-- `t` with every application of the definition `n` unfolded once (innermost first). -/
partial def unfoldIn (ctx : LocalCtx R) (n : Name) (t : Term R) : ElabM R (Term R) := do
  let inside (t : Term R) := t.mapChildrenM pure fun k c => unfoldIn (bindAnon ctx k) n c
  match t with
  | .app .. | .const .. =>
    -- the whole application at once: `f a` in `f a b` is not an occurrence of its own
    let (h, args) := Term.spine t
    let args ← args.mapM (unfoldIn ctx n)
    match h with
    | .const m _ =>
      let t' := args.foldl .app h
      if m != n then return t'
      match ← forceMeta (← evalIn ctx t') with
      | .unfold _ _ _ v =>
        foldRec ctx [n] (← zonk ctx.lvl (quote (← getGlobals) ctx.lvl (← forceRecursors v.get)))
      | _ => pure t'
    | h => return args.foldl .app (← inside h)
  | t => inside t

/-! ## Rewriting with an equation

`rewrite h` for `h : a = b` replaces the occurrences of `a` in the goal `G[a]` by `b`:
the new goal is `G[b]`, and the old one is solved by a cast along `G[b] = G[a]`, which
`transp` gets from `h` (as `Eq.substBack` in the prelude does). Occurrences are found
syntactically, on the normal forms the elaborator prints; the kernel checks the cast. -/

/-- `t` (under `depth` binders more than `a`) with the occurrences of `a` replaced by
the variable `depth`, the other variables making room for it; and whether there were any. -/
partial def abstractOcc (a : Term R) (t : Term R) (depth : Nat := 0) : StateM Bool (Term R) := do
  if t == a.lift depth then
    set true
    return .var depth
  match t with
  | .var i => pure (.var (if i ≥ depth then i + 1 else i))
  | t => t.mapChildrenM pure fun k c => abstractOcc a c (depth + k)

/-! ## Matching a rule, at a chosen occurrence (stage 6h)

`rewrite` takes a *complete* equation: `rw (h x)`. A simplifier rule is a telescope
`∀ x₁ … xₙ, lhs = rhs`, and its variables are found by **matching** `lhs` against a
subterm of the goal; a rule with a premise (`… → lhs = rhs`) is conditional. The Wiz
side (`lib/Prelude.wiz`) owns rule order, the traversal policy, the fuel and the
messages; the host owns only what needs `Term` and the unifier:

* `stripRule`: strip the `∀` binders, making a fresh metavariable for each;
* `matchRule`: unify the rule's left side with each subterm of the goal (pre-order),
  and require the instantiation to determine every metavariable;
* `abstractOccAt`: the occurrence selection for the transport (all, or the `n`th).

The step is the same `transp`/`cast` transport as `rewrite`, so the kernel checks it.
No metavariable is ever handed to Wiz: it sees a `RewriteResult` (no match, a new goal
and its reflected type, or a malformed rule). -/

mutual

/-- `t` with the selected occurrences of `a` abstracted as the variable `depth` (the
other variables make room for it): every occurrence when `occ` is `none`, the `n`th in
pre-order when `occ = some n`. The state is (was one replaced, occurrences so far). -/
partial def abstractOccAt (a : Term R) (t : Term R) (occ : Option Nat) (depth : Nat := 0) :
    StateM (Bool × Nat) (Term R) := do
  let (found, i) ← get
  if t == a.lift depth then
    match occ with
    | none => set (true, i + 1); return .var depth
    | some n =>
      if i == n then
        set (true, i + 1); return .var depth
      else do
        set (found, i + 1)
        abstractOccChildren a t occ depth
  else abstractOccChildren a t occ depth

/-- The children of `t`, with the occurrence search continued in each (for a term that
is not the selected occurrence). -/
partial def abstractOccChildren (a : Term R) (t : Term R) (occ : Option Nat) (depth : Nat) :
    StateM (Bool × Nat) (Term R) :=
  match t with
  | .var j => pure (.var (if j ≥ depth then j + 1 else j))
  | t => t.mapChildrenM pure fun k c => abstractOccAt a c occ (depth + k)

end

/-- The subterms of `t` in pre-order (the whole term first): the positions a rule's
left side is matched against. -/
partial def subtermsPre (t : Term R) : List (Term R) :=
  let cs : List (Term R) :=
    ((t.forChildren (m := StateM (List (Term R))) (fun _ => pure ())
      (fun _ c => modify fun xs => xs ++ [c])) []).2
  t :: cs.flatMap subtermsPre

/-- Strip the leading `∀` binders of a rule's type, making a fresh metavariable for
each: the body (the equation) and the metavariables, outermost first. `fuel` bounds
the number of binders (a telescope is finite). The body is kept **syntactically** when
it is an equation: an equation at a data type computes when it is evaluated (`b ^ 0` is
`1`, so `b ^ 0 = 1` computes to `True`), and such a rule (`Nat.pow_zero`,
`List.map_cons`, …) must still be readable as `lhs = rhs` for matching. -/
partial def stripRule (ctx : LocalCtx R) (fuel : Nat) (ty : Term R) :
    ElabM R (Term R × List (Term R)) := do
  if fuel == 0 then return (ty, [])
  let ty' ← whnfTerm ctx ty
  match ty' with
  | .pi _ _ _ dom body _ => do
    let m ← freshMeta ctx "simp" (some (← evalIn ctx dom))
    let (b, ms) ← stripRule ctx (fuel - 1) (body.instantiateAt 0 m)
    pure (b, m :: ms)
  | .eq .. => pure (ty', [])
  | _ =>
    -- (a definition that unfolds to an equation: `ty'`; else the equation as written)
    match ty with
    | .eq .. => pure (ty, [])
    | _ => pure (ty', [])

/-- Strip a telescope's binders, taking arguments from `args` where the term is already
applied and making a fresh metavariable otherwise. Returns the body (the equation), the
fresh metavariables, and each binder's `(domain, argument)` pair, for solving implicit
parameters from the arguments' types. The body is kept syntactically when it is an
equation (an equation that computes still reads as `lhs = rhs`). -/
partial def stripArgs (ctx : LocalCtx R) (fuel : Nat) (ty : Term R) (args : List (Term R)) :
    ElabM R (Term R × List (Term R) × List (Term R × Term R)) := do
  if fuel == 0 then return (ty, [], [])
  match ty with
  | .pi _ _ _ dom body _ =>
    match args with
    | a :: rest => do
      let (b, ms, ps) ← stripArgs ctx (fuel - 1) (body.instantiateAt 0 a) rest
      pure (b, ms, (dom, a) :: ps)
    | [] => do
      let m ← freshMeta ctx "simp" (some (← evalIn ctx dom))
      let (b, ms, ps) ← stripArgs ctx (fuel - 1) (body.instantiateAt 0 m) []
      pure (b, m :: ms, (dom, m) :: ps)
  | .eq .. => pure (ty, [], [])
  | _ => do
    let ty' ← whnfTerm ctx ty
    match ty' with
    | .pi .. => stripArgs ctx (fuel - 1) ty' args
    | .eq .. => pure (ty', [], [])
    | _ =>
      match ty with
      | .eq .. => pure (ty, [], [])
      | _ => pure (ty', [], [])

/-- The type of a rule term **as written**, at the goal's level: for a constant, its
declaration's type with its levels and already-applied arguments substituted and a
fresh metavariable for each remaining `∀` binder. `none` when the head is not a
constant (a local hypothesis: the kernel's evaluated type is used then). This is what
keeps rules like `Nat.pow_zero` (`b ^ 0 = 1`, whose *evaluated* type is `1 = 1`) and
`List.map_cons` usable: the equation is read before computation erases its sides. The
`(domain, argument)` pairs let the match solve implicit parameters (`{A : Type}`) from
the types of the arguments it determined. -/
def ruleType? (ctx : LocalCtx R) (g : Globals R) (t : Term R) :
    ElabM R (Option (Term R × Term R × List (Term R × Term R))) := do
  let (head, args) := Term.spine t
  match head with
  | .const n us =>
    let some d := g.find? n | return none
    let (body, ms, ps) ← stripArgs ctx 64 (d.type.instLevels d.levelParams us) args
    pure (some (body, ms.foldl (fun f m => .app f m) t, ps))
  | _ => return none

/-- Is this value a constructor payload (a data value)? -/
def isConVal : Val R → Bool
  | .con _ => true
  | _ => false

/-- Match the rule's pattern side `pat` (one side of the equation `lhs = rhs`, with the
telescope metavariables of `happ`) against each subterm of the goal type, in pre-order.
The first subterm whose unification determines every metavariable wins: the result is
the equation's type, its two sides, the instantiated lemma, and the matched subterm
(which is what the transport abstracts: it is the term the goal actually contains, and
the rule's side may differ from it only up to conversion). `pairs` are the rule's
binder domains with their arguments: the arguments' types solve the implicit
parameters that matching a value does not reach. `none` is no match. -/
partial def matchRule (gl : Goal R) (g : Globals R) (A pat lhs rhs happ : Term R)
    (pairs : List (Term R × Term R)) :
    ElabM R (Option (Term R × Term R × Term R × Term R × Term R)) := do
  let lvl := gl.ctx.lvl
  let goalT ← zonk lvl (quote g lvl gl.ty)
  let rc := RCtx.ofLocal gl.ctx
  let pvRaw ← evalIn gl.ctx pat
  let pvF ← force pvRaw
  -- (a pattern that computes to a data value: only a *closed* one is matched, by plain
  -- structural unification. A data value with rule variables (`List.map f (x :: xs)`)
  -- has already computed in the goal too, and asking the unifier about it against the
  -- goal's values can force an ill-typed `vApp`; such rules are refused. A pattern that
  -- does not compute to a data value is unified as evaluated; forcing it would unfold
  -- `Nat.add ?n 0` into a stuck form that no longer matches the goal's.)
  if isConVal pvF && !pat.mvars.isEmpty then return none
  let pv := if isConVal pvF then pvF else pvRaw
  let rec go : List (Term R) → ElabM R (Option (Term R × Term R × Term R × Term R × Term R))
    | [] => pure none
    | cand :: rest => do
      let cv ← evalIn gl.ctx cand
      if isConVal pv && !isConVal cv then go rest
      else do
        let s ← get
        let r ← try
          unify lvl pv cv
          -- the arguments' types solve the implicit parameters (the match works on values)
          for (dom, arg) in pairs do
            let arg' ← zonk lvl arg
            if arg'.mvars.isEmpty then
              match ← rc.typeOf? arg' with
              | some ty => unify lvl (← evalIn gl.ctx dom) ty
              | none => pure ()
          let app ← zonk lvl happ
          if !app.mvars.isEmpty then pure none
          else do
            let A' ← zonk lvl A
            let a' ← zonk lvl lhs
            let b' ← zonk lvl rhs
            if !A'.mvars.isEmpty || !a'.mvars.isEmpty || !b'.mvars.isEmpty then pure none
            -- (a rule that rewrites a term to itself is not a step)
            else if a' == b' then pure none
            else pure (some (A', a', b', app, cand))
        catch _ => pure none
        match r with
        | some p => pure (some p)
        | none => do set s; go rest
  go (subtermsPre goalT)

/-! ## Congruence: rewriting under binders

`subtermsPre` returns bare subterms; the terms under a binder use variables of the
extended context, so matching them in the goal's context is wrong. `rewriteDeep` walks
the goal type with the real context for each λ binder, matches the rule at every node
and rebuilds the term with a proof `new = old`:

* under a λ, the proof is the pointwise (definitional) equality of functions, `.lam`;
* at any other node, the child's proof is transported through the parent with
  `transp` on the one-hole context (`Term.abstract`);
* a `Π` (a type former) is not traversed: an equality of `Π`s is not pointwise in this
  kernel, so `simp` leaves it to `intro`/P1 rather than build an unsound transport;
* a match is attempted only where the rule's telescope instantiates in that context, so
  the replacement may mention the bound variable.

The Wiz driver still owns rule order, fuel and `all`: `rewriteDeep` rewrites the first
matching node, and the driver restarts the pass. -/

/-- Instantiate a rule's `∀` telescope in `ctx`, then match its left side against the
whole term `t`: the same checks as `matchRule`, one candidate. -/
partial def matchCand (_g : Globals R) (ctx : LocalCtx R) (A pat lhs rhs happ : Term R)
    (pairs : List (Term R × Term R)) (cand : Term R) :
    ElabM R (Option (Term R × Term R × Term R × Term R × Term R)) := do
  let lvl := ctx.lvl
  let rc := RCtx.ofLocal ctx
  let pvRaw ← evalIn ctx pat
  let pvF ← force pvRaw
  if isConVal pvF && !pat.mvars.isEmpty then return none
  let pv := if isConVal pvF then pvF else pvRaw
  let cv ← evalIn ctx cand
  if isConVal pv && !isConVal cv then return none
  else do
    let s ← get
    let r ← try
      unify lvl pv cv
      for (dom, arg) in pairs do
        let arg' ← zonk lvl arg
        if arg'.mvars.isEmpty then
          match ← rc.typeOf? arg' with
          | some ty => unify lvl (← evalIn ctx dom) ty
          | none => pure ()
      let app ← zonk lvl happ
      if !app.mvars.isEmpty then pure none
      else do
        let A' ← zonk lvl A
        let a' ← zonk lvl lhs
        let b' ← zonk lvl rhs
        if !A'.mvars.isEmpty || !a'.mvars.isEmpty || !b'.mvars.isEmpty then pure none
        else if a' == b' then pure none
        else pure (some (A', a', b', app, cand))
    catch _ => pure none
    match r with
    | some p => pure (some p)
    | none => do set s; pure none

/-- The kernel context of a local context (as `Goal.kernelCtx`, for a binder extension). -/
def localKernelCtx (g : Globals R) (ctx : LocalCtx R) : Ctx R :=
  { globals := g, env := ctx.env,
    names := ctx.names.reverse.toArray,
    qtys := (ctx.names.map fun _ => QPoly.const QuantitySyntax.explicitDefault).reverse.toArray,
    types := ctx.types.reverse.toArray, lvl := ctx.lvl, erased := true }

/-- Prepare `h` as a rule in `ctx`: its equation after the telescope (fresh metavariables
in `ctx`), the applied lemma and the binder arguments. -/
def prepareIn (g : Globals R) (ctx : LocalCtx R) (h : Term R) :
    ElabM R (Option (Term R × Term R × Term R × Term R × List (Term R × Term R))) := do
  let r? ← ruleType? ctx g h
  let (body, happ, pairs) ← match r? with
    | some p => pure p
    | none => do
      let hty ← match (← get).kernelInfer (localKernelCtx g ctx) h with
        | .ok ty => pure ty
        | .error e => throwAt ctx.info s!"simp: {e}" ErrorCode.tacticFailed
      let htyT ← zonk ctx.lvl (quote g ctx.lvl hty)
      let (b, ms) ← stripRule ctx 64 htyT
      pure (b, ms.foldl (fun f m => .app f m) h, [])
  match body with
  | .eq A lhs rhs => pure (some (A, lhs, rhs, happ, pairs))
  | _ => pure none

/-- `b = a` from `e : a = b`, by transport. -/
def eqSym (A a b : Term R) (e : Term R) : Term R :=
  .transp A a (.lam "x" (.eqTy (.var 0) (a.lift 1))) (.reflTy a) b e

/-- Rewrite the first node of goal `gl`'s type that the rule `h` matches, descending
through λs and non-dependent applications: `(new type, proof new = old)`. -/
partial def rewriteDeep (gl : Goal R) (g : Globals R) (h : Term R) (rtl : Bool) :
    ElabM R (Option (Term R × Term R)) := do
  let goalT ← zonk gl.ctx.lvl (quote g gl.ctx.lvl gl.ty)
  let rec go (ctx : LocalCtx R) (t : Term R) : ElabM R (Option (Term R × Term R)) := do
    let depth := ctx.lvl - gl.ctx.lvl
    let prepared ← prepareIn g ctx (h.lift depth)
    let matched ← match prepared with
      | some (A, lhs, rhs, happ, pairs) =>
        let pat := if rtl then rhs else lhs
        match ← matchCand g ctx A pat lhs rhs happ pairs t with
        | some (A', a', b', app, _) =>
          -- `a'` is the rule's left side, `b'` its right side; the node is `a'` up to
          -- conversion; return `new = old`
          if rtl then pure (some (a', app))
          else pure (some (b', eqSym A' a' b' app))
        | none => pure none
      | none => pure none
    match matched with
    | some r => pure (some r)
    | none => match t with
      | .pi .. => pure none
      | .lam x body => do
        let tyTerm ← freshTypeMeta ctx "simp binder"
        let ty ← evalIn ctx tyTerm
        let ctx' := ctx.bind x ty
        match ← go ctx' body with
        | some (bodyNew, pfBody) => pure (some (.lam x bodyNew, .lam x pfBody))
        | none => pure none
      | _ => do
        -- immediate children at binder depth 0, in order
        let kids := (t.forChildren (m := StateM (List (Term R))) (fun _ => pure ())
          (fun k c => if k == 0 then modify fun xs => xs ++ [c] else pure ()) []).2
        let rec tryKids : List (Term R) → ElabM R (Option (Term R × Term R))
          | [] => pure none
          | kid :: rest => do
            let s ← get
            match ← go ctx kid with
            | some (kidNew, pf) => do
              let C := t.abstract kid
              let parentNew := C.instantiateAt 0 kidNew
              if parentNew == t then do set s; tryKids rest
              else do
                -- `A` is the child's type: let the kernel solve the hole from the proof
                let A ← freshTypeMeta ctx "simp congr"
                let sym := .transp A kidNew (.lam "x" (.eqTy (.var 0) (kidNew.lift 1)))
                  (.reflTy kidNew) kid pf
                let P : Term R := .lam "x" (.eqTy (.app (C.lift 1) (.var 0)) (t.lift 1))
                pure (some (parentNew, .transp A kid P (.reflTy t) kidNew sym))
            | none => do set s; tryKids rest
        tryKids kids
  go gl.ctx goalT

end Wiz.Elab
