import Wiz.Elab.Zonk
import Wiz.Elab.Macro
import Wiz.Elab.Tactic
import Wiz.Elab.Class
import Wiz.Elab.Struct
import Wiz.Smt.Translate
import Wiz.Smt.Sat

/-!
# Elaborating terms

Bidirectional, like the kernel, but on `Syntax` and with metavariables:

    check ctx stx A : ElabM (Term R)          -- elaborate stx against type A
    infer ctx stx   : ElabM (Term R × VTy R)  -- elaborate stx and compute its type

## Implicit arguments

Two mechanisms, following elaboration-zoo `04-implicit-args`:

* **Insertion of implicit applications.** (Holes are untyped, so the type of an
  implicit argument is recorded for later when it fixes a universe level:
  `noteImplicitType`.) When a term of type `{A : Type} → A → A` is
  used where something that isn't an implicit function is expected, `?A` is inserted:
  `id` becomes `id ?A`. This happens before each explicit argument and in `check`'s
  fallback case. `@f` turns it off.
* **Insertion of implicit lambdas.** Checking a term against `{A : Type} → B`, unless
  the term is itself a `fun {A} => …`, elaborates it under an extra implicit binder.
  So `fun x => x` checks against `{A : Type} → A → A`.

## The node kinds handled here

See `Wiz.Parser.Builtin` for their children. Anything else is reported as
"no elaborator for syntax kind ...". Stage 6 makes that table extensible.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

/-! ## Reading binders -/

/-- One binder name with everything that applies to it. -/
structure BinderView where
  name : Name
  info : SourceInfo
  bi : BinderInfo
  qty : Option Syntax
  type : Option Syntax

private def binderName (s : Syntax) : Name :=
  match s with
  | .ident _ n => n
  | _ => "_"

/-- Expand a binder (`x`, `_`, `(1 x y : A)`, `{A}`, ...) into one view per name. -/
def binderViews (stx : Syntax) : Array BinderView :=
  match stx.kind with
  | "binder.explicit" | "binder.implicit" =>
    let bi := if stx.isOfKind "binder.implicit" then .implicit else .default
    let qty := (stx.getArg 1).args[0]?
    let type := (stx.getArg 3).args[1]?
    (stx.getArg 2).args.map fun n => { name := binderName n, info := n.info, bi, qty, type }
  | "binder.inst" =>
    let name := (((stx.getArg 1).args[0]?).bind Syntax.getId?).getD "inst✝"
    #[{ name, info := stx.info, bi := .instImplicit, qty := none, type := some (stx.getArg 2) }]
  | _ => #[{ name := binderName stx, info := stx.info, bi := .default, qty := none, type := none }]

/-- A quantity literal (`0`, `1`, `ω`, …) as a term. -/
def elabQtyLit (ctx : LocalCtx R) (stx : Syntax) (lit : String) : ElabM R (Term R) :=
  match QuantitySyntax.ofLiteral lit with
  | some r => pure (.qlit r)
  | none => throwAt (ctx.withInfo stx).info s!"'{lit}' is not a quantity of this rig"

def defaultQty (bi : BinderInfo) : Term R :=
  .qlit (if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault)

/-- **Exercise 4.2.** Elaborate a universe level (see `Builtin.levelLeading` for the
node kinds). A `level.param` must be one of the declaration's universe parameters
(`(← get).levelParams`); `_` is a fresh level metavariable. -/
partial def elabLevel (stx : Syntax) : ElabM R Level := do
  --<sol
  match stx.kind with
  | "level.num" => pure (Level.ofNat ((stx.getArg 0).getNat?.getD 0))
  | "level.param" =>
    let u := ((stx.getArg 0).getId?).getD "_"
    unless (← get).levelParams.contains u do
      throwAt stx.info s!"unknown universe level '{u}'"
    pure (.param u)
  | "level.hole" => freshLevelMeta
  | "level.paren" => elabLevel (stx.getArg 1)
  | "level.max" => return .max (← elabLevel (stx.getArg 1)) (← elabLevel (stx.getArg 2))
  | "level.imax" => return .imax (← elabLevel (stx.getArg 1)) (← elabLevel (stx.getArg 2))
  | "level.add" =>
    return (← elabLevel (stx.getArg 0)).addOffset ((stx.getArg 2).getNat?.getD 0)
  | k => throwAt stx.info s!"unexpected level syntax {k}"
  --|ex
  --| sorry
  --sol>

/-- Look a name up in the local context, innermost first. -/
def lookupLocal (ctx : LocalCtx R) (x : Name) : Option (Nat × VTy R) := Id.run do
  for n in ctx.names, ty in ctx.types, i in [0:ctx.lvl] do
    if n == x && x != "_" then return some (i, ty)
  none

/-- (Given) Metas are untyped, so what the type `dom` of the implicit argument `m` of
`f` says about universe levels is recorded, to be checked once `m` is solved
(`solveSortConstraints`): its universe, if it is a type (`{A : Type ?u}`), or its type,
if that mentions a level metavariable of `f` (`{C : Category.{?a, ?b}}`, where nothing
else may fix `?a` and `?b`). -/
def noteImplicitType (ctx : LocalCtx R) (f m : Term R) (dom : VTy R) : ElabM R Unit := do
  if let .sort l ← force dom then addSortConstraint ctx m l; return
  let some us := (match (Term.spine f).1 with | .const _ us => some us | _ => none) | return
  if ← us.anyM (fun u => return (← instLevel u).hasMVar) then addTypeConstraint ctx m dom

/-- **Exercise 3.7.** Insert implicit applications: while the type forces to an
*implicit* Π, apply the term to a fresh metavariable and instantiate the codomain with
the metavariable's value. -/
partial def insertImplicits (ctx : LocalCtx R) (t : Term R) (ty : VTy R) :
    ElabM R (Term R × VTy R) := do
  -- (given, stage 7) an instance argument: a hole for instance resolution
  if let .pi x .instImplicit _ dom cod _ ← force ty then
    let m ← freshMeta ctx s!"instance {x}"
    addInstProblem ctx m dom
    return ← insertImplicits ctx (.app t m) (← instM cod (← evalIn ctx m))
  --<sol
  match ← force ty with
  | .pi x .implicit _ dom cod _ =>
    let m ← freshMeta ctx s!"implicit argument {x}"
    noteImplicitType ctx t m dom
    insertImplicits ctx (.app t m) (← instM cod (← evalIn ctx m))
  | _ => pure (t, ty)  -- the type as it was (forcing would lose glued names)
  --|ex
  --| sorry
  --sol>

/-- Does this (function) type take only implicit and instance arguments before its
explicit ones, and at least one instance argument (`{B} → [C B] → T`)? Such trailing
instance arguments are inserted after an application. -/
partial def trailingInst (lvl : Lvl) (ty : VTy R) : ElabM R Bool := do
  match ← force ty with
  | .pi _ .instImplicit .. => pure true
  | .pi _ .implicit _ _ cod _ => trailingInst (lvl + 1) (← instM cod (Val.var lvl))
  | _ => pure false

/-- Is `h` (not shadowed) a constructor with implicit parameters (`Fin.mk : {n} → …`)?
Applied in check mode, it takes them from the expected type first (`checkApp`), so that
an argument whose type mentions them (`.mk (Nat.succ i) h`) is checked against
instantiated types. (Constructors are the inline declarations.) -/
def ctorWithParams (ctx : LocalCtx R) (h : Syntax) : ElabM R Bool := do
  unless h.isOfKind "term.ident" do return false
  let some n := (h.getArg 0).getId? | return false
  if (lookupLocal ctx n).isSome then return false
  let some d := (← getGlobals).find? (stripScope n) | return false
  return d.inline && d.type matches .pi _ .implicit ..

def isOwnVar (v : Val R) (l : Lvl) : Bool := match v with
  | .neutral (.local l') #[] => l' == l
  | _ => false

/-- Is every variable of the context its own value (none substituted away by a `match`
on an index)? -/
def placeholderFull (ctx : LocalCtx R) : Bool :=
  (ctx.env.zip (List.range ctx.lvl).reverse).all fun (v, l) => isOwnVar v l

/-- A placeholder metavariable for an argument (`checkApp`): like `freshMeta`, but
applied only to the bound variables that are their own values, so that unifying it with
the argument stays in the pattern fragment in a `match` branch whose context has
variables replaced by others (index unification). -/
def freshPlaceholder (ctx : LocalCtx R) : ElabM R (Term R) := do
  let m := (← get).metas.size
  let live := (ctx.bound.zip (ctx.env.zip (List.range ctx.lvl).reverse)).reverse.map fun (b, v, l) =>
    b && isOwnVar v l
  modify fun s => { s with metas := s.metas.push { info := ctx.info, desc := "an argument", arity := (live.filter id).length } }
  let mut t : Term R := .mvar m
  for b in live, lvl in [0:ctx.lvl] do
    if b then t := .app t (.var (ctx.lvl - lvl - 1))
  pure t

/-- Names the elaborator treats as data primitives when applied (and not shadowed). -/
def builtinNames : List Name :=
  ["Desc", "Desc.ret", "Desc.arg", "Desc.rec", "Desc.hrec", "Desc.elim", "Desc.interp", "Desc.All",
   "μ", "ν", "con", "ind", "out", "coit", "cocon"]

/-- `f a₁ … aₙ` where `f` is an unshadowed built-in name. -/
def builtinApp? (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Option (Name × Array Syntax)) := do
  unless stx.isOfKind "term.app" do return none
  let head := stx.getArg 0
  unless head.isOfKind "term.ident" do return none
  let some n := (head.getArg 0).getId? | return none
  if (lookupLocal ctx n).isSome then return none
  let n := stripScope n
  unless builtinNames.contains n do return none
  if (lookupLocal ctx n).isSome || (← getGlobals).contains n then return none
  return some (n, (stx.getArg 1).args)

/-- The term for a string literal, `String.mk [Char.mk n, …]` with numerals `n`. The
prelude's names are fixed here. -/
def mkStringLit (str : String) (us : List Level := []) : ElabM R (Term R) := do
  let S := ((← get).builtins.lookup "string").getD "String"
  let charTy : Term R := .const "Char" []
  let chr (c : Char) : Term R := .app (.const "Char.mk" []) (.natLit c.toNat)
  let list := str.toList.foldr (fun c t => Term.app (.app (.app (.const "List.cons" []) charTy) (chr c)) t)
    (.app (.const "List.nil" []) charTy)
  pure (.app (.const (S ++ ".mk") us) list)

/-- (HD9) A numeral `n` at a type `A` other than the `builtin nat` type:
`@OfNat.ofNat A n ?inst`, with an instance problem `OfNat A n` (the literal is an
index of the class, as in Lean, so an instance may inspect it). `none` if the Prelude
has no `OfNat` class. -/
def ofNatLit? (ctx : LocalCtx R) (n : Nat) (A : VTy R) : ElabM R (Option (Term R)) := do
  let s ← get
  unless s.classes.any (·.name == "OfNat") do return none
  let some d := s.globals.find? "OfNat.ofNat" | return none
  let us ← d.levelParams.mapM fun _ => freshLevelMeta
  let g ← getGlobals
  let fty := eval g [] (d.type.instLevels d.levelParams us)
  let .pi _ _ _ domA codA _ ← force fty | return none
  let qA := quote g ctx.lvl A
  if let .sort l ← force domA then addSortConstraint ctx qA l
  let .pi _ _ _ _ codN _ ← force (← instM codA A) | return none
  let .pi x .instImplicit _ dom _ _ ← force (← instM codN (.natLit n)) | return none
  let m ← freshMeta ctx s!"instance {x}"
  addInstProblem ctx m dom
  -- a numeral that doesn't fit a fixed-width word of lib/Word.wiz wraps around: say so
  -- (outside lib/Word.wiz the word types are opaque, 13b/22k: a constant applied to `w`)
  let word? : Option (Name × Val R) := match ← force A with
    | .mu _ _ _ _ _ (some (T, _, w :: _)) => some (T, w)
    | .neutral (.global T _) #[.app w] => some (T, w)
    | _ => none
  if let some (T, w) := word? then
    if T == "UIntN" || T == "IntN" then
      if let .natLit w := whnf w then
        if w ≤ 4096 then
          let limit := if T == "UIntN" then 2 ^ w - 1 else 2 ^ (w - 1)
          if n > limit then
            let bits := n % 2 ^ w
            let wrapped := if T == "IntN" && bits ≥ 2 ^ (w - 1) then s!"-{2 ^ w - bits}" else toString bits
            pushInfo (.done (.warning ctx.info
              s!"the numeral {n} does not fit in {T} {w} (at most {limit}): it wraps around to {wrapped}"))
  pure (some (.app (.app (.app (.const "OfNat.ofNat" us) qA) (.natLit n)) m))

/-- `(x).f y` parses as `(x)` applied to `.f` and `y` (an argument `.f` is a constructor
of the expected type): an argument `.f` right after the previous one, without a space,
is a field of it instead (`term.field`), as in `x.f y`. -/
def adjacentFields? (stx : Syntax) : Option Syntax := do
  guard (stx.isOfKind "term.app")
  let args := (stx.getArg 1).args
  let adjacent (prev a : Syntax) : Bool :=
    a.isOfKind "term.dotIdent" && a.info.start > 0 && a.info.start == prev.info.stop
  let mut items : Array Syntax := #[stx.getArg 0]
  let mut changed := false
  for a in args do
    if adjacent items.back! a then
      let prev := items.back!
      items := items.pop.push (.node { start := prev.info.start, stop := a.info.stop } "term.field"
        #[prev, a.getArg 0, a.getArg 1])
      changed := true
    else items := items.push a
  guard changed
  if items.size == 1 then pure items[0]!
  else pure (.node stx.info "term.app" #[items[0]!, .node {} "null" (items.extract 1 items.size)])

/-- Expand a macro at `stx`, with a fresh scope. -/
def expand? (stx : Syntax) : ElabM R (Option Syntax) := do
  if let some stx' := adjacentFields? stx then return some stx'
  let s ← get
  -- (11q) what expanded the syntax the user wrote, for hovers and go to definition
  let recordExp (h : SyntaxHandler) (stx' : Syntax) : ElabM R Unit :=
    if stx.info.stop > 0 then pushInfo (.done (.expansion stx.info stx.kind h (some stx'))) else pure ()
  match expandMacroRule? s.macros stx s.nextScope with
  | some (stx', r) =>
    modify (fun s => { s with nextScope := s.nextScope + 1 })
    recordExp (.rule r.site r.module) stx'
    pure (some stx')
  | none =>
    let some f := s.procMacros.lookup stx.kind | pure none
    let (traces, r) := s.runProcMacro f stx s.nextScope
    for t in traces do pushTrace stx.info t
    match r with
    | .ok (stx', next) =>
      modify (fun s => { s with nextScope := next })
      recordExp (.fn "macro" f) stx'
      pure (some stx')
    | .error e => throwAt stx.info e

/-- Expand the macros in a pattern (a list literal `[x, y]`, a user notation), outside
in: the pattern forms `patView` reads (constructors, applications, tuples, parentheses)
are left as they are and their parts expanded. A pattern that is no macro stays as it
is, for `patView` to accept or reject. -/
partial def expandPattern (stx : Syntax) : ElabM R Syntax := do
  match stx with
  | .node info k args =>
    if k == "null" || k == "term.paren" || k == "term.tuple" || k == "term.app" || k == "term.anon" || k == "term.asPat" then
      return .node info k (← args.mapM expandPattern)
    if k == "term.ident" || k == "term.hole" || k == "term.dotIdent" then return stx
    match ← expand? stx with
    | some stx' => expandPattern stx'
    | none => pure stx
  | _ => pure stx

/-- Unify, turning a failure into a readable type mismatch at `stx`.

Unification is untyped, so it misses the η-rule for `Unit` (`P x =?= P ()` with
`x : Unit`). When it fails, we ask the kernel's type-directed `convTy`, which treats
unsolved metas as rigid, before giving up. -/
def unifyAt0 (ctx : LocalCtx R) (stx : Syntax) (expected inferred : VTy R) : ElabM R Unit :=
  fun s => match unify ctx.lvl expected inferred s with
    | .ok r => .ok r
    | .error e =>
      if subTy s.globals ctx.types.reverse.toArray inferred expected then .ok ((), s) else
      let show' (v : VTy R) := elideLong ((quote s.globals ctx.lvl v).pretty ctx.names (some s.globals))
      .error { info := (ctx.withInfo stx).info,
               msg := s!"type mismatch\n  expected: {show' expected}\n  inferred: {show' inferred}" ++
                 mismatchReason (show' expected) (show' inferred) e.msg,
               code := if e.code == ErrorCode.nonPattern then e.code else ErrorCode.typeMismatch,
               -- what was recorded up to here (the info tree, `trace`s)
               state? := some s }

/-- A type evaluated while some of its holes were unsolved: an equation in it computed
(or got stuck) on the holes, and stays so after they are solved (`w ?n = 8`). Evaluate it
again with the solutions (`none` if it mentions no solved hole). -/
def reevalSolved? (ctx : LocalCtx R) (v : VTy R) : ElabM R (Option (VTy R)) := do
  let t := quote (← getGlobals) ctx.lvl (← forceMeta v)
  let ms := t.mvars
  if ms.isEmpty then return none
  let mut anySolved := false
  for m in ms do
    if (← lookupMeta m).solution.isSome then anySolved := true
  if !anySolved then return none
  return some (← evalIn ctx (← zonk ctx.lvl t))

/-- `unifyAt0`, and when it fails, once more with both types evaluated again with the
holes solved since (see `reevalSolved?`). -/
def unifyAt (ctx : LocalCtx R) (stx : Syntax) (expected inferred : VTy R) : ElabM R Unit := do
  let s ← get
  try unifyAt0 ctx stx expected inferred
  catch err =>
    set s
    let e' ← reevalSolved? ctx expected
    let i' ← reevalSolved? ctx inferred
    if e'.isNone && i'.isNone then throw err
    unifyAt0 ctx stx (e'.getD expected) (i'.getD inferred)

/-- Is this the type of a type (`… → Type u`)? -/
def endsInSort : Term R → Bool
  | .pi _ _ _ _ b _ => endsInSort b
  | .sort _ => true
  | _ => false

/-- The hint under "function expected" for `f : ty` given one more argument: `f` already
applied to arguments has too many; implicit arguments shown as holes can be given with
`@`. -/
def tooManyArgsHint (f : Term R) : String :=
  match Term.spine f with
  | (_, []) => ""
  | (h, _) =>
    let at_ := match h with
      | .const n _ => s!"; its implicit arguments (the ?m here) are filled in automatically: to give them, write @{Globals.privateBase n} …"
      | _ => ""
    if f.mvars.isEmpty then "\n  (it is given more arguments than its type takes)"
    else s!"\n  (it is given more arguments than its type takes{at_})"

/-- Is this a `fun` whose first binder is implicit? -/
private def isImplicitFun (stx : Syntax) : Bool :=
  stx.isOfKind "term.fun" &&
    match (stx.getArg 1).args[0]? with
    | some b => b.isOfKind "binder.implicit"
    | none => false

/-- `t.f` as `D.f t`, for a type `D a…` that is a glued definition (a structure, say)
with a declaration `D.f` (or, if `D a…` unfolds to another glued definition `E b…`, by
`E.f`, and so on): `D.f`'s implicits become holes and its first explicit argument is
`t`. `none` if there is no such declaration. -/
partial def fieldByTypeName? (ctx : LocalCtx R) (t : Term R) (ty : VTy R) (f : Name) :
    ElabM R (Option (Term R × VTy R)) := do
  let g ← getGlobals
  let mut v ← forceMeta ty
  for _ in [0:16] do
    match v with
    | .unfold n us _ next =>
      let Df := g.resolve (n ++ "." ++ f)
      if let some d := g.find? Df then
        if let some m := g.privateTo? Df then
          throwAt ctx.info s!"'{Globals.privateBase n}.{f}' is private to module {m}" "private"
        let dus ← d.levelParams.mapM fun _ => freshLevelMeta
        let fty : VTy R := eval g [] (d.type.instLevels d.levelParams dus)
        let (tm, fty) ← insertImplicits ctx (.const Df dus) fty
        let .pi _ _ _ dom cod _ ← force fty | return none
        unifyAt ctx (.missing) dom ty
        let _ := us
        return some (Term.app tm t, ← instM cod (← evalIn ctx t))
      v ← forceMeta next.get
    | _ => return none
  return none

/-- **Exercise 4.9.** Field access by name: `t.f₁.f₂…`. Starting from `t : ty`, for
each field name walk the Σ telescope of the (forced) type: if the current Σ's binder
name is the field, project with `fst`; otherwise move on with `snd`, instantiating the
second component's type with the first projection. Throw if the field isn't found.
Returns the projected term and its type. -/
partial def elabFields (ctx : LocalCtx R) (t : Term R) (ty : VTy R) (fields : List Name) :
    ElabM R (Term R × VTy R) := do
  -- (given, 7f) a value of a type not known yet (`(2 + 3).succ`): the stuck instance
  -- problems take their default instances first, which may decide it
  if !fields.isEmpty then
    if (← force ty) matches .neutral (.mvar _) _ then
      unless (← get).pendingInsts.isEmpty do synthDefaults
  -- (given, 13b) a structure with a constructor private to another module is opaque
  -- here: `t.f` is its projection function `S.f t`
  if let f :: rest := fields then
    if let .neutral (.global S us) _ ← force ty then
      let g ← getGlobals
      if g.opaques.contains S then
        let some d := g.find? (S ++ "." ++ f)
          | throwFix ctx.info s!"no field '{f}' in a value of type {← showVal ctx ty}" ErrorCode.noSuchField
              [("name", [f]), ("type", [S])]
        if let some m := g.privateTo? (S ++ "." ++ f) then
          throwAt ctx.info s!"'{Globals.privateBase S}.{f}' is private to module {m}" "private"
        let fty : VTy R := eval g [] (d.type.instLevels d.levelParams us)
        let (tm, fty) ← insertImplicits ctx (.const (S ++ "." ++ f) us) fty
        let .pi _ _ _ dom cod _ ← force fty | throwAt ctx.info s!"{S}.{f} is not a function of {S}"
        unifyAt ctx (.missing) dom ty
        return ← elabFields ctx (Term.app tm t) (← instM cod (← evalIn ctx t)) rest
  --<sol
  match fields with
  | [] => pure (t, ty)
  | f :: rest =>
    -- generalised field notation: `t.f` is `T.f t` for a nominal type `T`
    let hint? : Option (Name × List Level × List (Val R)) := match ← force ty with
      | .mu _ _ _ _ _ h | .nu _ _ _ _ _ h => h
      | _ => none
    if let some (T, us, args) := hint? then
      let Tf := (← getGlobals).resolve (T ++ "." ++ f)
      if let some d := (← getGlobals).find? Tf then
        if let some m := (← getGlobals).privateTo? Tf then
          throwAt ctx.info s!"'{Globals.privateBase T}.{f}' is private to module {m}" "private"
        -- `T.f : {…} → T … → F`: insert the implicits as metavariables, then unify
        let fty : VTy R := eval (← getGlobals) [] (d.type.instLevels d.levelParams us)
        let (tm, fty) ← insertImplicits ctx (.const Tf us) fty
        let .pi _ _ _ dom cod _ ← force fty | throwAt ctx.info s!"{T}.{f} is not a function of {T}"
        unifyAt ctx (.missing) dom ty
        let tm' := Term.app tm t
        return ← elabFields ctx tm' (← instM cod (← evalIn ctx t)) rest
    -- the type the field was looked up in, for the error (not what is left of its Σs)
    let ty0 := ty
    let noField : ElabM R (Term R × VTy R) := do
      let g ← getGlobals
      match structHead? g (← forceMeta ty0) with
      | some (S, _, _) =>
        let fields := ((structLayout? g S).map (·.fields)).getD []
        throwFix ctx.info s!"{Globals.privateBase S} has no field '{f}' (its fields are {", ".intercalate fields})"
          ErrorCode.noSuchField [("name", [f]), ("type", [S]), ("fieldsOnly", [])]
      | none =>
        let msg := s!"no field '{f}' in a value of type {← showVal ctx ty0}"
        throwFix ctx.info msg ErrorCode.noSuchField [("name", [f]), ("type", (hint?.map (·.1)).toList)]
    let rec walk (t : Term R) (ty : VTy R) : ElabM R (Term R × VTy R) := do
      match ← force ty with
      | .sigma x _ A B _ =>
        if x == f then pure (.fst t, A)
        else walk (.snd t) (← instM B (vFst (← evalIn ctx t)))
      | _ => noField
    let (t, ty) ← tryCatch (walk t ty) fun err => do
      -- not a field: generalised field notation by the name of the type, `D.f t` for a
      -- type `D a…` (a structure, or any definition, as the type is written: glued)
      match ← fieldByTypeName? ctx t ty f with
      | some r => pure r
      | none => throw err
    elabFields ctx t ty rest
  --|ex
  --| sorry
  --sol>

/-! ## Pattern matching (stage 4e)

`match` and equation-style definitions compile to a **case tree** over local
variables, built from the generated `T.casesOn` (and `T.rec` for structural recursion).
Splitting a variable `x : T Δ ξ`:

* the variables matched *after* `x` are reverted into the motive and re-introduced in
  every branch, so their types can mention `x`;
* if the indices `ξ` are distinct variables, the motive generalises them, and each
  branch sees them replaced by the constructor's indices (Cockx's *solution* rule);
* otherwise the motive takes an equation `idx_c = ξ`. Observational equality
  *computes* it: for an impossible constructor it contains `False`, and the branch is
  closed with `absurd` (so impossible cases can be left out). Injectivity and
  conflict therefore need no code of their own.

Structural recursion: in `def f : … | pats => rhs` where the right-hand sides call
`f`, the first column is split with `T.rec`, and a call `f y a…` on a recursive field
`y` becomes the induction hypothesis for `y` applied to `a…` (the other arguments are
generalised by the motive, so they may change in recursive calls). -/

/-- A clause of a case tree: one pattern per remaining variable, the right-hand side,
and the pattern variables bound so far (name, type, value). -/
structure MClause (R : Type) where
  pats : List Syntax
  rhs : Syntax
  binds : List (Name × VTy R × Val R) := []

inductive PatView where
  | var (n : Name)
  | wild
  /-- a constructor pattern: optional type name (from `T.c`), constructor, arguments -/
  | ctor (T : Option Name) (c : Name) (args : List Syntax)
  /-- a pair pattern `(a, b)` (`(a, b, c)` is `(a, (b, c))`) -/
  | tuple (a b : Syntax)
  /-- (13g) an as-pattern `x@p`: `p`, with `x` bound to the matched value -/
  | as (n : Name) (p : Syntax)
  /-- (13h) an anonymous constructor pattern `⟨p₁, …, pₙ⟩`: the constructor of the
  scrutinee's structure (or one-constructor data type), or a tuple -/
  | anon (args : List Syntax)
  /-- (13q) a literal pattern: a numeral `3` (or a string `"ab"`), the syntax itself -/
  | lit (stx : Syntax)
  /-- (13q) `p + k` with a numeral `k > 0`, at `Nat`: `succ` applied `k` times to `p` -/
  | plusK (p : Syntax) (k : Nat)
  deriving Inhabited

/-- (13q) The numeral `n` as syntax (at the range `info`). -/
def numStx (info : SourceInfo) (n : Nat) : Syntax :=
  .node info "term.num" #[.node info "num" #[.atom info (toString n)]]

/-- (13q) The pattern `p + k` as syntax (`Add.add p k`, as `+` expands). -/
def plusKStx (info : SourceInfo) (p : Syntax) (k : Nat) : Syntax :=
  if k == 0 then p else
  .node info "term.app" #[.node info "term.ident" #[.ident info "Add.add"], .node {} "null" #[p, numStx info k]]

def holeStx : Syntax := .node {} "term.hole" #[.atom {} "_"]

/-- Recursion context: the function's name, and which field levels have hypotheses.
A recursive call `f p… a…` passes the explicit parameters (`params`, the binders before
the colon) unchanged, and recurses on its argument number `pos` (after the parameters);
its other arguments go to the hypothesis. -/
structure RecCtx where
  fn : Name
  ihs : List (Lvl × Lvl) := []
  params : List Name := []
  pos : Nat := 0
  /-- the number of matched arguments: a call with no more arguments than that leaves
  the parameters out (they are fixed anyway) -/
  cols : Nat := 0
  /-- all the parameters, and whether each is explicit: `@f` passes them all -/
  allParams : List (Name × Bool) := []
  /-- (#249) whether each matched argument is explicit (empty: all are), in the
  definition's order: a call `f …` passes only the explicit ones -/
  colExplicit : List Bool := []
  /-- (#249) the matched arguments (in the definition's order) the hypothesis doesn't
  take: index variables generalised by the motive -/
  dropCols : List Nat := []

/-- The constructors of the data type `T` (the tags of its description). -/
def ctorNames (g : Globals R) (T : Name) : List Name :=
  match g.find? (T ++ ".desc") with
  | none => []
  | some descD =>
    let rec strip : Term R → Term R → Term R
      | .pi _ _ _ _ b _, .lam _ v => strip b v
      | _, v => v
    match descD.value with
    | some v => ((strip descD.type v).descTag?.map (·.1)).getD []
    | none => []

/-- A `mutual` block's constructor `n` (`Ev.s`, `ctorConst`): its family `F`, the data
type whose constructor it is (the head of its result type), if `n` is one of `F`'s
qualified tags. -/
def familyCtor? (g : Globals R) (n : Name) : Option Name := do
  guard (n.contains '.')
  let d ← g.find? n
  let rec res : Term R → Term R
    | .pi _ _ _ _ b _ => res b
    | t => t
  let .const F _ := (Term.spine (res d.type)).1 | none
  if (ctorNames g F).contains n then some F else none

/-- Is the qualified tag `X.c` of a `mutual` block's family (`ctorConst`) a constructor
of the type `ty`, that is, is `ty` the member `X := F F.Tag.X`? -/
def memberTag (g : Globals R) (tys : Array (VTy R)) (ty : VTy R) (t : Name) : Bool :=
  let X := (t.dropEnd ((ctorShort t).length + 1)).toString
  t.contains '.' && (g.find? X).isSome && convTy g tys ty (eval g [] (.const X []))

/-- The constructor that `.c` names at the expected type `expected`, a data type whose
`μ` has the nominal hint `T`: `T.c`; at a member of a `mutual` block (whose family `T`
holds the members' constructors under qualified tags, `ctorConst`), the member's own `c`
(`Ev.s`, not `Od.s`). -/
def dotCtor? (g : Globals R) (tys : Array (VTy R)) (T c : Name) (expected : VTy R) : Option Name :=
  if g.contains (T ++ "." ++ c) then some (T ++ "." ++ c) else
  let tags := (ctorNames g T).filter (·.contains '.')
  let cands := tags.filter fun t => ctorShort t == c
  let isMember := memberTag g tys expected
  match cands.find? isMember with
  | some t => some t
  | none =>
    -- the expected member is known and has no `c`; or it isn't known (a hole in the
    -- index), and only one member has a `c`
    if tags.any isMember then none else match cands with
    | [t] => some t
    | _ => none

partial def patView (g : Globals R) (stx : Syntax) : Except String PatView :=
  let ctorOf (n : Name) : Option (Name × Name) :=
    -- (13b) this module's private type's constructor, under its kernel name
    let n := g.resolve n
    match (n.splitOn ".").reverse with
    | c :: T@(_ :: _) =>
      let T := ".".intercalate T.reverse
      if g.contains (T ++ ".desc") && g.contains n then some (T, c)
      -- (13h) a structure's constructor
      else if c == "mk" && g.contains n && g.contains T then some (T, c)
      -- a `mutual` block's constructor `Ev.s`: the family, and the tag (the name itself)
      else (familyCtor? g n).map (·, n)
    | _ => none
  match stx.kind with
  | "term.paren" => patView g (stx.getArg 1)
  | "term.tuple" =>
    let rest := (stx.getArg 3).args.filter (!· matches .atom ..)
    match rest[0]? with
    | none => .error "invalid tuple pattern"
    | some b =>
      let b := if rest.size == 1 then b else
        .node stx.info "term.tuple" #[.atom {} "(", b, .atom {} ",", .node {} "null" (rest.extract 1 rest.size), .atom {} ")"]
      pure (.tuple (stx.getArg 1) b)
  | "term.hole" => pure .wild
  | "term.asPat" =>
    let x := stx.getArg 0
    if x.isOfKind "term.ident" then pure (.as ((x.getArg 0).getId?.getD "_") (stx.getArg 2))
    else .error "an as-pattern is `x@p` with a variable `x`"
  | "term.anon" => pure (.anon ((stx.getArg 1).args.filter (!· matches .atom ..)).toList)
  | "term.num" | "term.str" => pure (.lit stx)
  | "term.dotIdent" => pure (.ctor none ((stx.getArg 1).getId?.getD "_") [])
  | "term.ident" =>
    let n := (stx.getArg 0).getId?.getD "_"
    match ctorOf n with
    | some (T, c) => pure (.ctor (some T) c [])
    | none => pure (.var n)
  | "term.app" =>
    let h := stx.getArg 0
    let args := (stx.getArg 1).args.toList
    match h.kind with
    | "term.dotIdent" => pure (.ctor none ((h.getArg 1).getId?.getD "_") args)
    | "term.ident" =>
      let f := (h.getArg 0).getId?.getD "_"
      match ctorOf f with
      | some (T, c) => pure (.ctor (some T) c args)
      | none =>
        -- (13q) `p + k`, as `+` expands (`Add.add p k`, or `HAdd.hAdd p k`), with a numeral `k`
        -- (`HAdd.hAdd` too: `+` of the heterogeneous classes)
        match g.resolve f == "Add.add" || g.resolve f == "HAdd.hAdd", args with
        | true, [p, k] => match (if k.isOfKind "term.num" then (k.getArg 0).getNat? else none) with
          | some 0 => patView g p
          | some n => pure (.plusK p n)
          | none => .error "a pattern `p + k` needs a numeral `k` (as in `n + 2`)"
        | _, _ => .error "only constructors may be applied in patterns"
    | _ => .error "invalid pattern"
  | k => .error s!"invalid pattern ({k})"

/-- (13g) A pattern without its as-names: `x@y@p` is `([x, y], p)`. -/
partial def patViewAs (g : Globals R) (stx : Syntax) : Except String (List Name × PatView) := do
  match ← patView g stx with
  | .as n p => let (ns, v) ← patViewAs g p; pure (n :: ns, v)
  | v => pure ([], v)

/-- Is the pattern a constructor pattern (under as-names)? -/
def patIsCtor (g : Globals R) (stx : Syntax) : Bool :=
  match patViewAs g stx with
  | .ok (_, .ctor ..) | .ok (_, .lit _) | .ok (_, .plusK ..) => true
  | _ => false

/-- The pattern `x₁@…@xₙ@p`. -/
def asPatStx (ns : List Name) (p : Syntax) : Syntax :=
  ns.foldr (fun n acc => .node p.info "term.asPat" #[.node {} "term.ident" #[.ident {} n], .atom {} "@", acc]) p

/-- Find a component of type `False`/`Empty` inside a (Σ-nested) proof `e : ty`. -/
partial def findAbsurd (g : Globals R) (ty e : Val R) : Option (Val R) :=
  match ty with
  | .empty _ => some e
  | .sigma _ _ A B _ =>
    (findAbsurd g A (vFst e)).orElse fun _ => findAbsurd g (Closure.inst g B (vFst e)) (vSnd e)
  | _ => none

/-- The equations `a = b` (stuck, at a type `A`) inside a (Σ-nested) proof `e : ty`,
as `(proof, A, a, b)`. -/
partial def findEqs (g : Globals R) (ty e : Val R) : List (Val R × Val R × Val R × Val R) :=
  match ty with
  | .neutral (.eq A a b) #[] => [(e, A, a, b)]
  | .sigma _ _ A B _ => findEqs g A (vFst e) ++ findEqs g (Closure.inst g B (vFst e)) (vSnd e)
  | _ => []

/-- The number of leading Π binders of a type term, with their binder infos. -/
def piInfos : Term R → List (Name × BinderInfo × Term R)
  | .pi x bi _ A b _ => (x, bi, A) :: piInfos b
  | _ => []

/-- A proof of a proposition that holds by computation: `Unit`, pairs of such, and stuck
equations `a = b` (which hold by `refl` when they arise from a match on a family with a
concrete index, `SyntaxF .false`). -/
partial def trivialProof (g : Globals R) (tys : Array (VTy R)) (ty : Val R) : Option (Val R) :=
  match whnf ty with
  | .unit _ => some .tt
  | .sigma _ _ A B _ => do
    let a ← trivialProof g tys A
    let b ← trivialProof g tys (Closure.inst g B a)
    pure (.pair a b)
  -- (13b) `refl` only when the two sides are convertible *here* (`g` is the elaborator's
  -- view, where a type with a private constructor of another module is opaque): the
  -- kernel compares by shape, so the comparison can't be left to it (`sameSides`)
  | .neutral (.eq A a b) _ => if conv g tys A a b then some (.neutral (.refl A a) #[]) else none
  | .neutral (.eqTy X Y) _ => if convTy g tys X Y then some (.neutral (.reflTy X) #[]) else none
  | _ => none

/-- `Term.abstract`, but not inside the arguments of an unsolved hole: there the
scrutinee stays as it is (still in scope in every branch). Abstracted, `?A b` would be
`?A .false` in the branch for `.false`, outside the pattern fragment, and could not be
solved (`x ← match b with …` in a `do` block, where `?A` is the match's type). -/
partial def abstractOutsideHoles (t target : Term R) (depth : Nat := 0) : Term R :=
  if t == target.lift depth then .var depth else
  match t, (Term.spine t).1 with
  | .app .., .mvar _ => t.lift 1 depth
  | .var i, _ => if i ≥ depth then .var (i + 1) else .var i
  | t, _ => Id.run <| t.mapChildrenM pure (fun d c => pure (abstractOutsideHoles c target (depth + d)))

/-- `typeSort?`, but a hole's universe is the one recorded for it (`addSortConstraint`,
as for an implicit argument `{A : Type}`): the type of a `match` that is still `M ?A`
(`x ← match …` in a `do` block) has a universe. `tys`: the context's types, by level. -/
partial def elabTypeSort? (tys : Array (VTy R)) (v : VTy R) : ElabM R (Option Level) := do
  let g ← getGlobals
  if let some l := typeSort? g tys v then return some l
  match ← force v with
  | .neutral (.mvar m) _ =>
    for (_, t, l) in (← get).sortConstraints do
      if let .mvar m' := (Term.spine t).1 then
        if m' == m then return some (← instLevel l)
    return none
  | .pi _ _ _ A B _ =>
    let some a ← elabTypeSort? tys A | return none
    let some b ← elabTypeSort? (tys.push A) (← instM B (Val.var tys.size)) | return none
    return some (.imax a b)
  | .sigma _ _ A B _ =>
    let some a ← elabTypeSort? tys A | return none
    let some b ← elabTypeSort? (tys.push A) (← instM B (Val.var tys.size)) | return none
    return some (.max a b)
  | _ => return none

/-- Replace recursive calls `f y a…` (with `y` a field that has a hypothesis `h`) by
`h a…`, and `f (k e) a…` (with `k` an infinitary field) by `h e a…`. Returns the
rewritten syntax and the hypothesis bindings it needs. -/
partial def rewriteRecCalls (g : Globals R) (rc : RecCtx) (binds : List (Name × VTy R × Val R))
    (ihType : Lvl → Option (VTy R)) (lvl : Lvl) (tys : Array (VTy R)) (stx : Syntax) :
    Except String (Syntax × List (Name × VTy R × Val R)) := do
  let isF (h : Syntax) := h.isOfKind "term.ident" && (h.getArg 0).getId? == some rc.fn
  let isExplicitF (h : Syntax) := h.isOfKind "term.explicit" && (h.getArg 1).getId? == some rc.fn
  if stx.isOfKind "term.app" && (isF (stx.getArg 0) || isExplicitF (stx.getArg 0)) then
    let mut args := (stx.getArg 1).args
    if isExplicitF (stx.getArg 0) then
      -- `@f`: the implicit parameters come first too, unchanged (or `_`); leave them out
      let mut kept : Array Syntax := #[]
      for (p, expl) in rc.allParams, i in [0:rc.allParams.length] do
        let some a := args[i]? | throw s!"recursive call of @{rc.fn} without its parameter {p}"
        if expl then kept := kept.push a
        else unless a.isOfKind "term.hole" ||
            (a.isOfKind "term.ident" && (a.getArg 0).getId? == some p) do
          throw s!"recursive call of {rc.fn} must pass the parameter {p} unchanged"
      args := kept ++ args.extract rc.allParams.length args.size
    -- (#249) which columns the call passes: with `@f` all of them, else the explicit ones
    let atF := isExplicitF (stx.getArg 0)
    let explicitCols : List Nat := (List.range rc.cols).filter fun i =>
      atF || (rc.colExplicit[i]?.getD true)
    let nExpl := explicitCols.length
    -- (the old form passes every matched argument, with a `_` at the implicit ones)
    let allGiven (given : Array Syntax) : Bool :=
      given.size ≥ rc.cols &&
        (rc.colExplicit.zip (given.extract 0 rc.cols).toList).all fun (e, a) =>
          e || a.isOfKind "term.hole"
    -- is the argument at `i` a recursive field (a variable with a hypothesis)?
    let isFieldArg (i : Nat) : Bool := match args[i]? with
      | some a => a.isOfKind "term.ident" && (match (a.getArg 0).getId? with
          | some y => match binds.find? (·.1 == y) with
            | some (_, _, .neutral (.local fl) #[]) => rc.ihs.any (·.1 == fl)
            | _ => false
          | none => false)
      | none => false
    -- a partial application `f n y` passes the parameters and only some of the matched
    -- arguments: the parameters are there when they are the parameters' names and the
    -- structural argument after them is a recursive field (`f k _ e` takes no parameter
    -- there, it passes every column)
    let isParamsAt0 : Bool := !rc.params.isEmpty && args.size > rc.params.length &&
      (rc.params.zip (args.extract 0 rc.params.length).toList).all (fun (p, a) =>
        a.isOfKind "term.ident" && (a.getArg 0).getId? == some p) &&
      isFieldArg (rc.params.length + (explicitCols.idxOf? rc.pos).getD rc.pos)
    let np := if isParamsAt0 then rc.params.length
      else if args.size ≤ nExpl || (!atF && args.size ≤ rc.cols && allGiven args) then 0
      else rc.params.length
    for p in rc.params.take np, i in [0:np] do
      let ok := match args[i]? with
        | some a => a.isOfKind "term.ident" && (a.getArg 0).getId? == some p
        | none => false
      unless ok do throw s!"recursive call of {rc.fn} must pass the parameter {p} unchanged"
    let given := args.extract np args.size
    -- (the old form, all columns given: keep the explicit columns' arguments, then any
    -- further arguments after the columns)
    let colArgs := if !atF && given.size > nExpl && allGiven given then
        (explicitCols.map (given[·]!)).toArray ++ given.extract rc.cols given.size
      else given
    let some posE := explicitCols.idxOf? rc.pos
      | throw s!"recursive call of {rc.fn}: its structural argument is implicit; use @{rc.fn}"
    let some a := colArgs[posE]? | throw s!"recursive call of {rc.fn} without its structural argument"
    let rec unparen (s : Syntax) : Syntax := if s.isOfKind "term.paren" then unparen (s.getArg 1) else s
    let a := unparen a
    -- `y`, or `k e…` for an infinitary field `k`
    let (yStx, kargs) :=
      if a.isOfKind "term.app" then (a.getArg 0, (a.getArg 1).args) else (a, #[])
    let some y := (if yStx.isOfKind "term.ident" then (yStx.getArg 0).getId? else none)
      | throw (s!"recursive call of {rc.fn} must be on a variable, not {a.reprint}" ++ "\n  (structural recursion: a recursive call must be on a field of the matched constructor, like n in `| .succ n => … f n …`; for any other recursion, use `partial def`)")
    let some (_, _, .neutral (.local fl) #[]) := binds.find? (·.1 == y)
      | throw (s!"recursive call of {rc.fn} on {a.reprint}, which is not a recursive field" ++ "\n  (structural recursion: a recursive call must be on a field of the matched constructor, like n in `| .succ n => … f n …`; for any other recursion, use `partial def`)")
    let some (_, ihl) := rc.ihs.find? (·.1 == fl)
      | throw (s!"recursive call of {rc.fn} on {a.reprint}, which is not structurally smaller" ++ "\n  (structural recursion: a recursive call must be on a field of the matched constructor, like n in `| .succ n => … f n …`; for any other recursion, use `partial def`)")
    let some ty := ihType ihl | throw "internal error: hypothesis without a type"
    -- a family matched at a concrete index: the hypothesis first wants the (trivial)
    -- proof that the field's index is that index
    let ihVal : Val R := .neutral (.local ihl) #[]
    let (ihVal, ty) := match whnf ty with
      | .pi _ _ q dom cod _ => match q.toPoly?, trivialProof g tys dom with
        | some [], some p => (vApp g ihVal p, Closure.inst g cod p)
        | _, _ =>
          -- an infinitary field: the proof comes after `h`, so the hypothesis becomes
          -- `fun h => ih h proof : (h : H) → R[e := proof]` (built at level `lvl`, the
          -- right-hand side's context, by quoting and evaluating back)
          match kargs.isEmpty, whnf ty with
          | false, .pi hn hbi hq H hcod _ =>
            match whnf (Closure.inst g hcod (Val.var lvl)) with
            | .pi _ _ q' E cod2 _ => match q'.toPoly?, trivialProof g (tys.push H) E with
              | some [], some p =>
                let env : Env R := (List.range lvl).reverse.map Val.var
                let pTm := quote g (lvl + 1) p
                let tyTm : Term R := .pi hn hbi (quote g lvl hq) (quote g lvl H)
                  (quote g (lvl + 1) (Closure.inst g cod2 p)) none
                let valTm : Term R := .lam hn (.app (.app (.var (lvl - ihl)) (.var 0)) pTm)
                (eval g env valTm, eval g env tyTm)
              | _, _ => (ihVal, ty)
            | _ => (ihVal, ty)
          | _, _ => (ihVal, ty)
      | _ => (ihVal, ty)
    let ihName := "_ih_" ++ y
    -- (`term.recCall`: the hypothesis, after checking that no local variable named like
    -- the definition is in scope, see `infer`)
    let ident : Syntax := .node a.info "term.recCall"
      #[.ident (stx.getArg 0).info rc.fn, .node a.info "term.ident" #[.ident a.info ihName]]
    -- the other columns' arguments, in order: `_` for an implicit column, none for a
    -- column the hypothesis doesn't take; then any further arguments
    let mut others0 : Array Syntax := #[]
    let mut done := false
    for i in [0:rc.cols] do
      if done || i == rc.pos then continue
      match explicitCols.idxOf? i with
      | some t => match colArgs[t]? with
        | some arg => unless rc.dropCols.contains i do others0 := others0.push arg
        | none => done := true
      | none => unless rc.dropCols.contains i do others0 := others0.push holeStx
    let others := if done then others0 else others0 ++ colArgs.extract explicitCols.length colArgs.size
    let rest ← (kargs ++ others).mapM (rewriteRecCalls g rc binds ihType lvl tys ·)
    let restStx := rest.map (·.1)
    let newBinds := [(ihName, ty, ihVal)] ++ rest.toList.flatMap (·.2)
    let stx' := if restStx.isEmpty then ident
      else .node stx.info "term.app" #[ident, .node {} "null" restStx]
    return (stx', newBinds)
  if isF stx || isExplicitF stx then
    throw s!"{rc.fn} may only be used in structurally recursive calls (inside its equations, {rc.fn} is the definition: rename a local variable called {rc.fn})"
  match stx with
  | .node i k as =>
    let rs ← as.mapM (rewriteRecCalls g rc binds ihType lvl tys ·)
    return (.node i k (rs.map (·.1)), rs.toList.flatMap (·.2))
  | s => return (s, [])

/-- (For the language server) a `match` or equations on a value of type `ty` in the first
column: which constructors have a case, and where the alternatives are. -/
def recordMatch (info : SourceInfo) (alts : Array Syntax) (clauses : List (MClause R)) (ty : VTy R)
    (tys : Array (VTy R)) : ElabM R Unit := do
  let .mu _ _ _ _ _ (some (T, _, _)) ← force ty | return
  let (some first, some last) := (alts[0]?, alts.back?) | return
  let g ← getGlobals
  let firsts := clauses.filterMap (·.pats.head?)
  let views : List (Except String PatView) := firsts.map fun p => (patViewAs g p).map (·.2)
  let written := views.filterMap fun v => match v with
    | .ok (.ctor _ c _) => some c
    -- (13q) at `Nat`: `0`, and `n + 1` with a variable `n`
    | .ok (.lit l) => if (l.getArg 0).getNat? == some 0 then some "zero" else none
    | .ok (.plusK p 1) => if p.isOfKind "term.ident" || p.isOfKind "term.hole" then some "succ" else none
    | _ => none
  -- the constructors with a case; at a member of a `mutual` block, also the other
  -- members' (ruled out by the index)
  let covered := (ctorNames g T).filter fun t =>
    written.any (ctorSelects · t) || (t.contains '.' && !memberTag g tys ty t)
  let catchAll := views.any fun v => v matches .ok (.var _) || v matches .ok .wild
  let columns := (clauses.head?.map (·.pats.length)).getD 1
  pushInfo (.done (.matchCases info { type := T, covered, catchAll, columns, firstAlt := first.info, lastAlt := last.info }))

/-- The open goals of a tactic state, as contexts and types (for the info tree). -/
def openGoals (st : TacState R) : ElabM R (Array (LocalCtx R × VTy R)) :=
  st.open.toArray.filterMapM fun i => do
    let some gl := st.goals[i]? | pure none
    pure (if ← gl.isOpen then some (gl.ctx, gl.ty) else none)

/-- (13b) The types of `ctx`'s variables, by level, evaluated again with their holes
solved: a binder's type may have been a hole when it was bound (`e : Ex P` with `Ex`'s
implicit `A` solved later), and conversion and the kernel's inference take the types
as they are (a hole is rigid there). -/
def zonkedTypes (ctx : LocalCtx R) : ElabM R (Array (VTy R)) := do
  let g ← getGlobals
  let mut tys : Array (VTy R) := #[]
  for v in ctx.types.reverse do
    let j := tys.size
    let t ← zonk j (quote g j (← forceMeta v))
    tys := tys.push (eval g (ctx.env.drop (ctx.lvl - j)) t)
  pure tys

/-- (13b) The two sides of an equation that `rfl` is about to prove by `refl`/`reflTy`
must be definitionally equal **in the elaborator's view** (`Globals.elabView`: a type
with a private constructor, field or observation of another module is opaque). The
kernel checks `refl` too, but against the real definitions and by shape, so it accepts
`Look = Token` for a look-alike `Look` of a private `Token`, and `cast` along that
equation forges a `Token`. So the comparison is never left to the kernel: unify (which
may solve holes), and when unification fails, the type-directed conversion with the
elaborator's globals (η for `Unit`; holes are rigid). `A?` is the type of the sides, or
`none` for two types. -/
def sameSides (ctx : LocalCtx R) (A? : Option (VTy R)) (a b : Val R) : ElabM R Unit := do
  let s ← get
  try unify ctx.lvl a b
  catch e =>
    set s
    -- the sides were evaluated when the equation was formed, perhaps with holes that are
    -- solved by now (`P.mk s.1 s.2 = s`: `P.mk`'s parameters): evaluate them again
    let g ← getGlobals
    let again (v : Val R) : ElabM R (Val R) := do
      evalIn ctx (← zonk ctx.lvl (quote g ctx.lvl (← forceMeta v)))
    let a ← again a
    let b ← again b
    -- the types of the variables too: a binder's type may have been a hole when it was
    -- bound, and conversion (which infers the types of neutrals) takes holes as rigid
    let tys ← zonkedTypes ctx
    -- what the kernel does with `refl a`: its type `a = a` against `a = b`, both
    -- computed afresh (an equation at a Σ or Π computes by components, and then holds by
    -- η where the sides themselves are not compared by `conv`)
    let ok ← match A? with
      | some A => do
        let A ← again A
        pure (conv g tys A a b || convTy g tys (vEq g A a a) (vEq g A a b))
      | none => pure (convTy g tys a b || convTy g tys (vEqType g a a) (vEqType g a b))
    unless ok do
      let (l, r) := (← showVal ctx a, ← showVal ctx b)
      throwAt ctx.info (s!"rfl: the two sides are not definitionally equal\n  left:  {l}\n  right: {r}" ++ mismatchReason l r e.msg) ErrorCode.notDefeq

/-- A value evaluated again after its solved holes are filled in (an equation is computed
when it is formed, perhaps while the implicit arguments of its sides are still holes:
`Pair2.mk s.1 s.2 = s`). -/
def refreshVal (ctx : LocalCtx R) (v : Val R) : ElabM R (Val R) := do
  evalIn ctx (← zonk ctx.lvl (quote (← getGlobals) ctx.lvl (← forceMeta v)))

/-- `sameSides` as a test: no error, and the state (solved holes) restored on failure. -/
def sidesOk (ctx : LocalCtx R) (A? : Option (VTy R)) (a b : Val R) : ElabM R Bool := do
  let s ← get
  try sameSides ctx A? a b; pure true
  catch _ => set s; pure false

/-- `rfl` at an equation that has already computed: `succ a = succ b` at `Nat` is a Σ of
`True`s and `a = b`, an equation of functions a Π. (13n) At a Σ that `vEq` computed from
`a = b` with `a ≡ b`, the proof is one `refl a` (`eqSigmaSides?`). Otherwise build it by the same shape
(pairs, lambdas, `()`, and a case split for a Π over a tag type), with `refl` at the
equations left; the kernel checks them. -/
partial def rflProof (ctx : LocalCtx R) (ty : VTy R) : ElabM R (Option (Term R)) := do
  let g ← getGlobals
  match ← force ty with
  | .neutral (.eq A a b) #[] =>
    sameSides ctx (some A) a b
    pure (some (.refl (quote g ctx.lvl A) (quote g ctx.lvl a)))
  | .neutral (.eqTy X Y) #[] =>
    sameSides ctx none X Y
    pure (some (.reflTy (quote g ctx.lvl X)))
  | .unit _ => pure (some .tt)
  | ty'@(.sigma _ _ A B _) =>
    -- an equation `a = b` at a Σ type has computed to this Σ (`vEq`): if `a ≡ b`, one
    -- `refl` proves it, with no cast to see through (`s = s`, `P.mk s.1 s.2 = s`)
    if let some (T, a, b) := eqSigmaSides? ty' then
      let T ← refreshVal ctx T
      let a ← refreshVal ctx a
      let b ← refreshVal ctx b
      if convTy g (← zonkedTypes ctx) (vEq g T a b) (← refreshVal ctx ty') then
        if ← sidesOk ctx (some T) a b then
          return some (.refl (quote g ctx.lvl T) (quote g ctx.lvl a))
    let some a ← rflProof ctx A | pure none
    let some b ← rflProof ctx (← instM B (← evalIn ctx a)) | pure none
    pure (some (.pair a b))
  | .pi x _ _ A B _ =>
    let ctx' := ctx.bind x A
    match tagField? A with
    -- (4g) a Π over a tag type is proved tag by tag: an equation between two
    -- descriptions is `(t : Enum ls) → E t = E' t`, and under the binder `E t` is a stuck
    -- `ecase t …`, while at each tag it computes. `fun t => ecase t [p₀, …]`; a lifted tag
    -- (`ULift (Enum ls)`) is split through `down` (the result's type is the goal by η).
    | some (ls, lifted) =>
      let tagV (k : Nat) : Val R := if lifted then .up (.tag ls k) else .tag ls k
      let mut branches : List (Term R) := []
      for k in [0:ls.length] do
        let some p ← rflProof ctx' (← instM B (tagV k)) | return none
        branches := branches ++ [p]
      -- the motive, under one more binder `t : Enum ls` (in `ctx'`)
      let t : Val R := Val.var (ctx.lvl + 1)
      let motive := quote g (ctx.lvl + 2) (← instM B (if lifted then .up t else t))
      let split : Term R := .ecase "t" motive (if lifted then .down (.var 0) else .var 0) branches
      -- the binder is erased (quantity 0) and a case split uses its scrutinee, so the
      -- split goes inside a `transp` along `() = ()`, whose premises are checked erased:
      -- `transp Unit () (fun _ _ => goal) split () ()  :  goal`
      let goal := quote g (ctx.lvl + 3) (← instM B (Val.var ctx.lvl))
      pure (some (.lam x (.transp (.unit 1) .tt (.lam "_" (.lam "_" goal)) split .tt .tt)))
    | none =>
      let some b ← rflProof ctx' (← instM B (Val.var ctx.lvl)) | pure none
      pure (some (.lam x b))
  | _ => pure none

/-- (13q) Is `ty` the `builtin nat` type (whose numeral patterns are its constructors)? -/
def isNatType (ty : VTy R) : ElabM R Bool := do
  let some N := (← get).builtins.lookup "nat" | return false
  match ← force ty with
  | .mu _ _ _ _ _ (some (T, _, _)) => return T == N
  | _ => return false

/-- (13q) Numeral patterns at `Nat` (the data type `T`), one constructor at a time: `0` is
`.zero`, `n + 1` is `.succ n`, and `p + (k + 1)` is `.succ (p + k)`. Other views (and
other types) are left alone. -/
def natPatView (T : Name) (p : Syntax) (v : PatView) : ElabM R PatView := do
  let some N := (← get).builtins.lookup "nat" | return v
  unless T == N do return v
  let bs := (← get).builtins
  let ctor (b : String) : Name := ((bs.lookup b).map fun c => (c.splitOn ".").getLastD c).getD
    (if b == "nat.zero" then "zero" else "succ")
  match v with
  | .lit stx =>
    let some n := (stx.getArg 0).getNat?
      | throwAt p.info s!"a string pattern needs a String, not {T}"
    -- a numeral pattern is `succ` applied `n` times: the case tree grows with `n`
    if n > natPatLimit then
      throwAt p.info (s!"the numeral pattern {n} is too large: at Nat a numeral is matched by its constructors " ++
        s!"(`succ` applied {n} times), up to {natPatLimit}; test with `Nat.beq` instead")
    if n == 0 then return .ctor (some T) (ctor "nat.zero") []
    return .ctor (some T) (ctor "nat.succ") [numStx stx.info (n - 1)]
  | .plusK q k => return .ctor (some T) (ctor "nat.succ") [plusKStx p.info q (k - 1)]
  | v => return v
where natPatLimit : Nat := 256

/-- (13q) The type a literal pattern is compared at, by `T.beq`: the first `T` in the
chain of definitions `ty` unfolds through that has a `T.beq` (`BitVec 8`, then `UIntN 8`). -/
partial def beqHead? (g : Globals R) : Val R → Option Name
  | .unfold S _ _ v => if g.contains (S ++ ".beq") then some S else beqHead? g v.get
  | .mu _ _ _ _ _ (some (T, _, _)) => if g.contains (T ++ ".beq") then some T else none
  | .neutral (.global S _) _ => if g.contains (S ++ ".beq") then some S else none
  | _ => none

/-- (13q) Two literal patterns that are the same literal. -/
def sameLit (a b : Syntax) : Bool :=
  match (a.getArg 0).getNat?, (b.getArg 0).getNat? with
  | some m, some n => m == n
  | _, _ => match (a.getArg 0).getStr?, (b.getArg 0).getStr? with
    | some x, some y => x == y
    | _, _ => false

/-- (13a) Does an application have a named argument `(x := e)`? -/
def hasNamedArgs (stx : Syntax) : Bool :=
  stx.isOfKind "term.app" && (stx.getArg 1).args.any (·.isOfKind "term.namedArg")

mutual

/-- A binder's quantity: the default, a literal (`0`, `1`, `ω`), or (stage 4d)
`%t` for a term `t : Qty`, such as a quantity variable. -/
partial def elabQuantity (ctx : LocalCtx R) (bi : BinderInfo) : Option Syntax → ElabM R (Term R)
  | none => pure (defaultQty bi)
  | some q => match q.getArg 0 with
    | .atom _ "%" => check ctx (q.getArg 1) .qty
    | .atom _ v => elabQtyLit ctx q v
    | n => elabQtyLit ctx q ((n.getNat?.map toString).getD "?")

/-- Elaborate a type, returning it and its universe level (possibly a level
metavariable). -/
partial def checkType (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × Level) := do
  if stx.isOfKind "term.hole" then
    let m ← freshMeta (ctx.withInfo stx) "type"
    let u ← freshLevelMeta
    addSortConstraint ctx m u
    return (m, u)
  let (t, ty) ← infer ctx stx
  -- a type may still take implicit or instance arguments (`Commute e₁ e₂ m` with its
  -- `[Monad m]` …): insert them
  let (t, ty) ← if stx.isOfKind "term.explicit" then pure (t, ty) else insertImplicits ctx t ty
  match ← force ty with
  | .sort l => pure (t, l)
  | ty@(.neutral (.mvar _) _) =>
    let u ← freshLevelMeta
    unifyAt ctx stx (.sort u) ty
    pure (t, u)
  | ty => throwAt (ctx.withInfo stx).info s!"type expected, got a term of type {← showVal ctx ty}" ErrorCode.typeExpected

/-- `check` of a variable or an application against a glued definition `D a…` that
unfolds to an implicit or instance Π: if the term's own type is `D b…` too, unify the
two directly (`some` the term); otherwise `none`, and nothing happened. -/
partial def sameDefinition? (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Option (Term R)) := do
  unless stx.isOfKind "term.ident" || stx.isOfKind "term.app" do return none
  let .unfold n _ _ _ ← forceMeta expected | return none
  unless (← force expected) matches .pi _ .implicit .. || (← force expected) matches .pi _ .instImplicit .. do
    return none
  tryCatch (do
      let (t, ty) ← infer ctx stx
      let .unfold n' _ _ _ ← forceMeta ty | throwAt {} "another type"
      unless n' == n do throwAt {} "another definition"
      unify ctx.lvl expected ty
      pure (some t))
    (fun _ => pure none)

/-- **Exercise 3.8.** Elaborate `stx` against `expected`. Force `expected` first.

1. If `expected` is an implicit Π and `stx` is not an implicit `fun`
   (`isImplicitFun`), insert an implicit lambda: elaborate `stx` against the codomain
   in a context extended with the Π's variable, and wrap the result in `.lam`.
2. `term.fun`: the given `checkFun` does the work.
3. `term.let`: `elabLet` with the expected type.
4. `term.hole` / `term.syntheticHole`: a fresh meta. Use the hole's name for
   `?x` as its description.
5. `term.paren`: check the inner term.
6. Otherwise infer, insert implicits (unless `stx` is `term.explicit`), and
   `unifyAt` the expected and inferred types. -/
partial def check (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let ctx := ctx.withInfo stx
  recordExpected ctx stx expected
  if let some stx' ← expand? stx then return ← check ctx stx' expected
  if let some t ← checkData? ctx stx expected then return t
  -- a variable or application whose type is the expected type's own definition
  -- (`f : Comb i o` against `Comb ?i ?o`, `def Comb … := {r} → [Hw r] → …`): unify the
  -- two, without unfolding the definition to introduce implicit lambdas (that would make
  -- `fun {r} [_] => f`, with an instance hole created while `?r` is unsolved). Lean
  -- doesn't unfold a definition to find implicit binders either.
  if let some t ← sameDefinition? ctx stx expected then return t
  -- (given, stage 7) against `[x : C A] → B`, bind the instance as a local
  if let .pi x .instImplicit _ dom cod _ ← force expected then
    return .lam x (← check (ctx.bind x dom) stx (← instM cod (Val.var ctx.lvl)))
  --<sol
  match ← force expected with
  | .pi x .implicit _ dom cod _ =>
    if !isImplicitFun stx then
      let body ← check (ctx.bind x dom) stx (← instM cod (Val.var ctx.lvl))
      return .lam x body
    checkOther ctx stx expected
  -- pass the expected type unforced: glued names help unification
  | _ => checkOther ctx stx expected
where
  checkOther (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
    match stx.kind with
    | "term.fun" =>
      let bs := (stx.getArg 1).args.flatMap binderViews
      checkFun ctx bs.toList (stx.getArg 3) expected
    | "term.let" => return (← elabLet ctx stx (some expected)).1
    | "term.tuple" =>
      let items := #[stx.getArg 1] ++ ((stx.getArg 3).args.filter (!· matches .atom ..))
      checkTuple ctx items.toList expected
    | "term.unitVal" =>
      match ← force expected with
      | .unit _ => pure .tt
      -- `()` also fills a structure's phantom tail (`phantomTail`)
      | e@(.pi x ..) => do
        let g ← getGlobals
        match (if isPhantomName x then (quote g ctx.lvl e).phantomTailVal? else none) with
        | some t => pure t
        | none => do let (t, ty) ← infer ctx stx; unifyAt ctx stx expected ty; pure t
      | _ => do let (t, ty) ← infer ctx stx; unifyAt ctx stx expected ty; pure t
    | "term.letPair" => elabLetPair ctx stx expected
    | "term.letTuple" => elabLetPair ctx (letTupleToPairs stx) expected
    -- (linear-case stage 2) `let () := u; b`: consumes `u : Unit`
    | "term.letUnit" => do
      let u ← check ctx (stx.getArg 4) (.unit (.succ .zero))
      return .letUnit u (← check ctx (stx.getArg 6) expected)
    | "term.match" => elabMatch ctx stx expected
    | "term.by" => elabBy ctx stx expected
    | "term.num" =>
      let n := (stx.getArg 0).getNat?.getD 0
      match ← force expected with
      | .qty => elabQtyLit ctx stx (((stx.getArg 0).getNat?.map toString).getD "?")
      | .mu _ _ _ _ _ (some (T, _, _)) =>
        -- a numeral of the `builtin nat` type: `succ (… (succ zero))` (the kernel's Nat
        -- is unary; the runtime uses native numbers)
        let s ← get
        match s.builtins.lookup "nat" with
        | some N =>
          if N == T then pure (.natLit n) else
          -- (HD9) at another data type, through its `OfNat` instance
          match ← ofNatLit? ctx n expected with
          | some t => pure t
          | none => throwAt ctx.info s!"numerals are for {N}, not {T}"
        | none => throwAt ctx.info "numerals need `builtin nat := …`"
      -- (7f) an unsolved type: `@OfNat.ofNat ?T n ?i`, with a pending problem `OfNat ?T n`,
      -- so the type may still be decided by what follows; if nothing does, the default
      -- instance `OfNat Nat n` makes it a `Nat` (`applyDefaultInstance`), and zonking turns
      -- it back into the literal. Without an `OfNat` class (or a default instance for
      -- it) the numeral is a `Nat` at once.
      | .neutral (.mvar _) _ => do
        let s ← get
        if s.instances.any (fun i => i.isDefault && i.cls == "OfNat") then
          if let some t ← ofNatLit? ctx n expected then return t
        let (t, ty) ← infer ctx stx; unifyAt ctx stx expected ty; pure t
      -- (HD9) any other type (an axiom, a type variable with an instance): `OfNat`
      | _ => do
        match ← ofNatLit? ctx n expected with
        | some t => pure t
        | none => let (t, ty) ← infer ctx stx; unifyAt ctx stx expected ty; pure t
    | "term.str" =>
      match ← force expected with
      | .mu _ _ _ _ _ (some (T, us, _)) =>
        -- a string of the `builtin string` type: `String.mk [Char.mk n, …]`
        let s ← get
        match s.builtins.lookup "string" with
        | some S =>
          if S != T then throwAt ctx.info s!"string literals are for {S}, not {T}" else
          mkStringLit (((stx.getArg 0).getStr?).getD "") us
        | none => throwAt ctx.info "string literals need `builtin string := …`"
      | _ => do let (t, ty) ← infer ctx stx; unifyAt ctx stx expected ty; pure t
    -- `refl a` against an equation `a' =_A b'`: as elsewhere, infer and unify; if that
    -- fails, once more checking `a` against `A`, so that the metavariables in `a`'s type are
    -- solved by `A`. Inferring `a`'s type alone can leave a component's sort unknown
    -- (`fun x => x : ?m → ?m`), and then the equation computes by another rule than the
    -- expected one (at a proposition it is `True`, nu-transp), and the two don't unify.
    -- (`A` is read back from the computed Σ by `eqSigmaSides?`, a guess: the Σ may also be
    -- a constructor's payload equation, at the payload type; hence only as a second try.)
    | "term.refl" =>
      let s ← get
      try
        let (t, ty) ← infer ctx stx
        unifyAt ctx stx expected ty
        pure t
      catch err =>
        let s' ← get
        set s
        let A? : Option (VTy R) := match ← force expected with
          | .neutral (.eq A _ _) #[] => some A
          | e => (eqSigmaSides? e).map (·.1)
        let A? ← match A? with
          | some A => do
            let A ← force A
            pure (if A matches .sort _ then none else some A)
          | none => pure none
        match A? with
        | none =>
          set s'
          throw err
        | some A =>
          let g ← getGlobals
          try
            let a ← check ctx (stx.getArg 1) A
            let va ← evalIn ctx a
            unifyAt ctx stx expected (vEq g A va va)
            pure (.refl (quote g ctx.lvl A) a)
          catch _ =>
            set s'
            throw err
    | "term.rfl" =>
      let g ← getGlobals
      match ← force expected with
      | .neutral (.eq A a b) #[] =>
        sameSides ctx (some A) a b
        pure (.refl (quote g ctx.lvl A) (quote g ctx.lvl a))
      | .neutral (.eqTy X Y) #[] =>
        sameSides ctx none X Y
        pure (.reflTy (quote g ctx.lvl X))
      | .unit _ => pure .tt
      | e => match ← rflProof ctx e with
        | some t => pure t
        | none => throwAt ctx.info s!"rfl: the expected type is not an equation (it may have computed further): {← showVal ctx e}\n  try `refl x`"
    | "term.cast" =>
      let (t, A) ← infer ctx (stx.getArg 2)
      let e ← check ctx (stx.getArg 1) (vEqType (← getGlobals) A expected)
      let g ← getGlobals
      pure (.cast (quote g ctx.lvl A) (quote g ctx.lvl expected) e t)
    | "term.absurd" =>
      let (e, ety) ← infer ctx (stx.getArg 1)
      match ← force ety with
      | .empty _ => return .absurd (quote (← getGlobals) ctx.lvl expected) e
      | ety@(.sigma ..) =>
        -- (#258) a Σ with a `False` component (a constructor equation that computed, as
        -- `Bool.false = Bool.true`): the proof of that component
        let g ← getGlobals
        match findAbsurd g ety (← evalIn ctx e) with
        | some prf => return .absurd (quote g ctx.lvl expected) (quote g ctx.lvl prf)
        | none => throwAt (ctx.withInfo (stx.getArg 1)).info s!"absurd expects a proof of False or Empty, got {← showVal ctx ety}"
      | ety => throwAt (ctx.withInfo (stx.getArg 1)).info s!"absurd expects a proof of False or Empty, got {← showVal ctx ety}"
    | "term.hole" => freshMeta ctx
    | "term.syntheticHole" => freshMeta ctx s!"?{((stx.getArg 1).getId?).getD "_"}"
    -- (13h) `⟨a, b⟩` and `let ⟨a, b⟩ := s; body`
    | "term.anon" => elabAnon ctx stx expected
    | "term.letPat" => return (← elabLetPat ctx stx (some expected)).1
    | "term.paren" => check ctx (stx.getArg 1) expected
    | "term.app" =>
      if (stx.getArg 0).isOfKind "term.explicit" || (← builtinApp? ctx stx).isSome ||
          !((stx.getArg 1).args.any needsExpected || (← ctorWithParams ctx (stx.getArg 0)) ||
            holeAndNestedCheck (stx.getArg 1).args || (← numOperands ctx stx)) then
        let (t, ty) ← infer ctx stx
        unifyAt ctx stx expected ty
        pure t
      else checkApp ctx stx expected
    | _ =>
      let (t, ty) ← infer ctx stx
      let (t, ty) ← if stx.isOfKind "term.explicit" then pure (t, ty) else insertImplicits ctx t ty
      unifyAt ctx stx expected ty
      pure t
  --|ex
  --| sorry
  --sol>

/-- Check `fun b₁ … bₙ => body` against `expected`, one binder at a time.

* If `expected` is a Π with the same binder info as `b₁`: the binder's type (if
  given) must unify with the domain, and its quantity (if given) must equal the Π's.
* If `expected` is an implicit Π and `b₁` is explicit: insert an implicit lambda.
* Otherwise, fall back to inferring the whole `fun` and unifying. -/
partial def checkFun (ctx : LocalCtx R) (bs : List BinderView) (body : Syntax) (expected : VTy R) :
    ElabM R (Term R) := do
  match bs with
  | [] => check ctx body expected
  | b :: rest =>
    match ← force expected with
    | .pi x bi q dom cod _ =>
      if bi == b.bi then
        if let some tyStx := b.type then
          let (ty, _) ← checkType ctx tyStx
          unifyAt ctx tyStx dom (← evalIn ctx ty)
        if b.qty.isSome then
          let q' ← elabQuantity ctx b.bi b.qty
          let vq' ← evalIn ctx q'
          let ok ← tryCatch (do unify ctx.lvl q vq'; pure true) (fun _ => pure false)
          unless ok do
            throwAt b.info s!"binder quantity {← showTermM ctx q'} does not match the expected {← showVal ctx q}" ErrorCode.binderMismatch
        recordBinder ctx b.info b.name dom
        let t ← checkFun (ctx.bindQ b.name dom ((Val.toPoly? q).bind (·.isConst?))) rest body (← instM cod (Val.var ctx.lvl))
        return .lam b.name t
      else if bi == .implicit || bi == .instImplicit then
        let t ← checkFun (ctx.bind x dom) bs body (← instM cod (Val.var ctx.lvl))
        return .lam x t
      else throwAt b.info "unexpected implicit binder: the expected type takes an explicit argument" ErrorCode.binderMismatch
    | expected =>
      let (t, ty) ← inferFun ctx bs body
      unifyAt ctx body expected ty
      pure t

/-- Stage 4d: data forms that need their expected type: tags, `ecase` (which
generalises its scrutinee in the expected type), and the constructors `Desc.ret`,
`Desc.arg`, `Desc.rec`, `Desc.hrec`, `con`, `coit`, `cocon`. -/
partial def checkData? (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) :
    ElabM R (Option (Term R)) := do
  let g ← getGlobals
  let q := quote g ctx.lvl
  let w := QuantitySyntax.explicitDefault (R := R)
  let expected ← force expected
  let shapeError (what : String) : ElabM R (Option (Term R)) := do
    throwAt ctx.info s!"{what}, but the expected type is {← showVal ctx expected}"
  -- `.c` and `.c args`: a constructor of the expected (nominal) type
  let dot? : Option (Syntax × Name) := match stx.kind with
    | "term.dotIdent" => some (stx, ((stx.getArg 1).getId?).getD "_")
    | "term.app" =>
      let h := stx.getArg 0
      if h.isOfKind "term.dotIdent" then some (h, ((h.getArg 1).getId?).getD "_") else none
    | _ => none
  if let some (h, c) := dot? then
    match expected with
    | .mu l I D i sz (some (T, us, args)) =>
      let some cn := dotCtor? g ctx.types.reverse.toArray T c expected
        | throwFix h.info s!"{← if (ctorNames g T).any (·.contains '.') then showVal ctx expected else pure T} has no constructor {c}"
            ErrorCode.unknownConstructor [("name", [c]), ("type", [T])]
      let ident : Syntax := .node h.info "term.ident" #[.ident h.info cn]
      let stx' := if stx.isOfKind "term.app" then .node stx.info "term.app" #[ident, stx.getArg 1] else ident
      let sizedBase := match (sizeView sz).1 with
        | some (.neutral (.local _) #[]) | some (.neutral (.mvar _) _) => true
        | _ => false
      if !sizedBase then return some (← check ctx stx' expected)
      -- a sized expected type: the value has size `↑m`, where `m` is the size of its
      -- recursive arguments (the generated constructors themselves return `T^∞`)
      let m ← freshMeta ctx "a size"
      let vm ← evalIn ctx m
      if stx.isOfKind "term.app" then
        for a in (stx.getArg 1).args do
          let some (_, aty) ← tryCatch (some <$> infer ctx a) (fun _ => pure none) | continue
          if let .mu _ _ _ _ asz (some (T', _, _)) ← force aty then
            if T' == T then unifyAt ctx a vm asz
      let (t, _) ← infer ctx stx'
      let payload := quote g ctx.lvl (← evalIn ctx t)
      let ty : Val R := .mu l I D i (.szSuc vm) (some (T, us, args))
      unifyAt ctx stx expected ty
      return some (.ann payload (q ty))
    | .neutral (.global T _) _ =>
      -- (13b) a type with private constructors (fields, observations) of another module:
      -- opaque here, so `.c` is `T.c` (which may be private)
      let cn? := dotCtor? g ctx.types.reverse.toArray T c expected
      unless (g.opaqueHere? expected).isSome && cn?.isSome do
        return ← shapeError s!".{c} needs an expected inductive type"
      let ident : Syntax := .node h.info "term.ident" #[.ident h.info (cn?.getD c)]
      let stx' := if stx.isOfKind "term.app" then .node stx.info "term.app" #[ident, stx.getArg 1] else ident
      return some (← check ctx stx' expected)
    | .nu _ _ _ _ _ (some (T, _, _)) =>
      -- `.mk h t`: the coconstructor of a coinductive type (`T.mk`, a `cocon`)
      unless (← getGlobals).contains (T ++ "." ++ c) do
        throwFix h.info s!"{T} has no coconstructor {c}" ErrorCode.unknownConstructor [("name", [c]), ("type", [T])]
      let ident : Syntax := .node h.info "term.ident" #[.ident h.info (T ++ "." ++ c)]
      let stx' := if stx.isOfKind "term.app" then .node stx.info "term.app" #[ident, stx.getArg 1] else ident
      return some (← check ctx stx' expected)
    | .neutral (.mvar _) _ =>
      -- nothing says which type `.c` belongs to (yet)
      throwAt ctx.info s!".{c} needs an expected type that is an inductive type, and nothing here says which type it is; write T.{c}, or give the type, as in (.{c} : T)"
    | _ => return ← shapeError s!".{c} needs an expected inductive type"
  match stx.kind with
  | "term.tag" =>
    let x := ((stx.getArg 1).getId?).getD "_"
    let .enum ls := expected | shapeError s!"'{x} is a tag"
    match ls.idxOf? x with
    | some i => return some (.tag ls i)
    | none => throwAt ctx.info s!"'{x} is not one of the tags {ls}"
  | "term.ecase" =>
    let (s, sty) ← infer ctx (stx.getArg 1)
    let .enum ls ← force sty | throwAt ctx.info s!"ecase expects a tag, got {← showVal ctx sty}"
    let bs := (stx.getArg 3).args.filter (!· matches .atom ..)
    unless bs.size == ls.length do throwAt ctx.info s!"ecase needs {ls.length} branches"
    let s := q (← evalIn ctx s)
    let motive := (q expected).abstract s
    let bs ← bs.toList.mapIdxM fun k b => do
      check ctx b (eval g (.tag ls k :: ctx.env) motive)
    return some (.ecase "z" motive s bs)
  | _ =>
  let some (n, args) ← builtinApp? ctx stx | return none
  match n, args, expected with
  | "Desc.ret", #[i], .desc _ I => return some (.dret (← check ctx i I))
  | "Desc.arg", #[qs, S, D], .desc l I =>
    let qt ← check ctx qs .qty
    let S' ← check ctx S (.sort (.succ l))
    let vS ← evalIn ctx S'
    let D' ← check ctx D (ctx.sortVal g (.pi "s" .default (.qlit w) vS (.mk [I] (.desc l (.var 1))) none))
    return some (.darg qt S' D')
  | "Desc.rec", #[qs, j, D], .desc l I =>
    return some (.drec (← check ctx qs .qty) (← check ctx j I) (← check ctx D (.desc l I)))
  | "Desc.hrec", #[qs, H, j, D], .desc l I =>
    let (H', lH) ← checkType ctx H
    unifyLevel lH (.succ l)
    let jTy : VTy R := ctx.sortVal g (.pi "h" .default (.qlit w) (← evalIn ctx H') (.mk ctx.env (quote g (ctx.lvl + 1) I)) none)
    return some (.dhrec (← check ctx qs .qty) H' (← check ctx j jTy) (← check ctx D (.desc l I)))
  | "con", #[x], .mu l I D i _ _ => return some (.con (← check ctx x (vInterp g l I D (muFamily l I D) i)))
  | "coit", #[S, st, s], .nu l I D i _ _ =>
    let S' ← check ctx S (coitStateTy l I w)
    let vS ← evalIn ctx S'
    let st' ← check ctx st (coitStepTy g l I D vS w)
    let s' ← check ctx s (vApp g vS i)
    return some (.coit l (q I) (q D) S' st' (q i) s')
  | "cocon", #[x], .nu l I D i sz _ =>
    -- `cocon xs : ν^{↑s} D i` for a payload whose recursive fields are at `ν^s`
    let some s' := sizePred? sz
      | throwAt ctx.info s!"cocon builds a value of size ↑s, but the expected type is {← showVal ctx expected}"
    return some (.cocon (← check ctx x (vInterp g l I D (nuFamilyAt l I D s') i)))
  | "Desc.ret", _, _ | "Desc.arg", _, _ | "Desc.rec", _, _ | "Desc.hrec", _, _ =>
    shapeError s!"{n} builds a description"
  | "con", _, _ => shapeError "con builds an inductive value"
  | "coit", _, _ => shapeError "coit builds a coinductive value"
  | "cocon", _, _ => shapeError "cocon builds a coinductive value"
  | _, _, _ => return none

/-- Stage 4d: data primitives whose type can be inferred. -/
partial def inferData? (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Option (Term R × VTy R)) := do
  let g ← getGlobals
  let q := quote g ctx.lvl
  let w := QuantitySyntax.explicitDefault (R := R)
  let some (n, args) ← builtinApp? ctx stx | return none
  let descOf (D : Syntax) : ElabM R (Term R × Level × VTy R) := do
    let (D', dty) ← infer ctx D
    let .desc l I ← force dty | throwAt ctx.info s!"expected a description, got {← showVal ctx dty}"
    pure (D', l, I)
  match n, args with
  | "Desc", #[I] =>
    let (I', lI) ← checkType ctx I
    let l ← freshLevelMeta
    unifyLevel lI (.succ l)
    return some (.desc l I', .sort (.succ (.succ l)))
  | "μ", #[D, i] | "ν", #[D, i] =>
    let (D', l, I) ← descOf D
    let i' ← check ctx i I
    return some ((if n == "μ" then Term.mu else Term.nu) l (q I) D' i' .szInf none, .sort (.succ l))
  | "Desc.elim", #[P, a, b, c, h, D] =>
    let (D', l, I) ← descOf D
    let v ← freshLevelMeta
    let P' ← check ctx P (delimMotiveTy l v I w)
    let vP ← evalIn ctx P'
    let (ta, tb, tc, th) := delimMethodTys g l I vP w
    return some (.delim v P' (← check ctx a ta) (← check ctx b tb) (← check ctx c tc) (← check ctx h th) D',
                 vApp g vP (← evalIn ctx D'))
  | "Desc.interp", #[D, X, i] =>
    let (D', l, I) ← descOf D
    let X' ← check ctx X (coitStateTy l I w)
    let i' ← check ctx i I
    -- β-reduce the template: the kernel can't infer a type for a bare lambda
    let v ← evalIn ctx ([q I, D', X', i'].foldl .app (Templates.interpTm l))
    return some (q v, .sort (.succ l))
  | "Desc.All", #[D, X, P, i, xs] =>
    let (D', l, I) ← descOf D
    let X' ← check ctx X (coitStateTy l I w)
    let vX ← evalIn ctx X'
    let v ← freshLevelMeta
    -- (i : I) → X i → Sort v
    let Pty : VTy R := ctx.sortVal g <| eval g [vX, I] (.pi "i" .default (.qlit w) (.var 1)
      (.pi "_" .default (.qlit w) (.app (.var 1) (.var 0)) (.sort v) none) none)
    let P' ← check ctx P Pty
    let i' ← check ctx i I
    let xs' ← check ctx xs (vInterp g l I (← evalIn ctx D') vX (← evalIn ctx i'))
    let all ← evalIn ctx ([q I, D', X', P', i', xs'].foldl .app (Templates.allTm l v))
    return some (q all, .sort (.max (.succ l) v))
  | "ind", #[P, m, x] =>
    let (x', xty) ← infer ctx x
    let .mu l I D i _ _ ← force xty | throwAt ctx.info s!"ind expects an inductive value, got {← showVal ctx xty}"
    let v ← freshLevelMeta
    let P' ← check ctx P (indMotiveTy g l v I D w)
    let vP ← evalIn ctx P'
    let m' ← check ctx m (indMethodTy g l v I D vP w)
    return some (.ind l (q I) (q D) v P' m' (q i) x', vApp g (vApp g vP i) (← evalIn ctx x'))
  | "out", #[x] =>
    let (x', xty) ← infer ctx x
    let .nu l I D i _ _ ← force xty | throwAt ctx.info s!"out expects a coinductive value, got {← showVal ctx xty}"
    return some (.out x', vInterp g l I D (nuFamily l I D) i)
  | _, _ => return none

/-- Check `(a, b, c)` against a (right-nested) Σ. -/
partial def checkTuple (ctx : LocalCtx R) (items : List Syntax) (expected : VTy R) :
    ElabM R (Term R) := do
  match items with
  | [] => throwAt ctx.info "empty tuple"
  | [t] => check ctx t expected
  | t :: rest =>
    match ← force expected with
    | .sigma _ _ A B _ =>
      let a ← check ctx t A
      let b ← checkTuple ctx rest (← instM B (← evalIn ctx a))
      pure (.pair a b)
    | expected =>
      let (tm, ty) ← inferTuple ctx items
      unifyAt ctx t expected ty
      pure tm

/-- Infer a tuple's type as a non-dependent Σ. -/
partial def inferTuple (ctx : LocalCtx R) (items : List Syntax) : ElabM R (Term R × VTy R) := do
  match items with
  | [] => throwAt ctx.info "empty tuple"
  | [t] => infer ctx t
  | t :: rest =>
    let (a, aty) ← infer ctx t
    let (b, bty) ← inferTuple ctx rest
    let g ← getGlobals
    -- the second component's type, weakened under the Σ binder
    let bTerm := quote g (ctx.lvl + 1) bty
    return (.pair a b, ctx.sortVal g (.sigma "_" (.qlit QuantitySyntax.explicitDefault) aty (.mk ctx.env bTerm) none))

/-- `let q (x₁, x₂, …, xₙ) := e; body` (n ≥ 3) as right-nested pairs:
`let q (x₁, r₁) := e; let q (x₂, r₂) := r₁; …; let q (xₙ₋₁, xₙ) := rₙ₋₂; body`, with
names `rᵢ` that no user name can capture. -/
partial def letTupleToPairs (stx : Syntax) : Syntax :=
  let i := stx.info
  let names : List Syntax := [stx.getArg 3, stx.getArg 5] ++
    ((stx.getArg 7).args.toList.filter (· matches .ident ..))
  let pair (x y e body : Syntax) : Syntax :=
    .node i "term.letPair" #[stx.getArg 0, stx.getArg 1, .atom i "(", x, .atom i ",", y, .atom i ")",
      .atom i ":=", e, .node i Syntax.nullKind #[], body]
  let rec go : Nat → List Syntax → Syntax → Syntax
    | _, [x, y], e => pair x y e (stx.getArg 12)
    | k, x :: rest, e =>
      let r : Name := s!"tuple✝{k}"
      pair x (.ident i r) e (go (k + 1) rest (.node i "term.ident" #[.ident i r]))
    | _, _, e => e
  go 0 names (stx.getArg 10)

/-- (linear-case stage 2) The literal quantities a `split` at `q` binds its components
at, `q·p` and `q`, for a Σ whose first component is at `p` (when both are literals): a
component taken at 1 is linear (`LocalCtx.bindQ`), so a `match` on it is `casesOn1`. -/
partial def splitQtys (q : Term R) (p : Val R) : Option R × Option R :=
  match q with
  | .qlit r => (((Val.toPoly? p).bind (·.isConst?)).map (r * ·), some r)
  | _ => (none, none)

/-- `let q (x, y) := s; body`, check mode only (the motive is the expected type). -/
partial def elabLetPair (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let q ← elabQuantity ctx .default (stx.getArg 1).args[0]?
  let x := ((stx.getArg 3).getId?).getD "_"
  let y := ((stx.getArg 5).getId?).getD "_"
  let (s, sty) ← infer ctx (stx.getArg 8)
  match ← force sty with
  | .sigma _ p A B _ =>
    let g ← getGlobals
    let motive := quote g (ctx.lvl + 1) expected
    let (qx, qy) := splitQtys q p
    let ctx₂ := (ctx.bindQ x A qx).bindQ y (← instM B (Val.var ctx.lvl)) qy
    let body ← check ctx₂ (stx.getArg 10) expected
    pure (.split q s "z" motive x y body)
  | sty => throwAt (ctx.withInfo (stx.getArg 8)).info s!"let (x, y) := ... expects a pair, got {← showVal ctx sty}"

/-- `let q (x₁, (x₂, … xₙ)) := s; body` as nested splits at quantity `q`:
`split q s (x₁, r). split q r (x₂, r'). …`, with names `r` that no user name captures.
(One name: a `let`.) -/
partial def splitChain (ctx : LocalCtx R) (q : Term R) (s : Term R) (sty : VTy R) (names : List Name)
    (body : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let g ← getGlobals
  match names with
  | [] => throwAt ctx.info "internal error: nothing to bind"
  | [x] =>
    let sv ← evalIn ctx s
    let t ← check (ctx.define x sty sv) body expected
    pure (.letE x q (quote g ctx.lvl sty) s t)
  | x :: rest =>
    let .sigma _ p A B _ ← force sty
      | throwAt ctx.info s!"internal error: expected a pair, got {← showVal ctx sty}"
    let motive := quote g (ctx.lvl + 1) expected
    let Bty ← instM B (Val.var ctx.lvl)
    let (qx, qy) := splitQtys q p
    match rest with
    | [y] =>
      let t ← check ((ctx.bindQ x A qx).bindQ y Bty qy) body expected
      pure (.split q s "z" motive x y t)
    | _ =>
      let r : Name := "rest✝"
      let t ← splitChain ((ctx.bindQ x A qx).bind r Bty) (q.lift 2) (.var 0) Bty rest body expected
      pure (.split q s "z" motive x r t)

/-- (13h) `let q pat := e; body` for a pattern `⟨p₁, …, pₙ⟩` or `(.mk p₁ … pₙ)` (any
pattern in parentheses).

* Without a quantity it is `match e with | pat => body`: on a structure, the fields are
  bound by projections of `e`.
* With a quantity `q` it takes one structure (or tuple) apart with nested splits at
  `q`, one per component of the structure's Σ (`StructLayout`), so that a structure held
  at quantity 1 can be consumed; the patterns `pᵢ` are then names or `_`. Check mode
  only, like `let q (x, y) := e`. A component that is not a field and that the split
  would leave unused at `q` (today: the tail of every structure's Σ) is reported here,
  before the kernel counts the uses. -/
partial def elabLetPat (ctx : LocalCtx R) (stx : Syntax) (expected : Option (VTy R)) :
    ElabM R (Term R × VTy R) := do
  let pat := stx.getArg 2
  let body := stx.getArg 6
  let some qStx := (stx.getArg 1).args[0]? | do
    let i := stx.info
    let alt : Syntax := .node i "match.alt" #[.atom i "|", .node i "null" #[pat], .atom i "=>", body]
    let m : Syntax := .node i "term.match" #[.atom i "match", .node i "null" #[stx.getArg 4], .atom i "with",
      .node i "null" #[alt]]
    match expected with
    | some e => return (← check ctx m e, e)
    | none => return ← infer ctx m
  let some expected := expected
    | throwAt ctx.info "cannot infer the type of this expression; add a type ascription" ErrorCode.cannotInfer
  let q ← elabQuantity ctx .default (some qStx)
  let g ← getGlobals
  let v ← match patView g pat with
    | .ok v => pure v
    | .error e => throwAt pat.info e
  let (s, sty) ← infer ctx (stx.getArg 4)
  let sty ← forceMeta sty
  let nameOf (p : Syntax) : ElabM R Name := match patView g p with
    | .ok (.var n) => pure n
    | .ok .wild => pure "_"
    | _ => throwAt p.info "a `let` with a quantity takes one structure apart: its components are names or `_` (nest another `let` for a component)"
  let names ← match structHead? g sty with
    | some (S, _, _) =>
      if let some m := g.privateTo? (S ++ ".mk") then
        throwAt pat.info s!"cannot take a value of type {Globals.privateBase S} apart here: its constructor is private to module {m}" "private"
      let some L := structLayout? g S
        | throwAt pat.info (s!"cannot take a value of type {S} apart: {S} is opaque " ++
            s!"outside module {(g.opaqueTo? S).getD "?"} (it has private constructors or fields)") "private"
      let ps ← match v with
        | .ctor T c ps =>
          unless c == "mk" && (T.isNone || T == some S) do
            throwAt pat.info s!"{S} is a structure: its constructor is {S}.mk, not {(T.map (· ++ ".")).getD "."}{c}" ErrorCode.unknownConstructor
          pure ps
        | .anon ps => pure ps
        | _ => throwAt pat.info s!"`let` with a quantity expects a pattern ⟨…⟩ or (.mk …) for the structure {S}"
      let n := L.fields.length
      unless ps.length == n do
        throwAt pat.info s!"{S}.mk expects {n} argument{if n == 1 then "" else "s"} (the fields {", ".intercalate L.fields}), got {ps.length}" ErrorCode.wrongArgumentCount
      -- a component that is not a field, bound at `q` and never used
      let leftoverOk := match q with
        | .qlit r => QRig.le (0 : R) r
        | _ => false
      if L.comps.any (· == .marker false) && !leftoverOk then
        throwAt pat.info (s!"cannot take a value of the structure {S} apart at quantity {q.pretty ctx.names}: " ++
          s!"the Σ type of a structure ends in a component that is not a field (its marker tail), and this " ++
          s!"`let` would bind it at quantity {q.pretty ctx.names} and never use it. This is a limitation of " ++
          "how structures are encoded today; take the structure at quantity ω, use a tuple type, or a one-constructor " ++
          "`inductive` with fields at 1 (taken apart by `match`) for linear data")
      L.comps.mapM fun c => match c with
        | .field i => nameOf ps[i]!
        | .marker _ => pure "_"
    | none =>
      match v, ← force sty with
      | .anon ps, .sigma .. =>
        unless ps.length ≥ 2 do
          throwAt pat.info "an anonymous constructor pattern on a pair has at least two components"
        ps.mapM nameOf
      | _, sty => throwAt (ctx.withInfo (stx.getArg 4)).info s!"`let` with a quantity and a pattern expects a structure or a tuple, got {← showVal ctx sty}"
  pure (← splitChain ctx q s sty names body expected, expected)

/-- (13h) The anonymous constructor `⟨e₁, …, eₙ⟩`, checked against a structure `S`
(`S.mk e₁ … eₙ`), a pair (the tuple) or a data type with one constructor `c`
(`.c e₁ … eₙ`). -/
partial def elabAnon (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let g ← getGlobals
  let args := (stx.getArg 1).args.filter (!· matches .atom ..)
  let i := stx.info
  let app (h : Syntax) : Syntax := if args.isEmpty then h else .node i "term.app" #[h, .node {} "null" args]
  match structHead? g (← forceMeta expected) with
  | some (S, _, _) => check ctx (app (.node i "term.ident" #[.ident i (S ++ ".mk")])) expected
  | none =>
    match ← force expected with
    | .sigma .. =>
      unless args.size ≥ 2 do throwAt ctx.info "an anonymous constructor of a pair has at least two components"
      checkTuple ctx args.toList expected
    | .mu _ _ _ _ _ (some (T, _, _)) =>
      let [c] := ctorNames g T
        | throwAt ctx.info s!"an anonymous constructor ⟨…⟩ needs a type with one constructor, and {T} has {(ctorNames g T).length}"
      check ctx (app (.node i "term.dotIdent" #[.atom i ".", .ident i c])) expected
    | ty => throwAt ctx.info s!"an anonymous constructor ⟨…⟩ needs a structure, a pair or a data type with one constructor as its expected type, not {← showVal ctx ty}"

/-- (13i) Structure update `{ s with f₁ := v₁, … }`: `S.mk` with the named fields
replaced and the others projected from `s` (bound once, unless it is a variable). A
kept field whose type depends on a replaced one must still have its type. The fields
are read through `StructLayout`. (13p) A path `a.b := v` updates field `b` of the
structure in field `a`: `a := { s.a with b := v }`, and the updates of one field are
grouped (`a.b := v, a.c := w`). -/
partial def elabStructUpdate (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × VTy R) := do
  let sStx := stx.getArg 1
  let (s, sty) ← infer ctx sStx
  let ups := ((stx.getArg 3).args.filter (!· matches .atom ..)).toList.map fun u =>
    ((((u.getArg 0).getId?).getD "_").splitOn ".", u)
  structUpdateCore ctx stx s sty ups none

/-- (13i, 13p) `{ s with … }` for the term `s : sty`: `ups` are the updates as field paths
(each with its `structUpdate.field` node), `outer` the field path this structure sits at
(for messages), if it is inside another update. -/
partial def structUpdateCore (ctx : LocalCtx R) (stx : Syntax) (s : Term R) (sty : VTy R)
    (ups : List (List Name × Syntax)) (outer : Option String) : ElabM R (Term R × VTy R) := do
  let g ← getGlobals
  let at0 : SourceInfo := match outer, ups.head? with
    | some _, some (_, u) => u.info
    | _, _ => (ctx.withInfo (stx.getArg 1)).info
  let some (S, us, params) := structHead? g (← forceMeta sty)
    | match outer with
      | some o => throwAt at0 s!"field '{o}' is not a structure (its type is {← showVal ctx sty}), so its fields can't be updated"
      | none => throwAt at0 s!"structure update needs a value of a structure type, not one of type {← showVal ctx sty}"
  if let some m := g.privateTo? (S ++ ".mk") then
    throwAt at0 s!"cannot update a value of type {Globals.privateBase S} here: its constructor is private to module {m}" "private"
  let some L := structLayout? g S
    | throwAt at0 (s!"cannot update a value of type {S}: {S} is opaque " ++
        s!"outside module {(g.opaqueTo? S).getD "?"} (it has private constructors or fields)") "private"
  let some mk := g.find? (S ++ ".mk") | throwAt ctx.info s!"{S}.mk is missing"
  let pathStr (f : Name) : String := match outer with
    | some o => o ++ "." ++ f
    | none => f
  -- the updates, by field: a value, or updates inside the field (paths `f.…`)
  let mut direct : List (Name × Syntax × Syntax) := []
  let mut nested : List (Name × List (List Name × Syntax)) := []
  for (path, u) in ups do
    let f :: rest := path | continue
    unless L.fields.contains f do
      throwFix u.info s!"{S} has no field '{f}' (its fields are {", ".intercalate L.fields})" ErrorCode.noSuchField
        [("name", [f]), ("type", [S]), ("fieldsOnly", []), ("update", [])]
    match rest with
    | [] =>
      if direct.any (·.1 == f) || nested.any (·.1 == f) then
        throwAt u.info s!"field '{pathStr f}' is updated twice" ErrorCode.namedArgument
      direct := direct ++ [(f, u.getArg 2, u)]
    | _ =>
      if direct.any (·.1 == f) then throwAt u.info s!"field '{pathStr f}' is updated twice" ErrorCode.namedArgument
      nested := match nested.lookup f with
        | some us' => nested.map fun (h, l) => if h == f then (h, us' ++ [(rest, u)]) else (h, l)
        | none => nested ++ [(f, [(rest, u)])]
  -- `s` is read once per kept field: bind it, unless it is a variable
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  let isVar := s matches .var _
  let sVal0 ← evalIn ctx s
  let ctx' := if isVar then ctx else ctx.define "s✝" sty sVal0
  let sTm : Term R := if isVar then s else .var 0
  let sVal ← evalIn ctx' sTm
  let mut tm : Term R := .const (S ++ ".mk") us
  let mut fty : VTy R := eval g [] (mk.type.instLevels mk.levelParams us)
  for p in params do
    let .pi _ _ _ _ cod _ ← force fty | throwAt ctx.info s!"internal error: the type of {S}.mk"
    tm := .app tm (quote g ctx'.lvl p)
    fty ← instM cod p
  -- the components of `s`, with their types
  let mut compTys : Array (VTy R) := #[]
  let mut restTy ← force sty
  let mut restVal := sVal
  for _ in [0:L.comps.length - 1] do
    let .sigma _ _ A B _ := restTy | throwAt ctx.info s!"internal error: the layout of {S}"
    compTys := compTys.push A
    restTy ← force (← instM B (vFst restVal))
    restVal := vSnd restVal
  compTys := compTys.push restTy
  for f in L.fields, i in [0:L.fields.length] do
    let .pi _ _ _ dom cod _ ← force fty | throwAt ctx.info s!"internal error: the type of {S}.mk"
    let some k := L.fieldComp? i | throwAt ctx.info s!"internal error: the layout of {S}"
    -- the field keeps its type: it must still fit the constructor (whose earlier fields
    -- may have changed)
    let keepsType (what : String) : ElabM R Unit := do
      let st ← get
      try unifyAt ctx' stx dom compTys[k]!
      catch _ =>
        set st
        throwAt ctx.info (s!"field '{pathStr f}' {what}, but its type {← showVal ctx' compTys[k]!} depends on an updated field: " ++
          s!"it should now have type {← showVal ctx' dom}; update '{pathStr f}' too")
    let a ← match direct.find? (·.1 == f), nested.lookup f with
      | some (_, v, u), _ =>
        -- (13p) the field's name: its type (hover) and its declaration (go to definition)
        let fi := (u.getArg 0).info
        if fi.stop > 0 && !fi.synthetic && g.contains (S ++ "." ++ f) then
          pushInfo (.ident fi (S ++ "." ++ f) false ctx' dom)
        check ctx' v dom
      | none, some inner =>
        keepsType "is updated inside"
        let (t, _) ← structUpdateCore ctx' stx (L.compTerm k sTm) compTys[k]! inner (some (pathStr f))
        pure t
      | none, none =>
        keepsType "keeps its value"
        pure (L.compTerm k sTm)
    tm := .app tm a
    fty ← instM cod (← evalIn ctx' a)
  let t := if isVar then tm else .letE "s✝" w (quote g ctx.lvl sty) s tm
  pure (t, sty)

/-- `fun` in inference mode: untyped binders get a metavariable as their type. -/
partial def inferFun (ctx : LocalCtx R) (bs : List BinderView) (body : Syntax) :
    ElabM R (Term R × VTy R) := do
  match bs with
  | [] => infer ctx body
  | b :: rest =>
    let ty ← match b.type with
      | some s => pure (← checkType ctx s).1
      | none => freshMeta ctx s!"the type of {b.name}"
    let q ← elabQuantity ctx b.bi b.qty
    let vty ← evalIn ctx ty
    recordBinder ctx b.info b.name vty
    let ctx' := ctx.bind b.name vty
    let (t, bty) ← inferFun ctx' rest body
    let g ← getGlobals
    return (.lam b.name t, ctx.sortVal g (.pi b.name b.bi (← evalIn ctx q) vty (.mk ctx.env (quote g ctx'.lvl bty)) none))

/-- `ShareLet.share A B inst` if the class `ShareLet` is declared, `A` and `B` have no
holes, and an instance `ShareLet A B` is found (auto-share for `let`, HDL stage S0). -/
partial def autoShare? (ctx : LocalCtx R) (A B : VTy R) : ElabM R (Option (Term R)) := do
  unless (← get).classes.any (·.name == "ShareLet") do return none
  let g ← getGlobals
  let At ← zonk ctx.lvl (quote g ctx.lvl A)
  let Bt ← zonk ctx.lvl (quote g ctx.lvl B)
  unless At.mvars.isEmpty && Bt.mvars.isEmpty do return none
  let goalTy := vApp g (vApp g (eval g [] (.const "ShareLet" [])) A) B
  let some inst ← (try synthInstance ctx goalTy catch _ => pure none) | return none
  return some (.app (.app (.app (.const "ShareLet.share" []) At) Bt) inst)

/-- `let` in either mode. -/
partial def elabLet (ctx : LocalCtx R) (stx : Syntax) (expected : Option (VTy R)) :
    ElabM R (Term R × VTy R) := do
  let x := ((stx.getArg 2).getId?).getD "_"
  let q ← elabQuantity ctx .default (stx.getArg 1).args[0]?
  let (ty, val) ← match (stx.getArg 3).args[1]? with
    | some tyStx =>
      let (ty, _) ← checkType ctx tyStx
      pure (ty, ← check ctx (stx.getArg 5) (← evalIn ctx ty))
    | none =>
      let (val, vty) ← infer ctx (stx.getArg 5)
      pure (quote (← getGlobals) ctx.lvl vty, val)
  -- (P2) a `let`-bound proof is bound suspended, as the kernel binds it: the elaborator
  -- does not run it either (a proof need not have a normal form, and a short one can
  -- take a tower of exponentials of steps)
  let vTy ← evalIn ctx ty
  recordBinder ctx (stx.getArg 2).info x vTy
  let g ← getGlobals
  let vVal ← if g.lazyProofs && isProp g ctx.types.reverse.toArray vTy then pure (suspend g ctx.env val)
    else evalIn ctx val
  let ctx' := ctx.define x vTy vVal
  -- (21v) a linear `let` makes later `match`es additive (`LocalCtx.linearLvls`)
  let ctx' := match q with
    | .qlit r => if r != 0 && QRig.many? != some r then { ctx' with linearLvls := ctx.lvl :: ctx'.linearLvls } else ctx'
    | _ => ctx'
  let body := stx.getArg 7
  match expected with
  | some e =>
    -- auto-share (HDL stage S0): with no explicit quantity, a `let` whose value type `A`
    -- and body type `B` have an instance `ShareLet A B` becomes `ShareLet.share v (fun x
    -- => body)`; the body sees `x` as a variable, not a definition.
    if (stx.getArg 1).args.isEmpty then
      if let some share ← autoShare? ctx (← evalIn ctx ty) e then
        let b ← check (ctx.bind x (← evalIn ctx ty)) body e
        return (.app (.app share val) (.lam x b), e)
    return (.letE x q ty val (← check ctx' body e), e)
  | none =>
    let (b, bty) ← infer ctx' body
    return (.letE x q ty val b, bty)

/-- A Π telescope `b₁ → … → bₙ → body` (used by `depArrow` and `∀`). -/
partial def elabPis (ctx : LocalCtx R) (bs : List BinderView) (body : Syntax) :
    ElabM R (Term R × Level) := do
  match bs with
  | [] => checkType ctx body
  | b :: rest =>
    let (ty, l₁) ← match b.type with
      | some s => checkType ctx s
      | none => pure (← freshMeta ctx s!"the type of {b.name}", ← freshLevelMeta)
    let q ← elabQuantity ctx b.bi b.qty
    let vty ← evalIn ctx ty
    recordBinder ctx b.info b.name vty
    let (cod, l₂) ← elabPis (ctx.bind b.name vty) rest body
    return (.pi b.name b.bi q ty cod (some (.imax l₁ l₂)), .imax l₁ l₂)

/-- `(x : A) × (y : B) × C`, like `elabPis`. -/
partial def elabSigmas (ctx : LocalCtx R) (bs : List BinderView) (body : Syntax) :
    ElabM R (Term R × VTy R) := do
  match bs with
  | [] =>
    let (t, l) ← checkType ctx body
    return (t, .sort l)
  | b :: rest =>
    let (ty, l₁) ← match b.type with
      | some s => checkType ctx s
      | none => pure (← freshMeta ctx s!"the type of {b.name}", ← freshLevelMeta)
    let q ← elabQuantity ctx b.bi b.qty
    let vty ← evalIn ctx ty
    recordBinder ctx b.info b.name vty
    let (cod, s) ← elabSigmas (ctx.bind b.name vty) rest body
    let l₂ ← match ← force s with
      | .sort l => pure l
      | _ => freshLevelMeta
    return (.sigma b.name q ty cod (some (.max l₁ l₂)), .sort (.max l₁ l₂))

/-- (7e) After an application: its instance problems whose types its arguments have just
fixed (`Add ?A` in `a + 5`, now `Add Nat`) are solved now, not at the next instance
problem or the end of the command, so that the value computes when it meets a type
(`refl (a + 5) : Nat.lor a 5 = a + 5`: native arithmetic can't see an unsolved hole). -/
partial def solveReady : ElabM R Unit := do
  unless (← get).instReadyQ.isEmpty do discard synthPending

/-- (7e) A numeral, possibly negated or in parentheses (`3`, `-3`, `(3)`). -/
partial def numLike (stx : Syntax) : Bool :=
  stx.isOfKind "term.num" ||
  ((stx.isOfKind "term.paren" || stx.isOfKind "term.neg") && numLike (stx.getArg 1))

/-- (7f) A constructor of the expected type (`.succ n`, `.zero`), possibly in parentheses. -/
partial def dotLike (stx : Syntax) : Bool :=
  stx.isOfKind "term.dotIdent" || (stx.isOfKind "term.app" && (stx.getArg 0).isOfKind "term.dotIdent") ||
  (stx.isOfKind "term.paren" && dotLike (stx.getArg 1))

/-- (7f) Is the head of this application an operator marked `attribute [binop]` (`HAdd.hAdd`)? -/
partial def binopHead (ctx : LocalCtx R) (stx : Syntax) : ElabM R Bool := do
  unless stx.isOfKind "term.app" do return false
  let h := stx.getArg 0
  unless h.isOfKind "term.ident" do return false
  let s ← get
  unless s.classes.any (·.binop) do return false
  let x := stripScope (((h.getArg 0).getId?).getD "_")
  if (lookupLocal ctx x).isSome then return false
  let x := s.globals.resolve x
  return s.classes.any fun c => c.binop && c.fields.any fun f => c.name ++ "." ++ f == x

/-- (7f) A closed numeric expression: a numeral, or a `binop` applied to such (`10 * 2`,
`(1 + 2)`), seen through one macro step (the operator's notation). -/
partial def numTree (ctx : LocalCtx R) (stx : Syntax) : ElabM R Bool := do
  if numLike stx then return true
  if stx.isOfKind "term.paren" then return ← numTree ctx (stx.getArg 1)
  -- (a notation's node, which a macro rule expands; not an identifier, a literal, …)
  unless stx matches .node .. do return false
  if stx.isOfKind "term.ident" || stx.isOfKind "term.str" || stx.isOfKind "term.tuple" then return false
  let s ← get
  let stx' := if stx.isOfKind "term.app" then stx else (expandMacro? s.macros stx s.nextScope).getD stx
  unless stx'.isOfKind "term.app" && (← binopHead ctx stx') do return false
  for a in (stx'.getArg 1).args do
    unless ← numTree ctx a do return false
  return true

/-- (7e) An application of a class method to a numeral (`Add.add x 1`, `1 + x`, `-3`):
its numerals are elaborated after its other arguments and the expected type, which may
fix their type (`0 + a` with `a : Int`, `(-3 : Int)`), as Lean's `binop%` does. -/
partial def numOperands (ctx : LocalCtx R) (stx : Syntax) : ElabM R Bool := do
  unless stx.isOfKind "term.app" do return false
  let h := stx.getArg 0
  unless h.isOfKind "term.ident" do return false
  let x := stripScope (((h.getArg 0).getId?).getD "_")
  if (lookupLocal ctx x).isSome then return false
  if (stx.getArg 1).args.any numLike then
    if (← get).classes.any fun c => c.fields.any fun f => c.name ++ "." ++ f == x then return true
  -- (7f) a constructor operand of a `binop` waits too (`m * .succ n`), and a closed
  -- numeric operand (`(250 : U8) + 10 * 2`)
  if ← binopHead ctx stx then
    for a in (stx.getArg 1).args do
      if dotLike a || (← numTree ctx a) then return true
  return false

/-- A `fun` with a binder whose type isn't given: as an argument, it is elaborated after
the others (`checkApp`). -/
partial def postponable (stx : Syntax) : Bool :=
  (stx.isOfKind "term.paren" && postponable (stx.getArg 1)) ||
  (stx.isOfKind "term.fun" && ((stx.getArg 1).args.flatMap binderViews).any (·.type.isNone))

/-- The number of binders of a (parenthesised) `fun`. -/
partial def lambdaArity (stx : Syntax) : Nat :=
  if stx.isOfKind "term.paren" then lambdaArity (stx.getArg 1)
  else ((stx.getArg 1).args.flatMap binderViews).size

/-- Is the type (of a lambda argument) an unsolved hole, or is one of its first `k`
domains? Then the lambda is postponed (`postponable`). -/
partial def unknownDomains (lvl : Lvl) (ty : VTy R) : Nat → ElabM R Bool
  | 0 => pure false
  | k + 1 => do
    match ← force ty with
    | .neutral (.mvar _) _ => pure true
    | .pi _ _ _ dom cod _ =>
      if (← force dom) matches .neutral (.mvar _) _ then pure true
      else unknownDomains (lvl + 1) (← instM cod (Val.var lvl)) k
    | _ => pure false

/-- A tuple component that is a constructor of the expected type (`.c`, `.c args`, or a
tuple of such). -/
partial def dotComponent (stx : Syntax) : Bool :=
  (stx.isOfKind "term.paren" && dotComponent (stx.getArg 1)) ||
  stx.isOfKind "term.dotIdent" || stx.isOfKind "term.tag" ||
  (stx.isOfKind "term.app" && (stx.getArg 0).isOfKind "term.dotIdent") ||
  (stx.isOfKind "term.tuple" && (dotComponent (stx.getArg 1) ||
    ((stx.getArg 3).args.any fun c => !(c matches .atom ..) && dotComponent c)))

/-- Does elaborating this argument need its expected type to be known? -/
partial def needsExpected (stx : Syntax) : Bool :=
  (stx.isOfKind "term.paren" && needsExpected (stx.getArg 1)) ||
  stx.isOfKind "term.dotIdent" || stx.isOfKind "term.tag" || stx.isOfKind "term.rfl" ||
  (stx.isOfKind "term.app" && (stx.getArg 0).isOfKind "term.dotIdent") ||
  -- a tuple with a constructor component (`.ok (.nil, st)`)
  (stx.isOfKind "term.tuple" && (dotComponent (stx.getArg 1) ||
    ((stx.getArg 3).args.any fun c => !(c matches .atom ..) && dotComponent c))) ||
  -- check-only forms, also as the body of a `fun` (as in `bind x (fun y => match …)`);
  -- `term.block` is the prelude's `do`
  stx.isOfKind "term.match" || stx.isOfKind "term.by" || stx.isOfKind "term.block" ||
  -- a lambda's binder types usually come from the expected type
  stx.isOfKind "term.fun"

/-- The term inside parentheses. -/
partial def stripParens (a : Syntax) : Syntax := if a.isOfKind "term.paren" then stripParens (a.getArg 1) else a

/-- Arguments `_ … (g … rfl)`: a hole to be filled from the expected type, and an
application that is checked against its own expected type (`Ex.intro _ 3 (Ex.intro _ 3 rfl)`).
Inferring the outer application would check the inner one against `?P 3` with the hole
`?P` unsolved; take the outer one's type from the expected type first instead. -/
partial def holeAndNestedCheck (args : Array Syntax) : Bool :=
  args.any (fun a => (stripParens a).isOfKind "term.hole") &&
  args.any fun a =>
    let a := stripParens a
    a.isOfKind "term.app" && !(a.getArg 0).isOfKind "term.explicit" &&
      (a.getArg 1).args.any fun b => needsExpected b && !(stripParens b).isOfKind "term.fun"

/-- An application in check mode, using the **expected type first**: every explicit
argument gets a placeholder metavariable, the resulting type is unified with the
expected type (failure is fine here), and only then are the arguments elaborated,
against domains that are now usually known. That is what lets `.cons .zero .nil` find
its constructors. Each placeholder is then unified with its argument. -/
partial def checkApp (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  if hasNamedArgs stx then
    let (t, ty) ← inferAppNamed ctx stx
    unifyAt ctx stx expected ty
    return t
  let (f, fty) ← infer ctx (stx.getArg 0)
  let mut f := f
  let mut fty := fty
  let mut pending : Array (Syntax × Term R × VTy R × Bool) := #[]
  for arg in (stx.getArg 1).args do
    (f, fty) ← insertImplicits ctx f fty
    match ← force fty with
    | .pi _ _ _ dom cod _ =>
      let m ← freshPlaceholder (ctx.withInfo arg)
      -- (does the rest of the type mention the argument? If not, the placeholder occurs
      -- only in `f`, which `respine` rebuilds: it needn't be solved)
      let used := match cod with | .mk _ body => body.hasVar 0
      pending := pending.push (arg, m, dom, used)
      f := .app f m
      fty ← instM cod (← evalIn ctx m)
    | _ => return ← (do let (t, ty) ← inferApp ctx stx (postpone := false); unifyAt ctx stx expected ty; pure t)
  (f, fty) ← insertImplicits ctx f fty
  -- (speculative, so no guesses when the result type depends on the arguments: their
  -- placeholders are determined by the arguments, not by a first-order guess; see "When
  -- unification approximates" in `Unify.lean`)
  let holes := pending.filterMap fun (_, m, _, _) => match (Term.spine m).1 with
    | .mvar id => some id
    | _ => none
  let dependent := (quote (← getGlobals) ctx.lvl fty).mvars.any holes.contains
  let cur := (← get).approx
  let approx := if dependent then Approx.none else cur
  let _ ← tryCatch (withApprox approx (unify ctx.lvl expected fty)) (fun _ => pure ())
  let mut args : Array (Term R × Term R) := #[]
  -- a lambda with unannotated binders whose domains aren't known yet waits for the other
  -- arguments, which may fix them (`zipWith3 (fun b x y => if b then x else y) c t e`)
  let mut postponed : Array (Syntax × Term R × VTy R × Bool) := #[]
  -- (7e) the numerals of a class method's application wait too (`1 + x`); elsewhere a
  -- numeral may be what fixes a postponed lambda's domain (`mealy (fun s i => …) 0 xs`)
  let numPostpone ← numOperands ctx stx
  -- (7f) an operator marked `binop` (`HAdd.hAdd`): a numeral operand whose type is still a
  -- hole takes the type of the other operands, or else of the result (Lean's `binop%`,
  -- without coercions), so `x + 1` at `x : U8` is `HAdd U8 U8 ?C` at once, and `1 + x` too
  let binop ← if numPostpone then binopHead ctx stx else pure false
  for pass in [0:2] do
    for (arg, m, dom, used) in (if pass == 0 then pending else postponed) do
      if pass == 0 && ((postponable arg && (← unknownDomains ctx.lvl dom (lambdaArity arg))) ||
          (numPostpone && (numLike arg || (binop && (dotLike arg || (← numTree ctx arg)))) &&
            (← force dom) matches .neutral (.mvar _) _)) then
        postponed := postponed.push (arg, m, dom, used)
        continue
      if pass == 1 && binop && (numLike arg || dotLike arg || (← numTree ctx arg)) then
        if (← force dom) matches .neutral (.mvar _) _ then
          let others ← pending.filterMapM fun (a, _, d, _) => do
            if numLike a || dotLike a || (← numTree ctx a) then return none
            return some (d, !((← force d) matches .neutral (.mvar _) _))
          -- a known operand type, else the result type if known, else an operand's hole
          let target := match others.find? (·.2) with
            | some (d, _) => some d
            | none => none
          let target ← match target with
            | some d => pure (some d)
            | none =>
              if !((← force fty) matches .neutral (.mvar _) _) then pure (some fty)
              else pure ((others[0]?).map (·.1))
          if let some T := target then
            discard <| tryCatch (do unify ctx.lvl dom T; pure true) (fun _ => pure false)
      let a ← check ctx arg dom
      args := args.push (m, a)
      -- solving the placeholder evaluates the argument: along a nested spine
      -- (`List.cons x (List.cons y …)`) that would be quadratic, and nothing needs it
      unless used do continue
      -- solve the placeholder with `fun Γ => a` directly when we can: unification would
      -- quote `a`'s value, which can be expensive (normalising under binders)
      let unsolved ← match (Term.spine m).1 with
        | .mvar id => pure (if (← lookupMeta id).solution.isNone then some id else none)
        | _ => pure none
      match unsolved with
      | some mid =>
        if ctx.bound.all (· == true) && placeholderFull ctx then
          solveMeta mid (eval (← getGlobals) [] (ctx.names.reverse.foldr (fun x b => Term.lam x b) a))
        else
          -- solve it directly (unification would first try η for a pair, say, which
          -- leaves the pattern fragment)
          let vm ← evalIn ctx m
          let va ← evalIn ctx a
          -- (the value may mention a `let`-bound variable, such as a pattern variable
          -- standing for a component `fst✝ := p.1` of a tuple pattern: the hole can't,
          -- so try again with such variables replaced by their values)
          let solved ← match vm with
            | .neutral (.mvar mid') sp =>
              tryCatch (do solve ctx.lvl mid' sp va; pure true) fun _ =>
                tryCatch (do
                    let va' ← evalIn ctx (quote (← getGlobals) ctx.lvl va)
                    solve ctx.lvl mid' sp va'; pure true)
                  (fun _ => pure false)
            | _ => pure false
          unless solved do unifyAt ctx arg vm va
      | none => unifyAt ctx arg (← evalIn ctx m) (← evalIn ctx a)
  unifyAt ctx stx expected fty
  -- the application itself takes the arguments as written, not the placeholders (whose
  -- solutions would zonk to normal forms)
  let rec respine (t : Term R) : Term R := match t with
    | .app g x => .app (respine g) (((args.find? (·.1 == x)).map (·.2)).getD x)
    | t => t
  solveReady
  pure (respine f)

/-- (`wrong-argument-count`) What the quick fixes "give the implicit arguments with `@f`"
and "drop the `@`" need about an application of `fStx` to `n` arguments: its head, if it
is a global whose type has implicit (or instance) parameters, where the head starts, how
many explicit and implicit parameters the type has, and whether `@` was written. -/
partial def implicitsFix (ctx : LocalCtx R) (fStx : Syntax) (n : Nat) : ElabM R (Option (List (String × List String))) := do
  let explicitMode := fStx.isOfKind "term.explicit"
  unless fStx.isOfKind "term.ident" || explicitMode do return none
  if fStx.info.stop == 0 || fStx.info.synthetic then return none
  let some x := (fStx.getArg (if explicitMode then 1 else 0)).getId? | return none
  if (lookupLocal ctx x).isSome then return none
  let g ← getGlobals
  let some d := g.find? (g.resolve (stripScope x)) | return none
  let ps := piInfos d.type
  let nexp := (ps.filter (·.2.1 == .default)).length
  let nimp := ps.length - nexp
  if nimp == 0 then return none
  return some [("head", [x]), ("at", [toString fStx.info.start]), ("explicit", [toString nexp]),
    ("implicit", [toString nimp]), ("given", [toString n]), ("written", if explicitMode then ["@"] else [])]

/-- **Exercise 3.9.** Infer the type of an application `f a₁ … aₙ` (`term.app`, with
`f` = `stx.getArg 0` and the arguments in `(stx.getArg 1).args`).

Infer `f`. Then for each argument: unless `f` was written `@f`, insert implicits; force
the function type; if it is a Π, check the argument against the domain and instantiate
the codomain with the argument's value. If the function type is an unsolved meta,
unify it with a fresh Π `(x : ?A) → ?B x` first. Anything else is "not a function".

With `@f`, each argument fills the next Π whether implicit or explicit. -/
partial def inferApp (ctx : LocalCtx R) (stx : Syntax) (postpone : Bool := true) : ElabM R (Term R × VTy R) := do
  -- (given, 13a) named arguments `(x := e)`
  if hasNamedArgs stx then return ← inferAppNamed ctx stx
  --<sol
  let fStx := stx.getArg 0
  let explicitMode := fStx.isOfKind "term.explicit"
  -- (a lambda argument with unannotated binders is postponed: `checkApp` against an
  -- unknown type does that)
  if postpone && !explicitMode && ((stx.getArg 1).args.any postponable || (← numOperands ctx stx)) then
    let T ← freshMeta ctx "the type of an application"
    let vT ← evalIn ctx T
    let t ← checkApp ctx stx vT
    return (t, vT)
  let (f, fty) ← infer ctx fStx
  -- (`@f a…` with as many arguments as `f` has explicit parameters: the `@` is likely
  -- one too many, for the quick fix of whatever error the arguments give)
  if explicitMode then
    if let some data ← implicitsFix ctx fStx (stx.getArg 1).args.size then
      if (stx.getArg 1).args.size == (((data.lookup "explicit").bind (·.head?)).bind String.toNat?).getD 0 then
        pushInfo (.done (.fix stx.info "explicit-app" data))
  let mut f := f
  let mut fty := fty
  -- arguments whose type couldn't be unified yet (outside the pattern fragment): they
  -- wait, behind a placeholder, for the later arguments (which may solve the holes)
  let mut waiting : Array (Syntax × Term R × VTy R) := #[]
  for arg in (stx.getArg 1).args do
    if !explicitMode then
      (f, fty) ← insertImplicits ctx f fty
    let fty' ← match ← force fty with
      | ty@(.pi ..) => pure ty
      | ty@(.neutral (.mvar _) _) =>
        let a ← freshMeta ctx "a function domain"
        let va ← evalIn ctx a
        let b ← freshMeta (ctx.bind "x" va) "a function codomain"
        let pi : Val R := .pi "x" .default (.qlit QuantitySyntax.explicitDefault) va (.mk ctx.env b) none
        unifyAt ctx fStx ty pi
        pure pi
      | ty => do
        -- a type evaluated while its holes were unsolved (an equation stuck on a hole
        -- that is solved now, as in the type of a binder `α : NatTrans F P` whose
        -- category is a hole when `α` is bound): evaluated again, it may be a Π
        if let some ty' ← reevalSolved? ctx ty then
          if let .pi .. ← force ty' then
            pure ty'
          else
            throwAt (ctx.withInfo fStx).info s!"function expected\n  {← showTermM ctx f} : {← showVal ctx ty'}" ErrorCode.wrongArgumentCount
        else
        let msg := s!"function expected\n  {← showTermM ctx f} : {← showVal ctx ty}" ++ tooManyArgsHint f
        match ← implicitsFix ctx fStx (stx.getArg 1).args.size with
        | some data => throwFix (ctx.withInfo fStx).info msg ErrorCode.wrongArgumentCount data
        | none => throwAt (ctx.withInfo fStx).info msg ErrorCode.wrongArgumentCount
    match fty' with
    | .pi x bi _ dom cod _ =>
      -- `@f … _ …` at an instance argument: a problem for instance resolution
      let a ← if explicitMode && bi == .instImplicit && arg.isOfKind "term.hole" then do
          let m ← freshMeta (ctx.withInfo arg) s!"instance {x}"
          addInstProblem ctx m dom
          pure m
        else match ← tryCatch (Except.ok <$> check ctx arg dom) (fun e => pure (.error e)) with
          | .ok a => pure a
          | .error e =>
            if e.code != "non-pattern" then throw e
            let m ← freshPlaceholder (ctx.withInfo arg)
            waiting := waiting.push (arg, m, dom)
            pure m
      f := .app f a
      fty ← instArgM ctx cod a
    | _ => throwAt {} "unreachable"
  -- the waiting arguments, now; still outside the pattern fragment, with the flex-flex
  -- guess as the last resort (see "When unification approximates" in `Unify.lean`)
  let mut done : Array (Term R × Term R) := #[]
  for (arg, m, dom) in waiting do
    let a ← tryCatch (check ctx arg dom) fun e => do
      if e.code != "non-pattern" then throw e
      withApprox .last (check ctx arg dom)
    unifyAt ctx arg (← evalIn ctx m) (← evalIn ctx a)
    done := done.push (m, a)
  if !done.isEmpty then
    let rec respine (t : Term R) : Term R := match t with
      | .app g x => .app (respine g) (((done.find? (·.1 == x)).map (·.2)).getD x)
      | t => t
    f := respine f
  -- trailing instance arguments are inserted (`bitWidth A : Nat` for
  -- `bitWidth (0 A : Type) [BitPack A] : Nat`), as are implicits before them
  if !explicitMode && (← trailingInst ctx.lvl fty) then
    (f, fty) ← insertImplicits ctx f fty
  solveReady
  pure (f, fty)
  --|ex
  --| sorry
  --sol>

/-- (13a) The binder names of a Π telescope. -/
partial def binderNames (lvl : Lvl) (ty : VTy R) : ElabM R (List Name) := do
  match ← force ty with
  | .pi x _ _ _ cod _ => return x :: (← binderNames (lvl + 1) (← instM cod (Val.var lvl)))
  | _ => return []

/-- (13a) An application with named arguments `f a (x := e) b`, as in Lean. Walk `f`'s
type: a binder whose name has a named argument takes it, wherever it is (implicit,
instance or explicit); otherwise an explicit binder takes the next positional argument,
and an implicit or instance binder gets a metavariable or an instance problem (with
`@f`, every binder takes the next positional argument). Once the positional arguments
run out, the walk continues only while named arguments are left, so a named argument
after the last positional one fills its binder, inserting implicits before it; an
explicit binder before it, with no positional argument, is an error (Lean would
abstract it). Trailing instance arguments are inserted as for `inferApp`. -/
partial def inferAppNamed (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × VTy R) := do
  let fStx := stx.getArg 0
  let explicitMode := fStx.isOfKind "term.explicit"
  let args := (stx.getArg 1).args
  let mut named : Array (Name × Syntax × Syntax) := #[]
  let mut positional : Array Syntax := #[]
  for a in args do
    if a.isOfKind "term.namedArg" then
      let x := ((a.getArg 1).getId?).getD "_"
      if named.any (·.1 == x) then
        throwAt (ctx.withInfo a).info s!"argument '{x}' was already given" ErrorCode.namedArgument
      named := named.push (x, a.getArg 3, a)
    else positional := positional.push a
  let (f, fty) ← infer ctx fStx
  let mut f := f
  let mut fty := fty
  let mut pos := 0
  while pos < positional.size || !named.isEmpty do
    let .pi x bi _ dom cod _ ← force fty
      | if let some (y, _, a) := named[0]? then
          throwAt (ctx.withInfo a).info s!"no parameter named '{y}' (the function's type is {← showVal ctx fty})" ErrorCode.unknownParameter
        else
          throwAt (ctx.withInfo fStx).info (s!"function expected\n  {← showTermM ctx f} : {← showVal ctx fty}" ++ tooManyArgsHint f) ErrorCode.wrongArgumentCount
    let a ← match named.findIdx? (·.1 == x) with
      | some i =>
        let (_, e, _) := named[i]!
        named := named.eraseIdx! i
        check ctx e dom
      | none =>
        if bi == .default || explicitMode then
          match positional[pos]? with
          | some e =>
            pos := pos + 1
            if explicitMode && bi == .instImplicit && e.isOfKind "term.hole" then do
              let m ← freshMeta (ctx.withInfo e) s!"instance {x}"
              addInstProblem ctx m dom
              pure m
            else check ctx e dom
          | none =>
            let later ← binderNames ctx.lvl fty
            let (y, _, a) := named[0]!
            if let some (y, _, a) := named.find? (!later.contains ·.1) then
              throwAt (ctx.withInfo a).info s!"no parameter named '{y}' (the function's type is {← showVal ctx fty})" ErrorCode.unknownParameter
            throwAt (ctx.withInfo a).info s!"named argument '{y}' comes after the explicit parameter '{x}', which has no argument" ErrorCode.namedArgument
        else if bi == .instImplicit then do
          let m ← freshMeta ctx s!"instance {x}"
          addInstProblem ctx m dom
          pure m
        else do
          let m ← freshMeta ctx s!"implicit argument {x}"
          noteImplicitType ctx f m dom
          pure m
    f := .app f a
    fty ← instM cod (← evalIn ctx a)
  if !explicitMode && (← trailingInst ctx.lvl fty) then
    (f, fty) ← insertImplicits ctx f fty
  pure (f, fty)

/-- (13h) Column `k` of the first clause is a constructor pattern or `⟨…⟩`. If the
column's variable is a structure, rewrite the column's `.mk p…`/`S.mk p…`/`⟨p…⟩`
patterns to tuple patterns over the components of the structure's Σ (`StructLayout`:
the one place that knows the encoding) and compile that; the tuple patterns then bind
the fields by projections. An `⟨…⟩` on another type becomes a tuple pattern (a pair) or
the pattern of the type's only constructor. `none`: an ordinary constructor pattern. -/
partial def structPattern? (ctx : LocalCtx R) (vars : List Lvl) (clauses : List (MClause R))
    (goal : VTy R) (rc : Option RecCtx) (top : Bool) (k : Nat) : ElabM R (Option (Term R)) := do
  let g ← getGlobals
  let x := vars[k]!
  let xty ← forceMeta (ctx.types[ctx.lvl - x - 1]!)
  let p0 : Syntax := ((clauses.head?.bind (·.pats[k]?)).getD .missing)
  let rewrite (f : Syntax → PatView → ElabM R (Option Syntax)) : ElabM R (Term R) := do
    let clauses' ← clauses.mapM fun c => do
      let p := c.pats[k]!
      let (ns, v) ← match patViewAs g p with
        | .ok v => pure v
        | .error e => throwAt p.info e
      match ← f p v with
      | some p' => pure { c with pats := c.pats.take k ++ [asPatStx ns p'] ++ c.pats.drop (k + 1) }
      | none => pure c
    compileMatch ctx vars clauses' goal rc top
  match structHead? g xty with
  | some (S, _, _) =>
    if let some m := g.privateTo? (S ++ ".mk") then
      throwAt p0.info s!"cannot match on a value of type {Globals.privateBase S} here: its constructor is private to module {m}" "private"
    let some L := structLayout? g S
      | throwAt p0.info (s!"cannot match on a value of type {S}: {S} is opaque " ++
          s!"outside module {(g.opaqueTo? S).getD "?"} (it has private constructors or fields)") "private"
    let n := L.fields.length
    some <$> rewrite fun p v => do
      let ps? ← match v with
        | .ctor T c ps =>
          unless c == "mk" && (T.isNone || T == some S) do
            throwAt p.info s!"{S} is a structure: its constructor is {S}.mk, not {(T.map (· ++ ".")).getD "."}{c}" ErrorCode.unknownConstructor
          pure (some ps)
        | .anon ps => pure (some ps)
        | _ => pure none
      match ps? with
      | none => pure none
      | some ps =>
        unless ps.length == n do
          throwAt p.info s!"{S}.mk expects {n} argument{if n == 1 then "" else "s"} (the fields {", ".intercalate L.fields}), got {ps.length}" ErrorCode.wrongArgumentCount
        pure (some (L.tuplePattern p.info ps))
  | none =>
    let first ← match patViewAs g p0 with
      | .ok v => pure v.2
      | .error e => throwAt p0.info e
    unless first matches .anon .. do return none
    match ← force xty with
    | .sigma .. =>
      some <$> rewrite fun p v => do
        let .anon ps := v | pure none
        match ps with
        | a :: b :: rest =>
          let sep := (rest.flatMap fun q => [Syntax.atom {} ",", q])
          pure (some (.node p.info "term.tuple" #[.atom {} "(", a, .atom {} ",",
            .node {} "null" (#[b] ++ sep.toArray), .atom {} ")"]))
        | _ => throwAt p.info "an anonymous constructor pattern on a pair has at least two components"
    | .mu _ _ _ _ _ (some (T, _, _)) =>
      let [c] := ctorNames g T
        | throwAt p0.info s!"an anonymous constructor pattern ⟨…⟩ needs a type with one constructor, and {T} has {(ctorNames g T).length}"
      some <$> rewrite fun p v => do
        let .anon ps := v | pure none
        let h : Syntax := .node p.info "term.dotIdent" #[.atom {} ".", .ident p.info c]
        pure (some (if ps.isEmpty then h else .node p.info "term.app" #[h, .node {} "null" ps.toArray]))
    | ty => throwAt p0.info s!"an anonymous constructor pattern ⟨…⟩ needs a structure, a pair or a data type with one constructor, not {← showVal ctx ty}"

/-- (13q) Column `k` of the first clause is a literal `l` (a numeral, or a string) and the
column's type `T` is not `Nat`: test `T.beq x l`, as a new `Bool` column in front of
column `k`. Rows with the literal `l` want `.true` there (and `_` in column `k`), rows
with another literal `.false` (keeping theirs, for a later test), and catch-all rows
`_`. Literals don't cover a type, so the column needs a catch-all row. The branches
learn nothing about `x` (unlike a constructor split). -/
partial def compileLitTest (ctx : LocalCtx R) (vars : List Lvl) (clauses : List (MClause R))
    (goal : VTy R) (rc : Option RecCtx) (top : Bool) (k : Nat) : ElabM R (Term R) := do
  let g ← getGlobals
  let x := vars[k]!
  let xty := ctx.types[ctx.lvl - x - 1]!
  let some cl := clauses.head? | throwAt ctx.info "missing cases" "missing-case"
  let p0 := cl.pats[k]!
  let pview (p : Syntax) : ElabM R (List Name × PatView) := match patViewAs g p with
    | .ok v => pure v
    | .error e => throwAt p.info e
  let lit ← match (← pview p0).2 with
    | .lit l => pure l
    | _ => throwAt p0.info s!"a pattern `n + k` needs a Nat, not {← showVal ctx xty}"
  if rc.isSome && top then
    throwAt p0.info s!"structural recursion: the first argument must be matched by its constructors, and a literal pattern on {← showVal ctx xty} is an equality test"
  let some T := beqHead? g (← forceMeta xty)
    | throwAt p0.info (s!"a literal pattern needs Nat, or a type T with literals and an equality test " ++
        s!"T.beq : T → T → Bool; {← showVal ctx xty} has none")
  let catchAll ← clauses.anyM fun c => do
    let v := (← pview c.pats[k]!).2
    pure (v matches .var _ || v matches .wild)
  unless catchAll do
    throwAt p0.info (s!"a match on literals of type {← showVal ctx xty} needs a catch-all case " ++
      "(`_` or a variable) after them: literals don't cover the type") "missing-case"
  -- the test, on an alias of `x` (its own name may be shadowed)
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  let ctx1 := ctx.define "lit✝" xty (Val.var x)
  let idStx (n : Name) : Syntax := .node {} "term.ident" #[.ident {} n]
  let testStx : Syntax := .node {} "term.app" #[idStx (T ++ ".beq"), .node {} "null" #[idStx "lit✝", lit]]
  let (test, bty) ← infer ctx1 testStx
  let ctx2 := ctx1.define "test✝" bty (← evalIn ctx1 test)
  let ctorStx (c : Name) : Syntax := .node lit.info "term.dotIdent" #[.atom {} ".", .ident {} c]
  let clauses' ← clauses.mapM fun c => do
    let p := c.pats[k]!
    let (ns, v) ← pview p
    let (b, p') ← match v with
      | .lit l => pure (if sameLit l lit then (ctorStx "true", asPatStx ns holeStx) else (ctorStx "false", p))
      | .var _ | .wild => pure (holeStx, p)
      | .plusK .. => throwAt p.info s!"a pattern `n + k` needs a Nat, not {← showVal ctx xty}"
      | _ => throwAt p.info s!"literal patterns on {← showVal ctx xty} can't be mixed with other patterns in one column (only literals, `_` and variables)"
    pure { c with pats := c.pats.take k ++ [b, p'] ++ c.pats.drop (k + 1) }
  let body ← compileMatch ctx2 (vars.take k ++ [ctx1.lvl] ++ vars.drop k) clauses' goal rc top
  pure (.letE "lit✝" w (quote g ctx.lvl xty) (.var (ctx.lvl - x - 1))
    (.letE "test✝" w (quote g ctx1.lvl bty) test body))

/-- Compile clauses over the variables `vars` (levels) against `goal`. -/
partial def compileMatch (ctx : LocalCtx R) (vars : List Lvl) (clauses : List (MClause R))
    (goal : VTy R) (rc : Option RecCtx) (top : Bool) : ElabM R (Term R) := do
  let g ← getGlobals
  let q (v : Val R) : Term R := quote g ctx.lvl v
  let varTm (l : Lvl) : Term R := .var (ctx.lvl - l - 1)
  let typeOf (l : Lvl) : VTy R := ctx.types[ctx.lvl - l - 1]!
  let nameOf (l : Lvl) : Name := ctx.names[ctx.lvl - l - 1]!
  let some cl := clauses.head? | do
    -- (#250) an empty match: split the first variable whose constructors are all
    -- impossible (a pattern naming no constructor, so every branch must close itself)
    let noCtor : Syntax := .node {} "term.dotIdent" #[.atom {} ".", .ident {} "✝none"]
    let mut firstErr : Option (ElabError R) := none
    for x in vars, k in [0:vars.length] do
      if let .mu _ _ _ _ _ (some _) ← force (typeOf x) then
        let pats := (List.range vars.length).map fun i => if i == k then noCtor else holeStx
        try
          return ← compileMatch ctx vars [{ pats, rhs := holeStx }] goal rc top
        catch e => if firstErr.isNone then firstErr := some e
    match firstErr with
    | some e => throw e
    | none => throwAt ctx.info "missing cases" "missing-case"
  -- A catch-all last row of a multi-column match would be copied into every leaf of the
  -- split (one per pair of constructors, say): elaborate it once, as a local function
  -- of the scrutinees, and make the row call it. If it doesn't check generically (its
  -- right-hand side relies on what the other rows learnt), copy it as before.
  let isCatchAll (c : MClause R) : Bool := c.binds.isEmpty && c.pats.all fun p =>
    match patViewAs g p with
    | .ok (_, .var _) | .ok (_, .wild) => true
    | _ => false
  if let some last := clauses.getLast? then
    let n := vars.length
    -- (a small right-hand side is cheaper to copy than to call)
    let rec size : Syntax → Nat
      | .node _ _ args => args.foldl (fun acc a => acc + size a) 1
      | _ => 1
    if top && rc.isNone && n ≥ 2 && clauses.length ≥ 2 && isCatchAll last && !isCatchAll cl &&
        size last.rhs > 24 &&
        vars == (List.range n).map (ctx.lvl - n + ·) then
      let shared? ← tryCatch (some <$> do
        let w : Term R := .qlit QuantitySyntax.explicitDefault
        let body ← compileMatch ctx vars [last] goal none false
        let mut fn := body
        let mut fnTy := q goal
        for x in vars.reverse do
          fn := .lam (nameOf x) (fn.abstract (varTm x))
          fnTy := .pi (nameOf x) .default w (q (typeOf x)) (fnTy.abstract (varTm x)) none
        fnTy := ctx.sortType g fnTy
        let fnTyV ← evalIn ctx fnTy
        let ctx' := ctx.define "dflt✝" fnTyV (← evalIn ctx fn)
        let names := (List.range n).map fun i => s!"a✝{i}"
        let idStx (x : Name) : Syntax := .node {} "term.ident" #[.ident {} x]
        let callRhs : Syntax := .node {} "term.app" #[idStx "dflt✝", .node {} "null" (names.map idStx).toArray]
        let call : MClause R := { pats := names.map idStx, rhs := callRhs }
        let rest ← compileMatch ctx' vars (clauses.dropLast ++ [call]) goal none true
        pure (Term.letE "dflt✝" w fnTy fn rest)) (fun _ => pure none)
      if let some t := shared? then return t
  -- find the first constructor pattern of the first clause
  -- (13g) a pattern is its as-names and the pattern under them
  let pview (p : Syntax) : ElabM R (List Name × PatView) := match patViewAs g p with
    | .ok v => pure v
    | .error e => throwAt p.info e
  let asViews ← cl.pats.mapM pview
  let views := asViews.map (·.2)
  let some k := views.findIdx? (fun v => v matches .ctor .. || v matches .tuple .. || v matches .anon .. ||
      v matches .lit _ || v matches .plusK ..) | do
    -- all variables: bind them and elaborate the right-hand side
    let mut binds := cl.binds
    for (ns, v) in asViews, x in vars do
      for n in ns do binds := binds ++ [(n, typeOf x, Val.var x)]
      if let .var n := v then binds := binds ++ [(n, typeOf x, Val.var x)]
    let mut rhs := cl.rhs
    if let some rc := rc then
      let ihType (l : Lvl) : Option (VTy R) := ctx.types[ctx.lvl - l - 1]?
      match rewriteRecCalls g rc binds ihType ctx.lvl ctx.types.reverse.toArray cl.rhs with
      | .ok (r, extra) => rhs := r; binds := binds ++ extra
      | .error e => throwAt cl.rhs.info e ErrorCode.notStructural
    let mut ctx' := ctx
    for (n, ty, val) in binds do
      -- (linear-case stage 2) a pattern variable naming a linear variable (a field taken
      -- at 1) is linear too: a `match` on it is `casesOn1` again
      let lin := match val with
        | .neutral (.local l) #[] => ctx'.linearLvls.contains l
        | _ => false
      let lvl := ctx'.lvl
      ctx' := ctx'.define n ty val
      if lin then ctx' := { ctx' with linearLvls := lvl :: ctx'.linearLvls }
    -- (11q) the pattern variables, in the arm's context
    for v in views, x in vars, p in cl.pats do
      if let .var n := v then recordBinder ctx' p.info n (typeOf x)
    let body ← check ctx' rhs goal
    -- wrap the lets, innermost last. A pattern variable that names a variable (a field)
    -- is substituted instead: a `let` at ω would use an erased field at ω.
    let mut t := body
    let mut lvl := ctx'.lvl
    for (n, ty, val) in binds.reverse do
      lvl := lvl - 1
      match quote g lvl val with
      | v@(.var _) => t := t.instantiateAt 0 v
      | v => t := .letE n (.qlit QuantitySyntax.explicitDefault) (quote g lvl ty) v t
    return t
  -- (13q) a literal pattern on a type other than `Nat`: tests with `T.beq` (at `Nat`, a
  -- numeral is matched by its constructors, in the split below)
  if views[k]! matches .lit _ || views[k]! matches .plusK .. then
    if !(← isNatType (typeOf vars[k]!)) then
      return ← compileLitTest ctx vars clauses goal rc top k
  -- (13h) a constructor pattern on a structure, `.mk p…` or `⟨p…⟩`: the tuple pattern
  -- over the components of its Σ (`StructLayout`); `⟨p…⟩` is also a tuple pattern on a
  -- pair, and the constructor's pattern on a data type with one constructor
  if views[k]! matches .ctor .. || views[k]! matches .anon .. then
    if let some t ← structPattern? ctx vars clauses goal rc top k then return t
  -- a pair pattern: match the components, as two new (defined) variables
  if views[k]! matches .tuple .. then
    let x := vars[k]!
    let .sigma _ sq A B _ ← force (typeOf x)
      | throwAt (cl.pats[k]!).info s!"a tuple pattern needs a pair, not {← showVal ctx (typeOf x)}"
    let xv ← evalIn ctx (varTm x)
    let v1 := vFst xv
    let ty2 := Closure.inst g B v1
    let v2 := vSnd xv
    -- a first component at quantity 0 (a structure's erased field, `0 n : Nat`) is bound
    -- at 0: its projection is then in an erased position, and the component may only be
    -- used there (as by a constructor pattern on a data type, and the self-hosted frontend)
    let erased1 := ((Val.toPoly? sq).bind (·.isConst?)) == some 0
    let ctx1 := ctx.define "fst✝" A v1
    let ctx1 := if erased1 then { ctx1 with erasedLvls := ctx.lvl :: ctx1.erasedLvls } else ctx1
    let ctx2 := ctx1.define "snd✝" ty2 v2
    let vars' := vars.take k ++ [ctx.lvl, ctx.lvl + 1] ++ vars.drop (k + 1)
    let clauses' ← clauses.mapM fun c => do
      let p := c.pats[k]!
      let (ns, pv) ← pview p
      let asBinds := ns.map fun n => (n, typeOf x, xv)
      let (ps, binds) ← match pv with
        | .tuple a b => pure ([a, b], c.binds)
        | .var n => pure ([holeStx, holeStx], c.binds ++ [(n, typeOf x, xv)])
        | .wild => pure ([holeStx, holeStx], c.binds)
        | _ => throwAt p.info "expected a tuple pattern"
      pure { c with pats := c.pats.take k ++ ps ++ c.pats.drop (k + 1), binds := binds ++ asBinds }
    let body ← compileMatch ctx2 vars' clauses' goal rc top
    let w : Term R := .qlit QuantitySyntax.explicitDefault
    let w1 : Term R := if erased1 then .qlit 0 else w
    return .letE "fst✝" w1 (q A) (q v1) (.letE "snd✝" w (quote g (ctx.lvl + 1) ty2) (quote g (ctx.lvl + 1) v2) body)
  if rc.isSome && top && k != 0 then
    throwAt cl.rhs.info "structural recursion: the first argument must be matched first" ErrorCode.notStructural
  let x := vars[k]!
  let rsAll := vars.drop (k + 1)
  let xty ← force (typeOf x)
  let .mu _ _ _ ξi xsz (some (T, us, args)) := xty
    | if let some (T, m) := g.opaqueHere? xty then
        throwAt (cl.pats[k]!).info (s!"cannot match on a value of type {← showVal ctx xty}: {T} is opaque " ++
          s!"outside module {m} (it has private constructors or fields)") "private"
      else throwAt (cl.pats[k]!).info s!"cannot match on a value of type {← showVal ctx xty}"
  let some descD := g.find? (T ++ ".desc") | throwAt ctx.info s!"{T} is not an inductive type"
  -- (13b) a type declared `private` in another module: its recursors are private too
  if let some m := g.privateTo? (T ++ ".casesOn") then
    throwAt (cl.pats[k]!).info s!"cannot match on a value of type {T} here: its constructors are private to module {m}" "private"
  let nΔ := (piInfos descD.type).length
  let Δargs := args.take nΔ
  let ξ := args.drop nΔ
  let ξLvls := ξ.filterMap fun v => match v with
    | .neutral (.local l) #[] => some l
    | _ => none
  -- (#249) indices that are distinct variables are generalised by the motive, also when
  -- they are later columns (structural recursion puts its column first): they are then
  -- not reverted, so that the reverted variables' types see them as the constructor's
  -- indices (reverting them too would leave the index equation about the old ones)
  let idxVars := ξLvls.length == ξ.length && ξLvls.eraseDups.length == ξLvls.length &&
    !ξLvls.contains x
  let rs := if idxVars then rsAll.filter (!ξLvls.contains ·) else rsAll
  let modeA := idxVars && ξLvls.all (fun l => !rs.contains l)
  let useRec := rc.isSome && top
  -- a scrutinee of finite size is split with the sized eliminator, keeping field sizes
  let sized := !(xsz matches .szInf)
  if sized && useRec then
    throwAt ctx.info "structural recursion on a sized argument: give the definition a sized signature instead" ErrorCode.notStructural
  -- G := Π rs. goal
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  let mut G := q goal
  for r in rs.reverse do
    -- (21v) a reverted linear variable is re-bound at 1, so each branch may use it once
    let wr : Term R := if ctx.erasedLvls.contains r then .qlit 0 else if ctx.linearLvls.contains r then .qlit 1 else w
    G := .pi (nameOf r) .default wr (q (typeOf r)) (G.abstract (varTm r)) none
  G := ctx.sortType g G
  -- the motive's universe
  let tys := ctx.types.reverse.toArray
  let Gv ← evalIn ctx G
  let vG ← elabTypeSort? tys Gv
  let ctors : List Name := match descD.value.map (fun v => (piInfos descD.type).foldl (fun t _ => match t with
      | .lam _ b => b
      | t => t) v) with
    | some t => (t.descTag?.map (·.1)).getD []
    | none => []
  -- (13o) a constructor pattern of another type would match nothing (and the cases it was
  -- meant for would be reported missing): say so where it is, rather than report the
  -- scrutinee's constructors as missing (`if n then …` at `n : Nat` is a match on
  -- `.true`/`.false`). A pattern a macro wrote is reported at the match.
  unless ctors.isEmpty do
    -- a `mutual` block's tags are qualified (`Ev.s`), and the member's own constructors
    -- are the ones of its type (the other members' have the same family)
    let memberCtor (c : Name) : Bool := !c.contains '.' || memberTag g tys xty c
    for cl in clauses do
      if let (_, .ctor _ c' _) ← pview (cl.pats[k]!) then
        -- (`✝none`: #250's empty match names no constructor on purpose)
        unless ctors.any (fun c => ctorSelects c' c && memberCtor c) || c' == "✝none" do
          -- (a pattern a macro wrote, such as `if`'s `.true`, has no place of its own)
          let pi := (cl.pats[k]!).info
          let at_ := if pi.stop == 0 || pi.synthetic then ctx.info else pi
          let hint := if c' == "true" || c' == "false" then
            "; the condition of `if`, `&&` and `||` is a Bool" else ""
          throwFix at_ (s!"the value matched has type {T}, which has no constructor .{c'} " ++
            s!"(its constructors: {", ".intercalate (ctors.map (s!".{·}"))}){hint}")
            ErrorCode.unknownConstructor [("name", [c']), ("type", [T])]
  let nΞ := ξ.length
  -- a motive that depends on neither the indices nor the scrutinee: the non-dependent
  -- eliminator (`T.recN`), whose branches need no cast along the index equation
  -- (21v) with a variable bound at quantity 1 in scope: the additive case `T.casesOnA`,
  -- whose branches are alternatives, so that each may use the variable once (with
  -- `casesOn` the methods are separate ω arguments, and the uses add up)
  -- (linear-case stage 2) a scrutinee held at 1 (`linearLvls`): `T.casesOn1`, the
  -- additive case at quantity 1, whose branches receive the fields at their declared
  -- quantities (the kernel's `scase` at 1, K1)
  let linear := !sized && !useRec && ctx.linearLvls.contains x && (g.find? (T ++ ".casesOn1")).isSome
  let additive := linear || (!sized && !useRec && !ctx.linearLvls.isEmpty && (g.find? (T ++ ".casesOnA")).isSome)
  let nondep := !additive && modeA && !sized && nΞ > 0 && !((ξLvls ++ [x]).any fun l => G.hasVar (ctx.lvl - l - 1))
  let motive : Term R ←
    if nondep then pure G
    else if modeA then
      -- each abstraction puts `body` under one more binder, so later targets are lifted
      let mut body := G
      for l in ξLvls, i in [0:ξLvls.length] do body := body.abstract ((varTm l).lift i)
      body := body.abstract ((varTm x).lift ξLvls.length)
      pure ((ξLvls.map nameOf ++ [nameOf x]).foldr .lam body)
    else
      if G.hasVar (ctx.lvl - x - 1) then
        throwAt (cl.pats[k]!).info "this match needs index unification whose goal depends on the scrutinee; not supported yet"
      let .mu _ I _ _ _ _ := xty | unreachable!
      -- the tuple ends like the scrutinee's index: `()`, or a phantom tail's value
      let tail := q ((List.range nΞ).foldl (fun v _ => vSnd v) ξi)
      let lhs : Term R := (List.range nΞ).foldr (fun k acc => .pair (.var (nΞ - k)) acc) (tail.lift (nΞ + 1))
      let eqTm : Term R := .eq ((q I).lift (nΞ + 1)) lhs ((q ξi).lift (nΞ + 1))
      let body : Term R := .pi "e" .default (.qlit 0) eqTm (G.lift (nΞ + 2)) (vG.map (.imax 0 ·))
      pure ((List.range nΞ).foldr (fun k acc => .lam s!"i{k}" acc) (.lam "x" body))
  -- a type still to be found (an inferred `match`) is taken to be in `Type`
  let unknown := match whnf Gv with
    | .neutral (.mvar _) _ => true
    | _ => false
  let some v := vG.orElse fun _ => if unknown then some (.succ .zero) else none
    | throwAt ctx.info "could not determine the universe of the match's type"
  let elimName := T ++ (if linear then ".casesOn1" else if additive then ".casesOnA" else if sized then ".scasesOn" else if useRec then ".rec" else ".casesOn") ++
    (if nondep then "N" else "")
  let some ed := g.find? elimName | throwAt ctx.info s!"{elimName} is missing"
  let elimHead : Term R := .const elimName (us ++ [v])
  let sizeArgs : List (Val R) := if sized then [xsz] else []
  let mut f : Term R := ((Δargs ++ sizeArgs).map q).foldl .app elimHead |>.app motive
  -- the eliminator's type, instantiated with the parameters (size) and the motive
  let mut fty : VTy R := eval g [] (ed.type.instLevels ed.levelParams (us ++ [v]))
  for a in Δargs ++ sizeArgs ++ [← evalIn ctx motive] do
    let .pi _ _ _ _ cod _ ← force fty | throwAt ctx.info "internal error: eliminator type"
    fty ← instM cod a
  -- (21v, additive) the bundle's type `(t : Enum ls) → Br t`, and its branches
  let mut bundleTy : Option (VTy R × Closure R) := none
  let mut ups : Array (Term R) := #[]
  if additive then
    let .pi _ _ _ mA codA _ ← force fty | throwAt ctx.info "internal error: eliminator type"
    bundleTy := some (mA, codA)
  -- one method per constructor
  for c in ctors, ci in [0:ctors.length] do
    let some cd := g.find? (ctorConst T c) | throwAt ctx.info s!"missing constructor {c}"
    let fieldInfos := (piInfos cd.type).drop nΔ
    -- `T …`, or `(h : H) → T …` (an infinitary field: its hypothesis is a function)
    let isRecField (A : Term R) : Bool :=
      let head : Term R → Bool := fun A => match (Term.spine A).1 with
        | .const n _ => n == T
        | _ => false
      match A with
      | .pi _ _ _ _ B _ => head B
      | A => head A
    let nRec := if useRec then (fieldInfos.filter fun (_, _, A) => isRecField A).length else 0
    let (mTy, cod?) ← match bundleTy with
      | some (mA, _) => do
        -- `Br 'c` is `ULift (M_c)`
        let .pi _ _ _ _ brC _ ← force mA | throwAt ctx.info "internal error: additive eliminator type"
        let .ulift _ A ← force (← instM brC (.tag ctors ci)) | throwAt ctx.info "internal error: additive method type"
        pure (A, none)
      | none => do
        let .pi _ _ _ mTy cod _ ← force fty | throwAt ctx.info "internal error: eliminator type"
        pure (mTy, some cod)
    -- introduce fields, hypotheses, the equation, and the reverted variables
    let mut ctx' := ctx
    let mut mt := mTy
    if sized then
      -- the fields' size `j : Size< s`
      let .pi _ _ _ A B _ ← force mt | throwAt ctx.info "internal error: sized method"
      mt ← instM B (Val.var ctx'.lvl)
      ctx' := ctx'.bind "_j" A
    let mut fieldLvls : Array Lvl := #[]
    for (n, _, _) in fieldInfos do
      let .pi _ _ fq A B _ ← force mt | throwAt ctx.info "internal error: method type"
      fieldLvls := fieldLvls.push ctx'.lvl
      if ((Val.toPoly? fq).bind (·.isConst?)) == some 0 then
        ctx' := { ctx' with erasedLvls := ctx'.lvl :: ctx'.erasedLvls }
      mt ← instM B (Val.var ctx'.lvl)
      -- hidden: the patterns name the fields (`.ok items s1`), and a field's own name
      -- (`s`) must not shadow a variable of the same name in the right-hand side.
      -- A field the method takes at 1 is linear: a match on it is `casesOn1` again
      ctx' := ctx'.bindQ (n ++ "✝") A ((Val.toPoly? fq).bind (·.isConst?))
    let mut ihLvls : Array Lvl := #[]
    for _ in [0:nRec] do
      let .pi _ _ _ A B _ ← force mt | throwAt ctx.info "internal error: hypothesis type"
      ihLvls := ihLvls.push ctx'.lvl
      mt ← instM B (Val.var ctx'.lvl)
      ctx' := ctx'.bind "_ih" A
    let mut absurdBody : Option (Term R) := none
    let mut eInfo : Option (Lvl × VTy R) := none
    if !modeA then
      let .pi _ _ _ E B _ ← force mt | throwAt ctx.info "internal error: equation"
      let eLvl := ctx'.lvl
      eInfo := some (eLvl, E)
      mt ← instM B (Val.var eLvl)
      ctx' := ctx'.bind "e✝" E
      if let some prf := findAbsurd g (← force E) (Val.var eLvl) then
        absurdBody := some (.absurd (quote g ctx'.lvl mt) (quote g ctx'.lvl prf))
    -- (#250) the arms' branch for constructor `c` (when it is possible, the method's body)
    let elabBranch (clauses : List (MClause R)) : ElabM R (Term R) := do
        let mut ctx' := ctx'
        let mut mt := mt
        -- the solution rule with an equation: find `y = t` (or `t = y`) with `y` a field
        -- of this constructor, and substitute it in the later fields by re-binding them
        let mut solution : Option (Lvl × Val R × Bool × Val R × Val R) := none
        if let some (eLvl, E) := eInfo then
          for (prf, A, a, b) in findEqs g (← force E) (Val.var eLvl) do
            if solution.isSome then break
            for (yv, tv, yFirst) in [(a, b, true), (b, a, false)] do
              if let .neutral (.local y) #[] := yv then
                let later := fieldLvls.toList.filter (· ≥ y)
                let tTm := quote g ctx'.lvl tv
                if fieldLvls.contains y && later.all (fun l => !tTm.hasVar (ctx'.lvl - l - 1)) &&
                    solution.isNone then
                  solution := some (y, tv, yFirst, prf, A)
        let mut subst : List (Lvl × Val R) := []
        let mut fieldLvls' := fieldLvls
        let ctxBefore := ctx'
        if let some (y, tv, _, _, _) := solution then
          -- re-bind the fields after `y` with `y := t` (and earlier re-bound fields)
          subst := [(y, tv)]
          for d in fieldLvls.toList.filter (· > y) do
            let tyTm := quote g ctx'.lvl ctx'.types[ctx'.lvl - d - 1]!
            let env : Env R := (List.range ctx'.lvl).reverse.map fun l =>
              ((subst.find? (·.1 == l)).map (·.2)).getD (Val.var l)
            let ty' := eval g env tyTm
            subst := subst ++ [(d, Val.var ctx'.lvl)]
            fieldLvls' := fieldLvls'.map fun l => if l == d then ctx'.lvl else l
            if ctx'.erasedLvls.contains d then
              ctx' := { ctx' with erasedLvls := ctx'.lvl :: ctx'.erasedLvls }
            ctx' := ctx'.bind ctx'.names[ctx'.lvl - d - 1]! ty'
        let mut rsLvls : Array Lvl := #[]
        -- the motive over the reverted variables (the solution rule casts under them too)
        let mtRs := mt
        for r in rs do
          let .pi _ _ _ A B _ ← force mt | throwAt ctx.info "internal error: reverted variable"
          rsLvls := rsLvls.push ctx'.lvl
          mt ← instM B (Val.var ctx'.lvl)
          ctx' := ctx'.bindQ (nameOf r) A (if ctx.linearLvls.contains r then some 1 else none)
        -- the value of `x` in this branch, for variable patterns
        let ctorVal ← evalIn ctx' ((Δargs.map (quote g ctx'.lvl) ++ fieldLvls.toList.map
          (fun l => (.var (ctx'.lvl - l - 1) : Term R))).foldl .app (.const (ctorConst T c) us))
        let explicitIdx := fieldInfos.zipIdx.filter (fun ((_, bi, _), _) => bi == .default) |>.map (·.2)
        let mut cls : List (MClause R) := []
        -- a variable pattern is `x` itself (no object is rebuilt from its fields), unless
        -- the goal depends on `x` (then only the constructor has the refined type) or
        -- this is the recursor's split: its method also runs for the hypotheses,
        -- where the value at hand is the constructor, not `x`
        let xVal := if useRec || G.hasVar (ctx.lvl - x - 1) then ctorVal else Val.var x
        for cl' in clauses do
          let (asNames, pv) ← pview (cl'.pats[k]!)
          -- (13q) at `Nat`, a numeral or `p + k` is its outermost constructor
          let pv ← natPatView T (cl'.pats[k]!) pv
          -- (13g) the names of an as-pattern are bound like a variable pattern
          let cl' := { cl' with binds := cl'.binds ++ asNames.map fun n => (n, xty, xVal) }
          let before := cl'.pats.take k
          let after := cl'.pats.drop (k + 1)
          match pv with
          | .ctor _ c' ps =>
            if ctorSelects c' c then
              unless ps.length == explicitIdx.length do
                throwAt (cl'.pats[k]!).info (s!"the constructor {c} has {plural explicitIdx.length "explicit field"}, " ++
                  s!"but the pattern gives it {plural ps.length "argument"}") ErrorCode.wrongArgumentCount
              let sub := (List.range fieldInfos.length).map fun i =>
                match explicitIdx.idxOf? i with
                | some j => ps[j]!
                | none => holeStx
              cls := cls ++ [{ cl' with pats := before ++ sub ++ after }]
          | .var n =>
            let sub := fieldInfos.map fun _ => holeStx
            let binds := cl'.binds ++ [(n, xty, xVal)]
            cls := cls ++ [{ cl' with pats := before ++ sub ++ after, binds := binds }]
          | .wild =>
            cls := cls ++ [{ cl' with pats := before ++ (fieldInfos.map fun _ => holeStx) ++ after }]
          | .anon .. => throwAt (cl'.pats[k]!).info s!"an anonymous constructor pattern ⟨…⟩ needs a type with one constructor, and {T} has {ctors.length}"
          | .as .. => throwAt (cl'.pats[k]!).info "internal error: as-pattern"
          | .tuple .. => throwAt (cl'.pats[k]!).info "a tuple pattern needs a pair"
          | .lit _ | .plusK .. => throwAt (cl'.pats[k]!).info (s!"a literal pattern needs Nat, or a type T with " ++
              s!"literals and an equality test T.beq; {T} is a data type: match on its constructors")
        if cls.isEmpty then
          let fields := fieldInfos.filterMap fun (n, bi, _) =>
            if bi == .default then some (if n == "_" || n.contains '✝' then "x" else n) else none
          let pat := String.join ((s!".{c}" :: fields).intersperse " ")
          throwAt ctx.info s!"missing case for constructor {c}: add an alternative for {pat}" "missing-case"
        -- reverted variables are re-introduced at new levels: their hypotheses follow them
        let moved := rs.zip rsLvls.toList
        let rc := rc.map fun r => { r with ihs := r.ihs.map fun (a, b) => ((moved.lookup a).getD a, (moved.lookup b).getD b) }
        let rc' := rc.map fun r => { r with ihs := r.ihs ++ (if useRec then
          ((fieldLvls'.toList.zip (fieldInfos.map fun (f : Name × BinderInfo × Term R) => f.2.2)).filter
            (fun (_, A) => isRecField A)).map (·.1) |>.zip ihLvls.toList else []) }
        -- the hypotheses are extra (wildcard) columns, so that nested splits revert them too:
        -- their types mention the fields being split
        let ihCols := if useRec then ihLvls.toList else []
        let cls2 := cls.map fun cl => { cl with pats := cl.pats ++ ihCols.map fun _ => holeStx }
        -- (a column that wasn't reverted, an index variable, stays the outer variable)
        let restCols := rsAll.map fun l => ((rs.zip rsLvls.toList).lookup l).getD l
        -- (#249) the recursive calls leave out the arguments of the columns not reverted
        -- (the column's index in the definition's own order: the structural one was moved first)
        let origCol (pos j : Nat) : Nat := if j == 0 then pos else if j - 1 < pos then j - 1 else j
        let dropped (pos : Nat) : List Nat := rsAll.zipIdx.filterMap fun (l, i) =>
          if rs.contains l then none else some (origCol pos (k + 1 + i))
        let rc' := if useRec then rc'.map (fun r => { r with dropCols := dropped r.pos }) else rc'
        let inner ← compileMatch ctx' (vars.take k ++ fieldLvls'.toList ++ restCols ++ ihCols) cls2 mt rc' false
        let body0 := (rs.map nameOf).foldr .lam inner
        match solution with
        | none => pure body0
        | some (y, tv, yFirst, prf, A) =>
          -- cast `fun deps' => body0 : (Π deps[y := t]. M)` to `(Π deps. M)`, apply to deps
          let L := ctxBefore.lvl
          let deps := fieldLvls.toList.filter (· > y)
          let vt (l : Lvl) : Term R := .var (L - l - 1)
          let mut Gd := quote g L mtRs
          for d in deps.reverse do
            Gd := .pi ctxBefore.names[L - d - 1]! .default
              (if ctxBefore.erasedLvls.contains d then .qlit 0 else .qlit QuantitySyntax.explicitDefault)
              (quote g L ctxBefore.types[L - d - 1]!) (Gd.abstract (vt d)) none
          Gd := ctxBefore.sortType g Gd
          let Gdz := Gd.abstract (vt y)              -- under a binder for `y`
          let tTm := quote g L tv
          let Gdt := Gdz.instantiateAt 0 tTm
          let F := (deps.map fun d => ctxBefore.names[L - d - 1]!).foldr .lam body0
          let (aT, bT, Q, refl) :=
            if yFirst then  -- prf : y = t; Q z _ := (Π deps(z)) = (Π deps(y))
              (vt y, tTm, Term.lam "z" (.lam "h" (.eqTy (Gdz.lift 1) (Gd.lift 2))), Term.reflTy Gd)
            else            -- prf : t = y; Q z _ := (Π deps(t)) = (Π deps(z))
              (tTm, vt y, Term.lam "z" (.lam "h" (.eqTy (Gdt.lift 2) (Gdz.lift 1))), Term.reflTy Gdt)
          let eqPrf : Term R := .transp (quote g L A) aT Q refl bT (quote g L prf)
          let _ := Q
          let castTm : Term R := .cast Gdt Gd (if yFirst then eqPrf else eqPrf) F
          -- `body0` was built under the re-bound fields, which sit after `e` in the context
          pure (deps.foldl (fun acc d => .app acc (vt d)) castTm)
    -- (#250) an impossible constructor's branch is closed with `absurd`, but the arms that
    -- name it are still elaborated here (and the result dropped), so that their right-hand
    -- sides are type checked; a structural failure of this check (a missing nested case,
    -- an equation that can't be solved) is not reported, only an error inside a body
    let clausesHere ← if absurdBody.isNone then pure clauses else clauses.filterM fun cl' => do
      match patViewAs g (cl'.pats[k]!) with
      | .ok (_, pv) => match ← natPatView T (cl'.pats[k]!) pv with
        | .ctor _ c' _ => pure (c' == c)
        | _ => pure false
      | .error _ => pure false
    let inRhs (i : SourceInfo) : Bool := !i.synthetic && clausesHere.any fun cl' =>
      let r := cl'.rhs.info
      !r.synthetic && r.start ≤ i.start && i.stop ≤ r.stop && r.start < r.stop
    let body ← if let some b := absurdBody then
        if clausesHere.isEmpty then pure b else
        tryCatch (do let _ ← elabBranch clausesHere; pure b) fun err =>
          if inRhs err.info then throw err else pure b
      else elabBranch clausesHere
    -- lambdas for fields, hypotheses and the equation
    let names := (if sized then ["_j"] else []) ++ fieldInfos.map (·.1) ++ (List.replicate nRec "_ih") ++
      (if modeA then [] else ["e"])
    let method := names.foldr .lam body
    match cod? with
    | some cod =>
      f := .app f method
      fty ← instM cod (← evalIn ctx method)
    | none => ups := ups.push (.up (method.lift 1))  -- (under the bundle's `fun t`)
  -- (21v) the bundle `fun t => ecase t [up m_c…]`
  if let some (mA, codA) := bundleTy then
    let .pi _ _ _ _ brC _ ← force mA | throwAt ctx.info "internal error: additive eliminator type"
    let brTm := quote g (ctx.lvl + 2) (← instM brC (Val.var (ctx.lvl + 1)))
    let bundle : Term R := .lam "t" (.ecase "z" brTm (.var 0) ups.toList)
    f := .app f bundle
    fty ← instM codA (← evalIn ctx bundle)
  -- indices, scrutinee, equation proof, reverted variables
  for vξ in ξ do f := .app f (q vξ)
  f := .app f (varTm x)
  if !modeA then
    let .mu _ I _ _ _ _ := xty | unreachable!
    f := .app f (.refl (q I) (q ξi))
  for r in rs do f := .app f (varTm r)
  pure f
where
  nameOf' (_ : Lvl) : Name := "_"

/-- A numeral, or an `if`/`match` whose branches are all numerals (H14 S2). -/
partial def numeralish (stx : Syntax) : Bool :=
  numLike stx ||
  (stx.isOfKind "term.paren" && numeralish (stx.getArg 1)) ||
  (stx.isOfKind "term.ite" && numeralish (stx.getArg 3) && numeralish (stx.getArg 5)) ||
  (stx.isOfKind "term.match" && (stx.getArg 3).args.all fun a => a matches .atom .. || numeralish (a.getArg 3))

/-- (H14 S2) `if c then t else e` (the match `match c with | .true => t | .false => e` that the
prelude's `if` makes) when `c` is a signal: its type is not a data type and selects between
values of its own type (an instance `Mux C C`, as `r HwTy.bit` in the HDL). It is then
`Mux.mux c t e`, with an instance `Mux C A` at the expected type `A`. Any other condition
(a `Bool`, a hole, `Nat`, a type without a `Mux` instance) takes the ordinary path, and
its messages. -/
partial def ifMux? (ctx : LocalCtx R) (alts : Array Syntax) (c : Term R) (C expected : VTy R) :
    ElabM R (Option (Term R)) := do
  unless alts.size == 2 do return none
  let pat (a : Syntax) : Option Name :=
    match (a.getArg 1).args.filter (!· matches .atom ..) with
    | #[p] => if p.isOfKind "term.dotIdent" then (p.getArg 1).getId? else none
    | _ => none
  let some (tStx, eStx) := (match pat alts[0]!, pat alts[1]! with
      | some "true", some "false" => some (alts[0]!.getArg 3, alts[1]!.getArg 3)
      | some "false", some "true" => some (alts[1]!.getArg 3, alts[0]!.getArg 3)
      | _, _ => none) | return none
  match ← force C with
  | .mu .. | .neutral (.mvar _) _ => return none
  | _ => pure ()
  unless (← get).classes.any (·.name == "Mux") do return none
  let g ← getGlobals
  let Ct ← zonk ctx.lvl (quote g ctx.lvl C)
  unless Ct.mvars.isEmpty do return none
  let mux (A : VTy R) : VTy R := vApp g (vApp g (eval g [] (.const "Mux" [])) C) A
  let some _ ← (try synthInstance ctx (mux C) catch _ => pure none) | return none
  -- (H14 S4) `a && b` and `a || b` on a signal: the prelude makes them
  -- `if a then b else Bool.false` and `if a then Bool.true else b`; they are the gates
  -- `AndOp.and a b` and `OrOp.or a b` at the condition's type (`a &&& b`, `a ||| b`)
  let isConst (stx : Syntax) (n : Name) : Bool :=
    stx.isOfKind "term.ident" && (stx.getArg 0).getId? == some n
  let gate? : Option (Name × Syntax) :=
    if isConst eStx "Bool.false" then some ("AndOp.and", tStx)
    else if isConst tStx "Bool.true" then some ("OrOp.or", eStx)
    else none
  if let some (op, other) := gate? then
    unifyAt ctx other expected C
    let o ← check ctx other C
    let cls : Name := if op == "AndOp.and" then "AndOp" else "OrOp"
    let inst ← freshMeta ctx "an instance"
    addInstProblem ctx inst (vApp g (eval g [] (.const cls [])) C)
    return some (.app (.app (.app (.app (.const op []) Ct) inst) c) o)
  -- a branch that is a numeral (or an `if` of numerals) takes its type from the other
  -- one (`if c then 0 else x + 1`), so the other is elaborated first
  let (t, e) ← if numeralish tStx && !numeralish eStx then do
      let e ← check ctx eStx expected
      pure (← check ctx tStx expected, e)
    else pure (← check ctx tStx expected, ← check ctx eStx expected)
  let inst ← freshMeta ctx "an instance"
  addInstProblem ctx inst (mux expected)
  let At := quote (← getGlobals) ctx.lvl expected
  return some (.app (.app (.app (.app (.app (.app (.const "Mux.mux" []) Ct) At) inst) c) t) e)

/-- Elaborate `match e₁, …, eₙ with | p₁, …, pₙ => rhs …` against `expected`. -/
partial def elabMatch (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let g ← getGlobals
  let scruts := (stx.getArg 1).args.filter (!· matches .atom ..)
  let alts := (stx.getArg 3).args
  let clauses : List (MClause R) ← alts.toList.mapM fun a => do
    pure { pats := ← ((a.getArg 1).args.filter (!· matches .atom ..)).toList.mapM expandPattern, rhs := a.getArg 3 }
  -- bind every scrutinee to a fresh variable, generalising it in the goal
  let mut ctx' := ctx
  let mut ts : Array (Term R) := #[]
  -- zonk: solved metas in the expected type would otherwise hide its universe
  let mut goalTm ← zonk ctx.lvl (quote g ctx.lvl expected)
  let mut binders : Array (Name × Term R) := #[]
  -- (linear-case stage 2) a scrutinee that uses a linear local is bound at 1 and taken
  -- apart by `T.casesOn1`
  let mut linearScruts : Array Bool := #[]
  for s in scruts do
    let (t, ty) ← infer ctx s
    ts := ts.push t
    -- (H14 S2) a signal as the condition of `if`: a multiplexer
    if scruts.size == 1 then
      if let some m ← ifMux? ctx alts t ty expected then return m
    -- (only a data type with `T.casesOn1`, at size ∞: anything else would bind the
    -- scrutinee at 1 and then take it apart at ω)
    let hasCases1 := match ← force ty with
      | .mu _ _ _ _ .szInf (some (T, _, _)) => (g.find? (T ++ ".casesOn1")).isSome
      | _ => false
    linearScruts := linearScruts.push (hasCases1 && ctx.linearLvls.any fun l => t.hasVar (ctx.lvl - l - 1))
    -- an inaccessible name, so the user's own `x` isn't shadowed
    binders := binders.push ("x✝", quote g ctx.lvl ty)
  -- abstract the scrutinees, last first
  -- (each abstraction adds a binder: the later scrutinee terms are lifted over it)
  let mut absGoal := goalTm
  for t in ts, k in [0:ts.size] do absGoal := abstractOutsideHoles absGoal (t.lift k)
  let _ := goalTm
  let mut lvls : List Lvl := []
  -- a scrutinee's type mentions the earlier scrutinees (`match e, h with` for
  -- `h : P e`): abstract them too, so that matching on `e` refines `h`
  let mut absBinders : Array (Name × Term R) := #[]
  for (n, tyTm) in binders, i in [0:binders.size] do
    let mut A := tyTm
    for t in ts.extract 0 i, k in [0:i] do A := A.abstract (t.lift k)
    let vTy ← evalIn ctx' A
    absBinders := absBinders.push (n, A)
    lvls := lvls ++ [ctx'.lvl]
    ctx' := ctx'.bindQ n vTy (if linearScruts[i]! then some 1 else none)
  binders := absBinders
  goalTm := absGoal
  let goal ← evalIn ctx' goalTm
  if let some x := lvls.head? then recordMatch stx.info alts clauses ctx'.types[ctx'.lvl - x - 1]! ctx'.types.reverse.toArray
  let body ← compileMatch ctx' lvls clauses goal none true
  let lam := (binders.toList.map (·.1)).foldr .lam body
  -- (the `i`-th scrutinee's type is under the `i` binders before it)
  let piTy := (binders.toList.zip linearScruts.toList).foldr (fun ((n, A), lin) acc =>
    Term.pi n .default (.qlit (if lin then 1 else QuantitySyntax.explicitDefault)) A acc none) goalTm
  let piTy := ctx.sortType g piTy
  pure (ts.foldl .app (.ann lam piTy))

/-- **Exercise 6.2.** Elaborate the body of a quotation to a term that builds it as a
Wiz `Syntax` value: `SyntaxF.missing`, `SyntaxF.atom "v"`, `SyntaxF.node "k" args` with
`args` a chain of `SyntaxF.cons`/`SyntaxF.nil`, and `SyntaxF.ident "x✝"`: an
identifier gets the `✝` mark (its scope is chosen when the macro runs) unless it is
dotted or under one of the `unscopedParents`, as in `instantiate`. An antiquotation
`$x` is the local `x`, checked against `Syntax`. `mkStringLit` builds strings. -/
partial def elabQuote (ctx : LocalCtx R) (syntaxTy : VTy R) (parent : Name) (stx : Syntax) :
    ElabM R (Term R) := do
  --<sol
  let c (n : Name) : Term R := .const ("SyntaxF." ++ n) []
  if let some x := antiquotName? stx then
    return ← check ctx (.node stx.info "term.ident" #[.ident stx.info x]) syntaxTy
  match stx with
  | .missing => pure (c "missing")
  | .atom _ v => pure (.app (c "atom") (← mkStringLit v))
  | .ident _ n =>
    let n := if unscopedParents.contains parent || n.contains '.' then n else n ++ "✝"
    pure (.app (c "ident") (← mkStringLit n))
  | .node _ k args =>
    let mut list := c "nil"
    for a in args.reverse do
      list := .app (.app (c "cons") (← elabQuote ctx syntaxTy k a)) list
    pure (.app (.app (c "node") (← mkStringLit k)) list)
  --|ex
  --| sorry
  --sol>

/-- Infer the type of `stx`. -/
partial def infer (ctx : LocalCtx R) (stx : Syntax) : ElabM R (Term R × VTy R) := do
  let ctx := ctx.withInfo stx
  if let some stx' ← expand? stx then return ← infer ctx stx'
  match stx.kind with
  | "term.ident" | "term.explicit" | "term.identUniv" =>
    let x := (stx.getArg (if stx.isOfKind "term.explicit" then 1 else 0)).getId?.getD "_"
    let explicitLevels : Option (Array Syntax) := if stx.isOfKind "term.identUniv" then
        some ((stx.getArg 2).args.filter (!· matches .atom ..)) else none
    -- (stage 11) remember identifiers and their types, for hovers and go-to-definition
    let record (n : Name) (c : LocalCtx R) (ty : VTy R) : ElabM R Unit := do
      if stx.info.stop > 0 then pushInfo (.ident stx.info n (c.lvl > 0) c ty)
    if explicitLevels.isNone then
      if let some (ix, ty) := lookupLocal ctx x then
        record x ctx ty
        return (.var ix, ty)
    -- a macro-scoped name that isn't a local refers to the global of its base name
    let x := stripScope x
    -- (13b) this module's private declaration of that name, if any
    let x := (← getGlobals).resolve x
    match (← getGlobals).find? x with
    | some d =>
      -- (13b) a private name of another module
      if let some m := (← getGlobals).privateTo? x then
        throwAt ctx.info s!"'{x}' is private to module {m}" "private"
      let us ← match explicitLevels with
        | some ls =>
          unless ls.size == d.levelParams.length do
            throwAt ctx.info s!"{x} has {d.levelParams.length} universe parameters, {ls.size} given"
          ls.toList.mapM elabLevel
        | none => d.levelParams.mapM fun p => freshLevelMeta ctx.info s!"the universe level {p} of {x}"
      let ty ← evalIn {} (d.type.instLevels d.levelParams us)
      record x {} ty
      return (.const x us, ty)
    | none =>
      -- (13b) another module's private declaration of that name (under its own kernel
      -- name, `Globals.privateName`)
      let g ← getGlobals
      if let some (_, m) := g.privates.toList.find? fun (n, m) => m != g.module && n == Globals.privateName m x then
        throwAt ctx.info s!"'{x}' is private to module {m}" "private"
      -- built-in types
      let builtinLevel : Option Level := match explicitLevels with
        | some _ => none
        | none => some (if x == "True" || x == "False" then 0 else 1)
      match x, explicitLevels with
      | "Unit", some #[l] | "Empty", some #[l] =>
        let l ← elabLevel l
        return (if x == "Unit" then .unit l else .empty l, .sort l)
      | "Qty", none => return (.qty, .sort 1)
      | "Size", none => return (.size, .sort 1)
      | "Unit", none | "True", none => return (.unit builtinLevel.get!, .sort builtinLevel.get!)
      | "Empty", none | "False", none => return (.empty builtinLevel.get!, .sort builtinLevel.get!)
      | _, _ =>
      -- the definition being elaborated (`def f … := … f …`): recursion needs equations
      if (← get).defining == some x then
        throwAt ctx.info (s!"recursive call to {x} in a definition without equations; write it as equations " ++
          s!"(`def {x} … : T | p => …`), or as `:= match y with | p => …` on its own parameters, " ++
          "or make it `partial`") "recursive-without-equations"
      -- field access: `p.x.y`
      match x.splitOn "." with
      | base :: f :: fs =>
        -- the longest prefix that names something: `Tx.bundle.toEl` is the field `toEl` of
        -- the global `Tx.bundle`, not the fields `bundle.toEl` of `Tx`
        let parts := base :: f :: fs
        let g ← getGlobals
        let named (n : Name) : Bool := (lookupLocal ctx n).isSome || (g.find? (g.resolve n)).isSome
        let k := ((List.range (parts.length - 1)).reverse.map (· + 1)).find? (fun k =>
          named (".".intercalate (parts.take k))) |>.getD 1
        if k > 1 then
          let head := ".".intercalate (parts.take k)
          let (t, ty) ← infer ctx (.node stx.info "term.ident" #[.ident stx.info head])
          elabFields ctx t ty (parts.drop k)
        else
          -- `T.f` with `T` a type (or nothing at all) is a name, not a field access: say
          -- that the name is unknown (`Nat.ad`), not that types have no field `ad`
          let isName := (lookupLocal ctx base).isNone &&
            match g.find? (g.resolve base) with
            | some d => endsInSort d.type
            | none => !["Unit", "True", "Empty", "False", "Qty", "Size"].contains base &&
                      !(g.privates.toList.any fun (n, m) => m != g.module && n == Globals.privateName m base)
          if isName then
            -- a field of a structure that has no projection function (an erased one)
            if fs.isEmpty && (((structLayout? g (g.resolve base)).map (·.fields)).getD []).contains f then
              throwAt ctx.info s!"unknown identifier '{x}': the field {f} of {base} has no projection function (an erased field has none; take the structure apart with `match` or `let ⟨…⟩`)"
            pushInfo (.done (.unknownIdent ctx.info x ctx.names))
            throwAt ctx.info s!"unknown identifier '{x}'" "unknown-identifier"
          let (t, ty) ← infer ctx (.node stx.info "term.ident" #[.ident stx.info base])
          -- (#266) `T.f` with `T` a global type (or type family, or function) and no field
          -- `f`: a qualified name that doesn't exist (not imported, or its definition failed)
          let qualified := (lookupLocal ctx base).isNone && match ← force ty with
            | .sort _ | .pi .. => true
            | _ => false
          if qualified then
            try elabFields ctx t ty (f :: fs)
            catch e =>
              if e.msg.startsWith "no field '" then
                pushInfo (.done (.unknownIdent ctx.info x ctx.names))
                throwAt ctx.info s!"unknown identifier '{x}'" "unknown-identifier"
              else throw e
          else elabFields ctx t ty (f :: fs)
      | _ =>
        pushInfo (.done (.unknownIdent ctx.info x ctx.names))
        throwAt ctx.info s!"unknown identifier '{x}'" "unknown-identifier"
  | "term.recCall" =>
    -- a recursive call `f y …` of the definition whose equations these are, already the
    -- induction hypothesis (`rewriteRecCalls`). A local variable named `f` would make the
    -- call ambiguous (the second elaboration once called the local, T1): an error.
    let fn := ((stx.getArg 0).getId?).getD "_"
    if (lookupLocal ctx fn).isSome then
      throwAt ((ctx.withInfo (stx.getArg 0)).info)
        (s!"a local variable named {fn} shadows the recursive definition {fn}: inside the equations of {fn}, " ++
          s!"`{fn} …` is the recursive call; rename the local variable") "shadowed-recursive"
    infer ctx (stx.getArg 1)
  | "term.type" | "term.sort" =>
    let l ← match (stx.getArg 1).args[0]? with
      | some ls => elabLevel ls
      | none => pure .zero
    let l := if stx.isOfKind "term.type" then .succ l else l
    return (.sort l, .sort (.succ l))
  | "term.prop" => return (.sort .zero, .sort (.succ .zero))
  | "term.paren" => infer ctx (stx.getArg 1)
  | "term.namedArg" => throwAt ctx.info "a named argument `(x := e)` is only allowed as an argument of an application"
  | "term.ascription" =>
    let from_ := (← get).nextInst
    let (ty, _) ← checkType ctx (stx.getArg 3)
    -- (7f) the type's own stuck problems get their default instances now, as in Lean (a
    -- type is elaborated to the end): `(rfl : 1 + 1 = 2)`
    if (← get).nextInst > from_ then synthDefaults from_
    let vty ← evalIn ctx ty
    let t ← check ctx (stx.getArg 1) vty
    return (.ann t ty, vty)
  | "term.hole" | "term.syntheticHole" =>
    let a ← freshMeta ctx "the type of a hole"
    let desc := if stx.isOfKind "term.hole" then "_" else s!"?{((stx.getArg 1).getId?).getD "_"}"
    return (← freshMeta ctx desc, ← evalIn ctx a)
  | "term.app" =>
    if let some r ← inferData? ctx stx then return r
    inferApp ctx stx
  | "term.enum" =>
    let ls := ((stx.getArg 2).args.filterMap Syntax.getId?).toList
    return (.enum ls, .sort 1)
  | "term.ecase" =>
    -- non-dependent: the first branch's type is the type of every branch
    let (s, sty) ← infer ctx (stx.getArg 1)
    let .enum ls ← force sty | throwAt ctx.info s!"ecase expects a tag, got {← showVal ctx sty}"
    let bs := ((stx.getArg 3).args.filter (!· matches .atom ..)).toList
    let b₀ :: rest := bs | throwAt ctx.info "ecase needs branches"
    unless bs.length == ls.length do throwAt ctx.info s!"ecase needs {ls.length} branches"
    let (t₀, ty) ← infer ctx b₀
    let ts ← rest.mapM fun b => check ctx b ty
    let motive := (quote (← getGlobals) ctx.lvl ty).lift 1
    return (.ecase "z" motive s (t₀ :: ts), ty)
  | "term.fun" =>
    -- annotate: the kernel can't infer the type of a bare lambda (e.g. `(fun x => b) a`)
    let (t, ty) ← inferFun ctx ((stx.getArg 1).args.flatMap binderViews).toList (stx.getArg 3)
    return (.ann t (quote (← getGlobals) ctx.lvl ty), ty)
  | "term.let" => elabLet ctx stx none
  | "term.arrow" =>
    let (a, l₁) ← checkType ctx (stx.getArg 0)
    let (b, l₂) ← checkType (ctx.bind "_" (← evalIn ctx a)) (stx.getArg 2)
    return (.pi "_" .default (defaultQty .default) a b (some (.imax l₁ l₂)), .sort (.imax l₁ l₂))
  | "term.depArrow" =>
    let (t, l) ← elabPis ctx (binderViews (stx.getArg 0)).toList (stx.getArg 2)
    return (t, .sort l)
  | "term.forall" =>
    let (t, l) ← elabPis ctx ((stx.getArg 1).args.flatMap binderViews).toList (stx.getArg 3)
    return (t, .sort l)
  | "term.depSigma" =>
    let bs := (binderViews (stx.getArg 0)).toList
    elabSigmas ctx bs (stx.getArg 2)
  | "term.prod" =>
    let (a, l₁) ← checkType ctx (stx.getArg 0)
    let (b, l₂) ← checkType (ctx.bind "_" (← evalIn ctx a)) (stx.getArg 2)
    return (.sigma "_" (defaultQty .default) a b (some (.max l₁ l₂)), .sort (.max l₁ l₂))
  | "term.tuple" =>
    inferTuple ctx (#[stx.getArg 1] ++ ((stx.getArg 3).args.filter (!· matches .atom ..))).toList
  | "term.unitVal" => return (.tt, .unit 1)
  | "term.szInf" => return (.szInf, .size)
  | "term.szSuc" => return (.szSuc (← check ctx (stx.getArg 1) .size), .size)
  | "term.sizeLt" => return (.sizeLt (← check ctx (stx.getArg 1) .size), .sort 1)
  | "term.sized" =>
    let (T, ty) ← infer ctx (stx.getArg 0)
    let s ← check ctx (stx.getArg 2) .size
    let g ← getGlobals
    let q := quote g ctx.lvl
    let qh (h : Option (Name × List Level × List (Val R))) := h.map fun (n, us, as) => (n, us, as.map q)
    match ← force (← evalIn ctx T) with
    | .mu l I D i _ h => return (.mu l (q I) (q D) (q i) s (qh h), ty)
    | .nu l I D i _ h => return (.nu l (q I) (q D) (q i) s (qh h), ty)
    | v => throwAt ctx.info s!"only inductive and coinductive types have sizes, not {← showVal ctx v}"
  | "term.field" =>
    let (t, ty) ← infer ctx (stx.getArg 0)
    -- `.a.b.c` lexes as one dotted identifier
    let path := (((stx.getArg 2).getId?).getD "_").splitOn "."
    elabFields ctx t ty path
  | "term.proj" =>
    let (t, ty) ← infer ctx (stx.getArg 0)
    match ← force ty, (stx.getArg 2).getNat? with
    | .sigma _ _ A _ _, some 1 => return (.fst t, A)
    | .sigma _ _ _ B _, some 2 => return (.snd t, ← instM B (vFst (← evalIn ctx t)))
    | ty, _ => throwAt ctx.info s!"cannot project from a value of type {← showVal ctx ty}"
  | "term.eq" =>
    let (a, A) ← infer ctx (stx.getArg 0)
    let b ← check ctx (stx.getArg 2) A
    return (.eq (quote (← getGlobals) ctx.lvl A) a b, .sort 0)
  | "term.refl" =>
    let (a, A) ← infer ctx (stx.getArg 1)
    let g ← getGlobals
    let va ← evalIn ctx a
    match ← force A with
    | .sort _ => return (.reflTy a, vEqType g va va)
    | A => return (.refl (quote g ctx.lvl A) a, vEq g A va va)
  | "term.transp" =>
    let (e, ety) ← infer ctx (stx.getArg 3)
    let g ← getGlobals
    match ← force ety with
    | .neutral (.eq A a b) #[] =>
      let motiveTy : Val R := ctx.sortVal g (.pi "b" .default (.qlit 0) A
        (.mk [a, A] (.pi "_" .default (.qlit 0) (.eq (.var 2) (.var 1) (.var 0)) (.sort 0) (some 1))) none)
      let P ← check ctx (stx.getArg 1) motiveTy
      let vP ← evalIn ctx P
      let p ← check ctx (stx.getArg 2) (vApp g (vApp g vP a) (.neutral (.refl A a) #[]))
      let q := quote g ctx.lvl
      return (.transp (q A) (q a) P p (q b) e, vApp g (vApp g vP b) (← evalIn ctx e))
    | ety => throwAt ctx.info s!"transp: expected a proof of an equation, got {← showVal ctx ety}"
  | "term.cast" =>
    let (e, ety) ← infer ctx (stx.getArg 1)
    match ← force ety with
    | .neutral (.eqTy X Y) #[] =>
      let t ← check ctx (stx.getArg 2) X
      let g ← getGlobals
      return (.cast (quote g ctx.lvl X) (quote g ctx.lvl Y) e t, Y)
    -- (4g) an equation between data types computes (to the equation of their codes), and so
    -- do equations between `Π`s and `Σ`s: then the target can't be read off the proof's type
    | .neutral .. | .unfold .. => throwAt ctx.info "cannot infer the type of this cast; add a type ascription" ErrorCode.cannotInfer
    | _ => throwAt ctx.info "cannot infer the type of this cast: its proof's type is an equation that has computed, so it no longer shows the target type; write `(cast e t : T)`" ErrorCode.cannotInfer
  | "term.match" =>
    -- stage 13: the type is found from the alternatives (a metavariable, in `Type`)
    -- (not depending on the scrutinised variables: the motive abstracts them, which
    -- would leave the metavariable outside the pattern fragment)
    let scrut := (stx.getArg 1).args.toList.filterMap fun a =>
      if a.isOfKind "term.ident" then (a.getArg 0).getId? else none
    let firstIx (n : Name) : Option Nat := ctx.names.findIdx? (· == n)
    let hidden := scrut.filterMap firstIx
    let ctx' := { ctx with bound := ctx.bound.zipIdx.map fun (b, i) => b && !hidden.contains i }
    let ty ← evalIn ctx (← freshMeta ctx' "the type of this match")
    return (← check ctx stx ty, ty)
  | "term.letPair" | "term.letTuple" | "term.absurd" | "term.rfl" =>
    throwAt ctx.info "cannot infer the type of this expression; add a type ascription" ErrorCode.cannotInfer
  | "term.letUnit" => do
    let u ← check ctx (stx.getArg 4) (.unit (.succ .zero))
    let (b, ty) ← infer ctx (stx.getArg 6)
    return (.letUnit u b, ty)
  | "term.nativeRefl" =>
    throwAt ctx.info "native_refl can only be the whole body of a definition, `def X : a = b := native_refl` (with --trust-native)"
  -- (13g–i) as-patterns, anonymous constructors, pattern `let`, structure update
  | "term.asPat" => throwAt ctx.info "an as-pattern `x@p` is only allowed in a pattern"
  | "term.anon" => throwAt ctx.info "cannot infer the type of an anonymous constructor ⟨…⟩; add a type ascription" ErrorCode.cannotInfer
  | "term.letPat" => elabLetPat ctx stx none
  | "term.structUpdate" => elabStructUpdate ctx stx
  | "term.omega" => return (← elabQtyLit ctx stx "ω", .qty)
  | "term.num" =>
    -- an unannotated numeral is a `builtin nat`
    match (← get).builtins.lookup "nat" with
    | some N =>
      let ty := eval (← getGlobals) ctx.env (.const N [])
      -- (`check` comes back here unless the type is the data type `N`: don't loop)
      unless (← force ty) matches .mu _ _ _ _ _ (some _) do
        throwAt ctx.info s!"numerals need `builtin nat :=` a data type, and {N} is not one"
      return (← check ctx stx ty, ty)
    | none => throwAt ctx.info "numerals need `builtin nat := …` or a type ascription"
  | "term.str" =>
    match (← get).builtins.lookup "string" with
    | some S =>
      let ty := eval (← getGlobals) ctx.env (.const S [])
      return (← check ctx stx ty, ty)
    | none => throwAt ctx.info "string literals need `builtin string := …`"
  | k =>
    if k.startsWith "quote." then
      let syntaxTy ← evalIn {} (.const "Syntax" [])
      return (← elabQuote ctx syntaxTy "" (stx.getArg 3), syntaxTy)
    throwAt ctx.info s!"the syntax {k} has no meaning: no `macro_rules` (or `attribute [macro {k}] f`) for it is in scope (if one is defined above, it was rejected: see its error)" ErrorCode.unknownSyntax


-- Tactics (see `Elab/Tactic.lean`)

/-- Run the tactic syntax `stx`: expand macros, find the Wiz function registered for
its kind, run it to a `Tac` request chain, and interpret that. -/
partial def evalTacticStx (code : Code) (st : TacState R) (stx : Syntax) (record : Bool := true) :
    ElabM R (TacState R) := do
  if stx matches .atom .. then return st
  -- (for the language server) the open goals before and after each tactic
  if record && stx.info.stop > 0 then
    let before ← openGoals st
    let st' ← try evalTacticStx code st stx false
      catch e => throw { e with state? := e.state?.map fun s =>
        { s with infos := s.infos.push (.tactic stx.info false before before) } }
    pushInfo (.tactic stx.info false before (← openGoals st'))
    return st'
  if let some stx' ← expand? stx then return ← evalTacticStx code st stx'
  let some f := (← get).tactics.lookup stx.kind | throwAt stx.info s!"the tactic syntax {stx.kind} has no meaning: no `attribute [tactic {stx.kind}] f` (or macro) for it is in scope (if one is defined above, it was rejected: see its error)" ErrorCode.unknownSyntax
  if stx.info.stop > 0 then pushInfo (.done (.expansion stx.info stx.kind (.fn "tactic" f) none))
  let t := apply code (run code [] (.global "TacticM.run")) (apply code (run code [] (.global f)) (encodeSyntax stx))
  runTac code stx.info st t

/-- **Exercise 6.5** (the request loop). Interpret the requests of a `Tac` value (the
constructor numbers are in `TacTag`), threading the tactic state, until `done`.
Each request's last field is its continuation: apply it (`apply code`) to the encoded
answer and continue. A failure is an elaboration error; `catch` runs its handler
on the state from *before* the body (`ElabM` drops state changes on an exception). -/
partial def runTac (code : Code) (info : SourceInfo) (st : TacState R) (v : RVal) : ElabM R (TacState R) := do
  let g ← getGlobals
  let fld (i : Nat) : RVal := v.conField i
  let num (r : RVal) : ElabM R Nat := match r.toNat? with
    | some n => pure n
    | none => throwAt info "tactic: malformed number"
  let str (r : RVal) : ElabM R String := match r.toString? with
    | some s => pure s
    | none => throwAt info "tactic: malformed string"
  let stxOf (r : RVal) : ElabM R Syntax := match decodeLocated info r with
    | some s => pure s
    | none => throwAt info "tactic: malformed syntax"
  let goalOf (r : RVal) : ElabM R (Goal R) := do
    let some gl := st.goals[← num r]? | throwAt info "tactic: unknown goal"
    pure gl
  -- reflect a term (zonked first) in a goal's context
  -- (constructor applications by name, where the type `ty?` and the types inside `t` tell:
  -- `reflectT`; a term with no data in it takes the plain `reflect`)
  let refl (st : TacState R) (gl : Goal R) (t : Term R) (ty? : Option (VTy R) := none) :
      ElabM R (RVal × TacState R) := do
    let t ← zonk gl.ctx.lvl t
    if hasData t then
      let (r, hs) ← (reflectT (RCtx.ofLocal gl.ctx) t ty?).run st.handles
      pure (r, { st with handles := hs })
    else
      let (r, hs) := (reflect t gl.ctx.lvl).run st.handles
      pure (r, { st with handles := hs })
  -- the type of a term a request was handed, as far as its head tells
  let typeOf? (gl : Goal R) (t : Term R) : ElabM R (Option (VTy R)) :=
    (RCtx.ofLocal gl.ctx).typeOf? t
  let addGoal (st : TacState R) (gl : Goal R) : TacState R × Nat :=
    ({ st with goals := st.goals.push gl }, st.goals.size)
  let unifyGoal (gl : Goal R) (t : Term R) : ElabM R Unit := do
    unify gl.ctx.lvl (← evalIn gl.ctx gl.tm) (← evalIn gl.ctx t)
  --<sol
  let tag := (v.tag?).getD 1000
  if tag == TacTag.done then return st
  if tag == TacTag.result then throwAt info "a tactic may not return syntax"
  if tag == TacTag.fail then throwAt info (((fld 0).toString?).getD "tactic failed") ErrorCode.tacticFailed
  if tag == TacTag.trace then
    pushTrace info (((fld 0).toString?).getD "")
    return ← runTac code info st (fld 1)
  if tag == TacTag.fresh then
    let n := (← get).nextScope
    modify fun s => { s with nextScope := n + 1 }
    return ← runTac code info st (apply code (fld 0) (.nat n))
  if tag == TacTag.getGoals then
    let opens ← st.open.filterM fun i => match st.goals[i]? with
      | some gl => gl.isOpen
      | none => pure false
    return ← runTac code info { st with «open» := opens } (apply code (fld 0) (encodeList (opens.map encodeNat)))
  if tag == TacTag.setGoals then
    let some gs := decodeList (fld 0) | throwAt info "tactic: malformed goal list"
    return ← runTac code info { st with «open» := ← gs.mapM num } (fld 1)
  if tag == TacTag.evalTactic then
    let st ← evalTacticStx code st (← stxOf (fld 0))
    return ← runTac code info st (fld 1)
  if tag == TacTag.catch_ then
    let st' ← try runTac code info st (fld 0)
      catch e => runTac code info st (apply code (fld 1) (encodeString e.msg))
    return ← runTac code info st' (fld 2)
  if tag == TacTag.ctorInfo then
    let ans := match ctorInfo? g (← str (fld 0)) with
      | some (T, nParams, nFields) => mkCon 1 [encodePair (encodeString T) (encodePair (.nat nParams) (.nat nFields))]
      | none => mkCon 0 []
    return ← runTac code info st (apply code (fld 1) ans)
  if tag == TacTag.isDefinition then
    let ans := match g.find? (← str (fld 0)) with
      | some { value := some _, inline := false, .. } => mkCon 1 [encodeBool true]
      | some _ => mkCon 1 [encodeBool false]
      | none => mkCon 0 []
    return ← runTac code info st (apply code (fld 1) ans)
  if tag == TacTag.satSolve then
    -- (28b) untrusted: the proof is checked by the kernel
    let some cs := decodeList (fld 1) | throwAt info "tactic: malformed clauses"
    let clauses ← cs.mapM fun c => do
      let some ls := decodeList c | throwAt info "tactic: malformed clause"
      ls.mapM num
    let ans := match Smt.satSolve (← get).smt (← num (fld 0)) clauses with
      | .unsat p => mkCon 0 [encodeList (p.map fun (id, ls, hs) =>
          encodePair (.nat id) (encodePair (encodeList (ls.map .nat)) (encodeList (hs.map .nat))))]
      | .sat m => mkCon 1 [encodeList (m.map .nat)]
      | .error e => mkCon 2 [encodeString e]
    return ← runTac code info st (apply code (fld 2) ans)
  -- the rest are about a goal, the first field
  let gl ← goalOf (fld 0)
  let lvl := gl.ctx.lvl
  if tag == TacTag.nativeDecide then
    -- (28e) `X.satK.native✝ : Sat.IsTrue e` (else `e = .true`), decided by running `e`
    -- (as `native_refl` does)
    let s ← get
    unless s.smt.trustNative do
      throwAt info "native evaluation is not enabled: deciding by running compiled code is trusted, not checked by the kernel; run with --trust-native to allow it"
    if s.smtDecl.isEmpty then throwAt info "tactic: an axiom can only be added in the body of a definition"
    let e ← zonk lvl (← reify st.handles (fld 1) lvl)
    let some e := (List.range lvl).foldlM (fun t _ => t.strengthen? 0) e
      | throwAt info "native evaluation: the term mentions the goal's variables (it must be closed)"
    let boolT : Term R := .const "Bool" []
    let trueT : Term R := .const "Bool.true" []
    -- (the command decides it, by `Native.decideNative`, before it adds the axiom)
    let ax := s!"{s.smtDecl}.sat{s.sideDecls.size + 1}.native✝"
    -- (stated as `Sat.IsTrue e`, a definition, not as the equation it unfolds to: the
    -- kernel's equation type computes both sides when it is evaluated (F5 of
    -- wiz-notes/kernel-eval.md), so every use would run the check again; the glued
    -- `IsTrue e` is compared with the use's type by its arguments)
    let ty : Term R := if g.contains "Sat.IsTrue" then .app (.const "Sat.IsTrue" []) e else .eq boolT e trueT
    let d : Decl R := { name := ax, levelParams := [], type := ty, value := none }
    modify fun s => { s with globals := s.globals.insert d, sideDecls := s.sideDecls.push d, unifyFails := {} }
    let (r, st) ← refl st gl (Term.const ax [])
    return ← runTac code info st (apply code (fld 2) r)
  if tag == TacTag.define then
    -- (28c) `X.def✝k := fun ctx => val : Π ctx, ty`, checked by the kernel with `X`
    let s ← get
    if s.smtDecl.isEmpty then throwAt info "tactic: a definition can only be added in the body of a definition"
    unless gl.ctx.bound.all id do throwAt info "tactic: a definition can't be added in a context with a `let`"
    let names := gl.ctx.names.reverse
    let env := gl.ctx.env.reverse.toArray
    let types ← (List.range lvl).zip gl.ctx.types.reverse |>.mapM fun (j, A) => do
      let t ← zonk j (quote g j A)
      pure (eval g (env.extract 0 j).toList.reverse t)
    let ty ← zonk lvl (← reify st.handles (fld 1) lvl)
    let val ← zonk lvl (← reify st.handles (fld 2) lvl)
    unless (Term.mvars ty).isEmpty && (Term.mvars val).isEmpty do throwAt info "tactic: a definition with holes"
    let q : Term R := .qlit QuantitySyntax.explicitDefault
    -- (a closed value is defined as it is, not over the context: a closed constant can be
    -- shared with closed terms, such as what native evaluation decides)
    let closed? : Option (Term R × Term R) := do
      let ty' ← (List.range lvl).foldlM (fun t _ => t.strengthen? 0) ty
      let val' ← (List.range lvl).foldlM (fun t _ => t.strengthen? 0) val
      pure (ty', val')
    let k := match closed? with | some _ => 0 | none => lvl
    let (ty, val) := closed?.getD (ty, val)
    let dTy := (List.range k).reverse.foldl (fun body j => .pi (names[j]!) .default q (quote g j types[j]!) body none) ty
    let dVal := (List.range k).reverse.foldl (fun body j => Term.lam (names[j]!) body) val
    let n := s!"{s.smtDecl}.def✝{s.sideDecls.size + 1}"
    let d : Decl R := { name := n, levelParams := s.levelParams, type := dTy, value := some dVal }
    modify fun s => { s with globals := s.globals.insert d, sideDecls := s.sideDecls.push d, unifyFails := {} }
    let use : Term R := (List.range k).foldl (fun f j => Term.app f (.var (lvl - 1 - j)))
      (Term.const n (s.levelParams.map Level.param))
    let (r, st) ← refl st gl use
    return ← runTac code info st (apply code (fld 3) r)
  if tag == TacTag.eqView then
    -- (28b) inside an equation: `a = b` at `A`
    let t ← zonk lvl (← reify st.handles (fld 1) lvl)
    let t ← match t with
      | .eq .. => pure t
      | _ => do pure (quote g lvl (whnf (← evalIn gl.ctx t)))
    match t with
    | .eq A a b =>
      let (rA, st) ← refl st gl A
      let (ra, st) ← refl st gl a (some (← evalIn gl.ctx A))
      let (rb, st) ← refl st gl b (some (← evalIn gl.ctx A))
      return ← runTac code info st (apply code (fld 2) (mkCon 1 [encodePair rA (encodePair ra rb)]))
    | _ => return ← runTac code info st (apply code (fld 2) (mkCon 0 []))
  if tag == TacTag.smt then
    -- (28a) trusted: the goal becomes an axiom, on the solver's word
    let s ← get
    unless s.smt.trust do
      throwAt info "SMT solving is not enabled: `smt` closes a goal on an SMT solver's word, which the kernel does not check; run with --trust-smt to allow it"
    if s.smtDecl.isEmpty then throwAt info "smt: only in the body of a definition (`def X : P := by smt`)"
    unless gl.ctx.bound.all id do throwAt info "smt: the goal's context has a `let`; not supported yet"
    let tyT ← zonk lvl (quote g lvl gl.ty)
    if !(Term.mvars tyT).isEmpty then throwAt info "smt: the goal has holes"
    let names := gl.ctx.names.reverse
    -- (the context's types with their solved holes filled: a hypothesis
    -- `Nat.lt (UIntN.toNat x) 256 = .true` has the width as a solved hole)
    let env := gl.ctx.env.reverse.toArray
    let types ← (List.range lvl).zip gl.ctx.types.reverse |>.mapM fun (j, A) => do
      let t ← zonk j (quote g j A)
      pure (eval g (env.extract 0 j).toList.reverse t)
    let q ← match Smt.translate g names types (gl.ctx.bound.reverse) (← evalIn gl.ctx tyT) with
      | .ok q => pure q
      | .error e => throwAt info e
    let secs := max 1 (s.smt.timeoutMs / 1000)
    -- (only a definite answer is kept in the cache; a timeout or a crash is not)
    let definite (a : Smt.Answer) : Bool :=
      let l := ((a.stdout.trimAscii.toString.splitOn "\n").headD "").trimAscii.toString
      l == "sat" || l == "unsat"
    let (sid, ans) ← match Smt.runSolver s.smt s.smt.solver ["-smt2", s!"-T:{secs}", "{in}"] q.script "smt2" false definite with
      | .ok r => pure r
      | .error e => throwAt info s!"smt: {e}"
    let out := ans.stdout.trimAscii.toString
    let first := ((out.splitOn "\n").headD "").trimAscii.toString
    if first == "sat" then
      let model := ((out.splitOn "\n").drop 1) |> "\n".intercalate
      let model := q.shown.foldl (fun m (x, u) => m.replace x u) model
      throwAt info s!"smt: the solver found a counterexample:\n{model}"
    unless first == "unsat" do
      throwAt info s!"smt: the solver gave no proof ({sid}): {if first.isEmpty then "no answer" else out}"
    -- `X.smt✝k⟨z3 4.13.0⟩ : Π ctx, goal`, erased binders
    let short := Smt.shortId sid
    let ax := s!"{s.smtDecl}.smt✝{s.sideDecls.size + 1}⟨{short}⟩"
    let axTy := (List.range lvl).reverse.foldl (fun body j =>
      .pi (names[j]!) .default (.qlit 0) (quote g j types[j]!) body none) tyT
    -- (smt-review B4) the definition's universe parameters are the axiom's too
    let d : Decl R := { name := ax, levelParams := s.levelParams, type := axTy, value := none }
    modify fun s => { s with globals := s.globals.insert d, sideDecls := s.sideDecls.push d, unifyFails := {} }
    let use := (List.range lvl).foldl (fun f j => Term.app f (.var (lvl - 1 - j)))
      (Term.const ax (s.levelParams.map Level.param))
    unifyGoal gl use
    return ← runTac code info st (fld 1)
  if tag == TacTag.ppGoal then
    return ← runTac code info st (apply code (fld 1) (encodeString (← gl.show)))
  if tag == TacTag.ppExpr then
    let t ← zonk lvl (← reify st.handles (fld 1) lvl)
    return ← runTac code info st (apply code (fld 2) (encodeString (← showTermM gl.ctx t)))
  if tag == TacTag.goalType then
    let (r, st) ← refl st gl (quote g lvl gl.ty)
    return ← runTac code info st (apply code (fld 1) r)
  if tag == TacTag.goalExpr then
    let (r, st) ← refl st gl gl.tm (some gl.ty)
    return ← runTac code info st (apply code (fld 1) r)
  if tag == TacTag.goalHyps then
    let mut st := st
    let mut hyps : Array RVal := #[]
    for j in [0:lvl] do
      let (r, st') ← refl st gl (quote g lvl gl.ctx.types[j]!)
      st := st'
      hyps := hyps.push (encodePair (encodeString gl.ctx.names[j]!) r)
    return ← runTac code info st (apply code (fld 1) (encodeList hyps.toList))
  if tag == TacTag.intro then
    let x ← str (fld 1)
    let .pi _ _ _ dom cod _ ← force gl.ty | throwAt info "intro: the goal is not a function type" ErrorCode.tacticFailed
    let ctx' := gl.ctx.bind x dom
    let m ← freshMeta ctx' "goal"
    unifyGoal gl (.lam x m)
    let (st, id) := addGoal st { ctx := ctx', ty := ← instM cod (Val.var lvl), tm := m }
    return ← runTac code info st (apply code (fld 2) (.nat id))
  if tag == TacTag.introFresh then
    let .pi bx _ _ dom cod _ ← force gl.ty | throwAt info "intro: the goal is not a function type" ErrorCode.tacticFailed
    let x := introName gl.ctx.names (← str (fld 1)) bx (isProp g gl.ctx.types.reverse.toArray dom)
      (decodeBool (fld 2) == some true)
    let ctx' := gl.ctx.bind x dom
    let m ← freshMeta ctx' "goal"
    unifyGoal gl (.lam x m)
    let (st, id) := addGoal st { ctx := ctx', ty := ← instM cod (Val.var lvl), tm := m }
    return ← runTac code info st (apply code (fld 3) (encodePair (encodeString x) (.nat id)))
  if tag == TacTag.rename then
    let i ← num (fld 1)
    unless i < lvl do throwAt info "rename: no such hypothesis" ErrorCode.tacticFailed
    -- names are not part of terms: the same hole, in a context that differs in a name
    let (st, id) := addGoal st { gl with ctx := { gl.ctx with names := gl.ctx.names.set i (← str (fld 2)) } }
    return ← runTac code info st (apply code (fld 3) (.nat id))
  if tag == TacTag.change then
    let ty ← evalIn gl.ctx (← reify st.handles (fld 1) lvl)
    try unify lvl gl.ty ty
    catch e => throwAt info s!"change: the new goal is not convertible with the old one ({e.msg})" ErrorCode.tacticFailed
    let m ← freshMeta gl.ctx "goal"
    unifyGoal gl m
    let (st, id) := addGoal st { ctx := gl.ctx, ty, tm := m }
    return ← runTac code info st (apply code (fld 2) (.nat id))
  if tag == TacTag.whnf then
    let t ← zonk lvl (← reify st.handles (fld 1) lvl)
    let (r, st) ← refl st gl (← whnfTerm gl.ctx t) (← typeOf? gl t)
    return ← runTac code info st (apply code (fld 2) r)
  if tag == TacTag.unfold then
    let n ← str (fld 1)
    let t ← zonk lvl (← reify st.handles (fld 2) lvl)
    -- not a definition (a constructor, an axiom, an unknown name): nothing to unfold, the
    -- term comes back unchanged, so a library can try it without catching; the `unfold`
    -- tactic reports the reason (`TacticM.isDefinition`)
    let t' ← match g.find? n with
      | some { value := some _, inline := false, .. } => unfoldIn gl.ctx n t
      | _ => pure t
    let (r, st) ← refl st gl t' (← typeOf? gl t)
    return ← runTac code info st (apply code (fld 3) r)
  if tag == TacTag.rewrite then
    let h ← zonk lvl (← reify st.handles (fld 1) lvl)
    let rtl := decodeBool (fld 2) == some true
    unless h.mvars.isEmpty do throwAt info "rewrite: the equation has holes" ErrorCode.tacticFailed
    -- the universe levels of its constants (fresh after reflection), from the arguments' types
    let h ← if h.hasLevelMVar then do
        let _ ← (RCtx.ofLocal gl.ctx).typeOfUnifying? h
        zonk lvl h
      else pure h
    -- (the variables' types with the holes solved since they were bound, as the kernel
    -- takes a hole as rigid: `U : UnitCounit F G` with `F`'s categories holes then)
    let hty ← match (← get).kernelInfer (gl.kernelCtx g) h with
      | .ok ty => pure ty
      | .error e =>
        match (← get).kernelInfer { gl.kernelCtx g with types := (← zonkedTypes gl.ctx).toList.reverse } h with
        | .ok ty => pure ty
        | .error _ => throwAt info s!"rewrite: {e}" ErrorCode.tacticFailed
    let (A, a, b) ← match ← force hty with
      | .neutral (.eq A a b) #[] => pure (quote g lvl A, quote g lvl a, quote g lvl b)
      | v => throwAt info s!"rewrite: not an equation between two terms: {← showVal gl.ctx v}" ErrorCode.tacticFailed
    let goalT ← zonk lvl (quote g lvl gl.ty)
    -- the side to replace, and its replacement
    let (old, new) := if rtl then (b, a) else (a, b)
    let (body, found) := (abstractOcc old goalT).run false
    unless found do throwAt info s!"rewrite: the goal does not mention {← showTermM gl.ctx old}" ErrorCode.tacticFailed
    let newT := body.instantiateAt 0 new
    -- `P x _ := G[x] = G[a]` (or `G[a] = G[x]`, right to left), transported along `h : a = b`
    let Ga := body.instantiateAt 0 a
    let eqn (x y : Term R) : Term R := if rtl then .eqTy y x else .eqTy x y
    let P : Term R := .lam "x" (.lam "_" (eqn (body.lift 1) (Ga.lift 2)))
    let pf : Term R := .transp A a P (.reflTy Ga) b h
    let m ← freshMeta gl.ctx "goal"
    unifyGoal gl (.cast newT goalT pf m)
    let (st, id) := addGoal st { ctx := gl.ctx, ty := ← evalIn gl.ctx newT, tm := m }
    return ← runTac code info st (apply code (fld 3) (.nat id))
  if tag == TacTag.exact then
    let stx ← stxOf (fld 1)
    let t ← check (gl.ctx.withInfo stx) stx gl.ty
    unifyGoal gl t
    return ← runTac code info st (fld 2)
  if tag == TacTag.elabInfer then
    let (t, ty) ← infer gl.ctx (← stxOf (fld 1))
    let (r₁, st) ← refl st gl t (some ty)
    let (r₂, st) ← refl st gl (quote g lvl ty)
    return ← runTac code info st (apply code (fld 2) (encodePair r₁ r₂))
  if tag == TacTag.assign then
    let t ← zonk lvl (← reify st.handles (fld 1) lvl)
    let mut st := st
    if t.mvars.isEmpty then
      match (← get).kernelInfer (gl.kernelCtx g) t with
      | .ok ty => unifyAt gl.ctx .missing gl.ty ty
      | .error e => throwAt info s!"assign: {e}" ErrorCode.tacticFailed
    else
      -- with holes its type can't be inferred yet: at the end of the block (`elabBy`)
      st := { st with unchecked := st.unchecked.push (gl, t) }
    unifyGoal gl t
    return ← runTac code info st (fld 2)
  if tag == TacTag.assignLate then
    -- (28c) as `assign`, but the term is not inferred by the kernel now: the declaration's
    -- own check (`addDeclSorted`) is its check
    let t ← zonk lvl (← reify st.handles (fld 1) lvl)
    unless t.mvars.isEmpty do throwAt info "assignLate: the term has holes"
    unifyGoal gl t
    return ← runTac code info st (fld 2)
  if tag == TacTag.newGoal then
    let ty ← evalIn gl.ctx (← reify st.handles (fld 1) lvl)
    let m ← freshMeta gl.ctx "goal"
    let (st, id) := addGoal st { ctx := gl.ctx, ty, tm := m }
    return ← runTac code info st (apply code (fld 2) (.nat id))
  if tag == TacTag.normalize then
    let t ← reify st.handles (fld 1) lvl
    let v' ← evalIn gl.ctx t
    let (r, st) ← refl st gl (quote g lvl v') (← typeOf? gl (← zonk lvl t))
    return ← runTac code info st (apply code (fld 2) r)
  if tag == TacTag.instantiate then
    let body ← reify st.handles (fld 1) (lvl + 1)
    let arg ← reify st.handles (fld 2) lvl
    let t := body.instantiateAt 0 arg
    let (r, st) ← refl st gl t (← typeOf? gl (← zonk lvl t))
    return ← runTac code info st (apply code (fld 3) r)
  if tag == TacTag.isDefEq then
    let a ← evalIn gl.ctx (← reify st.handles (fld 1) lvl)
    let b ← evalIn gl.ctx (← reify st.handles (fld 2) lvl)
    let ok ← try unify lvl a b; pure true catch _ => pure false
    return ← runTac code info st (apply code (fld 3) (encodeBool ok))
  if tag == TacTag.inferType then
    let t ← zonk lvl (← reify st.handles (fld 1) lvl)
    unless t.mvars.isEmpty do throwAt info "inferType: the term has holes"
    let ty ← match (← get).kernelInfer (gl.kernelCtx g) t with
      | .ok ty => pure ty
      | .error e => throwAt info s!"inferType: {e}"
    let (r, st) ← refl st gl (quote g lvl ty)
    return ← runTac code info st (apply code (fld 2) r)
  throwAt info s!"tactic: unknown request {tag}"
  --|ex
  --| sorry
  --sol>

/-- `by tac₁; tac₂ …`: a hole of the expected type, filled by running the tactics. -/
partial def elabBy (ctx : LocalCtx R) (stx : Syntax) (expected : VTy R) : ElabM R (Term R) := do
  let s ← get
  let code ← match s.compileCode ("TacticM.run" :: s.tactics.map (·.2)) with
    | .ok c => pure c
    | .error e => throwAt ctx.info e
  let m ← freshMeta ctx "by"
  let mut st : TacState R := { goals := #[{ ctx, ty := expected, tm := m }], «open» := [0] }
  -- each step is `[tactic, [";"?]]`
  let tacs := (stx.getArg 1).args.filterMap fun step => step.args[0]?
  for t in tacs do
    st ← try evalTacticStx code st t
      catch e =>
        -- (for the language server) the block, so the goals before the failing tactic show
        let e := { e with state? := e.state?.map fun s =>
          { s with infos := s.infos.push (.tactic stx.info true #[(ctx, expected)] #[]) } }
        throw (if e.info.stop == 0 then { e with info := (ctx.withInfo t).info } else e)
  let mut rest : Array String := #[]
  for i in st.open do
    if let some gl := st.goals[i]? then
      if ← gl.isOpen then rest := rest.push (← gl.show)
  pushInfo (.tactic stx.info true #[(ctx, expected)] (← openGoals st))
  unless rest.isEmpty do throwAt ctx.info s!"unsolved goals:\n{"\n\n".intercalate rest.toList}" "unsolved-goals"
  -- (13b) the terms `assign` took with holes: now that the holes are solved, their types
  -- are inferred and compared with their goals here, in the elaborator's view (where a
  -- type with a private constructor is opaque), not left to the kernel
  for (gl, t) in st.unchecked do
    let t ← zonk gl.ctx.lvl t
    unless t.mvars.isEmpty do throwAt ctx.info "assign: the assigned term still has holes at the end of the tactic block" ErrorCode.tacticFailed
    -- (the context's types with their holes solved: they may have been holes when the
    -- goal was made, and the kernel takes a hole as rigid)
    let kctx := { gl.kernelCtx (← getGlobals) with types := (← zonkedTypes gl.ctx).toList.reverse }
    match (← get).kernelInfer kctx t with
    | .ok ty => unifyAt gl.ctx stx gl.ty ty
    | .error e => throwAt ctx.info s!"assign: {e}" ErrorCode.tacticFailed
  pure m

end

end Wiz.Elab
