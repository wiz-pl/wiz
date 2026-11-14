import Wiz.Elab.Recursor
import Wiz.Elab.Mark
import Wiz.Compiler.Run
import Wiz.Compiler.Native
import Wiz.Compiler.IRRun
import Wiz.Compiler.Lower
import Wiz.FFI.CParse
import Wiz.FFI.CGlue
import Wiz.Compiler.C
import Wiz.Elab.ProcMacro
import Wiz.Elab.Reflect
import Wiz.Frontend.Parse
import Wiz.Elab.Witness
import Wiz.Elab.Info

/-!
# Elaborating commands

* `def f binders : T := v`: elaborate the binders into a local context, then `T` and
  `v` inside it, abstract over the binders, zonk, and hand the result to the
  **kernel** (`addDecl`). The kernel re-checks everything, including quantities, so
  linearity errors come from there.
* `axiom f binders : T`
* `#check t`: print `t : T` without inserting implicit arguments.
* `#reduce t`: print the normal form of `t`.
* `syntax`, `declare_syntax_cat`: update the parser tables.

There is no recursion: a definition can't mention itself, because its name isn't in
the environment until the kernel has accepted it. Recursion over data arrives in
stage 4, through eliminators.
-/

namespace Wiz

open Elab

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

inductive Severity where
  | info
  | error
  | warning
  deriving BEq, Repr, Inhabited

structure Msg where
  info : SourceInfo
  severity : Severity
  text : String
  /-- a stable name for the kind of error (`unknown-identifier`, …), or `""` -/
  code : String := ""
  deriving Repr, Inhabited

def Msg.render (input : String) (m : Msg) : String :=
  let (l, c) := lineCol input m.info.start
  let sev := match m.severity with | .error => "error" | .warning => "warning" | .info => "info"
  s!"{l + 1}:{c + 1}: {sev}: {m.text}"

/-- The error at an `import` of a module `m` (text `src`) whose own check reported
`errs`. Its own errors are listed once, one per line with their positions in `m`; an
error that is itself about a module `m` imports (code `module-errors`) is passed on as
it is, named through `m`, instead of nested inside another list. So a broken module's
errors appear once in every importer, however deep. -/
def importErrorsText (m : String) (src : String) (errs : Array Msg) : String :=
  let own := errs.filter (·.code != "module-errors")
  let through := errs.filter (·.code == "module-errors")
  let ownTxt := if own.isEmpty then "" else
    s!"module {m} has errors:" ++ String.join (own.toList.map fun e => s!"\n  {m}:{e.render src}")
  let throughTxt := through.toList.map fun e => s!"imported module {m} → {e.text}"
  "\n".intercalate ((if ownTxt.isEmpty then [] else [ownTxt]) ++ throughTxt)

/-- (11s) A declaration, for documentation: what made it (`def`, `inductive`,
`structure`, `class`, `instance`, `axiom`, `coinductive`, `extern`, …, or `constructor`
and `field` for those of a type, `auxiliary` for what the elaborator adds for its own
use), its doc comment (`/-- … -/`, Markdown, delimiters and indentation removed), and,
for a constructor or field, its type. -/
structure DeclDoc where
  kind : String
  doc : Option String := none
  parent : Option Name := none
  /-- where it is declared (its command, constructor or field; an offset in its module):
  a `mutual` block's definitions each have their own -/
  start : Nat := 0
  deriving Inhabited, Repr, BEq

structure CommandState (R : Type) where
  globals : Globals R := {}
  tables : ParserTables := Builtin.tables
  messages : Array Msg := #[]
  /-- coinductive types and their observations (name, recursive?) -/
  coinductives : List (Name × List (Name × Bool)) := []
  /-- library sources by module name (supplied by the caller: the frontend is pure) -/
  loader : Name → Option String := fun _ => none
  imported : List Name := []
  /-- `builtin key := name` registrations -/
  builtins : List (Name × Name) := []
  /-- `attribute [macro k] f` registrations, latest first -/
  procMacros : List (Name × Name) := []
  /-- `attribute [tactic k] f` registrations, latest first -/
  tactics : List (Name × Name) := []
  /-- (HD8) `attribute [macro k] f` for `f : CommandMacro`, and `attribute [deriver C] f`,
  latest first -/
  cmdMacros : List (Name × Name) := []
  derivers : List (Name × Name) := []
  /-- the erased code of every registered macro and tactic, made on first use (a `Thunk`
  remembers its value) and remade when one is registered -/
  metaCode : Thunk (Except String Code) := Thunk.pure (.ok {})
  /-- type classes and instances (stage 7) -/
  classes : List ClassInfo := []
  instances : Array InstanceInfo := #[]
  /-- preprocessed C headers, for `import_c` (the command line runs the preprocessor) -/
  cHeaders : String → Option String := fun _ => none
  /-- the C functions glue code may call: from imported headers, and earlier glue -/
  cFuncs : List (String × List FFI.GTy × FFI.GTy) := []
  /-- (9i) the structs of imported headers, for glue code: fields by spelling -/
  cStructs : List (String × List (String × FFI.GTy)) := []
  /-- C code to emit: header includes and the glue functions -/
  cCode : Array String := #[]
  /-- foreign pointer types and their finalizers -/
  foreignTypes : List (Name × String) := []
  /-- (9f) where the `link_c "f.c"` files are: by module (`""`: the main file) and the path
  as written, the file's absolute path, or `none` if it doesn't exist (the command line
  resolves them, relative to each module's file: the frontend is pure). Without a
  resolver (the language server), paths are kept as written and not checked. -/
  cSources : Option (String → String → Option String) := none
  /-- (9f) the C files to compile and link with the program, and the libraries (`link_lib`) -/
  linkC : Array String := #[]
  linkLibs : Array String := #[]
  /-- for the language server (stage 11): the info tree of this file (identifiers, expected
  types, tactic states, …), and where each global was declared (its command's range, and
  module; `""` is the main file) -/
  infos : Array (Info R) := #[]
  /-- record the expected type of every checked term (the language server turns it on) -/
  termInfo : Bool := false
  declSites : Std.HashMap Name (SourceInfo × String) := {}
  /-- (11s) what each declaration is and its doc comment (`/-- … -/`), for `wiz doc` and
  hovers: filled by the frontend (`runFrontend.step`), replayed by the cache -/
  declDocs : Std.HashMap Name DeclDoc := {}
  /-- the module being elaborated (`""` for the main file) -/
  module : String := ""
  /-- the modules whose `builtin` registrations are trusted: the toolchain's library
  (`lib/`). The main file never is, nor a module from a `-I` directory. -/
  trustedModule : String → Bool := fun _ => false
  /-- (27a) `--trust-native`: `native_refl` may decide a closed equation by running it
  (off by default: it trusts the compiler, see `Native.lean`) -/
  trustNative : Bool := false
  /-- (27a) `--native-fuel N`: the interpreter steps `native_refl` may take -/
  nativeFuel : Nat := NativeRun.defaultFuel
  /-- (28) solvers: `--sat-solver`, `--solver-timeout`, the answer cache -/
  smt : Smt.Config := {}
  /-- macro rules, latest first -/
  macros : List MacroRule := []
  /-- (11q) where each syntax kind and syntax category was declared (the command's range,
  and module), for go to definition on syntax -/
  kindSites : Std.HashMap Name (SourceInfo × String) := {}
  catSites : Std.HashMap Name (SourceInfo × String) := {}
  nextScope : Nat := 1000000
  /-- inside the commands a `mutual` block of inductive types expands to: its family's
  constructors are named by their members (`A.c`, `ctorConst`) -/
  mutualCtors : Bool := false
  /-- (`runFrontend`) the modules already checked in isolation, with their errors
  (`none` while one is being checked: an import cycle) -/
  checked : Std.HashMap Name (Option (Array Msg)) := {}
  /-- no command has been elaborated into this state yet (it is the initial state, up to
  messages and the info tree) -/
  pristine : Bool := true
  /-- (13m) what `local` commands of the module being elaborated added, latest first: node
  kinds and syntax categories, and macro rules and `attribute [macro]` registrations
  (numbered from the oldest). They are dropped when the module's import ends
  (`CommandState.endModule`). -/
  localKinds : List Name := []
  localCats : List Name := []
  localRules : List Nat := []
  localProcs : List Nat := []
  /-- (11w) `local instance`s: their positions in `instances` (numbered from the oldest) -/
  localInsts : List Nat := []

  /-- (11r) unexpanders declared with `app_unexpander c` and `attribute [app_unexpander c] f`,
  latest first, and which of them are `local` (numbered from the oldest) -/
  ppUser : List UnexpanderEntry := []
  localPP : List Nat := []
  /-- (11r) the atoms of `syntax`/`notation` rules as declared, whitespace included, by
  node kind: they decide the spacing of printed notation -/
  rawAtoms : Std.HashMap Name (Array String) := {}

/-- Run a kernel entry on a declaration, with the proof markers the kernel requires
(`Mark`) **when it asks for them**. The marking pass is a typed traversal of the whole
term, about as much work as the kernel's own check, and most declarations need at most a
marker on their body. So the kernel is tried on, in turn:

1. the declaration with a marker on its body, if the body is a proof that is not
   neutral-shaped (`Decl.withTopMarks`: a theorem; any other declaration is left as it is);
2. the declaration marked by the pass (`Decl.withMarks`), only if the kernel answered
   "unmarked proof" to the first.

The error reported is the last attempt's, and the kernel has accepted exactly the term
that is stored. -/
def withMarksOnDemand (g : Globals R) (d : Decl R) (k : Decl R → TCM (Globals R)) : TCM (Globals R) :=
  match k (d.withTopMarks g) with
  | .error (.unmarkedProof t ty l) =>
    let go := fun (_ : Unit) => k (d.withMarks g)
    if g.traceProofSteps then dbgTrace s!"marks-on-demand {d.name}: {(t.take 80).replace "\n" " "} : {(ty.take 60).replace "\n" " "} in Sort {l}" go else go ()
  | r => r

/-- (11s) The doc comment of a declaration, if it has one. -/
def CommandState.docOf? (s : CommandState R) (n : Name) : Option String :=
  (s.declDocs.get? n).bind (·.doc)

/-- "'n' has already been declared", naming the module that declared it if that is not
the one being elaborated (two modules, or a module and the file importing it). -/
def CommandState.alreadyDeclared (s : CommandState R) (n : Name) : String :=
  let whose (m : String) : String := if m.isEmpty then "this file" else s!"module {m}"
  match s.declSites.get? n with
  | some (_, m) => if m == s.module then s!"'{n}' has already been declared" else
    -- (the message of the cache's replay, `Cache.Effect.apply`)
    s!"'{n}' is declared by both {whose m} and {whose s.module}"
  | none => s!"'{n}' has already been declared"

/-- (13b) The types that are opaque in the module being elaborated: declared in another
module with a private constructor, field or observation. Sorted, for stable messages. -/
def foreignOpaques (g : Globals R) : List Name :=
  (g.opaques.toList.filterMap fun (n, m) => if m == g.module then none else some n).mergeSort

/-- (13b) **The strict privacy check** (`wiz --strict-privacy`; off by default, an
experiment). The kernel compares types by shape, so it takes a
look-alike for a type whose constructor is private to another module, and every
comparison the elaborator leaves to it is answered that way (`rfl`, a term assigned by a
tactic while it had holes, the solutions of untyped unification). So when such a type is
visible, the declaration is checked a second time, by the same kernel checker, against
the elaborator's view of the environment (`Globals.elabView`), where those types have no
definition. A declaration that passes used no hidden shape. The first check, against the
real environment, is the one soundness rests on; this one only rejects.

It is off by default because it also rejects legitimate declarations: the elaborator
quotes evaluated values into terms, so a proof that computes through a library operation
on such a type contains a raw pair or projection at it, which has no type with the
definition hidden (`drafts/rust/lowered/03_get_mut.wiz`: `get_mut.is_place`,
`get_mut.spec_under`). With it on, a type with private parts is abstract for proofs too.

On a failure, the types whose shape was used are those that make the check fail when
hidden alone. `kind` chooses the kernel entry (`addDecl`, or `addPartialDecl`). -/
def privacyCheck (g : Globals R) (d : Decl R) (kind : Globals R → Decl R → TCM (Globals R) := addDecl) : TCM Unit := do
  unless g.strictPrivacy do return
  let ops := foreignOpaques g
  if ops.isEmpty then return
  match kind g.elabView d with
  | .ok _ => pure ()
  | .error e =>
    let hide (n : Name) : Globals R := match g.decls[n]? with
      | some t => { g with decls := g.decls.insert n { t with value := none } }
      | none => g
    let used := ops.filter fun n => match kind (hide n) d with
      | .ok _ => false
      | .error _ => true
    let used := if used.isEmpty then ops else used
    let show1 (n : Name) : String := s!"{n} (module {(g.opaques[n]?).getD "?"})"
    throw (.other (s!"{d.name} depends on the definition of {", ".intercalate (used.map show1)}, which is hidden outside " ++
      s!"its module (it has private parts): with the definition hidden, {e}"))

/-- `addDecl` with the sorts of the elaborator's `Π`/`Σ` filled in first (`Sorts`), the
proof markers the kernel requires (`withMarksOnDemand`), and then the privacy check (with
the markers too: an unmarked proof is not a privacy failure). -/
def addDeclSorted (g : Globals R) (d : Decl R) : TCM (Globals R) := do
  -- the kernel's own check is against the full environment: never the elaborator's view,
  -- whose `hidden` definitions (13b) `conv` would consult
  unless g.hidden.isEmpty do throw (.other s!"internal error: {d.name} checked against the elaborator's view")
  let d := d.withSorts g
  let kind := fun (g' : Globals R) (d' : Decl R) => withMarksOnDemand g' d' (addDecl g')
  let g' ← kind g d
  privacyCheck g d kind
  pure g'

/-- Replace each const `n` by `f n`. -/
partial def Term.renameConsts (f : Name → Name) (t : Term R) : Term R :=
  match t with
  | .const n ls => .const (f n) ls
  | t => Id.run (t.mapChildrenM pure fun _ c => pure (c.renameConsts f))

/-- (13b) Give the declarations `added` (just declared, privately, in `s.module`) their
private kernel names (`Globals.privateName`), in the declarations themselves (a recursive
definition mentions itself) and in the `builtin`/`extern` registrations. -/
def renamePrivate (s : CommandState R) (added : Array Name) : CommandState R :=
  if added.isEmpty then s else
  let f (n : Name) : Name := if added.contains n then Globals.privateName s.module n else n
  let rn (t : Term R) := t.renameConsts f
  let g := s.globals
  let decls := added.foldl (fun m n => match m[n]? with
    | some d => (m.erase n).insert (f n) { d with name := f n, type := rn d.type, value := d.value.map rn,
                                                   impl := d.impl.map rn, witness := d.witness.map rn }
    | none => m) g.decls
  let order := g.order.map f
  let heights := Std.HashMap.ofList (order.toList.zipIdx)
  let rb (bs : List (Name × Name)) := bs.map fun (k, n) => (k, f n)
  -- (the instantiation cache follows the renamed values: `Globals.instValue`)
  let instCache := added.foldl (fun c n => match decls[f n]? with
    | some d => { g with instCache := c.erase n }.cacheInst d
    | none => c.erase n) g.instCache
  { s with globals := { g with decls, order, heights, instCache, builtins := rb g.builtins, assumed := rb g.assumed },
           builtins := rb s.builtins }

/-- Metas are untyped, so `?A : Sort ?u` never learns `?u` from `?A := A`, and
`?C : Category.{?a, ?b}` never learns `?a`, `?b` from `?C := C`. For each recorded
constraint (`addSortConstraint`, `addTypeConstraint`) whose hole is now solved, ask the
kernel for the solution's type and unify it with the recorded one. A solved level may
complete another constraint's solution, so this runs until nothing changes. -/
def solveSortConstraints : ElabM R Unit := do
  finishInstances
  -- size metavariables nothing constrained default to `∞`
  let ms := (← get).metas
  for e in ms, m in [0:ms.size] do
    if e.desc == "a size" && e.solution.isNone then
      let sol : Term R := (List.range e.arity).foldl (fun t _ => .lam "_" t) .szInf
      solveMeta m (eval (← getGlobals) [] sol)
  -- the solution's type, if it is complete and the kernel can infer it (in the context of
  -- the hole, with the variables' types as they are now: a binder's type may have been a
  -- hole when it was bound)
  let typeOf (ctx : LocalCtx R) (t : Term R) : ElabM R (Option (VTy R)) := do
    let t ← zonk ctx.lvl t
    if !t.mvars.isEmpty then return none
    let kctx : Ctx R := { globals := ← getGlobals, env := ctx.env, names := ctx.names,
                          qtys := ctx.names.map fun _ => QPoly.const QuantitySyntax.explicitDefault,
                          types := ctx.types, lvl := ctx.lvl, proof := true }
    match Wiz.infer kctx t with
    | .ok (ty, _) => return some ty
    | .error _ =>
      match Wiz.infer { kctx with types := (← zonkedTypes ctx).toList.reverse } t with
      | .ok (ty, _) => return some ty
      | .error _ => return none
  let solvedLevels : ElabM R Nat := do
    return (← get).levelMetas.foldl (fun n l => if l.isSome then n + 1 else n) 0
  let mut doneSort : Std.HashSet Nat := {}
  let mut doneType : Std.HashSet Nat := {}
  repeat
    let before ← solvedLevels
    for (ctx, t, l) in (← get).sortConstraints, i in [0:(← get).sortConstraints.size] do
      if doneSort.contains i then continue
      let some ty ← typeOf ctx t | continue
      doneSort := doneSort.insert i
      if let .sort l' ← force ty then
        try unifyLevel l l' catch e => throwAt ctx.info e.msg
    for (ctx, t, A) in (← get).typeConstraints, i in [0:(← get).typeConstraints.size] do
      if doneType.contains i then continue
      -- (nothing left to learn once the type's levels are known)
      let g ← getGlobals
      unless (← zonk ctx.lvl (quote g ctx.lvl A)).hasLevelMVar do
        doneType := doneType.insert i; continue
      let some ty ← typeOf ctx t | continue
      doneType := doneType.insert i
      -- (a mismatch is the kernel's to report, with the whole declaration)
      let s ← get
      try unify ctx.lvl (← refreshVal ctx A) ty catch _ => set s
    if (← solvedLevels) == before then break
/-- Elaborate the header and body of a `def` or `axiom` to closed, zonked terms. -/
def elabDeclTerms (binders : Array Syntax) (typeStx : Option Syntax) (valStx : Option Syntax)
    (info : SourceInfo) (declName? : Option (Name × SourceInfo × Nat) := none) :
    ElabM R (Term R × Option (Term R)) := do
  let (ctx, tele) ← elabTelescope { info } (binders.flatMap binderViews).toList
  let ty ← match typeStx with
    | some s => pure (← Elab.checkType ctx s).1
    | none => freshMeta ctx "the type of this definition"
  -- (for the language server) the type after the binders, and where ` : T` would go
  if let some (n, ni, at_) := declName? then
    pushInfo (.decl ni n ctx ty typeStx.isSome at_)
    modify fun s => { s with defining := some n }
  -- the type's instance problems that are already determined, solved before the body is
  -- checked: an equation stuck on such a hole then computes when it meets the body's type
  -- (`unifyAt`). (The type isn't zonked here: an equation that stays as written lets
  -- `rfl` be `refl` of its sides.) (7f) Stuck problems get their default instances here:
  -- the type is complete before the body is checked (`theorem t : 1 + 1 = 2 := rfl`).
  synthDefaults
  -- (7e) with the instances solved, the type's instance holes are replaced by their
  -- solutions: the kernel's native arithmetic (`vNatOp`) can't see a solved hole, so
  -- `Nat.land a (b + 5)` with `+`'s instance a hole would unfold `Nat.land`'s unary
  -- definition instead. (Only the instance holes, `zonkInsts`: the other holes stay, so
  -- the equation stays as written, as above.)
  let ty ← if (← get).pendingInsts.isEmpty then zonkInsts ctx.lvl ty else pure ty
  let val ← valStx.mapM fun s => do Elab.check ctx s (← evalIn ctx ty)
  let ty := tele.foldr (fun (x, bi, q, a) b => Term.pi x bi q a b none) ty
  let val := val.map fun v => tele.foldr (fun (x, _, _, _) b => Term.lam x b) v
  solveSortConstraints
  let ty ← zonk 0 ty
  ensureNoMVars ty info
  let val ← val.mapM (zonk 0)
  if let some v := val then ensureNoMVars v info
  pure (ty, val)

/-- Where a type ascription goes in `def f binders := v`: after the last of the name, the
universe parameters and the binders. -/
def declInsertAt (cmd : Syntax) : Nat :=
  [1, 2, 3].foldl (fun acc i => max acc (cmd.getArg i).info.stop) 0

partial def syntaxMentions (n : Name) : Syntax → Bool
  | .ident _ m => m == n
  | .node _ _ as => as.any (syntaxMentions n)
  | _ => false

/-- A recursive definition with a sized first argument, `def f {i : Size} : T^i → … | …`,
compiles to `sfix`. Inside, `f` is a local definition `fun {j : Size< s} y => rec j () y`,
so a recursive call type-checks only on an argument of a smaller size: that is the
termination check. Nested matches give fields of ever smaller sizes, so
course-of-values recursion (`fib (n + 2) = fib n + fib (n + 1)`) works. (Non-indexed
types only, for now.) -/
def elabSizedDef (name : Name) (cmd : Syntax) (ctx : LocalCtx R) (tele : Array (Name × BinderInfo × Term R × Term R))
    (ty : Term R) (si : Lvl) (clauses : List (MClause R)) : ElabM R (Term R × Term R) := do
  let info := cmd.info
  let g ← getGlobals
  let w : R := QuantitySyntax.explicitDefault
  let .pi x0 bi0 q0 A0 B s0 := ty | throwAt info "internal error: sized definition"
  -- the outer `fun x0 =>`
  let vA0 ← evalIn ctx A0
  let .mu l I D idx _ hint ← force vA0 | throwAt info "internal error: sized argument"
  -- (an index type that is only a phantom tail, `phantomTail`, has one value too)
  unless (← force I) matches .unit _ | .pi .. do
    throwAt info "sized recursion is only supported on non-indexed types (for now)"
  let c1 := ctx.bind x0 vA0
  let q (c : LocalCtx R) (v : Val R) : Term R := quote g c.lvl v
  -- P := fun _ x' => B[x0 := x']   (B is under the x0 binder)
  -- (in `c1`: `B` lives under `x0`, which becomes the inner binder; the rest shift by 2)
  let P : Term R := .lam "_" (.lam x0 (B.lift 2 1))
  let vP ← evalIn c1 P
  let some vlev := typeSort? g c1.types.reverse.toArray (← evalIn c1 B)
    | throwAt info "could not determine the universe of the result"
  -- F := fun s rec i x' => let f := …; fun rest => tree
  let fty := sfixFunTy g l I D vP w
  let .pi _ _ _ _ c_s _ ← force fty | throwAt info "internal error"
  let ctxS := c1.bind "s" .size
  let sv := Val.var c1.lvl
  let afterS ← instM c_s sv
  let .pi _ _ _ recTy c_rec _ ← force afterS | throwAt info "internal error"
  let ctxR := ctxS.bind "rec" recTy
  let recV := Val.var ctxS.lvl
  let afterRec ← instM c_rec recV
  let .pi _ _ _ iTy c_i _ ← force afterRec | throwAt info "internal error"
  let ctxI := ctxR.bind "i" iTy
  let iV := Val.var ctxR.lvl
  let afterI ← instM c_i iV
  let .pi _ _ _ xTy c_x _ ← force afterI | throwAt info "internal error"
  -- keep the nominal display (the match compiler finds `T` through it)
  let xTy := match xTy with
    | .mu l' I' D' i' s' _ => Val.mu l' I' D' i' s' hint
    | t => t
  let ctxX := ctxI.bind x0 xTy
  let xLvl := ctxI.lvl
  let goalP ← instM c_x (Val.var xLvl)
  -- the local `f : {j : Size< s} → (y : T^j) → P () y`
  let L := ctxX.lvl
  let sT : Term R := .var (L - c1.lvl - 1)
  let recT : Term R := .var (L - ctxS.lvl - 1)
  -- (the hint sits in `y`'s domain, under `j` only)
  let hintT := hint.map fun (n, us, as) => (n, us, as.map (quote g (L + 1)))
  let fTyTm : Term R := .pi "j" .implicit (.qlit 0) (.sizeLt sT)
    (.pi "y" .default (.qlit w) (.mu l (q ctxX I |>.lift 1) (q ctxX D |>.lift 1) (q ctxX idx |>.lift 1) (.var 0) hintT)
      ((Term.app (Term.app ((P.lift (L - c1.lvl)).lift 2) ((q ctxX idx).lift 2)) (.var 0))) none) none
  -- β-reduce `P () y` (the kernel can't infer the type of an applied lambda)
  let fTyTm := quote g L (← evalIn ctxX fTyTm)
  let fValTm : Term R := .lam "j" (.lam "y" (.app (.app (.app (recT.lift 2) (.var 1)) ((q ctxX idx).lift 2)) (.var 0)))
  let ctxL := ctxX.define name (← evalIn ctxX fTyTm) (← evalIn ctxX fValTm)
  -- introduce the remaining arguments
  let mut ctx' := ctxL
  let mut goal := goalP
  let mut vars : List Lvl := [xLvl]
  let mut names : List Name := []
  let n := (clauses.head?.map (·.pats.length)).getD 1
  for k in [1:n] do
    let .pi x _ xq A Bc _ ← force goal | throwAt info s!"{name} takes fewer than {n} arguments" ErrorCode.wrongArgumentCount
    let x := if x == "_" then s!"a{k}" else x
    vars := vars ++ [ctx'.lvl]
    names := names ++ [x]
    goal ← instM Bc (Val.var ctx'.lvl)
    if ((Val.toPoly? xq).bind (·.isConst?)) == some 0 then
      ctx' := { ctx' with erasedLvls := ctx'.lvl :: ctx'.erasedLvls }
    ctx' := ctx'.bindQ x A ((Val.toPoly? xq).bind (·.isConst?))
  let tree ← compileMatch ctx' vars clauses goal none true
  let body := Term.letE name (.qlit w) fTyTm fValTm (names.foldr .lam tree)
  let F : Term R := .lam "s" (.lam "rec" (.lam "i" (.lam x0 body)))
  let sizeVarT : Term R := .var (c1.lvl - si - 1)
  let sfixT : Term R := .sfix l (q c1 I) (q c1 D) vlev P F sizeVarT (q c1 idx) (.var 0)
  solveSortConstraints
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) (.lam x0 sfixT)
  let fullTy := tele.foldr (fun (x, bi, qq, a) b => Term.pi x bi qq a b none) (Term.pi x0 bi0 q0 A0 B s0)
  let val ← zonk 0 val
  ensureNoMVars val info
  let fullTy ← zonk 0 fullTy  -- (the telescope's holes, solved by now)
  ensureNoMVars fullTy info
  pure (fullTy, val)

/-- Derivation gives up (`fn` and the reason are for debugging). -/
def deriveBail {α : Type} (_fn _why : String) : Option α := none

/-- **The compiled equations of a structurally recursive definition, derived from its
checked value** (docs/Status.md T1; wiz-notes/impl-unchecked.md, "Design"). `val` is
`λ tele cols. [let …] T.rec Δ motive m₁ … mₙ ξ x rs` (`compileMatch` with a recursion
context; `nT` telescope variables, `n` columns, the structural one at `pos`). The result
is the same term with `T.casesOn` for `T.rec` and each method
`m_c = λ fields ihs. body` replaced by `λ fields. body[ih := C]`, where `C` is the direct
call the hypothesis stands for:

* a field `y : T Δ js`: `λ rs. @f tele[ξ := js] (y at pos, rs elsewhere)`;
* an infinitary field `k : (h : H) → T Δ (js h)`: `λ h rs. @f tele[ξ := js h] (k h …)`.

Nothing is elaborated again, so the source can't be read differently. `none` (compiled
code then runs the value) for an index-unification match (mode B: the hypothesis wants the
index equation) and when an index variable occurs in `Δ`, the motive or a method (the
recursor keeps the outer index in every step, a direct call would pass the field's). -/
partial def deriveImpl (g : Globals R) (fn : Name) (us : List Level) (nT n pos : Nat) (val : Term R) :
    Option (Term R) := do
  let (xs, body) ← peel (nT + n) val
  let body' ← go (nT + n) body
  let body' := Push.betaCalls fn body'
  pure (xs.foldr .lam body')
where
  peel : Nat → Term R → Option (List Name × Term R)
    | 0, t => some ([], t)
    | k + 1, .lam x b => do let (xs, r) ← peel k b; pure (x :: xs, r)
    | _, _ => none
  go (L : Nat) : Term R → Option (Term R)
    | .letE x q ty v b => do pure (.letE x q ty v (← go (L + 1) b))
    | t => split L t
  recView (T : Name) (nΔ : Nat) (A : Term R) : Option (Option (Name × Term R) × List (Term R)) :=
    match Term.spine A with
    | (.const m _, args) => if m == T then some (none, args.drop nΔ) else none
    | (.pi h _ _ H Bd _, []) => match Term.spine Bd with
      | (.const m _, args) => if m == T then some (some (h, H), args.drop nΔ) else none
      | _ => none
    | _ => none
  lamN (x : Name) : Nat → (Array (B R) → B R) → B R
    | 0, k => k #[]
    | m + 1, k => B.lam x fun v => lamN x m fun vs => k (#[v] ++ vs)
  split (L : Nat) (t : Term R) : Option (Term R) := do
    let (.const r rus, args) := t.spine | deriveBail fn "not a spine"
    let base (k : Nat) : Name := String.ofList (r.toList.take (r.length - k))
    let (T, cases) ← if r.endsWith ".recN" then some (base 5, base 5 ++ ".casesOnN")
      else if r.endsWith ".rec" then some (base 4, base 4 ++ ".casesOn") else deriveBail fn s!"head {r}"
    let Td ← g.find? T
    let descD ← g.find? (T ++ ".desc")
    let rd ← g.find? r
    let nΔ := (piInfos descD.type).length
    let nΞ := (piInfos Td.type).length - nΔ
    let recBs := piInfos rd.type
    let nc := recBs.length - nΔ - nΞ - 2
    -- mode A: Δ, motive, methods, ξ, x, then the other columns (mode B has the index
    -- equation's proof after `x`)
    let modeB := args.length == recBs.length + n
    unless args.length == recBs.length + (n - 1) || modeB do
      deriveBail fn s!"arity {args.length} {recBs.length} {n}"
    let Δargs := args.take nΔ
    let motive := args[nΔ]!
    let methods := (args.drop (nΔ + 1)).take nc
    let ξ := (args.drop (nΔ + 1 + nc)).take nΞ
    let rest := args.drop (nΔ + 1 + nc + nΞ)
    -- the index variables: telescope variables, by level
    let idxLvls ← if modeB then pure [] else ξ.mapM fun a => match a with
      | .var i => if L - 1 - i < nT then some (L - 1 - i) else deriveBail fn "idx not tele"
      | _ => deriveBail fn "idx not var"
    if idxLvls.any (fun l => (Δargs ++ [motive] ++ methods).any (·.hasVar (L - 1 - l))) then deriveBail fn "idx escapes"
    let ctors := ((recBs.drop (nΔ + 1)).take nc).map fun (m, _, _) => String.ofList (m.toList.drop 2)
    let Δb : List (B R) := Δargs.map fun a => fun d => a.lift (d - L)
    let mut methods' : List (Term R) := []
    for c in ctors, m in methods do
      let cd ← g.find? (ctorConst T c)
      let fields := (peelPis cd.type).1.drop nΔ
      let F := fields.length
      let recs := fields.zipIdx.filterMap fun ((_, _, _, A), fi) => (recView T nΔ A).map (·, fi)
      let k := recs.length
      let (fieldNames, m1) ← peel F m
      let (_, mbody) ← peel k m1
      let fieldB (fi : Nat) : B R := B.bvar (L + fi)
      let call (js : List (B R)) (y : B R) : B R :=
        lamN "r" (n - 1) fun rsB =>
          let teleArgs := (List.range nT).map fun tv => match idxLvls.idxOf? tv with
            | some q => js[q]!
            | none => B.bvar tv
          let colArgs := (List.range n).map fun cI =>
            if cI == pos then y else rsB[if cI < pos then cI else cI - 1]!
          B.app (B.closed (.const fn us)) (teleArgs ++ colArgs)
      -- mode B: the hypothesis takes the index equation first. Where the field's index is
      -- the scrutinee's (`js ≡ ξ`), the direct call fits; otherwise the hypothesis can
      -- only be used with an equation between different indices (a field of another
      -- sort of a mutual family, typically unused): it stays the recursor itself, which
      -- is what the value computes there
      let liftB (t : Term R) : B R := fun d => t.lift (d - L)
      let sameIdx (js : List (B R)) (d : Nat) : Bool :=
        js.length == ξ.length && (js.zip ξ).all fun (j, x) => B.norm g j d == B.norm g (liftB x) d
      let viaRec (js : List (B R)) (y : B R) : B R :=
        B.app (B.closed (.const r rus)) (Δb ++ [liftB motive] ++ methods.map liftB ++ js ++ [y])
      let hyp (js : List (B R)) (y : B R) (d : Nat) : B R :=
        if !modeB then call js y
        else if sameIdx js d then B.lam "e" fun _ => call js y
        -- (under its equation, so that compiled code builds a closure, never runs it:
        -- such a hypothesis is only ever applied to a proof that two different indices
        -- are equal)
        else B.lam "e" fun ev => B.app (viaRec js y) [ev]
      let Cs : List (B R) := recs.map fun ((v, js), fi) =>
        let σ : Array (B R) := (Δb ++ (List.range fi).map fieldB).toArray
        match v with
        | none => hyp (js.map (B.ofTele · σ)) (fieldB fi) (L + F)
        | some (h, _) => B.lam h fun hv => hyp (js.map (B.ofTele · (σ.push hv))) (B.app (fieldB fi) [hv]) (L + F + 1)
      let mut b := mbody
      for j in [0:k] do
        let i := k - 1 - j
        b := b.instantiateAt 0 ((Cs[i]! (L + F)).lift i)
      methods' := methods' ++ [fieldNames.foldr .lam b]
    pure ((Δargs ++ [motive] ++ methods' ++ ξ ++ rest).foldl .app (.const cases rus))

/-- Does the checked value of a structurally recursive definition use an index variable
of its scrutinee's type anywhere but as the recursor's index argument (in the parameters,
the motive or a method: a right-hand side mentions the outer index)? `val` is
`λ tele cols. [let …] T.rec Δ motive m… ξ x …`. Then direct recursion is not what the
recursor computes: the recursor's hypothesis keeps the outer index in every step, while a
direct call `f xs` passes the field's index (it is an implicit argument, inferred from
`xs`). `def g {n} : V n → Nat | .cons _ xs => n + g xs` computes `3 + 3 + 3` by its value
and `3 + 2 + 1` by such an implementation. The definition then gets no implementation
(compiled code runs the value). -/
def indexEscapes (g : Globals R) (val : Term R) : Bool :=
  let rec body : Term R → Term R
    | .lam _ b => body b
    | .letE _ _ _ _ b => body b
    | t => t
  match (body val).spine with
  | (.const r _, args) =>
    let base (k : Nat) : Name := String.ofList (r.toList.take (r.length - k))
    let T := if r.endsWith ".recN" then some (base 5) else if r.endsWith ".rec" then some (base 4) else none
    match T.bind fun T => (g.find? T).bind fun Td => (g.find? (T ++ ".desc")).bind fun descD =>
        (g.find? r).map fun rd => (Td, descD, rd) with
    | some (Td, descD, rd) =>
      let nΔ := (piInfos descD.type).length
      let nΞ := (piInfos Td.type).length - nΔ
      -- Δ, the motive and the methods come before the indices
      let nBefore := (piInfos rd.type).length - nΞ - 1
      let before := args.take nBefore
      let idxVars := (args.drop nBefore).take nΞ |>.filterMap fun a => match a with
        | .var i => some i
        | _ => none
      idxVars.any fun i => before.any (·.hasVar i)
    | none => false
  | _ => false

/-- `def f binders : T | p… => rhs …`: the alternatives match the leading explicit
arguments of `T`; a right-hand side that calls `f` makes it structurally recursive. -/
def elabDefEqns (name : Name) (cmd : Syntax) (isPartial : Bool := false) :
    ElabM R (Term R × Term R × Option (Term R)) := do
  let info := cmd.info
  let (ctx, tele) ← elabTelescope { info } (((cmd.getArg 3).args.flatMap binderViews)).toList
  let tyStx := (cmd.getArg 4).getArg 1
  let (ty, _) ← Elab.checkType ctx tyStx
  finishInstances
  let ty ← zonk ctx.lvl ty
  ensureNoMVars ty info
  let alts := (cmd.getArg 5).args
  let clauses : List (MClause R) ← alts.toList.mapM fun a => do
    pure { pats := ← ((a.getArg 1).args.filter (!· matches .atom ..)).toList.mapM expandPattern, rhs := a.getArg 3 }
  let n := (clauses.head?.map (·.pats.length)).getD 0
  -- introduce `n` arguments of the type
  let mut ctx' := ctx
  let mut tyv ← evalIn ctx ty
  let mut vars : List Lvl := []
  let mut names : List Name := []
  let mut colExplicit : List Bool := []
  for i in [0:n] do
    let .pi x bi xq A B _ ← force tyv | throwAt tyStx.info s!"{name} takes fewer than {n} arguments" ErrorCode.wrongArgumentCount
    colExplicit := colExplicit ++ [bi == .default]
    let x := if x == "_" then s!"a{i}" else x
    vars := vars ++ [ctx'.lvl]
    names := names ++ [x]
    tyv ← instM B (Val.var ctx'.lvl)
    if ((Val.toPoly? xq).bind (·.isConst?)) == some 0 then
      ctx' := { ctx' with erasedLvls := ctx'.lvl :: ctx'.erasedLvls }
    ctx' := ctx'.bindQ x A ((Val.toPoly? xq).bind (·.isConst?))
  let mentions (stx : Syntax) : Bool := syntaxMentions name stx
  -- (a partial definition calls itself as a declared constant instead)
  let recursive := !isPartial && clauses.any (fun c => mentions c.rhs)
  -- structural recursion is on the first argument the first clause matches: put its
  -- column first (the others follow in order, as the hypotheses take them)
  let g ← getGlobals
  let pos : Nat := if !recursive then 0 else
    match clauses.head? with
    | some c => (c.pats.findIdx? (patIsCtor g)).getD 0
    | none => 0
  let perm {α : Type} (xs : List α) : List α :=
    match xs.drop pos with
    | x :: rest => if pos == 0 then xs else x :: (xs.take pos ++ rest)
    | [] => xs
  let params := (tele.filterMap fun (x, bi, _, _) => if bi == .default then some x else none).toList
  let allParams := (tele.map fun (x, bi, _, _) => (x, bi == .default)).toList
  let rc : Option RecCtx := if recursive then some { fn := name, params, pos, cols := n, allParams, colExplicit } else none
  if let some x := vars.head? then recordMatch cmd.info alts clauses ctx'.types[ctx'.lvl - x - 1]! ctx'.types.reverse.toArray
  -- a recursive definition whose first argument has a size-variable size: compile to `sfix`
  if rc.isSome && pos == 0 then
    if let some x0 := vars.head? then
      if let .mu _ _ _ _ (.neutral (.local si) #[]) _ ← force ctx'.types[ctx'.lvl - x0 - 1]! then
        if si < ctx.lvl then
          let (t, v) ← elabSizedDef name cmd ctx tele ty si clauses
          return (t, v, none)
  let clauses := clauses.map fun c => { c with pats := perm c.pats }
  let body ← compileMatch ctx' (perm vars) clauses tyv rc true
  solveSortConstraints
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) (names.foldr .lam body)
  let fullTy := tele.foldr (fun (x, bi, q, a) b => Term.pi x bi q a b none) ty
  let val ← zonk 0 val
  ensureNoMVars val info
  let fullTy ← zonk 0 fullTy  -- (the telescope's holes, solved by now)
  ensureNoMVars fullTy info
  -- for the compiler: the value with each hypothesis replaced by the direct call it stands
  -- for (`deriveImpl`), so that only the recursive calls the program makes are computed;
  -- the kernel checks that it agrees with the value (`checkImplAgrees`). None when an
  -- index variable escapes into a method (`indexEscapes`): compiled code runs the value
  let g ← getGlobals
  let us := (← get).levelParams.map Level.param
  let impl := if rc.isNone || indexEscapes g val then none
    else deriveImpl g name us tele.size names.length pos val
  pure (fullTy, val, impl)

/-- Does the identifier `n` occur anywhere in `stx`? -/
partial def mentionsIdent (n : Name) (stx : Syntax) : Bool :=
  (stx.isOfKind "term.ident" && (stx.getArg 0).getId? == some n) || stx.args.any (mentionsIdent n)

/-- The names a `fun`'s binders bind, and its body under any nested `fun`s; `none` for an
implicit or instance binder. -/
partial def peelFunBinders (t : Syntax) (acc : Array Name := #[]) : Option (Array Name × Syntax) :=
  if t.isOfKind "term.fun" then do
    let mut acc := acc
    for b in (t.getArg 1).args do
      match b with
      | .ident _ n => acc := acc.push n
      | _ =>
        if b.isOfKind "term.hole" then acc := acc.push "_"
        else if b.isOfKind "binder.explicit" then
          for n in (b.getArg 2).args do
            acc := acc.push (match n with | .ident _ m => m | _ => "_")
        else none
    peelFunBinders (t.getArg 3) acc
  else some (acc, t)

/-- A recursive `def f bs : T := fun ys => match x₁, …, xₖ with | p… => rhs …` whose
scrutinees are parameters (of `bs` or `ys`), as the equations it means:
`def f bs₀ : (bs₁) → T | q… => rhs …`, where `bs₁` are the parameters from the first
scrutinee on (moved into the type; explicit, with a type) and the columns `q` are the
alternative's pattern for a scrutinee (`x@p` if the right-hand side mentions `x`) and the
variable itself for any other parameter. A plain `def` can't call itself (it is no
global yet); its equations are structurally recursive. `none` if the body has another
shape: it is then elaborated as it is. -/
def defMatchAsEqns? (name : Name) (cmd : Syntax) : Option Syntax := do
  let val := cmd.getArg 6
  guard (syntaxMentions name val)
  let tyStx ← (cmd.getArg 4).args[1]?
  -- the def's binders, one per name: (name, the binder for it alone, explicit with a type)
  let mut items : Array (Name × Option Syntax × Bool) := #[]
  for b in (cmd.getArg 3).args do
    if b.isOfKind "binder.explicit" || b.isOfKind "binder.implicit" then
      for n in (b.getArg 2).args do
        let single : Syntax := .node b.info b.kind #[b.getArg 0, b.getArg 1, .node {} "null" #[n], b.getArg 3, b.getArg 4]
        let nm := match n with | .ident _ m => m | _ => "_"
        items := items.push (nm, some single, b.isOfKind "binder.explicit" && (b.getArg 3).args.size > 0)
    else items := items.push ("inst✝", some b, false)
  let (funNames, body) ← peelFunBinders val
  guard (body.isOfKind "term.match")
  let nDef := items.size
  for n in funNames do items := items.push (n, none, true)
  let scruts := (body.getArg 1).args.filter (!· matches .atom ..)
  let scrutNames ← scruts.toList.mapM fun t =>
    if t.isOfKind "term.ident" then (t.getArg 0).getId? else none
  guard (scrutNames.eraseDups.length == scrutNames.length)
  -- each scrutinee is exactly one parameter (not `_`, not shadowed)
  for x in scrutNames do
    guard (x != "_" && (items.filter (·.1 == x)).size == 1)
  let i0 ← items.findIdx? fun (n, _, _) => scrutNames.contains n
  let moved := items.extract i0 items.size
  guard (moved.all (·.2.2))
  let info := cmd.info
  let ident (n : Name) : Syntax := .node {} "term.ident" #[.ident {} n]
  let hole : Syntax := .node {} "term.hole" #[.atom {} "_"]
  -- the type: the moved binders of the def, then `T`
  let movedDef := (items.extract i0 nDef).toList
  let ty := movedDef.foldr (fun (_, b, _) acc => match b with
    | some b => Syntax.node info "term.depArrow" #[b, .atom {} "→", acc]
    | none => acc) tyStx
  let kept := (items.extract 0 (min i0 nDef)).filterMap (·.2.1)
  let alts ← (body.getArg 3).args.mapM fun a => do
    guard (a.isOfKind "match.alt")
    let ps := (a.getArg 1).args.filter (!· matches .atom ..)
    guard (ps.size == scrutNames.length)
    let rhs := a.getArg 3
    let cols := moved.toList.map fun (n, _, _) =>
      match scrutNames.idxOf? n with
      | some k =>
        let p := ps[k]!
        let simple := p.isOfKind "term.ident" && (p.getArg 0).getId? == some n
        if !simple && mentionsIdent n rhs then
          Syntax.node p.info "term.asPat" #[ident n, .atom {} "@", p]
        else p
      | none => if n == "_" then hole else ident n
    let sep := (cols.flatMap fun c => [Syntax.atom {} ",", c]).drop 1
    pure (Syntax.node a.info "match.alt" #[a.getArg 0, .node {} "null" sep.toArray, a.getArg 2, rhs])
  pure (.node info "command.defEqns" #[cmd.getArg 0, cmd.getArg 1, cmd.getArg 2, .node {} "null" kept,
    .node {} "null" #[.atom {} ":", ty], .node {} "null" alts])

/-- How the fields of the coinductive type `T` sit in its payload (Q4: a small field is
lifted, `descFieldLifts`), read off `T.desc`. -/
def coinductiveLifts (g : Globals R) (T : Name) : List FieldLift :=
  match g.find? (T ++ ".desc") with
  | some { value := some v, type, .. } =>
    let rec strip : Nat → Term R → Term R
      | n + 1, .lam _ b => strip n b
      | _, t => t
    descFieldLifts (strip (peelPis type).1.length v)
  | _ => []

/-- The copattern alternative for observation `o`, if any. -/
def copatternAlt? (alts : List Syntax) (o : Name) : Option Syntax :=
  alts.find? fun a =>
    match (a.getArg 1).args[0]? with
    | some p => p.isOfKind "term.dotIdent" && (p.getArg 1).getId? == some o
    | none => false

/-- Is `rhs` a corecursive call `f e…` (or a bare `f`)? -/
def isCorecCall (name : Name) (rhs : Syntax) : Bool :=
  let h := if rhs.isOfKind "term.app" then rhs.getArg 0 else rhs
  h.isOfKind "term.ident" && (h.getArg 0).getId? == some name

/-- The corecursive case of `elabCopatterns`: `coit`. -/
def elabCopatternsCoit (name : Name) (cmd : Syntax) (obs : List (Name × Bool)) : ElabM R (Term R × Term R) := do
  let info := cmd.info
  let g ← getGlobals
  let (ctx, tele) ← elabTelescope { info } (((cmd.getArg 3).args.flatMap binderViews)).toList
  let tyStx := (cmd.getArg 4).getArg 1
  let (ty, _) ← Elab.checkType ctx tyStx
  finishInstances
  let ty ← zonk ctx.lvl ty
  ensureNoMVars ty info
  let .nu l I D i _ (some (T, us, args)) ← force (← evalIn ctx ty)
    | throwAt tyStx.info "copatterns need a coinductive result type"
  let q (lvl : Lvl) (v : Val R) : Term R := quote g lvl v
  -- the state: the explicit binders
  let explicit := (tele.toList.zipIdx.filter fun ((_, bi, _, _), _) => bi == .default)
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  let stateTy : Term R := explicit.zipIdx.foldr (fun (((x, _, _, _), k), j) acc =>
    .sigma x w ((q ctx.lvl ctx.types[ctx.lvl - k - 1]!).lift j) acc none) (.unit (.succ l))
  let vS ← evalIn ctx stateTy
  -- the step function's context: i, s, then the explicit binders re-bound from s
  let mut sctx := (ctx.bind "i" I).bind "s" vS
  let sLvl := ctx.lvl + 1
  let mut sv : Val R := Val.var sLvl
  for ((x, _, _, _), k) in explicit do
    sctx := sctx.define x ctx.types[ctx.lvl - k - 1]! (vFst sv)
    sv := vSnd sv
  -- one component per observation, in order
  let alts := (cmd.getArg 5).args.toList
  let lifts := coinductiveLifts g T
  let mut comps : List (Term R) := []
  for (o, isRec) in obs, k in [0:obs.length] do
    let some alt := alts.find? fun a =>
        match (a.getArg 1).args[0]? with
        | some p => p.isOfKind "term.dotIdent" && (p.getArg 1).getId? == some o
        | none => false
      | throwAt info s!"missing copattern .{o}" ErrorCode.missingCopattern
    let rhs := alt.getArg 3
    if isRec then
      -- `f e…`: the next state
      let (h, es) := if rhs.isOfKind "term.app" then (rhs.getArg 0, (rhs.getArg 1).args.toList) else (rhs, [])
      unless h.isOfKind "term.ident" && (h.getArg 0).getId? == some name do
        throwAt rhs.info s!"the observation .{o} must be a corecursive call of {name} (guardedness)"
      unless es.length == explicit.length do
        throwAt rhs.info s!"{name} takes {plural explicit.length "explicit argument"}, but is given {es.length}" ErrorCode.wrongArgumentCount
      let mut es' : List (Term R) := []
      for e in es, ((_, _, _, _), k) in explicit do
        es' := es' ++ [← Elab.check sctx e ctx.types[ctx.lvl - k - 1]!]
      comps := comps ++ [es'.foldr .pair .tt]
    else
      let some od := g.find? (T ++ "." ++ o) | throwAt info s!"unknown observation {o}"
      -- the observation's type at our parameters: {Δ} → T Δ → F
      let mut oty : VTy R := eval g [] (od.type.instLevels od.levelParams us)
      for a in args do
        let .pi _ _ _ _ cod _ ← force oty | throwAt info "internal error: observation type"
        oty ← instM cod a
      let .pi _ _ _ _ cod _ ← force oty | throwAt info "internal error: observation type"
      let F ← instM cod (Val.var 0)
      comps := comps ++ [(lifts[k]?.getD .none).wrap (← Elab.check sctx rhs F)]
  -- the index equation: `()` at `Unit`; for a phantom tail (`phantomTail`), `refl`
  let e : Term R ← match ← force I with
    | .unit _ => pure .tt
    | _ => pure (.refl (q sctx.lvl I) (q sctx.lvl i))
  let payload : Term R := comps.foldr .pair (.pair e .tt)
  -- wrap the lets for the re-bound binders
  let mut stepBody := payload
  let mut lvl := sctx.lvl
  for ((x, _, _, _), _) in explicit.reverse do
    lvl := lvl - 1
    stepBody := .letE x w (q lvl sctx.types[sctx.lvl - lvl - 1]!) (q lvl (vFst (Val.var 0))) stepBody
  -- recompute the let values properly (projections of s), innermost last
  let mut body := payload
  let mut j := explicit.length
  for ((x, _, _, _), k) in explicit.reverse do
    j := j - 1
    let lv := sLvl + 1 + j
    let proj : Term R := .fst ((List.range j).foldl (fun t _ => .snd t) (.var (lv - sLvl - 1)))
    body := .letE x w (q lv ctx.types[ctx.lvl - k - 1]!) proj body
  let _ := stepBody
  let step : Term R := .lam "i" (.lam "s" body)
  let Sfun : Term R := .lam "_" (stateTy.lift 1)
  let init : Term R := (explicit.map fun ((_, _, _, _), k) => (.var (ctx.lvl - k - 1) : Term R)).foldr .pair .tt
  let coit : Term R := .coit l (q ctx.lvl I) (q ctx.lvl D) Sfun step (q ctx.lvl i) init
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) coit
  let fullTy := tele.foldr (fun (x, bi, qq, a) b => Term.pi x bi qq a b none) ty
  -- (7e) the right-hand sides' instance problems (`nats (n + 1)`)
  finishInstances
  let val ← zonk 0 val
  ensureNoMVars val info
  let fullTy ← zonk 0 fullTy  -- (the telescope's holes, solved by now)
  ensureNoMVars fullTy info
  pure (fullTy, val)

/-- **Exercise 4.24.** The non-corecursive case of `elabCopatterns`: `cocon` of the
observations, so `register a s | .head => a | .tail => s` is one cell in front of `s`.

The result type is `ν^sz D i`; its payload is `⟦D⟧ (ν^{s'}) i` for `sz = ↑s'` (or `∞`).
Walk that Σ type: check each observation's right-hand side against the component (a
recursive observation against the nominal type one size down, so its hint survives),
and instantiate the rest with the value. Reject a right-hand side that mentions the
definition itself (guardedness). The payload ends in `((), ())`. -/
def elabCopatternsCocon (name : Name) (cmd : Syntax) (obs : List (Name × Bool)) : ElabM R (Term R × Term R) := do
  let info := cmd.info
  let g ← getGlobals
  let (ctx, tele) ← elabTelescope { info } (((cmd.getArg 3).args.flatMap binderViews)).toList
  let tyStx := (cmd.getArg 4).getArg 1
  let (ty, _) ← Elab.checkType ctx tyStx
  finishInstances
  let ty ← zonk ctx.lvl ty
  ensureNoMVars ty info
  let .nu l I D i sz hint ← force (← evalIn ctx ty)
    | throwAt tyStx.info "copatterns need a coinductive result type"
  let some s' := sizePred? sz
    | throwAt tyStx.info s!"a copattern definition builds a value of size ↑s or ∞, not {← showVal ctx sz}"
  --<sol
  let alts := (cmd.getArg 5).args.toList
  -- walk the payload's Σ type, one component per observation
  let mut pty : VTy R := vInterp g l I D (nuFamilyAt l I D s') i
  let mut comps : List (Term R) := []
  for (o, isRec) in obs do
    let some alt := copatternAlt? alts o | throwAt info s!"missing copattern .{o}" ErrorCode.missingCopattern
    let rhs := alt.getArg 3
    if mentionsIdent name rhs then
      throwAt rhs.info s!"the observation .{o} must be a corecursive call of {name} (guardedness)"
    let .sigma _ _ A B _ ← force pty | throwAt info "internal error: observation type"
    -- a recursive observation: the same nominal type, one size down
    let A := if isRec then .nu l I D i s' hint else A
    -- (Q4) a lifted field (`ULift A'`, made by the elaborator): check against the
    -- field's own type, and box it
    let (A, lifted) ← match isRec, ← force A with
      | false, .ulift _ A' => pure (A', true)
      | _, _ => pure (A, false)
    let c ← Elab.check ctx rhs A
    let c := if lifted then .up c else c
    comps := comps ++ [c]
    pty ← instM B (← evalIn ctx c)
  -- the index equation: `()` at `Unit`; for a phantom tail (`phantomTail`), `refl`
  let e : Term R ← match ← force I with
    | .unit _ => pure .tt
    | _ => pure (.refl (quote g ctx.lvl I) (quote g ctx.lvl i))
  let payload : Term R := comps.foldr .pair (.pair e .tt)
  let val := tele.foldr (fun (x, _, _, _) b => Term.lam x b) (Term.cocon payload)
  let fullTy := tele.foldr (fun (x, bi, qq, a) b => Term.pi x bi qq a b none) ty
  -- (7e) the right-hand sides' instance problems (`nats (n + 1)`)
  finishInstances
  let val ← zonk 0 val
  ensureNoMVars val info
  let fullTy ← zonk 0 fullTy  -- (the telescope's holes, solved by now)
  ensureNoMVars fullTy info
  pure (fullTy, val)
  --|ex
  --| sorry
  --sol>

/-- Copatterns: `def f binders : T args | .obs => rhs …` for a coinductive `T`
compiles to `coit`. The state is the tuple of the explicit binders; a recursive
observation must be a corecursive call `f e…` (that is the guardedness condition),
whose arguments become the next state.

When no observation is corecursive (`register a s | .head => a | .tail => s`), the
definition is not recursive at all: it compiles to `cocon` of the observations, one
cell in front of the given streams, and `f` may not occur on any right-hand side. -/
def elabCopatterns (name : Name) (cmd : Syntax) (obs : List (Name × Bool)) : ElabM R (Term R × Term R) := do
  let alts := (cmd.getArg 5).args.toList
  for (o, _) in obs do
    if (copatternAlt? alts o).isNone then throwAt cmd.info s!"missing copattern .{o}" ErrorCode.missingCopattern
  let corecursive := obs.any fun (o, isRec) =>
    isRec && ((copatternAlt? alts o).map fun a => isCorecCall name (a.getArg 3)).getD false
  if corecursive then elabCopatternsCoit name cmd obs else elabCopatternsCocon name cmd obs

/-- `runElabH`, with (28) the solver settings and the definition's name, and the axioms
that tactics added on success (`ElabState.sideDecls`; the trusted `smt` of 28a will). -/
def runElabS (g : Globals R) (x : ElabM R α) (levelParams : List Name := [])
    (macros : List MacroRule := []) (builtins : List (Name × Name) := [])
    (procMacros : List (Name × Name) := []) (tactics : List (Name × Name) := [])
    (metaCode : Thunk (Except String Code) := Thunk.pure (.ok {}))
    (classes : List ClassInfo := []) (instances : Array InstanceInfo := #[]) (termInfo : Bool := false)
    (smt : Smt.Config := {}) (smtDecl : Name := "") :
    Except (ElabError R) (α × Array (Decl R)) × Array (Info R) :=
  -- macros and tactics run against the globals as they are when this command starts
  let compileCode (roots : List Name) := match metaCode.get with
    | .ok c => if roots.all c.contains then .ok c
      else (compileReachable g builtins roots (externImpls := false)).mapError (s!"cannot compile the environment: {·}")
    | .error e => .error e
  let runProcMacro f stx scope := match compileCode [f, "Macro.run"] with
    | .ok code => Elab.runProcMacro code f stx scope (macroEnv g)
    | .error e => (#[], .error e)
  -- (the elaborator's terms carry no proof markers yet: `proof`)
  let kernelInfer (ctx : Ctx R) (t : Term R) := (Wiz.infer { ctx with proof := true } t).map (·.1) |>.mapError toString
  -- (13b) structures with a constructor private to another module don't unfold here
  match x.run { globals := g.elabView, levelParams, macros, builtins, procMacros, runProcMacro, tactics, compileCode,
                kernelInfer, classes, instances, termInfo, smt, smtDecl } with
  | .ok (a, st) => (.ok (a, st.sideDecls), finishInfos st)
  | .error e => (.error e, (e.state?.map finishInfos).getD #[])

/-- Run the elaborator; also returns the info tree it recorded (even after an error). -/
def runElabH (g : Globals R) (x : ElabM R α) (levelParams : List Name := [])
    (macros : List MacroRule := []) (builtins : List (Name × Name) := [])
    (procMacros : List (Name × Name) := []) (tactics : List (Name × Name) := [])
    (metaCode : Thunk (Except String Code) := Thunk.pure (.ok {}))
    (classes : List ClassInfo := []) (instances : Array InstanceInfo := #[]) (termInfo : Bool := false) :
    Except (ElabError R) α × Array (Info R) :=
  -- (one body: `runElabS` without solver settings, so no tactic adds a declaration)
  match runElabS g x levelParams macros builtins procMacros tactics metaCode classes instances termInfo with
  | (.ok (a, _), infos) => (.ok a, infos)
  | (.error e, infos) => (.error e, infos)

def runElab (g : Globals R) (x : ElabM R α) (levelParams : List Name := [])
    (macros : List MacroRule := []) (builtins : List (Name × Name) := [])
    (procMacros : List (Name × Name) := []) (tactics : List (Name × Name) := [])
    (metaCode : Thunk (Except String Code) := Thunk.pure (.ok {}))
    (classes : List ClassInfo := []) (instances : Array InstanceInfo := #[]) : Except (ElabError R) α :=
  (runElabH g x levelParams macros builtins procMacros tactics metaCode classes instances).1

/-- The erased code of the registered macros and tactics (and what they reach), on demand. -/
def mkMetaCode (g : Globals R) (builtins procMacros tactics : List (Name × Name)) (more : List Name := []) :
    Thunk (Except String Code) :=
  Thunk.mk fun _ =>
    let roots := "TacticM.run" :: "Macro.run" :: (procMacros ++ tactics).map (·.2) ++ more
    (compileReachable g builtins roots (externImpls := false)).mapError (s!"cannot compile the macros and tactics: {·}")

/-- The method functions of a class `C` (from its structure declaration):
`C.f : {Δ} → [self : C Δ] → F`, the field `f` of `self`, where earlier fields in `F`
become projections of `self`. With `selfBi := .default`, the projection functions of a
structure `S`: `S.f : {Δ} → (self : S Δ) → F` (`Signal.map BitVec.toNat s`). Erased
fields get none. -/
def classMethods (sDecl : Decl R) (levelParams : List Name)
    (selfBi : BinderInfo := .instImplicit) : List (Decl R) := Id.run do
  let C := sDecl.name
  let us := levelParams.map Level.param
  let (Δ, _) := peelPis sDecl.type
  let nΔ := Δ.length
  let rec stripLams : Nat → Term R → Term R
    | 0, t => t
    | n + 1, .lam _ b => stripLams n b
    | _, t => t
  let rec fieldsOf : Term R → List (Name × Term R × Term R)
    | .sigma x q A rest _ => (x, q, A) :: fieldsOf rest
    | _ => []
  let fields := fieldsOf (stripLams nΔ (sDecl.value.getD .tt))
  let proj (i : Nat) (t : Term R) : Term R := .fst ((List.range i).foldl (fun t _ => .snd t) t)
  let implicitΔ := Δ.map fun (x, _, _, A) => (x, BinderInfo.implicit, (.qlit 0 : Term R), A)
  let Capp : Term R := ((List.range nΔ).map fun j => Term.var (nΔ - 1 - j)).foldl .app (.const C us)
  let w : Term R := .qlit QuantitySyntax.explicitDefault
  let mut out := []
  for (x, q, A) in fields, k in [0:fields.length] do
    if q == .qlit 0 then continue
    -- `A` lives under the earlier fields: insert `self` below them, then replace them
    let mut A' := A.lift 1 k
    for i in (List.range k).reverse do
      A' := A'.instantiateAt 0 (proj i (.var i))
    let type := implicitΔ.foldr (fun (y, bi, q, B) acc => .pi y bi q B acc none) (.pi "self" selfBi w Capp A' none)
    let value := Δ.foldr (fun (y, _, _, _) acc => .lam y acc) (.lam "self" (proj k (.var 0)))
    let d : Decl R := { name := C ++ "." ++ x, levelParams, type, value := some value }
    out := out ++ [d]
  pure out

/-- `notation` and `infixl`/`infixr`/`infix`: register a syntax rule and a macro rule.
Returns the new tables and the macro rule. -/
def notationRule (tables : ParserTables) (cmd : Syntax) :
    Except String (ParserTables × MacroRule) := do
  let antiquot (v : Name) : Syntax := .node {} "antiquot" #[.atom {} "$", .ident {} v]
  -- items: `.inl op` for an atom, `.inr (name, prec?)` for an argument
  let (prec, items, rhs) ← if cmd.isOfKind "command.infix" then do
      let kw := match cmd.getArg 0 with
        | .atom _ v => v
        | _ => "infix"
      let p := ((cmd.getArg 2).getNat?).getD 0
      let some op := (cmd.getArg 3).getStr? | throw "infix needs an operator string"
      let (lp, rp) := if kw == "infixl" then (p, p + 1) else if kw == "infixr" then (p + 1, p) else (p + 1, p + 1)
      let f := cmd.getArg 5
      let rhs : Syntax := .node {} "term.app" #[f, .node {} "null"
        #[.node {} "term.ident" #[.ident {} "a"], .node {} "term.ident" #[.ident {} "b"]]]
      pure (p, [Sum.inr ("a", some lp), Sum.inl op, Sum.inr ("b", some rp)], rhs)
    else do
      let precOpt := cmd.getArg 1
      let p ← if precOpt.isNone then pure maxPrec else precValue (precOpt.getArg 1)
      let items ← (cmd.getArg 2).args.toList.mapM fun it => do
        let x := it.getArg 0
        match x.getStr? with
        | some s => pure (Sum.inl s)
        | none =>
          let v := (x.getId?).getD "_"
          let po := it.getArg 1
          if po.isNone then pure (Sum.inr (v, none))
          else pure (Sum.inr (v, some (← precValue (po.getArg 1))))
      pure (p, items, cmd.getArg 4)
  let descr (it : String ⊕ (Name × Option Nat)) : ParserDescr := match it with
    | .inl s => .atom s.trimAscii.toString
    | .inr (_, p?) => .cat "term" (p?.getD 0)
  let pat (it : String ⊕ (Name × Option Nat)) : Syntax := match it with
    | .inl s => .atom {} s.trimAscii.toString
    | .inr (v, _) => antiquot v
  let vars := items.filterMap fun | .inr (v, _) => some v | _ => none
  match items with
  | .inr (_, lp?) :: rest =>
    let ps := rest.map descr
    let p := if h : ps.length = 1 then ps[0] else .seq ps.toArray
    let kind := mkKindName tables "term" p
    let tables := tables.addTrailing "term" { kind, prec, lhsPrec := lp?.getD prec, p }
    pure (tables, { kind, pattern := .node {} kind (items.map pat).toArray, template := rhs, vars, site := cmd.info })
  | _ =>
    let ps := items.map descr
    let p := if h : ps.length = 1 then ps[0] else .seq ps.toArray
    let kind := mkKindName tables "term" p
    let tables := tables.addLeading "term" { kind, prec, p }
    pure (tables, { kind, pattern := .node {} kind (items.map pat).toArray, template := rhs, vars, site := cmd.info })

/-- Is a `builtin key := d` registration well formed? Numerals and the native operations
need the shapes they assume: `nat` a type, `nat.zero : N`, `nat.succ : N → N`, the
operations `N → N → N` (or `N → N → B` for the comparisons), each a definition (when an
argument isn't a literal, the definition computes). Otherwise the kernel's numerals
would be ill-typed or stuck (`builtin nat := E` for an empty `E` crashed the checker). -/
def builtinShapeError (g : Globals R) (key : Name) (d : Decl R) : Option String :=
  let rec doms : Term R → List (Term R) × Term R
    | .pi _ _ _ a b _ => let (as, r) := doms b; (a :: as, r)
    | t => ([], t)
  let isN (N : Name) : Term R → Bool
    | .const c [] => c == N
    | _ => false
  if key == "nat" || key == "string" || key == "int" then
    match d.type, d.value.map (eval g []) with
    | .sort _, some (.mu _ _ _ _ _ (some (T, _, _))) => if T == d.name then none else some "it must be an inductive type"
    | _, _ => some "it must be an inductive type"
  else if key == "memo" then none
  else match g.builtins.lookup "nat" with
    | none => some "register `builtin nat := …` first"
    | some N =>
      let (as, r) := doms d.type
      let arity := natOpArity key
      -- numerals unfold through `nat.zero` and `nat.succ`: they must be `N`'s own
      -- constructors, not definitions that only have their types
      let rec isCtor : Term R → Bool
        | .lam _ b => isCtor b
        | .con _ => true
        | _ => false
      if d.value.isNone then some "it must be a definition"
      else if as.length != arity || !as.all (isN N) then
        some s!"it must take {arity} argument{if arity == 1 then "" else "s"} of type {N}"
      else if (key == "nat.zero" || key == "nat.succ") && !(d.inline && (d.value.map isCtor).getD false) then
        some s!"it must be a constructor of {N}"
      else if !(key == "nat.beq" || key == "nat.blt") && !isN N r then some s!"its result must have type {N}"
      else none

/-- Mutual inductive types (stage 13) as one family indexed by a tag type:

    mutual inductive A … inductive B … end   ↦   inductive A_B.Tag | A | B
                                                 inductive A_B : A_B.Tag → Type (all constructors)
                                                 def A : Type := A_B A_B.Tag.A   (and B)

Inside the constructors, `A` and `B` stand for their family members. Each constructor
is named by its member, `A.c` (the family's tag for it is `A.c`, `ctorConst`), so two
members may have constructors of the same name, and `.c` at an expected `A` is `A.c`
(`dotCtor?`). Matching works on the family's constructors (at a concrete index).
`deriving C` on a member derives `C` for the family. No parameters or indices yet. -/
partial def mutualInductive (tables : ParserTables) (defs : Array Syntax) : Except String (List Syntax) := do
  let names := defs.map fun d => ((d.getArg 1).getId?).getD "_"
  for d in defs do
    unless (d.getArg 2).args.isEmpty && (d.getArg 3).args.isEmpty && (d.getArg 4).args.isEmpty do
      throw "mutual inductive types may not have universe parameters, parameters or indices (yet)"
  let fam := "_".intercalate names.toList
  let parse (text : String) : Except String Syntax := match parseCommand text.toList.toArray tables 0 with
    | .ok (stx, _) => pure stx
    | .error _ => throw s!"internal error: could not parse {text}"
  -- the tags name the members without dots (a private member is `_private.M._0.A`)
  let tagOf (n : Name) : Name := (Globals.privateBase n).replace "." "_"
  let tagCmd ← parse s!"inductive {fam}.Tag where{String.join (names.toList.map (s!"\n  | " ++ tagOf ·))}"
  let famFrame ← parse s!"inductive {fam} : {fam}.Tag → Type where"
  let substs ← names.mapM fun n => match parseCategory tables "term" s!"({fam} {fam}.Tag.{tagOf n})" with
    | .ok t => pure (n, t)
    | .error e => throw s!"internal error: {e}"
  let rec subst (stx : Syntax) : Syntax := match stx with
    | .node i "term.ident" #[.ident j n] => match substs.find? (·.1 == n) with
      | some (_, t) => t
      | none => .node i "term.ident" #[.ident j n]
    | .node i k as => .node i k (as.map subst)
    | s => s
  -- each constructor is named by its member (`A.c`, `ctorConst`): two members may have
  -- constructors of the same name
  let ctors := (defs.zip substs).flatMap fun (d, (n, self)) => (d.getArg 6).args.map fun c =>
    let c := subst c
    let c := match c.getArg 2 with
      | .ident i x => c.setArg 2 (.ident i (n ++ "." ++ x))
      | _ => c
    if (c.getArg 4).args.isEmpty then c.setArg 4 (.node {} "null" #[.atom {} ":", self]) else c
  let famCmd := famFrame.setArg 6 (.node {} "null" ctors)
  let typeDefs ← names.mapM fun n => parse s!"def {n} : Type := {fam} {fam}.Tag.{tagOf n}"
  -- `deriving C` on a member: for the family (one instance `C (A_B t)` covers every
  -- member, and its methods recurse through all of them)
  let classes := defs.foldl (init := ([] : List Name)) fun acc d =>
    let stx := d.child "deriving"
    if stx.isNone then acc else
    (stx.getArg 1).args.foldl (fun acc c => match c.getId? with
      | some C => if acc.contains C then acc else acc ++ [C]
      | none => acc) acc
  let derivs ← if classes.isEmpty then pure [] else
    pure [← parse s!"deriving instance {", ".intercalate classes} for {fam}"]
  pure ([tagCmd, famCmd] ++ typeDefs.toList ++ derivs)

/-- (13b) Does a `structure` command say `private mk ::` after `where`? -/
def structurePrivateMk (cmd : Syntax) : Bool :=
  let spec := (cmd.child "where").child "ctor"
  !spec.args.isEmpty && !(spec.getArg 0).args.isEmpty

/-- (13b) The fields (observations) of a `structure` or `coinductive` command marked
`private`. -/
def privateFields (cmd : Syntax) : List Name :=
  (cmd.child "fields").args.toList.filterMap fun f =>
    if (f.child "private").args.isEmpty then none else (f.child "name").getId?

/-- The result of `runElabH`, for a command that keeps no info tree (`#check`, `#eval`,
`instance`, …): the `trace`s of its tactics and macros still become info messages. -/
def withTraces (r : Except (ElabError R) α × Array (Info R)) : StateM (CommandState R) (Except (ElabError R) α) := do
  for i in r.2 do
    match i with
    | .trace info text => modify fun s => { s with messages := s.messages.push { info, severity := .info, text } }
    -- (11q) the rest of the tree too (hovers in `#check`, an inductive type's binders)
    | .warning .. => pure ()
    | i => modify fun s => { s with infos := s.infos.push i }
  pure r.1

/-- (11r) Normalise syntax for an unexpander: no positions, no parentheses (the
formatter puts them where precedence needs them), and the variables of a `notation`
(`vars`, plain identifiers in its template) as antiquotations. -/
partial def ppNormalize (vars : List Name) : Syntax → Syntax
  | .node _ "term.paren" #[_, t, _] => ppNormalize vars t
  | .node _ "term.ident" #[.ident _ n] =>
    if vars.contains n then .node {} "antiquot" #[.atom {} "$", .ident {} n]
    else .node {} "term.ident" #[.ident {} n]
  | .node _ k as => .node {} k (as.map (ppNormalize vars))
  | .atom _ v => .atom {} v
  | .ident _ n => .ident {} n
  | .missing => .missing

/-- (11r) The atoms of a `syntax` rule's items as written (`stx.atom`), in order. -/
partial def stxAtoms : Syntax → Array String
  | .node _ "stx.atom" as => ((as[0]?.bind Syntax.getStr?)).toArray
  | .node _ _ as => as.foldl (· ++ stxAtoms ·) #[]
  | _ => #[]

/-- The antiquotations of syntax. -/
partial def antiquotVars : Syntax → List Name
  | .node _ "antiquot" as => match as[1]? with
    | some (Syntax.ident _ x) => [x]
    | _ => []
  | .node _ _ as => as.toList.flatMap antiquotVars
  | _ => []

/-- (11r) An application pattern for `head`: `c $x₁ … $xₙ` as syntax, its head, and `n`. -/
def ppAppPattern? (pat : Syntax) : Option (Option Name × Nat) :=
  match pat with
  | .node _ "term.app" #[f, .node _ "null" args] => match f with
    | .node _ "term.ident" #[.ident _ c] => some (some c, args.size)
    | .node _ "antiquot" _ => some (none, args.size)
    | _ => none
  | .node _ "term.ident" #[.ident _ c] => some (some c, 0)
  | .node _ "antiquot" _ => some (none, 0)
  | _ => none

/-- (11r) A macro rule read backwards, when its template is a constant applied to
arguments (`notation:65 a " + " b => Add.add a b`, `- $x => Neg.neg $x`) and every
variable of its pattern occurs in the template: an unexpander for that constant, from
the template back to the pattern (Lean makes these for `notation`). -/
def invertMacroRule? (r : MacroRule) : Option UnexpanderEntry := do
  let tmpl := ppNormalize r.vars r.template
  let (some c, arity) ← ppAppPattern? tmpl | none
  let pat := ppNormalize r.vars r.pattern
  unless pat.isOfKind r.kind && r.kind.startsWith "term." do none
  let tv := antiquotVars tmpl
  unless (antiquotVars pat).all tv.contains do none
  pure { head := c, arity, how := .rule tmpl pat }

/-- (11r) Make the pretty printer's table (`Globals.pp`) from the macro rules, the declared
unexpanders and the grammar; the `pp.notation` option stays as it is. Procedural
unexpanders run in the interpreter, on code compiled once, on first use. -/
def CommandState.refreshPP (s : CommandState R) : CommandState R :=
  let fromMacros := s.macros.reverse.filterMap invertMacroRule?
  let entries := fromMacros ++ s.ppUser.reverse
  let unexpanders := entries.foldl (init := ({} : Std.HashMap Name (List UnexpanderEntry))) fun m e =>
    m.insert e.head (e :: m.getD e.head [])
  let formats := s.tables.cats.fold (init := ({} : Std.HashMap Name PPFormat)) fun m c cat =>
    let m := cat.leading.foldl (init := m) fun m lp =>
      if lp.kind == "antiquot" || lp.kind.startsWith "quote." then m else
      m.insert lp.kind { cat := c, leading := true, prec := lp.prec, p := lp.p, raw := s.rawAtoms.getD lp.kind #[] }
    cat.trailing.foldl (init := m) fun m tp =>
      m.insert tp.kind { cat := c, leading := false, prec := tp.prec, lhsPrec := tp.lhsPrec, p := tp.p,
                         raw := s.rawAtoms.getD tp.kind #[] }
  let fns := s.ppUser.filterMap fun e => match e.how with
    | .fn f => some f
    | _ => none
  let g := s.globals
  let builtins := s.builtins
  let code : Thunk (Except String Code) := Thunk.mk fun _ =>
    (compileReachable g builtins ("Macro.run" :: fns) (externImpls := false)).mapError toString
  let run (f : Name) (stx : Syntax) : Option Syntax := match code.get with
    | .ok c => match (Elab.runProcMacro c f stx 0).2 with
      | .ok (out, _) => some out
      | .error _ => none
    | .error _ => none
  let run := if fns.isEmpty then fun _ _ => none else run
  { s with globals := { s.globals with pp := { s.globals.pp with unexpanders, formats, run } } }

/-- (13m) The end of an imported module: `inner` is the state after it, `outer` the
importer's before the `import`. The module's `local` notation is dropped: its parsers
(and categories), the macro rules and macros of its kinds, and its `local` macro rules
and registrations; tokens no remaining parser mentions are no longer reserved. Kind
names stay taken, so a later notation gets a new kind and none of the dropped rules. -/
def CommandState.endModule (inner outer : CommandState R) : CommandState R :=
  let kinds := inner.localKinds.take (inner.localKinds.length - outer.localKinds.length)
  let cats := inner.localCats.take (inner.localCats.length - outer.localCats.length)
  let rules := inner.localRules.take (inner.localRules.length - outer.localRules.length)
  let procs := inner.localProcs.take (inner.localProcs.length - outer.localProcs.length)
  let insts := inner.localInsts.take (inner.localInsts.length - outer.localInsts.length)
  let pps := inner.localPP.take (inner.localPP.length - outer.localPP.length)
  -- (11r) `set_option pp.…` is the module's own
  let reset := { inner with localKinds := outer.localKinds, localCats := outer.localCats,
                            localRules := outer.localRules, localProcs := outer.localProcs,
                            localInsts := outer.localInsts, localPP := outer.localPP,
                            globals := { inner.globals with pp := { inner.globals.pp with useNotation := outer.globals.pp.useNotation } } }
  -- (11w) a `local instance` is found only in its module (its definition stays: a name)
  let reset := if insts.isEmpty then reset else
    { reset with instances := (reset.instances.zipIdx.filter fun (_, i) => !insts.contains i).map (·.1) }
  if kinds.isEmpty && cats.isEmpty && rules.isEmpty && procs.isEmpty && pps.isEmpty then reset else
  let t := inner.tables
  let cats' := t.cats.fold (init := ({} : Std.HashMap Name Category)) fun acc c cat =>
    if cats.contains c then acc else
    acc.insert c { leading := cat.leading.filter (!kinds.contains ·.kind),
                   trailing := cat.trailing.filter (!kinds.contains ·.kind) }
  let used : Std.HashSet String := cats'.fold (init := {}) fun acc _ cat =>
    let acc := cat.leading.foldl (fun acc lp => lp.p.tokens.foldl (·.insert ·) acc) acc
    cat.trailing.foldl (fun acc tp => tp.p.tokens.foldl (·.insert ·) acc) acc
  -- (entries numbered from the oldest, as `local` recorded them)
  let keep {α : Type} (key : α → Name) (xs : List α) (dropped : List Nat) : List α :=
    let n := xs.length
    (xs.zipIdx.filter fun (x, i) => !kinds.contains (key x) && !dropped.contains (n - 1 - i)).map (·.1)
  let s' := { reset with
    tables := { t with cats := cats', tokens := t.tokens.filter used.contains }
    macros := keep (·.kind) inner.macros rules
    procMacros := keep (·.1) inner.procMacros procs
    tactics := inner.tactics.filter (!kinds.contains ·.1)
    cmdMacros := inner.cmdMacros.filter (!kinds.contains ·.1)
    ppUser := keep (·.head) inner.ppUser pps }
  s'.refreshPP

/-- Elaborate one command, updating the state and adding messages. -/
partial def elabCommand (cmd : Syntax) : StateM (CommandState R) Unit := do
  -- (13b) privacy is per module: the globals know which one is being elaborated
  modify fun s => if s.globals.module == s.module then s else { s with globals := { s.globals with module := s.module } }
  let s ← get
  let report (sev : Severity) (info : SourceInfo) (text : String) : StateM (CommandState R) Unit :=
    modify fun s => { s with messages := s.messages.push { info, severity := sev, text } }
  -- an error with a code (`ErrorCode`)
  let reportC (info : SourceInfo) (text code : String) : StateM (CommandState R) Unit :=
    modify fun s => { s with messages := s.messages.push { info, severity := .error, text, code } }
  -- the kernel's error, for the declaration `name`
  let reportKernel (info : SourceInfo) (name : Name) (e : TypeError) (extra : String := "") : StateM (CommandState R) Unit :=
    reportC info (kernelRejected name e ++ extra) (kernelRejectedCode e)
  -- a second declaration of a name (code `duplicate-declaration`: an import reports it as it is)
  let reportDup (info : SourceInfo) (n : Name) : StateM (CommandState R) Unit :=
    modify fun s => { s with messages := s.messages.push { info, severity := .error, text := s.alreadyDeclared n,
                                                           code := "duplicate-declaration" } }
  let reportErr (e : ElabError R) : StateM (CommandState R) Unit :=
    modify fun s =>
      -- an unknown identifier: the names close to it (computed here, not where it is
      -- thrown: elaboration may throw and catch many on its way)
      let hint := if e.code != "unknown-identifier" then "" else
        match e.state?.bind fun st => st.infos.findRev? (· matches .done (.unknownIdent ..)) with
        | some (.done (.unknownIdent _ x locals)) =>
          let h := didYouMean s.globals x locals
          -- a name of the Prelude, which this file doesn't import
          let inPrelude := !s.imported.contains "Prelude" && s.module != "Prelude" &&
            match s.loader "Prelude" with
            | some src => ["def", "inductive", "structure", "class", "axiom"].any fun k =>
                (src.splitOn s!"\n{k} {x} ").length > 1 || (src.splitOn s!"\n{k} {x}.\{").length > 1 ||
                (src.splitOn s!"\n{k} {x}\n").length > 1
            -- (`wiz check` loads only the modules the file imports: the best-known names)
            | none => ["Nat", "Bool", "List", "Option", "String", "Char", "Except", "Monad",
                       "Add", "Sub", "Mul", "OfNat", "Syntax", "Tactic"].contains x
          if h.isEmpty && inPrelude then s!"; {x} is defined in the Prelude: add `import Prelude`"
          else h
        | _ => ""
      { s with messages := s.messages.push { info := e.info, severity := .error, text := e.msg ++ hint,
                                             code := ErrorCode.reported e.code } }
  -- the info tree of a declaration; its `trace`s become info messages
  let addInfos (is : Array (Info R)) : StateM (CommandState R) Unit :=
    unless is.isEmpty do modify fun s =>
      -- (`trace`s become info messages, and (7e) `warning`s warnings; the warnings stay in
      -- the tree too)
      let msgs := is.filterMap fun
        | .trace info text => some { info, severity := .info, text }
        | .warning info text => some { info, severity := .warning, text }
        | _ => none
      if msgs.isEmpty then { s with infos := s.infos ++ is }
      else { s with infos := s.infos ++ is.filter (!· matches .trace ..), messages := s.messages ++ msgs }
  -- the finalizer of a foreign pointer type (for a foreign function's result)
  let finOf (t : Term R) : String := match (Term.spine t).1 with
    | .const n _ => ((s.foreignTypes.find? (·.1 == n)).map (·.2)).getD ""
    | _ => ""
  -- how a foreign function's parameter or result is marshalled (stage 9a, `ExternSig`)
  let ffiKind (t : Term R) : Option Char := match t with
    | .unit _ => some 'v'
    -- a type variable: any Wiz value, passed as it is
    | .var _ => some 'w'
    | t => match (Term.spine t).1 with
      | .const "Nat" _ => some 'n'
      | .const "UInt64" _ => some 'u'
      | .const "Float64" _ => some 'f'
      | .const "String" _ => some 's'
      | .const "Bool" _ => some 'b'
      | .const "Bytes" _ | .const "Array" _ | .const "Str" _ | .const "StrMap" _ => some 'w'
      | .var _ => some 'w'
      | .const n _ =>
        if s.foreignTypes.any (·.1 == n) then some 'p'
        -- a Wiz data type (`UIntN w`): the value as it is, for runtime natives
        else if (s.globals.find? n).any (·.value.isSome) then some 'w' else none
      | _ => none
  -- the parameters and result of a function type, and whether the result is in `IO`
  let rec ffiParams : Term R → List (Term R × Term R) × Term R
    | .pi _ _ q A B _ => let (ps, r) := ffiParams B; ((q, A) :: ps, r)
    | t => ([], t)
  let ffiIO (res : Term R) : Bool × Term R := match Term.spine res with
    | (.const "IO" _, [A]) => (true, A)
    | _ => (false, res)
  -- (9g) a function that C calls: Wiz values come in (`n u f s b p w`) and go out
  -- (`n u f s b v w`); none erased, none a callback
  let ffiCallSig (ty : Term R) : Option RVal.CallbackSig := do
    let (ps, res) := ffiParams ty
    let (io, res) := ffiIO res
    let ks ← ps.mapM fun (q, A) => if q == .qlit 0 then none else
      match ffiKind A with
      | some 'v' => none
      | k => k
    let rk ← match ffiKind res with
      | some 'p' => none
      | k => k
    pure { params := ks, result := rk, io }
  -- (9i) the C struct a Wiz structure stands for (`c_struct`), as a marshalling kind
  let structKind? (n : Name) : Option RVal.FKind :=
    (s.builtins.find? fun (k, x) => x == n && k.startsWith "cstruct:").bind fun (k, _) =>
      (RVal.FKind.parseOne (k.drop 8).toString.toList).map (·.1)
  -- (HD8) the code of the registered macros, tactics and derivers
  let remakeMetaCode : StateM (CommandState R) Unit := modify fun s =>
    let more := if s.cmdMacros.isEmpty && s.derivers.isEmpty then []
      else "CommandMacro.run" :: (s.cmdMacros ++ s.derivers).map (·.2)
    { s with metaCode := mkMetaCode s.globals s.builtins s.procMacros s.tactics more }
  let metaCodeFor (f : Name) (runner : Name := "CommandMacro.run") : Except String Code := match s.metaCode.get with
    | .ok c => if c.contains f && c.contains runner then .ok c
      else (compileReachable s.globals s.builtins [f, runner] (externImpls := false)).mapError (s!"cannot compile {f}: {·}")
    | .error e => .error e
  -- elaborate the commands a command macro or deriver produced
  let elabExpansion (what : String) (r : Array String × Except String (Array Syntax × Nat)) (info : SourceInfo) :
      StateM (CommandState R) Unit := do
    for t in r.1 do report .info info t
    match r.2 with
    | .error e => report .error info s!"{what}: {e}"
    | .ok (cmds, next) =>
      modify fun s => { s with nextScope := next }
      for c in cmds do elabCommand c
  -- `deriving C` for the type `T`: run `C`'s deriver
  let derive (C T : Name) (info : SourceInfo) : StateM (CommandState R) Unit := do
    let s ← get
    match s.derivers.lookup C with
    | none => report .error info s!"no deriver for {C} (register one with `attribute [deriver {C}] f`)"
    | some f =>
      let r := match metaCodeFor f with
        | .ok code => Elab.runDeriver code f T info s.nextScope (macroEnv s.globals)
        | .error e => (#[], .error e)
      elabExpansion s!"deriving {C} for {T}" r info
  let derivingClause (stx : Syntax) (T : Name) : StateM (CommandState R) Unit := do
    unless stx.isNone do
      for c in (stx.getArg 1).args do
        if let some C := c.getId? then derive C T c.info
  let addDeclChecked (name : Name) (levelParams : List Name) (ty : Term R) (val : Option (Term R))
      (impl : Option (Term R) := none) := do
    match addDeclSorted s.globals { name, levelParams, type := ty, value := val, impl } with
    | .ok g => modify fun s => { s with globals := g }
    | .error e =>
      -- the implementation (a recursive definition's equations compiled a second time,
      -- `elabDefEqns`) is the elaborator's own: if only it fails, the bug is ours
      let ours := impl.isSome &&
        (addDeclSorted s.globals { name, levelParams, type := ty, value := val }) matches .ok _
      reportKernel cmd.info name e (if ours then
        "\n(the definition itself checks: this is a bug in Wiz's compilation of recursive definitions, not in your code; please report it)" else "")
  match cmd.kind with
  | "command.private" =>
    -- (13b) every name the command declares is private to this module
    let before := s.globals.order.size
    -- In a module, a private type (`inductive`, `structure`, `class`, `coinductive`, or a
    -- `mutual` block of inductives) is declared under its private kernel name
    -- (`Globals.privateName`) from the start, so that its constructors, fields,
    -- recursors and the side tables about them are all under that name: the command is
    -- elaborated with the type's name rewritten, wherever it occurs in it (`T`, `T.f`)
    let typeKinds := ["command.inductive", "command.structure", "command.class", "command.coinductive"]
    let inner := cmd.getArg 1
    let typeNames : Array Name :=
      if s.module.isEmpty then #[] else
      if typeKinds.contains inner.kind then ((inner.getArg 1).getId?).toArray
      else if inner.isOfKind "command.mutual" && (inner.getArg 1).args.all (·.isOfKind "command.inductive") then
        (inner.getArg 1).args.filterMap (·.getArg 1 |>.getId?)
      else #[]
    let inner := if typeNames.isEmpty then inner else
      inner.renameIdents fun n => typeNames.findSome? fun T =>
        if n == T then some (Globals.privateName s.module T)
        else if n.startsWith (T ++ ".") then some (Globals.privateName s.module T ++ (n.drop T.length).toString)
        else none
    elabCommand inner
    modify fun s =>
      let added := s.globals.order.extract before s.globals.order.size
      -- In a module, a private function, axiom or foreign function gets a kernel name of
      -- its own (`Globals.privateName`), so that another module's private declaration of
      -- the same name is a different constant (no clash at the import); in the module,
      -- the source name resolves to it (`Globals.resolve`). (Types: above.)
      let inner := cmd.getArg 1
      let inner := if inner.isOfKind "command.partial" then inner.getArg 2 else inner
      let renamed := !s.module.isEmpty &&
        (["command.def", "command.defEqns", "command.axiom", "command.extern"].contains inner.kind ||
         (inner.isOfKind "command.mutual" && (inner.getArg 1).args.all (!·.isOfKind "command.inductive")))
      let s := if renamed then renamePrivate s added else s
      let added := s.globals.order.extract before s.globals.order.size
      { s with globals := { s.globals with
          privates := added.foldl (fun m n => m.insert n s.module) s.globals.privates } }
  | "command.sealed" =>
    -- (22k) `sealed inductive T …`: declare the seal, an axiom `T.seal✝ : Type` private to
    -- this module; `elabInductive` then puts it in `T`'s index tail. Only this
    -- declaration can write the name, and a constant is compared by name, so no other
    -- declaration is convertible to `T`.
    let inner := cmd.getArg 1
    if !inner.isOfKind "command.inductive" then
      report .error cmd.info "`sealed` applies to an `inductive` declaration"
    else
      let T := ((inner.getArg 1).getId?).getD "_"
      if s.globals.contains T then
        report .error (inner.getArg 1).info s!"'{T}' has already been declared"
      else
        match addDeclSorted s.globals { name := sealName T, levelParams := [], type := .sort 1, value := none } with
        | .error e => reportKernel cmd.info (sealName T) e
        | .ok g =>
          let g := { g with privates := g.privates.insert (sealName T) s.module,
                            builtins := (sealKey T, sealName T) :: g.builtins }
          modify fun s => { s with globals := g, builtins := (sealKey T, sealName T) :: s.builtins }
          -- (`T.desc` is private when a constructor is, 13b: a native type's always is, so
          -- `μ (T.desc …) i` written out elsewhere can't hand the seal to unification; a
          -- sealed type with public constructors unfolds anyway)
          elabCommand inner
  | "command.local" =>
    -- (13m) grammar that stays in this module: remember what the command adds
    let inner := cmd.getArg 1
    unless ["command.syntax", "command.declareSyntaxCat", "command.notation", "command.infix",
            "command.macroRules", "command.attrMacro", "command.instance", "command.appUnexpander", "command.attrUnexpander"].contains inner.kind do
      report .error cmd.info "only `syntax`, `declare_syntax_cat`, `notation`, `infixl`/`infixr`/`infix`, `macro_rules`, `attribute [macro …]`, `instance` and unexpanders can be `local`"
      return
    let before ← get
    elabCommand inner
    modify fun s =>
      let kinds := s.tables.kinds.toList.filterMap fun (k, _) => if before.tables.kinds.contains k then none else some k
      let cats := s.tables.cats.toList.filterMap fun (c, _) => if before.tables.cats.contains c then none else some c
      { s with localKinds := kinds ++ s.localKinds, localCats := cats ++ s.localCats
               localRules := (List.range' before.macros.length (s.macros.length - before.macros.length)).reverse ++ s.localRules
               localProcs := (List.range' before.procMacros.length (s.procMacros.length - before.procMacros.length)).reverse ++ s.localProcs
               localInsts := (List.range' before.instances.size (s.instances.size - before.instances.size)).reverse ++ s.localInsts
               localPP := (List.range' before.ppUser.length (s.ppUser.length - before.ppUser.length)).reverse ++ s.localPP }
  | "command.def" | "command.axiom" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    let binders := (cmd.getArg 3).args
    let typeStx := (cmd.getArg 4).args[1]?
    let valStx := if cmd.isOfKind "command.def" then some (cmd.getArg 6) else none
    -- a recursive `:= match` on the parameters: the equations it means
    if let some eqns := (if cmd.isOfKind "command.def" && !s.globals.contains name then defMatchAsEqns? name cmd else none) then
      elabCommand eqns
      return
    if s.globals.contains name then
      reportDup (cmd.getArg 1).info name
    else if let some nr := valStx.filter (·.isOfKind "term.nativeRefl") then
      -- (27a) `def X : a = b := native_refl`: decided by running `a` and `b`
      if !s.trustNative then
        report .error nr.info "native evaluation is not enabled: `native_refl` decides an equation by running compiled code, which the kernel does not check; run with --trust-native to allow it"
      else if !binders.isEmpty || !levelParams.isEmpty || typeStx.isNone then
        report .error nr.info "native_refl proves a closed equation: `def X : a = b := native_refl`, with a type and without parameters or universe parameters"
      else match runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals (elabDeclTerms binders typeStx none cmd.info (declName? := some (name, (cmd.getArg 1).info, declInsertAt cmd))) [] with
      | (.error e, hv) => addInfos hv; reportErr e
      | (.ok (ty, _), hv) =>
        addInfos hv
        let g := s.globals
        -- (as written: the kernel's equality computes, observationally, at data types)
        match ty with
        | .eq A a b =>
          match Native.decideNative g s.builtins A a b s.nativeFuel with
          | .error e => report .error nr.info s!"native_refl: {e}"
          | .ok v =>
            let ax := name ++ ".native✝"
            -- (`addDeclSorted` without `withSorts`' evaluation of the type, which is for
            -- checking a value against it: evaluating an equation computes both sides, F5)
            -- (nor `Sorts.type`'s: an equation's sort is `Prop`; its sides get their sorts)
            -- (P2: and the proof markers of its sides, `Mark.type`, which does not evaluate it
            -- either; `Decl.withMarks` would, for checking a value)
            let axD : Decl R := { name := ax, type := (Mark.type { globals := g } (Sorts.term g #[] [] ty)).1, value := none }
            match (do let g' ← addDecl g axD; privacyCheck g axD; pure g' : TCM (Globals R)) with
            | .error e => report .error cmd.info s!"kernel rejected {ax}: {e}"
            | .ok g' =>
              -- the value mentions the native implementations the run can reach (erased
              -- `let`s), so that `#print axioms` walks what they reach too
              let one := Level.succ .zero
              let val := v.natives.foldr (fun m body => match g'.find? m with
                | some d => .letE "_" (.qlit 0) (d.type.instLevels d.levelParams (d.levelParams.map fun _ => one))
                    (.const m (d.levelParams.map fun _ => one)) body
                | none => body) (Term.const ax [])
              -- Added without the kernel's check: checking `val` against the type evaluates
              -- the equation, and the kernel's `vEq` computes both sides (F5 of
              -- wiz-notes/kernel-eval.md), which is what native evaluation is for. The
              -- check is the constant rule: `X.native✝` was declared (just above, by the
              -- kernel) at this very type, and each `let` binds a constant at its own
              -- declared type, erased, which the body does not mention.
              -- (The header is the kernel's: the type is checked to be a well-formed type,
              -- `a b : T`, which does not evaluate the equation.)
              let axTy := ((g'.find? ax).map (·.type)).getD ty
              let d : Decl R := { name, type := axTy, value := some val }
              match checkHeader g' d with
              | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
              | .ok () =>
                modify fun s => { s with globals := g'.insert d }
                report .warning nr.info s!"{name} is accepted on the strength of native evaluation (--trust-native, {v.steps} steps), not checked by the kernel: its proof is the axiom {ax}, which `#print axioms` lists for everything that uses {name}"
        | _ => report .error nr.info "native_refl proves an equation `a = b`; this type is not one"
    else match runElabS (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) (smt := { s.smt with trustNative := s.trustNative, nativeFuel := s.nativeFuel }) (smtDecl := name) s.globals (elabDeclTerms binders typeStx valStx cmd.info (declName? := some (name, (cmd.getArg 1).info, declInsertAt cmd))) levelParams with
      | (.ok ((ty, val), sides), hv) =>
        addInfos hv
        if sides.isEmpty then addDeclChecked name levelParams ty val
        else
          -- (28) declarations a tactic added: definitions (28c, `TacticM.define`), checked
          -- by the kernel like any other, and axioms, checked as types (an axiom's
          -- statement is what was trusted); then the definition, which uses them
          let mut g := s.globals
          let mut ok := true
          for d in sides do
            -- (28e) an axiom `….native✝` a tactic asked for is decided here, by running it
            if d.value.isNone && d.name.endsWith ".native✝" then
              let eqn : Option (Term R × Term R × Term R) := match d.type with
                | .eq A a b => some (A, a, b)
                | .app (.const "Sat.IsTrue" _) e => some (.const "Bool" [], e, .const "Bool.true" [])
                | _ => none
              match eqn with
              | some (A, a, b) =>
                match Native.decideNative g s.builtins A a b s.nativeFuel with
                | .ok _ => pure ()
                | .error e => report .error cmd.info s!"{d.name}: native evaluation: {e}"; ok := false; break
              | none => report .error cmd.info s!"{d.name}: not an equation"; ok := false; break
            let r : Except String (Globals R) := if d.value.isSome then
                (addDeclSorted g d).mapError toString
              else
                let d := { d with type := Sorts.term g #[] [] d.type }
                (do let g' ← addDecl g d; privacyCheck g d; pure g' : TCM (Globals R)).mapError toString
            match r with
            | .ok g' => g := g'
            | .error e => report .error cmd.info s!"kernel rejected {d.name}: {e}"; ok := false; break
          if ok then
            match addDeclSorted g { name, levelParams, type := ty, value := val } with
            | .ok g' =>
              modify fun s => { s with globals := g' }
              let axs := sides.filter (·.value.isNone)
              let names := ", ".intercalate (axs.toList.map (·.name))
              let pl := if axs.size == 1 then "" else "s"
              if axs.isEmpty then pure ()
              else if axs.all (fun d => (d.name.splitOn ".smt✝").length > 1) then
                report .warning cmd.info s!"{name} is accepted on the word of an SMT solver (--trust-smt), not checked by the kernel: its proof uses the axiom{pl} {names}, which `#print axioms` lists for everything that uses {name}"
              else
                report .warning cmd.info s!"{name} is accepted on the strength of the axiom{pl} {names} that its tactics added, not checked by the kernel; `#print axioms` lists {if axs.size == 1 then "it" else "them"} for everything that uses {name}"
            | .error e => report .error cmd.info s!"kernel rejected {name}: {e}"
      | (.error e, hv) => addInfos hv; reportErr e
  | "command.partial" | "command.mutual" =>
    -- each definition, with the witness written for it (`partial (default := w) def …`)
    let unwrap (d : Syntax) : Syntax × Option Syntax :=
      if d.isOfKind "command.partial" then
        (d.getArg 2, if (d.getArg 1).isNone then none else some ((d.getArg 1).getArg 3))
      else (d, none)
    let members := if cmd.isOfKind "command.partial" then #[unwrap cmd] else (cmd.getArg 1).args.map unwrap
    let defs := members.map (·.1)
    if cmd.isOfKind "command.mutual" && defs.all (·.isOfKind "command.inductive") then
      match mutualInductive s.tables defs with
      | .ok cmds =>
        modify fun s => { s with mutualCtors := true }
        for c in cmds do elabCommand c
        modify fun s => { s with mutualCtors := false }
      | .error e => report .error cmd.info e
      return
    let typeOf (d : Syntax) : Option Syntax :=
      if d.isOfKind "command.defEqns" then some ((d.getArg 4).getArg 1) else (d.getArg 4).args[1]?
    -- the signatures first, as axioms (so the bodies can call each other)
    let mut g := s.globals
    let mut sigs : Array (Syntax × Name × List Name) := #[]
    for (d, wStx) in members do
      unless d.isOfKind "command.def" || d.isOfKind "command.defEqns" do
        report .error d.info "only definitions can be partial"
        return
      let name := ((d.getArg 1).getId?).getD "_"
      let levelParams := ((d.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
      if g.contains name then
        reportDup (d.getArg 1).info name
        return
      let some tyStx := typeOf d | report .error d.info "a partial definition needs a type"; return
      match runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) g (elabDeclTerms (d.getArg 3).args (some tyStx) none d.info) levelParams with
      | (.ok (ty, _), _) =>
        -- the kernel takes `name : ty` only with a witness of `ty`: the one written, or
        -- one the elaborator finds
        let findW : ElabM R (Option (Term R)) := match wStx with
          | some w => do
            let t ← Elab.check {} w (← evalIn {} ty)
            solveSortConstraints
            let t ← zonk 0 t
            ensureNoMVars t w.info
            pure (some t)
          | none => findWitness ty
        let w ← match runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) g findW levelParams with
          | .ok (some w) => pure w
          | .ok none =>
            report .error (d.getArg 1).info s!"partial definition {name}: no witness found for its type {ty.pretty [] (some s.globals)}; give one with `partial (default := w) def {name} …` (the kernel takes {name} only if its type is inhabited)"
            return
          | .error e => reportErr e; return
        let pd := Decl.withSorts g { name, levelParams, type := ty, value := none, witness := some w }
        let addP := fun (g' : Globals R) (d' : Decl R) => withMarksOnDemand g' d' (addPartialDecl g')
        match (do
            unless g.hidden.isEmpty do throw (.other s!"internal error: {pd.name} checked against the elaborator's view")
            let g' ← addP g pd; privacyCheck g pd addP; pure g' : TCM (Globals R)) with
        | .ok g' => g := g'
        | .error e => reportKernel (d.getArg 1).info name e; return
        sigs := sigs.push (d, name, levelParams)
      | (.error e, _) => reportErr e; return
    -- then the bodies, checked by the kernel and kept as the implementations
    for (d, name, levelParams) in sigs do
      let body : ElabM R (Term R) :=
        if d.isOfKind "command.defEqns" then do
          let (_, v, _) ← elabDefEqns name d (isPartial := true)
          pure v
        else do
          let (_, v) ← elabDeclTerms (d.getArg 3).args (typeOf d) (some (d.getArg 6)) d.info
          pure (v.getD (.const name []))
      match runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) g body levelParams with
      | (.ok v, hv) =>
        addInfos hv
        let v := match g.find? name with
          | some d => Sorts.value g #[] [] v (eval g [] d.type)
          | none => v
        -- (the proof markers, if the kernel asks for them: `withMarksOnDemand`)
        let r := match addPartialImpl g name v with
          | .error (.unmarkedProof ..) => match g.find? name with
            | some d => addPartialImpl g name (Mark.check { globals := g } v (eval g [] d.type))
            | none => addPartialImpl g name v
          | r => r
        match r with
        | .ok g' => g := g'
        | .error e => reportKernel d.info name e; return
      | (.error e, hv) => addInfos hv; reportErr e; return
    modify fun s => { s with globals := g }
  | "command.check" =>
    let r ← withTraces <| runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals do
      let (t, ty) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      let ty ← zonk 0 (quote (← getGlobals) 0 ty)
      -- an inferred `fun` carries its type as an annotation; don't print it twice
      let t := match t with
        | .ann tm _ => tm
        | t => t
      let g ← getGlobals
      pure s!"{t.pretty [] (some g)} : {ty.pretty [] (some g)}"
    match r with
    | .ok text => report .info cmd.info text
    | .error e => reportErr e
  | "command.reduce" =>
    let r ← withTraces <| runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals do
      let (t, _) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      ensureNoMVars t
      -- (P2) with its proofs marked: `nf` suspends them, and reads each back within the
      -- step budget (a proof need not have a normal form)
      let g ← getGlobals
      pure ((nf g (Mark.infer { globals := g } t).1).pretty [] (some g))
    match r with
    | .ok text => report .info cmd.info text
    | .error e => reportErr e
  | "command.defEqns" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      reportDup (cmd.getArg 1).info name
    else
      let pats := (cmd.getArg 5).args.toList.filterMap fun a => (a.getArg 1).args[0]?
      -- the coinductive type named by the result type, if it is one (two types may have
      -- the same observations: another module's private one, say); else the first whose
      -- observations the copatterns are
      let rec resultHead (stx : Syntax) : Option Name :=
        match stx.kind with
        | "term.ident" => (stx.getArg 0).getId?
        | "term.app" => resultHead (stx.getArg 0)
        | "term.paren" => resultHead (stx.getArg 1)
        | "term.arrow" | "term.depArrow" => resultHead (stx.getArg 2)
        | _ => none
      let declared := (resultHead ((cmd.getArg 4).getArg 1)).map s.globals.resolve
      let coinductiveOf? : Option (Name × List (Name × Bool)) :=
        if pats.all (·.isOfKind "term.dotIdent") then
          let fits := fun (T, obs) =>
            if pats.all (fun p => obs.any (·.1 == ((p.getArg 1).getId?).getD "_")) then some (T, obs) else none
          match s.coinductives.find? (some ·.1 == declared) with
          | some c => fits c
          | none => s.coinductives.findSome? fits
        else none
      -- (13b) copatterns define every observation: not outside the module of a private one
      if let some (T, obs) := coinductiveOf? then
        if let some (o, m) := obs.findSome? fun (o, _) => (s.globals.privateTo? (T ++ "." ++ o)).map (o, ·) then
          let T := Globals.privateBase T
          report .error cmd.info (s!"'{T}.{o}' is private to module {m}: a {T} can't be defined by " ++
            "copatterns outside it")
          return
      let r := match coinductiveOf?.map (·.2) with
        | some obs => runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals (do let (t, v) ← elabCopatterns name cmd obs; pure (t, v, none)) levelParams
        | none => runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals (elabDefEqns name cmd) levelParams
      match r with
      | (.ok (ty, val, impl), hv) =>
        addInfos hv
        addDeclChecked name levelParams ty (some val) impl
      | (.error e, hv) => addInfos hv; reportErr e
  | "command.coinductive" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      reportDup (cmd.getArg 1).info name
    else
      match ← withTraces (runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals (elabCoinductive cmd levelParams) levelParams) with
      | .error e => reportErr e
      | .ok (decls, obs) =>
        let mut g := s.globals
        for d in decls do
          match addDeclSorted g d with
          | .ok g' => g := g'
          | .error e =>
            reportKernel cmd.info (d.name) e
            return
        -- (13b) private observations: private to this module with the coconstructor
        -- `T.mk`, and elsewhere `T` is opaque (`Globals.elabView`), so a value of it is
        -- neither observed nor built except through the module's own definitions
        let privObs := privateFields cmd
        unless privObs.isEmpty do
          -- (and the description: `ν T.desc i` written out is the type with nothing hidden)
          let names := privObs.map (name ++ "." ++ ·) ++ [name ++ ".mk", name ++ ".desc"]
          g := { g with privates := names.foldl (fun m n => m.insert n s.module) g.privates,
                        opaques := g.opaques.insert name s.module }
        modify fun s => { s with globals := g, coinductives := s.coinductives ++ [(name, obs)] }
  | "command.class" =>
    let name := ((cmd.getArg 1).getId?).getD "_"
    let levelParams := ((cmd.getArg 2).getArg 1).args.toList.filterMap Syntax.getId?
    if s.globals.contains name then
      reportDup (cmd.getArg 1).info name
    else if let some f := (cmd.getArg 6).args.find? fun f => !(f.getArg 0).args.isEmpty then
      report .error f.info "a class's methods can't be private (make the class private instead)"
    else
      match runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
          (elabStructure cmd levelParams) levelParams with
      | .error e => reportErr e
      | .ok decls =>
        let decls := decls ++ classMethods (decls[0]!) levelParams
        let mut g := s.globals
        for d in decls do
          match addDeclSorted g d with
          | .ok g' => g := g'
          | .error e =>
            reportKernel cmd.info (d.name) e
            return
        let (Δ, _) := peelPis (decls[0]!).type
        let outParams := Δ.map fun (_, _, _, A) => match (Term.spine A).1 with
          | .const n _ => n == "outParam"
          | _ => false
        let fields := (cmd.getArg 6).args.toList.filterMap fun f => (f.getArg 2).getId?
        modify fun s => { s with globals := g, classes := { name, outParams, fields } :: s.classes }
  | "command.instance" =>
    let prioOpt := cmd.getArg 1
    let priority := if prioOpt.isNone then 1000 else ((prioOpt.getArg 3).getNat?).getD 1000
    -- (7f) an optional name
    let nameOpt := cmd.getArg 2
    let binders := (cmd.getArg 3).args
    let typeStx := cmd.getArg 5
    -- `:= v` or `where fields` (the branch's items are inline: `cmd[6]` is the keyword)
    let isWhere := (cmd.getArg 6) matches .atom _ "where"
    let body := cmd.getArg 7
    -- `instAddNat` from the identifiers of the type
    let rec idents (stx : Syntax) : List Name := match stx with
      | .ident _ n => [n]
      | .node _ _ as => as.toList.flatMap idents
      | _ => []
    -- (HD8) named after the conclusion of a Π-type (as derivers write them), without macro scopes
    let rec concl (stx : Syntax) : Syntax :=
      if stx.isOfKind "term.depArrow" then concl (stx.getArg 2) else stx
    -- ((13b) this module's private types and classes by their kernel names, so that two
    -- modules' instances for their private `Color`s have different names)
    let base := "inst" ++ String.join ((idents (concl typeStx)).map fun n => ((s.globals.resolve (stripScope n)).replace "." "").capitalize)
    let given? : Option Name := if nameOpt.isNone then none else
      (if nameOpt.isOfKind "null" then nameOpt.getArg 0 else nameOpt).getId?
    let name := match given? with
      | some n => n
      | none => if !s.globals.contains base then base else
        ((List.range 1000).map (s!"{base}_{·}")).find? (!s.globals.contains ·) |>.getD base
    -- `where f := v …` builds the class's constructor applied to the fields, in order
    let rec headIdent (stx : Syntax) : Option Name :=
      match stx.kind with
      | "term.ident" => (stx.getArg 0).getId?
      | "term.app" => headIdent (stx.getArg 0)
      | "term.paren" => headIdent (stx.getArg 1)
      | _ => none
    -- (an error: its message and code)
    let valStx : Except (String × String) Syntax :=
      if !isWhere then pure body else do
        let some C := headIdent typeStx | throw ("an instance's type must be an application of a class", ErrorCode.unknownClass)
        let C := s.globals.resolve C
        let some info := s.classes.find? (·.name == C)
          | throw (if s.globals.contains C then s!"{C} is not a class" else s!"unknown class '{C}'", ErrorCode.unknownClass)
        let given := body.args.toList.map fun f => (((f.getArg 0).getId?).getD "_", f.getArg 2)
        for (x, _) in given do
          unless info.fields.contains x do throw (s!"{C} has no field {x}", ErrorCode.noSuchField)
        let args ← info.fields.mapM fun x => match given.lookup x with
          | some v => pure (Syntax.node v.info "term.paren" #[.atom {} "(", v, .atom {} ")"])
          | none => throw (s!"missing field {x}", ErrorCode.missingField)
        let head := Syntax.node cmd.info "term.ident" #[.ident cmd.info (C ++ ".mk")]
        pure (if args.isEmpty then head else .node cmd.info "term.app" #[head, .node {} "null" args.toArray])
    -- the universe names in the binders and the type are the instance's universe
    -- parameters (an instance has no `.{u}` of its own; derivers write `Type u`)
    let rec levelNames (stx : Syntax) : List Name := match stx with
      | .node _ k as =>
        if k == "level.param" then ((stx.getArg 0).getId?).toList
        else as.toList.flatMap levelNames
      | _ => []
    let levelParams := (binders.toList.flatMap levelNames ++ levelNames typeStx).eraseDups
    match valStx with
    | .error (e, code) => reportC cmd.info e code
    | .ok _ => if given?.isSome && s.globals.contains name then reportDup nameOpt.info name else
    match valStx with
    | .error (e, code) => reportC cmd.info e code
    | .ok valStx =>
      match ← withTraces (runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics)
          (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
          (elabDeclTerms binders (some typeStx) (some valStx) cmd.info) levelParams) with
      | .error e => reportErr e
      | .ok (ty, val) =>
        let (_, concl) := peelPis ty
        match (Term.spine concl).1 with
        | .const C _ =>
          if s.classes.any (·.name == C) then
            addDeclChecked name levelParams ty val
            modify fun s => { s with instances := s.instances.push { name, cls := C, priority } }
          else reportC cmd.info s!"{C} is not a class" ErrorCode.unknownClass
        | _ => report .error cmd.info "an instance's type must be an application of a class"
  | "command.inductive" | "command.structure" =>
    -- (children by name, `childNames`: positions shift when the grammar grows)
    let name := ((cmd.child "name").getId?).getD "_"
    let levelParams := ((cmd.child "univParams").getArg 1).args.toList.filterMap Syntax.getId?
    let ctorSpec := if cmd.isOfKind "command.structure" then (cmd.child "where").child "ctor" else .missing
    -- a constructor's name is one identifier (only a `mutual` block's are qualified by
    -- their member, `ctorConst`)
    let dotted := if cmd.isOfKind "command.inductive" && !s.mutualCtors then
      (cmd.child "ctors").args.find? fun c => ((c.child "name").getId?).any (·.contains '.') else none
    if s.globals.contains name then
      reportDup (cmd.child "name").info name
    else if let some c := dotted then
      report .error (c.child "name").info s!"a constructor's name is a single identifier, not {((c.child "name").getId?).getD "_"}"
    else if cmd.isOfKind "command.structure" && !ctorSpec.args.isEmpty &&
        (ctorSpec.getArg 1).getId? != some "mk" then
      report .error (ctorSpec.getArg 1).info s!"a structure's constructor is `mk` (only `private mk ::` can be written)"
    else
      let elabCmd := if cmd.isOfKind "command.inductive" then elabInductive cmd levelParams
        else elabStructure cmd levelParams
      match ← withTraces (runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals elabCmd levelParams) with
      | .error e => reportErr e
      | .ok decls =>
        -- a structure's projection functions `S.f` (unless the name is taken, as `S.mk`)
        let decls := if cmd.isOfKind "command.structure" then
            decls ++ (classMethods (decls[0]!) levelParams .default).filter fun d =>
              !s.globals.contains d.name && !decls.any (·.name == d.name)
          else decls
        let mut g := s.globals
        for d in decls do
          match addDeclSorted g d with
          | .ok g' => g := g'
          | .error e =>
            reportKernel cmd.info (d.name) e
            return
        -- the recursors need the declarations above
        if cmd.isOfKind "command.inductive" then
          let ctors := (cmd.child "ctors").args.toList.filterMap fun c => (c.child "name").getId?
          -- (indexed families also get `recN`/`casesOnN`, for motives that don't depend
          -- on the scrutinee)
          let indexed := isIndexed g name
          let mut recNames : List Name := []
          for (withIH, sized, nondep) in [(false, false, false), (true, false, false), (false, true, false)] ++
              (if indexed then [(false, false, true), (true, false, true)] else []) do
            match mkRecursor g name ctors withIH sized nondep with
            | .error e => report .error cmd.info s!"could not generate the recursor: {e}"; return
            | .ok d =>
              recNames := recNames ++ [d.name]
              match addDeclSorted g d with
              | .ok g' => g := g'
              | .error e =>
                reportKernel cmd.info d.name e s!"\n  {d.type.pretty [] (some s.globals)}"
                return
          -- (21v) the additive case `T.casesOnA`, for a `match` whose branches share a
          -- linear variable (none for a type without constructors: its bundle would be
          -- a linear argument nothing uses)
          -- (linear-case stage 2) and `T.casesOn1`, the case on a scrutinee held at 1
          unless ctors.isEmpty do
            for linear in [false, true] do
              match mkRecursor g name ctors false (additive := true) (linear := linear) with
              | .error e => report .error cmd.info s!"could not generate the recursor: {e}"; return
              | .ok d =>
                recNames := recNames ++ [d.name]
                match addDeclSorted g d with
                | .ok g' => g := g'
                | .error e =>
                  report .error cmd.info s!"kernel rejected {d.name}: {e}\n  {d.type.pretty}"
                  return
          -- (13b) `| private c`: the constructor is private to this module, and so are the
          -- recursors (their cases would hand out a private constructor's fields, and
          -- they are what a `match` compiles to); elsewhere `T` is opaque
          -- (`Globals.elabView`): it isn't matched there, and nothing else converts to it
          let privCtors := (cmd.child "ctors").args.toList.filterMap fun c =>
            if (c.child "private").args.isEmpty then none else (c.child "name").getId?
          unless privCtors.isEmpty do
            -- (and the description: `μ T.desc i` written out is the type with nothing
            -- hidden; a raw `con` builds a value of it, and it lists the private fields)
            let names := privCtors.map (ctorConst name ·) ++ recNames ++ [name ++ ".desc"]
            g := { g with privates := names.foldl (fun m n => m.insert n s.module) g.privates,
                          opaques := g.opaques.insert name s.module }
        -- (13b) `private mk ::`: the constructor is private to this module, and elsewhere
        -- the type is opaque (`Globals.elabView`): only its projections read it
        if cmd.isOfKind "command.structure" && structurePrivateMk cmd then
          g := { g with privates := g.privates.insert (name ++ ".mk") s.module,
                        opaques := g.opaques.insert name s.module }
        -- (13b) `private f : A`: the projection `S.f` is private, and elsewhere `S` is
        -- opaque, so the field isn't read through the Σ (`p.1`) either
        let privFields := if cmd.isOfKind "command.structure" then privateFields cmd else []
        unless privFields.isEmpty do
          g := { g with privates := privFields.foldl (fun m f => m.insert (name ++ "." ++ f) s.module) g.privates,
                        opaques := g.opaques.insert name s.module }
        modify fun s => { s with globals := g }
        derivingClause (cmd.child "deriving") name
  | "command.builtin" =>
    let key := ((cmd.getArg 1).getId?).getD "_"
    let n := ((cmd.getArg 3).getId?).getD "_"
    let known := ["nat", "nat.zero", "nat.succ", "nat.pred", "nat.add", "nat.sub", "nat.mul", "nat.beq", "nat.blt", "string", "memo", "int",
      "nat.div", "nat.mod", "nat.pow", "nat.land", "nat.lor", "nat.xor", "nat.shiftLeft", "nat.shiftRight", "nat.log2"]
    if !known.contains key then report .error cmd.info s!"unknown builtin {key}; known: {known}"
    -- one registration per key, and one key per constant: a second `builtin nat.add := K`
    -- would redirect how the first one's constant unfolds (the kernel finds the definition
    -- by key), an assumption that no declaration using it would show
    else if let some m := s.globals.builtins.lookup key then
      report .error cmd.info s!"builtin {key} is already registered (as {m}); a builtin can be registered only once"
    else if let some (k, _) := s.globals.builtins.find? fun (k, m) => m == n && known.contains k then
      report .error cmd.info s!"{n} is already registered as builtin {k}"
    else match s.globals.find? n with
    | none => reportC cmd.info s!"unknown declaration '{n}'" ErrorCode.unknownDeclaration
    | some d =>
      match builtinShapeError s.globals key d with
      | some e => report .error cmd.info s!"builtin {key} := {n}: {e}"
      | none =>
        -- the toolchain's library is trusted (its registrations are reviewed: README,
        -- "Trusted base"); anywhere else, nothing checks that `n` computes like the native
        -- operation, so the registration is an axiom of whatever depends on `n`
        -- (`builtin int` only says how values print: nothing to trust)
        let trusted := s.trustedModule s.module || key == "int"
        modify fun s => { s with builtins := (key, n) :: s.builtins,
                                 globals := { s.globals with builtins := (key, n) :: s.globals.builtins,
                                                             assumed := if trusted then s.globals.assumed
                                                                        else (key, n) :: s.globals.assumed } }
        unless trusted do
          report .warning cmd.info s!"builtin {key} := {n} is not checked: it is an axiom of every declaration that depends on {n} (see `#print axioms`)"
  | "command.printAxioms" =>
    let n := ((cmd.getArg 2).getId?).getD "_"
    if !s.globals.contains n then reportC (cmd.getArg 2).info s!"unknown declaration '{n}'" ErrorCode.unknownDeclaration
    else match s.globals.axiomsOf n with
      | [] => report .info cmd.info s!"'{n}' does not depend on any axioms"
      | as =>
        -- (a native implementation is trusted to agree with its definition; proofs
        -- never run it, compiled code does)
        let note := if as.any (·.startsWith "native ") then
          "\n(native: an implementation that compiled code runs, trusted to agree with its definition)" else ""
        -- (27a) a `native_refl` axiom
        let note := note ++ if as.any (·.endsWith ".native✝") then
          "\n(.native✝: a closed proposition decided by running it (native_refl, --trust-native, sat_decide_native): trusted are erasure, the interpreter and the native implementations listed)" else ""
        let note := note ++ if as.any (fun a => (a.splitOn ".smt✝").length > 1) then
          "\n(.smt✝N⟨solver⟩: a goal closed by an SMT solver (the smt tactic, --trust-smt): trusted are the solver named in the axiom, Wiz's translation to SMT-LIB (Wiz/Smt/Translate.lean) and the answer cache)" else ""
        report .info cmd.info s!"'{n}' depends on axioms: [{", ".intercalate as}]{note}"
  | "command.foreignType" =>
    -- an opaque C pointer type; values are released with the finalizer
    let name := ((cmd.getArg 1).getId?).getD "_"
    let fin := if (cmd.getArg 2).isNone then "" else (((cmd.getArg 2).getArg 3).getStr?).getD ""
    -- (9i) `(c := "T")`: `T *` in an imported header is this type
    let cty := if (cmd.getArg 3).isNone then [] else [(s!"ctype:{(((cmd.getArg 3).getArg 3).getStr?).getD ""}", name)]
    match addDeclSorted s.globals { name, type := .sort 1, value := none } with
    | .ok g => modify fun s => { s with globals := { g with builtins := cty ++ g.builtins }, builtins := cty ++ s.builtins,
                                        foreignTypes := (name, fin) :: s.foreignTypes }
    | .error e => reportKernel cmd.info (name) e
  | "command.importC" =>
    -- bind every function of a C header whose types we can marshal
    let header := ((cmd.getArg 1).getStr?).getD "_"
    let isPure := !(cmd.getArg 2).isNone
    -- (9i) opt-outs: `(no_auto)`, `(skip := "names")`
    let opts := (cmd.getArg 3).args
    let noAuto := opts.any (·.args.size == 3)
    let skips := opts.toList.flatMap fun o => match (o.getArg 3).getStr? with
      | some str => (str.splitOn " ").filter (· ≠ "")
      | none => []
    match s.cHeaders header with
    | none => report .error cmd.info s!"{header} was not preprocessed (run through `wiz check` or `wiz run`)"
    | some src =>
      let tyOf (k : RVal.FKind) (st : CommandState R) : Term R := match k with
        | .k 'n' => .const "Nat" []
        | .k 'f' => .const "Float64" []
        | .k 's' => .const "String" []
        | .k 'b' => .const "Bool" []
        | .k 'y' => .const "Bytes" []
        | .k 'p' => .const "_" []
        | .struct c h fs =>
          let key := s!"cstruct:{(RVal.FKind.struct c h fs).toKey}"
          .const (((st.builtins.find? (·.1 == key)).map (·.2)).getD "_") []
        | _ => .unit 1
      let w : Term R := .qlit QuantitySyntax.explicitDefault
      let (funcs, structs) := FFI.parseHeaderFull src
      -- glue code may call these, and needs the header
      let usable := funcs.toList.filterMap fun f => do
        if f.variadic then none
        let ps ← f.params.mapM FFI.GTy.ofC
        pure (f.name, ps, ← FFI.GTy.ofC f.ret)
      -- (a field glue can't use is `void`: it can't be read, and a local of the struct must be initialised)
      let hstructs := structs.toList.filterMap fun st => st.fields.map fun fs =>
        (st.spelling, fs.map fun (f, t) => (f, (FFI.GTy.ofC t).getD .void))
      let hstructs := hstructs.flatMap fun (sp, fs) => (sp, fs) :: (((structs.find? (·.spelling == sp)).map (·.aliases)).getD []).map (·, fs)
      modify fun s => { s with cFuncs := usable ++ s.cFuncs, cCode := s.cCode.push s!"#include <{header}>",
                               cStructs := hstructs ++ s.cStructs }
      let structOf (sp : String) : Option FFI.CStruct := structs.find? (·.spelling == sp)
      let spellings (sp : String) : List String := sp :: ((structOf sp).map (·.aliases)).getD []
      let skipped (sp : String) : Bool := (spellings sp).any skips.contains
      -- the Wiz name of a C struct: its typedef name if it has one
      let wizName (sp : String) : Name :=
        "C." ++ (match ((structOf sp).map (·.aliases)).getD [] with
          | a :: _ => a
          | [] => sp.replace "struct " "struct_")
      -- (9i) a C struct by value, as a Wiz structure: a `c_struct` declared for it, or one
      -- made here (`C.div_t`, `C.struct_timespec`) when every field can be marshalled
      let rec structFor (sp : String) (fuel : Nat) : StateM (CommandState R) (Option RVal.FKind) := do
        if fuel == 0 || noAuto || skipped (sp) then return none
        let st ← get
        let mine := st.builtins.find? fun (k, _) => k.startsWith "cstruct:" &&
          match RVal.FKind.parseOne (k.drop 8).toString.toList with
          | some (.struct c _ _, _) => (spellings sp).contains c
          | _ => false
        if let some (k, _) := mine then return (RVal.FKind.parseOne (k.drop 8).toString.toList).map (·.1)
        let some { fields := some fs, .. } := structOf sp | return none
        let mut lines : Array String := #[]
        for (f, t) in fs do
          let t := match t with | .const t => t | t => t
          let fty ← match t with
            | .int "_Bool" => pure (some "Bool")
            | .int _ => pure (some "Nat")
            | .float _ => pure (some "Float64")
            | .ptr (.int "char") | .ptr (.const (.int "char")) => pure (some "String")
            | .array (.int c) (some _) | .array (.const (.int c)) (some _) =>
              pure (if c == "char" || c == "unsigned char" || c == "signed char" then some "Bytes" else none)
            | .struct sp' => do
              match ← structFor sp' (fuel - 1) with
              | some k => pure ((← get).builtins.find? (·.1 == s!"cstruct:{k.toKey}") |>.map (·.2))
              | none => pure none
            | _ => pure none
          let some fty := fty | return none
          lines := lines.push s!"  {f} : {fty}"
        let text := s!"c_struct \"{sp}\" (header := \"{header}\") {wizName sp} where\n{"\n".intercalate lines.toList}\n"
        let st ← get
        let some (stx, _) := (parseCommand text.toList.toArray st.tables 0).toOption | return none
        let n0 := st.messages.size
        elabCommand stx
        let st' ← get
        if (st'.messages.extract n0 st'.messages.size).any (·.severity == .error) then
          -- (a field name Wiz can't take, say): leave the struct out
          set { st' with messages := st'.messages.extract 0 n0 }
          return none
        let k := st'.builtins.find? fun (k, x) => x == wizName sp && k.startsWith "cstruct:"
        return k.bind fun (k, _) => (RVal.FKind.parseOne (k.drop 8).toString.toList).map (·.1)
      -- (9i) a pointer to a struct (or to an opaque typedef): a foreign type, the user's
      -- (`foreign_type T (c := "FILE")`) or one made here (no finalizer)
      let ptrFor (sp : String) : StateM (CommandState R) (Option Name) := do
        if noAuto || skipped sp then return none
        let st ← get
        if let some (_, n) := st.builtins.find? fun (k, _) => k.startsWith "ctype:" && (spellings sp).contains (k.drop 6).toString then
          return some n
        let n := wizName sp
        if st.foreignTypes.any (·.1 == n) then return some n
        if st.globals.contains n then return none
        match addDeclSorted st.globals { name := n, type := .sort 1, value := none } with
        | .ok g =>
          let key := s!"ctype:{sp}"
          modify fun s => { s with globals := { g with builtins := (key, n) :: g.builtins }, builtins := (key, n) :: s.builtins,
                                   foreignTypes := (n, "") :: s.foreignTypes }
          return some n
        | .error _ => return none
      let rec kindOf (t : FFI.CType) (isResult : Bool) : StateM (CommandState R) (Option (RVal.FKind × Option Name)) := match t with
        | .const t => kindOf t isResult
        | .int "_Bool" => pure (some (.k 'b', none))
        | .int _ => pure (some (.k 'n', none))
        | .float _ => pure (some (.k 'f', none))
        | .void => pure (if isResult then some (.k 'v', none) else none)
        | .struct sp => do pure ((← structFor sp 8).map (·, none))
        | .ptr t => match t with
          | .int "char" | .const (.int "char") => pure (some (.k 's', none))
          | .struct sp | .const (.struct sp) => do pure ((← ptrFor sp).map fun n => (RVal.FKind.k 'p', some n))
          | _ => pure none
        | _ => pure none
      -- (9i) a read-only buffer and its length (`const void *buf, size_t n`): `Bytes`
      let lenNames := ["n", "__n", "len", "__len", "nbytes", "__nbytes", "length", "__length"]
      let isBuf (t : FFI.CType) : Bool := match t with
        | .ptr (.const .void) | .ptr (.const (.int "unsigned char")) => true
        | _ => false
      for f in funcs do
        let name : Name := "C." ++ f.name
        if f.variadic || (← get).globals.contains name || skips.contains f.name then continue
        -- the parameters, with buffers and their lengths as one
        let names := f.paramNames ++ List.replicate (f.params.length - f.paramNames.length) ""
        let arr := (f.params.zip names).toArray
        let mut ps : Array (Option FFI.CType) := #[]
        let mut i := 0
        while i < arr.size do
          let t := arr[i]!.1
          let isLen := match arr[i + 1]? with
            | some (l, ln) => (match l with | .int _ | .const (.int _) => true | _ => false) && lenNames.contains ln
            | none => false
          if !noAuto && isBuf t && isLen then
            ps := ps.push none; i := i + 2
          else
            ps := ps.push (some t); i := i + 1
        let mut ks : Array (RVal.FKind × Option Name) := #[]
        let mut ok := true
        for p in ps do
          match p with
          | none => ks := ks.push (.k 'y', none)
          | some t => match ← kindOf t false with
            | some k => ks := ks.push k
            | none => ok := false; break
        if !ok then continue
        let some (rk, rn) ← kindOf f.ret true | continue
        let st ← get
        let ty1 (k : RVal.FKind × Option Name) : Term R := match k.2 with
          | some n => .const n []
          | none => tyOf k.1 st
        let res := if isPure then ty1 (rk, rn) else .app (.const "IO" []) (ty1 (rk, rn))
        -- (9i) a foreign pointer result gets its type's finalizer (`foreign_type … (c := …)`)
        let fin := match rn with
          | some n => (List.lookup n (st.foreignTypes : List (Name × String))).getD ""
          | none => ""
        let ty := ks.toList.foldr (fun k acc => .pi "_" .default w (ty1 k) acc none) res
        let key : Name := s!"extern:{f.name}:{String.join (ks.toList.map (·.1.toKey))}:{rk.toKey}:{if isPure then "pure" else "io"}:{header}:{fin}"
        match addDeclSorted st.globals { name, type := ty, value := none } with
        | .ok g => modify fun s => { s with builtins := (key, name) :: s.builtins,
                                            globals := { g with builtins := (key, name) :: g.builtins } }
        | .error e => reportKernel cmd.info (name) e
  | "command.glue" =>
    -- a foreign function defined by checked C code
    let name := ((cmd.getArg 1).getId?).getD "_"
    let binders := (cmd.getArg 2).args
    let body := ((cmd.getArg 6).getStr?).getD ""
    if s.globals.contains name then reportDup (cmd.getArg 1).info name
    else
      let elabTy := runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
        (elabDeclTerms binders (some (cmd.getArg 4)) none cmd.info) []
      match elabTy with
      | .error e => reportErr e
      | .ok (ty, _) =>
        let names := (binders.flatMap Elab.binderViews).toList.map (·.name)
        let kind (t : Term R) : Option RVal.FKind := match t with
          | .unit _ => some (.k 'v')
          | t => match (Term.spine t).1 with
            | .const "Nat" _ => some (.k 'n') | .const "UInt64" _ => some (.k 'u') | .const "Float64" _ => some (.k 'f')
            | .const "String" _ => some (.k 's') | .const "Bool" _ => some (.k 'b')
            | .const n _ => if s.foreignTypes.any (·.1 == n) then some (.k 'p') else structKind? n
            | _ => none
        let rec gparams : Term R → List (Term R) × Term R
          | .pi _ _ _ A B _ => let (ps, r) := gparams B; (A :: ps, r)
          | t => ([], t)
        let (ps, res) := gparams ty
        let (io, res) := match Term.spine res with
          | (.const "IO" _, [A]) => (true, A)
          | _ => (false, res)
        match ps.mapM kind, kind res with
        | some ks, some rk =>
          if names.length != ks.length then report .error cmd.info "glue: every parameter needs a name" else
          let gty (k : RVal.FKind) : FFI.GTy := match k with
            | .k 'f' => .dbl | .k 's' => .str | .k 'v' => .void | .k 'p' => .ptr | .struct c _ _ => .struct c | _ => .int
          let cty (k : RVal.FKind) : String := match k with
            | .k 'f' => "double" | .k 's' => "const char *" | .k 'v' => "void" | .k 'b' => "int" | .k 'p' => "void *"
            | .struct c _ _ => c | _ => "uint64_t"
          let pairs := (names.zip ks).filter (·.2 != .k 'v')
          -- (9i) the structs in scope: the `c_struct`s (their declared fields), and the headers'
          let declared := s.builtins.filterMap fun (key, _) =>
            if !key.startsWith "cstruct:" then none else
            match RVal.FKind.parseOne (key.drop 8).toString.toList with
            | some (.struct c _ fs, _) => some (c, fs.filterMap fun (f, k) => match k with
                | .k 'e' | .k 'y' => none
                | k => some (f, gty k))
            | _ => none
          match FFI.checkGlue body (pairs.map fun (x, k) => (x, gty k)) s.cFuncs (gty rk) (s.cStructs ++ declared) with
          | .error e => report .error (cmd.getArg 6).info s!"glue: {e}"
          | .ok () =>
            let cname := "wiz_glue_" ++ ((C.mangle name).drop 2).toString
            let cparams := ", ".intercalate (pairs.map fun (x, k) => s!"{cty k} {x}")
            let code := s!"static {cty rk} {cname}({if cparams.isEmpty then "void" else cparams}) \{
{body}
}"
            let key : Name := s!"extern:{cname}:{String.join (ks.map (·.toKey))}:{rk.toKey}:{if io then "io" else "pure"}::{finOf res}"
            match addDeclSorted s.globals { name, type := ty, value := none } with
            | .ok g =>
              modify fun s => { s with builtins := (key, name) :: s.builtins,
                                       globals := { g with builtins := (key, name) :: g.builtins },
                                       cCode := s.cCode.push code,
                                       cFuncs := (cname, pairs.map (gty ·.2), gty rk) :: s.cFuncs }
            | .error e => reportKernel cmd.info (name) e
        | _, _ =>
          let msg := "a glue function's arguments and result must be Nat, UInt64, Float64, String, Bool, Unit, a foreign type or a c_struct (the result may be in IO)"
          report .error cmd.info msg
  | "command.cStruct" =>
    -- (9i) a Wiz structure standing for a C struct, passed to and from C by value
    let name := ((cmd.getArg 3).getId?).getD "_"
    let header := if (cmd.getArg 2).isNone then "" else (((cmd.getArg 2).getArg 3).getStr?).getD ""
    let ctype := if (cmd.getArg 1).isNone then "wiz_s" ++ ((C.mangle name).drop 1).toString
      else (((cmd.getArg 1).getArg 0).getStr?).getD "_"
    let fields := (cmd.getArg 5).args
    if s.globals.contains name then reportDup (cmd.getArg 3).info name
    else if fields.isEmpty then report .error cmd.info "a c_struct needs at least one field"
    else if ctype.contains ':' || ctype.contains '|' || ctype.contains '<' || header.contains ':' || header.contains '|' then
      report .error cmd.info "c_struct: unexpected characters in the C type or header"
    else
      -- each field's type, on its own (fields may not depend on each other)
      let fieldKind (f : Syntax) : Except (SourceInfo × String) (String × RVal.FKind) := do
        let fname := ((f.getArg 2).getId?).getD "_"
        let q0 := !(f.getArg 1).isNone && ((f.getArg 1).getArg 0 |>.getArg 0).getNat? == some 0
        if q0 then return (fname, .k 'e')
        match runElab (macros := s.macros) (builtins := s.builtins) (classes := s.classes) (instances := s.instances) s.globals
            (elabDeclTerms #[] (some (f.getArg 4)) none f.info) [] with
        | .error e => throw (e.info, s!"c_struct field {fname}: {e.msg} (fields may not depend on other fields)")
        | .ok (ty, _) =>
          let k : Option RVal.FKind := match (Term.spine ty).1 with
            | .const "Nat" _ => some (.k 'n')
            | .const "UInt64" _ => some (.k 'u')
            | .const "Float64" _ => some (.k 'f')
            | .const "String" _ => some (.k 's')
            | .const "Bool" _ => some (.k 'b')
            -- a byte array `char f[N]`: its size comes from the header
            | .const "Bytes" _ => if header != "" then some (.k 'y') else none
            | .const n _ => if s.foreignTypes.any (·.1 == n) then some (.k 'p') else structKind? n
            | _ => none
          match k with
          | some k => pure (fname, k)
          | none => throw (f.info, s!"c_struct field {fname}: a field must be Nat, UInt64, Float64, String, Bool, a foreign type, another c_struct or (with a header) Bytes")
      match fields.toList.mapM fieldKind with
      | .error (info, e) => report .error info e
      | .ok kinds =>
        let parse (text : String) : Option Syntax := match parseCommand text.toList.toArray s.tables 0 with
          | .ok (stx, _) => some stx
          | .error _ => none
        match parse s!"structure {name} where" with
        | none => report .error cmd.info "internal error: c_struct"
        | some frame =>
          let n0 := (← get).messages.size
          elabCommand ((frame.setArg 6 (Syntax.mkNull fields)).setArg 7 (cmd.getArg 6))
          if (← get).messages.extract n0 (← get).messages.size |>.any (·.severity == .error) then return
          let k : RVal.FKind := .struct ctype header kinds
          let code := if header == "" then C.structDefinition ctype kinds else s!"#include <{header}>"
          modify fun s => { s with builtins := (s!"cstruct:{k.toKey}", name) :: s.builtins,
                                   globals := { s.globals with builtins := (s!"cstruct:{k.toKey}", name) :: s.globals.builtins },
                                   cCode := if s.cCode.contains code then s.cCode else s.cCode.push code }
  | "command.linkC" =>
    -- (9f) an unchecked C source file, compiled and linked with the program
    let rel := ((cmd.getArg 1).getStr?).getD ""
    let file ← match s.cSources with
      | none => pure (some rel)
      | some resolve => pure (resolve s.module rel)
    match file with
    | none => report .error (cmd.getArg 1).info s!"link_c: no file {rel} (paths are relative to the .wiz file)"
    | some f => unless s.linkC.contains f do modify fun s => { s with linkC := s.linkC.push f }
  | "command.linkLib" =>
    -- (9f) a library to link with (`-lNAME`)
    let lib := ((cmd.getArg 1).getStr?).getD ""
    if lib.isEmpty || lib.startsWith "-" || lib.any Char.isWhitespace then
      report .error (cmd.getArg 1).info s!"link_lib: give the library's name, as in link_lib \"m\" for -lm"
    else unless s.linkLibs.contains lib do modify fun s => { s with linkLibs := s.linkLibs.push lib }
  | "command.extern" =>
    -- an axiom, bound to a C function: the marshalling follows the Wiz type
    let cname := ((cmd.getArg 1).getStr?).getD "_"
    let header := if (cmd.getArg 2).isNone then "" else (((cmd.getArg 2).getArg 3).getStr?).getD ""
    let name := ((cmd.getArg 3).getId?).getD "_"
    if s.globals.contains name then reportDup (cmd.getArg 3).info name
    else
      let elabTy := runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
        (elabDeclTerms #[] (some (cmd.getArg 5)) none cmd.info) []
      match elabTy with
      | .error e => reportErr e
      | .ok (ty, _) =>
        let kind (t : Term R) : Option RVal.FKind := match t with
          | .unit _ => some (.k 'v')
          -- a type variable: any Wiz value, passed as it is
          | .var _ => some (.k 'w')
          | t => match (Term.spine t).1 with
            | .const "Nat" _ => some (.k 'n')
            | .const "UInt64" _ => some (.k 'u')
            | .const "Float64" _ => some (.k 'f')
            | .const "String" _ => some (.k 's')
            | .const "Bool" _ => some (.k 'b')
            | .const "Bytes" _ | .const "Array" _ | .const "Str" _ | .const "StrMap" _ => some (.k 'w')
            | .var _ => some (.k 'w')
            | .const n _ =>
              if s.foreignTypes.any (·.1 == n) then some (.k 'p')
              -- (9i) a structure declared with `c_struct`: the C struct, by value
              else if let some k := structKind? n then some k
              -- a Wiz data type (`UIntN w`): the value as it is, for runtime natives
              else if (s.globals.find? n).any (·.value.isSome) then some (.k 'w') else none
            | _ => none
        let rec params : Term R → List (Term R × Term R) × Term R
          | .pi _ _ q A B _ => let (ps, r) := params B; ((q, A) :: ps, r)
          | t => ([], t)
        let (ps, res) := params ty
        let (io, res) := match Term.spine res with
          | (.const "IO" _, [A]) => (true, A)
          | _ => (false, res)
        -- erased parameters (`{A : Type}`) are passed as ◾ and ignored
        -- a runtime native (`wiz_…`, runtime/) takes and returns any other Wiz value
        -- as it is: an opaque type's (`Chan p`, `MVar A`), a closure, a Σ pair (25a)
        let kind (t : Term R) : Option RVal.FKind :=
          match kind t with
          | some k => some k
          | none => if cname.startsWith "wiz_" then some (.k 'w') else none
        -- (9g) a function is passed as a callback: borrowed for the call, or, as a
        -- `Callback T`, owned by the C side (runtime natives take closures as they are)
        let native := cname.startsWith "wiz_"
        let callback? (A : Term R) : Option (Option RVal.FKind) :=
          if native then none else
          match A with
          | .pi .. => some ((ffiCallSig A).map (.callback false ·))
          | A => match Term.spine A with
            | (.const "Callback" _, [T]) => some ((ffiCallSig T).map (.callback true ·))
            | _ => none
        let pkind (qa : Term R × Term R) : Option RVal.FKind :=
          if qa.1 == .qlit 0 then some (.k 'e') else
          match callback? qa.2 with
          | some k => k
          | none => kind qa.2
        match ps.mapM pkind, kind res with
        | some ks, some rk =>
          if !io && ks.any (fun k => match k with | .callback _ c => c.io | _ => false) then
            report .error cmd.info "a foreign function that takes a callback in IO must be in IO itself"
          -- (linear-case stage 2) side effects live in `IO` (the world), never in an
          -- erasable or contentless result: a pure `… → Unit` call has nothing to keep, so
          -- erasure may drop it (inside an erased position, an erased closure, a dead `let`)
          else if resultContentless s.globals (eval s.globals [] ty) then
            report .error cmd.info ("a foreign function's result must carry something at run time: this one returns " ++
              "Unit, a proposition, a type or another value with no runtime content (outside IO), so compiled code " ++
              "may drop the call. A pure extern returns data; an effect belongs in IO (`… → IO Unit`)")
          else
          let key : Name := s!"extern:{cname}:{String.join (ks.map (·.toKey))}:{rk.toKey}:{if io then "io" else "pure"}:{header}:{finOf res}"
          match addDeclSorted s.globals { name, type := ty, value := none } with
          | .ok g => modify fun s => { s with builtins := (key, name) :: s.builtins,
                                              globals := { g with builtins := (key, name) :: g.builtins } }
          | .error e => reportKernel cmd.info (name) e
        | _, _ =>
          let msg := "a foreign function's arguments and result must be Nat, UInt64, Float64, String, Bool, Unit, a c_struct, a Wiz data type or a function of those (a callback; the result may be in IO)"
          report .error cmd.info msg
  | "command.export" =>
    -- (9g) a C symbol for a Wiz function: the inverse of `extern`
    let cname := ((cmd.getArg 1).getStr?).getD "_"
    let fStx := cmd.getArg 2
    let f := (fStx.getId?).getD "_"
    match s.globals.find? f with
    | none => reportC fStx.info s!"unknown declaration '{f}'" ErrorCode.unknownDeclaration
    | some d =>
      -- an optional type, which must be the definition's
      let ty? : Except (ElabError R) (Term R) :=
        if (cmd.getArg 3).isNone then pure d.type else do
          let (ty, _) ← runElab (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) s.globals
            (elabDeclTerms #[] (some ((cmd.getArg 3).getArg 1)) none cmd.info) []
          pure ty
      match ty? with
      | .error e => reportErr e
      | .ok ty =>
        if !d.levelParams.isEmpty then report .error fStx.info s!"{f} has universe parameters: only closed functions can be exported"
        else if !convTy s.globals #[] (eval s.globals [] d.type) (eval s.globals [] ty) then
          report .error (cmd.getArg 3).info s!"{f} has type {d.type.pretty [] (some s.globals)}, not {ty.pretty [] (some s.globals)}"
        else if !C.isCIdent cname then report .error (cmd.getArg 1).info s!"{cname} is not a C identifier"
        else if s.builtins.any (fun (k, _) => (RVal.ExternSig.ofExportKey? k).any (·.cname == cname)) then
          report .error (cmd.getArg 1).info s!"{cname} is exported already"
        else match ffiCallSig ty with
          | none =>
            report .error cmd.info "an exported function's arguments must be Nat, UInt64, Float64, String, Bool, a foreign pointer or a Wiz data type, and its result one of those (not a foreign pointer) or Unit, maybe in IO"
          | some c =>
            let key : Name := s!"export:{cname}:{String.ofList c.params}:{c.result}:{if c.io then "io" else "pure"}"
            modify fun s => { s with builtins := (key, f) :: s.builtins }
  | "command.attrMacro" =>
    let k := ((cmd.getArg 3).getId?).getD "_"
    let f := ((cmd.getArg 5).getId?).getD "_"
    let hasType (T : Name) := runElab s.globals do
      let (_, ty) ← Elab.infer {} (.node cmd.info "term.ident" #[cmd.getArg 5])
      let macroTy ← evalIn {} (.const T [])
      unifyAt {} cmd macroTy ty
    -- (HD8) a command macro expands one command into several
    let isCommandMacro := k.startsWith "command." && s.globals.contains "CommandMacro" &&
      (hasType "CommandMacro" matches .ok ())
    if isCommandMacro then
      modify fun s => { s with cmdMacros := (k, f) :: s.cmdMacros }
      remakeMetaCode
    else match hasType "Macro" with
    | .error e => report .error e.info s!"{f} is not a macro: {e.msg}"
    | .ok () =>
      modify fun s => { s with procMacros := (k, f) :: s.procMacros }
      remakeMetaCode
  | "command.appUnexpander" =>
    -- (11r) `app_unexpander c | `(term| $_ $x …) => `(term| …)`: printing notation for `c`
    let c := ((cmd.getArg 1).getId?).getD "_"
    let c := if s.globals.contains c then c else s.globals.resolve c
    let mut entries := #[]
    for alt in (cmd.getArg 2).args do
      let lhs := (alt.getArg 1).args[0]?.getD .missing
      let rhs := alt.getArg 3
      unless lhs.kind == "quote.term" && rhs.kind == "quote.term" do
        report .error alt.info "an unexpander rule is `| `(term| pattern) => `(term| notation)`"
        return
      let pat := ppNormalize [] (lhs.getArg 3)
      let arity ← match ppAppPattern? pat with
        | some (_, n) => pure n
        | none =>
          report .error alt.info "an unexpander's pattern is an application `$_ $x …` (or `$_`)"
          return
      -- the head is the constant, whatever the pattern calls it
      let pat := match pat with
        | .node i "term.app" #[_, args] => .node i "term.app" #[Tagged.identStx c, args]
        | _ => Tagged.identStx c
      entries := entries.push ({ head := c, arity, how := .rule pat (ppNormalize [] (rhs.getArg 3)) } : UnexpanderEntry)
    -- the first alternative is tried first
    modify fun s => CommandState.refreshPP { s with ppUser := entries.toList ++ s.ppUser }
  | "command.attrUnexpander" =>
    -- (11r) `attribute [app_unexpander c] f` with `f : Unexpander` (a `Macro`)
    let c := ((cmd.getArg 3).getId?).getD "_"
    let c := if s.globals.contains c then c else s.globals.resolve c
    let f := ((cmd.getArg 5).getId?).getD "_"
    let ok := runElab s.globals do
      let (_, ty) ← Elab.infer {} (.node cmd.info "term.ident" #[cmd.getArg 5])
      let macroTy ← evalIn {} (.const "Macro" [])
      unifyAt {} cmd macroTy ty
    match ok with
    | .error e => report .error e.info s!"{f} is not an unexpander (a `Syntax → MacroM Syntax`): {e.msg}"
    | .ok () =>
      unless s.globals.contains c do
        report .error (cmd.getArg 3).info s!"unknown constant {c}"
        return
      modify fun s => CommandState.refreshPP { s with ppUser := { head := c, arity := 0, how := .fn f } :: s.ppUser }
  | "command.setOption" =>
    -- (11r) `set_option pp.notation false` (`pp.all true`: the same)
    let opt := ((cmd.getArg 1).getId?).getD ""
    let v : Option Bool := match cmd.getArg 2 with
      | .ident _ "true" => some true
      | .ident _ "false" => some false
      | _ => none
    let set (b : Bool) : StateM (CommandState R) Unit :=
      modify fun s => { s with globals := { s.globals with pp := { s.globals.pp with useNotation := b } } }
    match opt, v with
    | "pp.notation", some b => set b
    | "pp.all", some b => set !b
    | "pp.notation", none | "pp.all", none => report .error (cmd.getArg 2).info "expected `true` or `false`"
    | o, _ => report .error (cmd.getArg 1).info s!"unknown option {o} (there are pp.notation and pp.all)"
  | "command.attrTactic" =>
    let k := ((cmd.getArg 3).getId?).getD "_"
    let f := ((cmd.getArg 5).getId?).getD "_"
    let ok := runElab s.globals do
      let (_, ty) ← Elab.infer {} (.node cmd.info "term.ident" #[cmd.getArg 5])
      let tacticTy ← evalIn {} (.const "Tactic" [])
      unifyAt {} cmd tacticTy ty
    match ok with
    | .error e => report .error e.info s!"{f} is not a tactic: {e.msg}"
    | .ok () =>
      modify fun s => { s with tactics := (k, f) :: s.tactics }
      remakeMetaCode
  | "command.attrImplementedBy" =>
    -- `attribute [implemented_by g] f`: compiled code runs `g` wherever it would run `f`
    -- (erasure takes `g`'s code for `f`); the kernel and proofs keep `f`'s definition. So
    -- `g` must have `f`'s type (up to conversion), at the same universe levels.
    let impl := ((cmd.getArg 3).getId?).getD "_"
    let getStx? := (cmd.getArg 4).args[0]?
    let fStx := cmd.getArg 6
    let f := (fStx.getId?).getD "_"
    -- the constructor's erased code `λ…. ⟨t f₀ … fₙ₋₁⟩`, with one runtime field `var j`
    let ctorShape? (d : Decl R) : Option (Nat × Nat × Nat × Nat × Nat) := do
      let .ok e := eraseDecl s.globals d | none
      let rec peel : ETerm → Nat × ETerm
        | .lam _ b => let (n, b) := peel b; (n + 1, b)
        | t => (0, t)
      let (n, .obj t fs) := peel e | none
      let live := (List.range fs.size).filter fun k => !(fs[k]! matches .erased)
      let [r] := live | none
      let .var j := fs[r]! | none
      pure (t, fs.size, r, n, n - 1 - j)
    -- the name of the `μ` type at the end of a Π type, and the number of its binders
    let rec target (g : Globals R) (lvl : Nat) : Val R → Nat → Option Name × Nat
      | ty, fuel + 1 => match whnf ty with
        | .pi _ _ _ _ cod _ => let (T, n) := target g (lvl + 1) (Closure.inst g cod (.var lvl)) fuel; (T, n + 1)
        | .mu _ _ _ _ _ (some (T, _, _)) => (some T, 0)
        | _ => (none, 0)
      | _, 0 => (none, 0)
    let rec lastDom (g : Globals R) (lvl : Nat) : Val R → Nat → Option Name
      | ty, fuel + 1 => match whnf ty with
        | .pi _ _ _ dom cod _ => match whnf (Closure.inst g cod (.var lvl)) with
          | .pi .. => lastDom g (lvl + 1) (Closure.inst g cod (.var lvl)) fuel
          | _ => match whnf dom with
            | .mu _ _ _ _ _ (some (T, _, _)) => some T
            | _ => none
        | _ => none
      | _, 0 => none
    match s.globals.find? f, s.globals.find? impl with
    | none, _ => reportC fStx.info s!"unknown declaration '{f}'" ErrorCode.unknownDeclaration
    | _, none => reportC (cmd.getArg 3).info s!"unknown declaration '{impl}'" ErrorCode.unknownDeclaration
    | some df, some di =>
      if let some getStx := getStx? then
        -- `attribute [implemented_by mk get] T.mk` (stage 22d): values of `T` are native.
        -- `mk` builds one from the constructor's arguments (it has the constructor's
        -- type), `get` reads its one runtime field back; the kernel keeps the model.
        let get := (getStx.getId?).getD "_"
        let g := s.globals
        let (T?, _) := target g 0 (eval g [] df.type) 1000
        match s.globals.find? get, ctorShape? df, T? with
        | none, _, _ => reportC getStx.info s!"unknown declaration '{get}'" ErrorCode.unknownDeclaration
        | _, none, _ | _, _, none =>
          report .error fStx.info s!"{f} is not a constructor with exactly one runtime field"
        | some dg, some (tag, nfields, r, mkArity, p), some T =>
          let us := df.levelParams.map Level.param
          if di.levelParams.length != df.levelParams.length || dg.levelParams.length != df.levelParams.length then
            report .error (cmd.getArg 3).info s!"{impl} and {get} must have {f}'s universe parameters"
          else if !convTy g #[] (eval g [] df.type) (eval g [] (di.type.instLevels di.levelParams us)) then
            report .error (cmd.getArg 3).info
              s!"{impl} can't implement {f}: its type {di.type.pretty [] (some s.globals)} is not {f}'s type {df.type.pretty [] (some s.globals)}"
          else if lastDom g 0 (eval g [] dg.type) 1000 != some T then
            report .error getStx.info s!"{get} must take a value of {T} as its last argument"
          else if (reprOf? s.builtins T).isSome then
            report .error fStx.info s!"{T} already has a native representation"
          -- (22k) found by the seal, so `T` has no look-alikes; and built only in its
          -- module (R5: the module keeps the invariant the natives rely on)
          else if !s.builtins.any (·.1 == sealKey T) then
            report .error fStx.info s!"a native representation needs `sealed inductive {T}`: a look-alike of an unsealed type is the same type"
          else if (s.globals.privates.get? f) != some s.module then
            report .error fStx.info s!"a native representation needs a private constructor (`| private {(f.splitOn ".").getLast!} …`): {T}'s module keeps the invariant its natives rely on"
          else
            let (_, getArity) := target g 0 (eval g [] dg.type) 1000
            let key := ReprInfo.key T { mkImpl := impl, getImpl := get, tag, nfields, r, mkArity, p, getArity }
            modify fun s => { s with builtins := (key, f) :: s.builtins,
                                     globals := { s.globals with builtins := (key, f) :: s.globals.builtins } }
      else if s.builtins.any (fun (k, x) => x == f && k != inlineKey && !k.startsWith RVal.exportPrefix) then
        report .error fStx.info s!"{f} is a builtin or foreign function: it already has an implementation"
      else if f == impl then report .error (cmd.getArg 3).info s!"{f} can't be implemented by itself"
      -- (linear-case stage 2) as for `extern`: an implementation is where an effect could
      -- hide, and a result of type Unit (or a type) carries nothing erasure must keep
      -- (a proposition is allowed: the implementation is a proof, erased as well)
      else if resultContentless s.globals (eval s.globals [] df.type) && !resultProp s.globals (eval s.globals [] df.type) then
        report .error fStx.info s!"{f}'s result has no runtime content (Unit, a type, …): its implementation could only matter through an effect, which compiled code may drop; return IO or data instead"
      else if df.levelParams.length != di.levelParams.length then
        report .error (cmd.getArg 3).info
          s!"{impl} has {di.levelParams.length} universe parameters, {f} has {df.levelParams.length}"
      else
        let us := df.levelParams.map Level.param
        let tyI := di.type.instLevels di.levelParams us
        let g := s.globals
        if !convTy g #[] (eval g [] df.type) (eval g [] tyI) then
          report .error (cmd.getArg 3).info
            s!"{impl} can't implement {f}: its type {tyI.pretty [] (some s.globals)} is not {f}'s type {df.type.pretty [] (some s.globals)}"
        else
          -- (the kernel checks the constant at `f`'s type too: no implementation is
          -- stored unchecked)
          match setImpl s.globals f (.const impl us) with
          | .ok g' => modify fun s => { s with globals := g' }
          | .error e => report .error (cmd.getArg 3).info s!"kernel rejected {impl} as the implementation of {f}: {e}"
  | "command.attrInline" =>
    -- `attribute [inline] f` (22i): compiled code substitutes `f`'s body where `f` is
    -- applied to all its arguments, so a lambda argument is applied directly (no
    -- closure). Registered as the builtin key `inline`; the kernel doesn't see it.
    let fStx := cmd.getArg 4
    let f := (fStx.getId?).getD "_"
    match s.globals.find? f with
    | none => reportC fStx.info s!"unknown declaration '{f}'" ErrorCode.unknownDeclaration
    | some d =>
      if d.value.isNone then report .error fStx.info s!"{f} has no definition to inline"
      else if s.builtins.any (fun (k, x) => x == f && !k.startsWith RVal.exportPrefix) then
        report .error fStx.info s!"{f} is a builtin, foreign or inline function already"
      else
        modify fun s => { s with builtins := s.builtins ++ [(inlineKey, f)],
                                 globals := { s.globals with builtins := s.globals.builtins ++ [(inlineKey, f)] } }
  | "command.attrDefaultInstance" =>
    -- (7f) `attribute [default_instance p] i`: when instance problems are stuck, the
    -- instance `i` is tried on those of its class, highest `p` (default 1000) first
    -- (`applyDefaultInstance`)
    let prio := if (cmd.getArg 3).isNone then 1000 else
      (((if (cmd.getArg 3).isOfKind "null" then (cmd.getArg 3).getArg 0 else cmd.getArg 3).getNat?).getD 1000)
    let iStx := cmd.getArg 5
    let i := s.globals.resolve ((iStx.getId?).getD "_")
    match s.instances.find? fun j => j.name == i && !j.isDefault with
    | none => report .error iStx.info s!"{i} is not an instance"
    | some j => modify fun s => { s with instances := s.instances.push { j with priority := prio, isDefault := true } }
  | "command.attrBinop" =>
    -- (7f) `attribute [binop] C.f`: numeral operands of `C.f` take the type of the others
    let fStx := cmd.getArg 4
    let f := s.globals.resolve ((fStx.getId?).getD "_")
    match s.classes.find? fun c => c.fields.any fun x => c.name ++ "." ++ x == f with
    | none => report .error fStx.info s!"{f} is not a method of a class"
    | some c => modify fun s => { s with classes := s.classes.map fun c' => if c'.name == c.name then { c' with binop := true } else c' }
  | "command.attrDeriver" =>
    let C := ((cmd.getArg 3).getId?).getD "_"
    let f := ((cmd.getArg 5).getId?).getD "_"
    let ok := runElab s.globals do
      let (_, ty) ← Elab.infer {} (.node cmd.info "term.ident" #[cmd.getArg 5])
      let deriverTy ← evalIn {} (.const "Deriver" [])
      unifyAt {} cmd deriverTy ty
    match ok with
    | .error e => report .error e.info s!"{f} is not a deriver: {e.msg}"
    | .ok () =>
      modify fun s => { s with derivers := (C, f) :: s.derivers }
      remakeMetaCode
  | "command.deriving" =>
    -- `deriving instance C₁, C₂ for T₁, T₂`
    let ids (stx : Syntax) := stx.args.toList.filter (·.getId?.isSome)
    for T in ids (cmd.getArg 4) do
      for C in ids (cmd.getArg 2) do
        derive (C.getId?.getD "_") (s.globals.resolve (T.getId?.getD "_")) C.info
  | "command.erase" =>
    let n := ((cmd.getArg 1).getId?).getD "_"
    match s.globals.find? n with
    | none => reportC cmd.info s!"unknown declaration '{n}'" ErrorCode.unknownDeclaration
    | some d => match eraseDecl s.globals d with
      | .ok e => report .info cmd.info s!"{n} := {e}"
      | .error err => report .error cmd.info s!"cannot erase {n}: {err}"
  | "command.eval" =>
    -- elaborate, erase, run, and read the result back using its type
    let r ← withTraces <| runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals do
      let (t, _) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      ensureNoMVars t cmd.info
      pure t
    match r with
    | .error e => reportErr e
    | .ok t =>
      let ctx : Ctx R := { globals := s.globals, proof := true }
      let result := do
        let (ty, _) ← Wiz.infer ctx t
        let e ← eraseTop ctx t ty
        let (code, failed) ← compileReachableE s.globals s.builtins (e.globals.toList) (externImpls := false)
        pure (ty, e, code, failed)
      match result with
      | .ok (_, _, _, (n, err) :: _) =>
        -- the interpreter can't fail: running a stub would print a wrong value
        report .error cmd.info s!"cannot run this: cannot erase {n}: {err}"
      | .ok (ty, e, code, []) =>
        let v := run code [] e
        report .info cmd.info ((readback s.globals s.builtins ty v).pretty [] (some s.globals))
      | .error err => report .error cmd.info s!"cannot run this: {err}"
  | "command.run" =>
    -- like `#eval`, but through the IR, with reference counting, on a checked heap
    let r ← withTraces <| runElabH (macros := s.macros) (builtins := s.builtins) (procMacros := s.procMacros) (tactics := s.tactics) (metaCode := s.metaCode) (classes := s.classes) (instances := s.instances) (termInfo := s.termInfo) s.globals do
      let (t, _) ← Elab.infer {} (cmd.getArg 1)
      solveSortConstraints
      let t ← zonk 0 t
      ensureNoMVars t cmd.info
      pure t
    match r with
    | .error e => reportErr e
    | .ok t =>
      let ctx : Ctx R := { globals := s.globals, proof := true }
      let result : Except String (VTy R × RVal) := do
        let (ty, _) ← (Wiz.infer ctx t).mapError toString
        let e ← (eraseTop ctx t ty).mapError toString
        let code ← (compileReachable s.globals s.builtins e.globals.toList (externImpls := false)).mapError toString
        let decls ← IR.lowerProgram code e
        let (v, _) ← IR.runProgram (IR.optimizeProgram decls)
        pure (ty, v)
      match result with
      | .ok (ty, v) => report .info cmd.info ((readback s.globals s.builtins ty v).pretty [] (some s.globals))
      | .error err => report .error cmd.info s!"#run: {err}"
  | "command.ir" =>
    let n := ((cmd.getArg 1).getId?).getD "_"
    let result : Except String (Array IR.Decl) := do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n)
    match result with
    | .ok decls =>
      -- (not the owned wrappers for closures, stage 8e)
      let mine := (IR.optimizeProgram decls).filter fun d =>
        d.name == n || (d.name.startsWith (n ++ ".") && !d.name.endsWith "._owned")
      report .info cmd.info ("\n".intercalate (mine.toList.map (·.toString)))
    | .error err => report .error cmd.info s!"#ir: {err}"
  | "command.syntax" | "command.declareSyntaxCat" =>
    match updateTables s.tables cmd with
    | .ok tables =>
      -- (11q) where the new kinds and categories were declared
      let site := (cmd.info, s.module)
      let kindSites := tables.kinds.fold (init := s.kindSites) fun m k _ =>
        if s.tables.kinds.contains k then m else m.insert k site
      let catSites := tables.cats.fold (init := s.catSites) fun m c _ =>
        if s.tables.cats.contains c then m else m.insert c site
      -- (11r) the atoms as written, for printing the new kinds
      let raw := stxAtoms (cmd.getArg 4)
      let rawAtoms := tables.kinds.fold (init := s.rawAtoms) fun m k _ =>
        if s.tables.kinds.contains k || raw.isEmpty then m else m.insert k raw
      modify fun s => { s with tables, kindSites, catSites, rawAtoms }
      modify CommandState.refreshPP
    | .error msg => report .error cmd.info msg
  | "command.macroRules" =>
    for alt in (cmd.getArg 1).args do
      let lhs := (alt.getArg 1).args[0]?.getD .missing
      let rhs := alt.getArg 3
      unless lhs.kind.startsWith "quote." && rhs.kind.startsWith "quote." do
        report .error alt.info "a macro rule is `| `(cat| pattern) => `(cat| template)`"
        return
      let pattern := lhs.getArg 3
      let rule : MacroRule := { kind := pattern.kind, pattern, template := rhs.getArg 3, site := alt.info, module := s.module }
      modify fun s => { s with macros := rule :: s.macros }
    modify CommandState.refreshPP
  | "command.notation" | "command.infix" =>
    match notationRule s.tables cmd with
    | .ok (tables, rule) =>
      let raw := if cmd.isOfKind "command.infix" then ((cmd.getArg 3).getStr?).toArray
        else (cmd.getArg 2).args.filterMap fun it => (it.getArg 0).getStr?
      modify fun s => { s with tables, macros := { rule with module := s.module } :: s.macros,
                               kindSites := s.kindSites.insert rule.kind (cmd.info, s.module),
                               rawAtoms := s.rawAtoms.insert rule.kind raw }
      modify CommandState.refreshPP
    | .error e => report .error cmd.info e
  | k =>
    -- user-defined command syntax: expand a macro, if one applies
    -- (11q) what expanded a command the user wrote
    let recordExp (h : SyntaxHandler) (out : Option Syntax) : StateM (CommandState R) Unit :=
      if cmd.info.stop > 0 && !cmd.info.synthetic then
        modify fun s => { s with infos := s.infos.push (.expansion cmd.info k h out) }
      else pure ()
    match Elab.expandMacroRule? s.macros cmd s.nextScope with
    | some (cmd', r) =>
      modify fun s => { s with nextScope := s.nextScope + 1 }
      recordExp (.rule r.site r.module) (some cmd')
      elabCommand cmd'
    | none =>
      -- (HD8) a command macro, written in Wiz
      match s.cmdMacros.lookup k with
      | some f =>
        recordExp (.fn "command macro" f) none
        let r := match metaCodeFor f with
          | .ok code => Elab.runCommandMacro code f cmd s.nextScope (macroEnv s.globals)
          | .error e => (#[], .error e)
        for t in r.1 do report .info cmd.info t
        match r.2 with
        | .error e => report .error cmd.info s!"macro {f}: {e}"
        | .ok (cmds, next) =>
          modify fun s => { s with nextScope := next }
          for c in cmds do
            -- located output (Elab/ProcMacro.lean): diagnostics and generated source,
            -- placed at a node of the macro's input
            let info := Elab.pathInfo cmd (c.getArg 0)
            -- marked source (Elab/ProcMacro.lean, "Positions inside generated source")
            let (text, spans) := Elab.stripMarks (Elab.atomText (c.getArg 1))
            match c.kind with
            | "macro.error" => report .error info text
            | "macro.info" => report .info info text
            | "macro.source" =>
              let chars := text.toList.toArray
              let mut pos := 0
              let errorsBefore : Nat := ((← get).messages.filter (·.severity == .error)).size
              for _ in [0:chars.size + 1] do
                if skipWs chars pos ≥ chars.size then break
                match parseCommand chars (← get).tables pos with
                | .ok (stx, stop) =>
                  let before := (← get).globals.order.size
                  elabCommand (Elab.locateMarked cmd info spans stx)
                  -- what it declares is declared at the input node (go to definition
                  -- inside the block; the frontend keeps these over the whole command)
                  if !spans.isEmpty then
                    modify fun s =>
                      let added := s.globals.order.extract before s.globals.order.size
                      { s with declSites := added.foldl (fun m n => m.insert n (info, s.module)) s.declSites }
                  pos := stop
                | .error e =>
                  report .error info s!"macro {f}: the generated source does not parse: {e.render text}\n{text}"
                  break
              let errorsAfter : Nat := ((← get).messages.filter (·.severity == .error)).size
              if errorsAfter > errorsBefore then
                report .error info s!"macro {f}: the generated source was rejected (an internal error of the macro, unless reported above); it is:\n{text}"
            | _ => elabCommand c
      | none => match s.procMacros.lookup k with
        | some f =>
          -- a `Macro` for a command kind: one command
          recordExp (.fn "macro" f) none
          let r := match metaCodeFor f "Macro.run" with
            | .ok code =>
              let (tr, r) := Elab.runProcMacro code f cmd s.nextScope (macroEnv s.globals)
              (tr, r.map fun (out, next) => (#[out], next))
            | .error e => (#[], .error e)
          elabExpansion s!"macro {f}" r cmd.info
        | none => report .error cmd.info s!"the command syntax {k} has no meaning: no `macro_rules` (or `attribute [macro {k}] f`) for it is in scope (if one is defined above, it was rejected: see its error)"

end Wiz
