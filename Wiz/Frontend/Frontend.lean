import Wiz.Elab.Command
import Wiz.Module
import Wiz.Rig.Instances
import Wiz.Parser.DocComment

/-!
# The frontend

Parse a command, elaborate it, repeat. The parser tables come from the command state,
so a `syntax` command affects everything after it.
-/

namespace Wiz

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-! ## Modules in isolation, once per process

Nearly every file starts with `import Prelude`, and `runFrontend` elaborates each import
in isolation (below). A process that runs the frontend many times (the language server,
on every document it opens; a test that checks several files) would elaborate the
Prelude again each time, so the isolated results are kept, per process, under a key that
determines them:

    key = hash(the base state's settings, text of M, M's C headers, key of each import of M)

The base state must be an initial one (`pristine`, with no declarations, imports or info
tree), so that it is determined by its settings: the loader and the C headers enter the
key through the texts they give, and the rest (`termInfo`, the kernel options, …) is
hashed. A module whose imports run in a cycle is not kept (its errors depend on where
the cycle was entered). Since the key determines what the module elaborates to, a hit
gives what elaborating again would: `runFrontend` stays a function of its arguments,
although it reads and writes a global table (an `IO.Ref`, through `unsafeBaseIO`, behind
the opaque `isoGet`/`isoPut`). The table is per quantity rig (`IsoCache`): it holds
states of one `R`, and rigs without an instance are not cached. -/

/-- A module elaborated in isolation: its state, and its errors. -/
structure Isolated (R : Type) where
  state : CommandState R
  errs : Array Msg

instance : Inhabited (Isolated R) := ⟨{ state := {}, errs := #[] }⟩

/-- Where this process keeps the modules elaborated in isolation, for quantities `R`. -/
class IsoCache (R : Type) where
  ref : Option (IO.Ref (Std.HashMap UInt64 (Isolated R)))

instance (priority := low) : IsoCache R := ⟨none⟩

initialize isoCacheZOM : IO.Ref (Std.HashMap UInt64 (Isolated ZeroOneMany)) ← IO.mkRef {}

instance : IsoCache ZeroOneMany := ⟨some isoCacheZOM⟩

/-- How many entries the table keeps (it starts again when full). -/
def isoCacheSize : Nat := 256

private unsafe def isoGetImpl (ref : IO.Ref (Std.HashMap UInt64 (Isolated R))) (k : UInt64) : Option (Isolated R) :=
  unsafeBaseIO (do pure ((← ref.get).get? k))

/-- The module kept under `k`, if any. -/
@[implemented_by isoGetImpl]
opaque isoGet (ref : IO.Ref (Std.HashMap UInt64 (Isolated R))) (k : UInt64) : Option (Isolated R)

private unsafe def isoPutImpl (ref : IO.Ref (Std.HashMap UInt64 (Isolated R))) (k : UInt64) (v : Isolated R) : Isolated R :=
  unsafeBaseIO (do
    ref.modify fun m => (if m.size ≥ isoCacheSize then {} else m).insert k v
    pure v)

/-- Keep `v` under `k`; returns `v` (the caller uses the result, so the write happens). -/
@[implemented_by isoPutImpl]
opaque isoPut (ref : IO.Ref (Std.HashMap UInt64 (Isolated R))) (k : UInt64) (v : Isolated R) : Isolated R

/-- The key of module `m` elaborated in isolation from `base` (see above), or `none` if
it is not to be kept: `base` is not an initial state, or `m`'s imports run in a cycle. -/
partial def isoKey (base : CommandState R) (m : Name) : Option UInt64 := do
  unless base.pristine && base.globals.order.isEmpty && base.imported.isEmpty && base.infos.isEmpty do none
  let g := base.globals
  -- (every option of `Globals` that a module's state depends on or carries)
  -- (and every field of `Globals` that is not data checked empty above: the kept state
  -- carries them to the importer, `pp.notation` included)
  unless g.decls.isEmpty && g.privates.isEmpty && g.opaques.isEmpty && g.declModule.isEmpty do none
  let ppKeys (m : List Name) : List Name := m.mergeSort (fun a b => decide (a ≤ b))
  let settings := hash (base.termInfo, base.nextScope, g.eager, g.predicativeProp, toString (repr g.regularity),
    toString (repr g.inertReg), g.builtins, g.unboxStructs, g.lazyProofs,
    -- (P2) the marker's requirement and the read-back budget decide what a module's
    -- proofs elaborate to and what it reports
    g.strictProofs, g.proofSteps, g.traceProofSteps,
    -- (27a) and whether `native_refl` may run, and how far
    base.trustNative, base.nativeFuel)
  let settings := mixHash settings (hash (g.assumed, g.quoteErasesProofs, g.pushCalls, g.strictPrivacy, g.module,
    g.pp.useNotation, ppKeys (g.pp.unexpanders.toList.map (·.1)), ppKeys (g.pp.formats.toList.map (·.1))))
  let (k, _) ← go [] m {}
  pure (mixHash settings k)
where
  go (stack : List Name) (m : Name) (memo : Std.HashMap Name UInt64) : Option (UInt64 × Std.HashMap Name UInt64) :=
    match memo.get? m with
    | some k => some (k, memo)
    | none =>
      if stack.contains m then none else
      match base.loader m with
      | none => some (hash ("unknown", m), memo)
      | some src => do
        -- (9f) the files a module links are resolved per run: not kept across runs
        if base.cSources.isSome && !(Module.cSourcesOf src).isEmpty then none
        let k₀ := mixHash (hash m) (hash src)
        let k₀ := (Module.headersOf src).foldl (fun k h => mixHash k (hash ((base.cHeaders h).getD ""))) k₀
        let (k, memo) ← (Module.importsOf src).foldlM (fun (k, memo) n => do
          let (kn, memo) ← go (m :: stack) n memo
          pure (mixHash k kn, memo)) (k₀, memo)
        pure (k, memo.insert m k)

/-! ## Doc comments (11s) -/

/-- The first identifier among a node's own arguments (a declaration's name). -/
def Syntax.firstIdent? (stx : Syntax) : Option Name :=
  stx.args.findSome? (·.getId?)

/-- The nodes of kind `k` in `stx` (not looking inside them). -/
partial def Syntax.nodesOfKind (k : Name) (stx : Syntax) : Array Syntax :=
  if stx.isOfKind k then #[stx] else stx.args.foldl (fun acc a => acc ++ a.nodesOfKind k) #[]

/-- Is `n` the declaration written `x` (or its private kernel name)? -/
def declIs (n x : Name) : Bool := n == x || n.endsWith ("._0." ++ x)

/-- What a command's declarations are, and their doc comments (`docCommentBefore`, at
the command, a constructor, a field). `added`: the names the command declared, in order.
A `mutual` block's commands each have their own; `private`, `partial`, `sealed` and
`local` keep the comment before them. -/
partial def declDocsOf (chars : Array Char) (cmd : Syntax) (added : Array Name)
    (m : Std.HashMap Name DeclDoc) : Std.HashMap Name DeclDoc :=
  let m := (go cmd (docCommentBefore chars cmd.info.start) "" m)
  -- what is left is the elaborator's own
  added.foldl (fun m n => if m.contains n then m else m.insert n { kind := "auxiliary" }) m
where
  go (c : Syntax) (doc : Option String) (pre : String) (m : Std.HashMap Name DeclDoc) : Std.HashMap Name DeclDoc :=
    let k := c.kind
    if k == "command.mutual" then
      c.args.foldl (fun m a => (a.args.foldl (fun m c => go c (docCommentBefore chars c.info.start) pre m)) m) m
    else if k == "command.private" || k == "command.sealed" || k == "command.local" || k == "command.partial" then
      let inner := c.args.back?.getD .missing
      let word := if k == "command.local" then "" else (k.drop 8).toString ++ " "
      go inner doc (pre ++ word) m
    else
      let kind := match (k.drop 8).toString with
        | "defEqns" => "def"
        | "foreignType" => "foreign type"
        | w => w
      let primary : Option Name := match c.firstIdent? with
        | some x => added.find? (declIs · x)
        | none => if k == "command.instance" then added.find? (!m.contains ·) else none
      match primary with
      | none => m
      | some p =>
        let m := m.insert p { kind := pre ++ kind, doc, start := c.info.start }
        -- constructors (`| c …`), and a structure's own (`where mk ::`)
        let m := (c.nodesOfKind "inductive.ctor").foldl (fun m ctor =>
          match ctor.firstIdent? with
          | some x => match added.find? (· == p ++ "." ++ x) with
            | some n => m.insert n { kind := "constructor", parent := some p, doc := docAt ctor, start := ctor.info.start }
            | none => m
          | none => m) m
        let m := (c.nodesOfKind "structure.where").foldl (fun m w =>
          match (w.args.findSome? fun a => a.firstIdent?) with
          | some x => match added.find? (· == p ++ "." ++ x) with
            | some n => m.insert n { kind := "constructor", parent := some p }
            | none => m
          | none => m) m
        let m := (c.nodesOfKind "structure.field").foldl (fun m f =>
          match f.firstIdent? with
          | some x => match added.find? (· == p ++ "." ++ x) with
            | some n => m.insert n { kind := "field", parent := some p, doc := docAt f, start := f.info.start }
            | none => m
          | none => m) m
        -- a structure's constructor, by default `mk`
        if (k == "command.structure" || k == "command.class" || k == "command.coinductive") then
          match added.find? (· == p ++ ".mk") with
          | some n => if m.contains n then m else m.insert n { kind := "constructor", parent := some p }
          | none => m
        else m
  /-- before the node, or (`| /-- … -/ c`) before its name -/
  docAt (node : Syntax) : Option String :=
    match docCommentBefore chars node.info.start with
    | some d => some d
    | none => match node.args.find? (·.getId?.isSome) with
      | some x => docCommentBefore chars x.info.start
      | none => none

variable [IsoCache R]

/-- (11q) The syntax a command the user wrote refers to: its nodes of declared kinds
(`syntax`, `notation`, `infix…`; not the built-in ones), and the names of declared
syntax categories (in `syntax … : c`, `c:prec` items and quotations `` `(c| …) ``). -/
partial def syntaxRefs (s : CommandState R) (cmd : Syntax) : Array (Info R) :=
  go cmd #[]
where
  user (i : SourceInfo) : Bool := i.stop > 0 && !i.synthetic
  cat (c : Syntax) (name : Option Name) (acc : Array (Info R)) : Array (Info R) :=
    match name with
    | some n => if user c.info && s.catSites.contains n then acc.push (.syntaxRef c.info (.cat n)) else acc
    | none => acc
  go (stx : Syntax) (acc : Array (Info R)) : Array (Info R) :=
    match stx with
    | .node i k as =>
      let acc := if user i && s.kindSites.contains k then acc.push (.syntaxRef i (.kind k)) else acc
      let acc :=
        if k == "stx.cat" then cat (stx.getArg 0) (stx.getArg 0).getId? acc
        else if k == "command.syntax" then cat (stx.getArg 6) (stx.getArg 6).getId? acc
        else if k.startsWith "quote." then cat (stx.getArg 1) (some (k.drop 6).toString) acc
        else acc
      as.foldl (fun acc a => go a acc) acc
    | _ => acc

/-- Run the frontend on `input` from the state `s`.

`import M` elaborates the library module `M` (once) into the current state. Like
`wiz check` (`Cache.elaborateWith`), a module sees only what it imports: it is first
checked **in isolation**, from the initial state `base` plus its own imports, and its
errors are reported at the `import`. Then, unless the importer's state is still the
initial one (`pristine`: then the isolated result is what it would get), it is
elaborated again into the importer's state, which is what the rest of the file sees.
Each module is checked in isolation once per run (its errors are kept in
`CommandState.checked`, its isolated state in `memo` for as long as one call runs), and,
from an initial state, once per process (`isoKey`). -/
partial def runFrontend (input : String) (s : CommandState R := {}) : CommandState R :=
  go input s input.toList.toArray 0 s
where
  go (input : String) (base : CommandState R) (chars : Array Char) (pos : Nat) (s : CommandState R) : CommandState R :=
    (go' input base chars pos s {}).1
  go' (input : String) (base : CommandState R) (chars : Array Char) (pos : Nat) (s : CommandState R)
      (memo : Std.HashMap Name (CommandState R)) : CommandState R × Std.HashMap Name (CommandState R) :=
    if skipWs chars pos ≥ chars.size then (s, memo) else
    match parseCommand chars s.tables pos with
    | .ok (cmd, stop) =>
      if cmd.isOfKind "command.import" then
        let m := ((cmd.getArg 1).getId?).getD "_"
        if s.imported.contains m then go' input base chars stop s memo else
        let err (text code : String) : CommandState R :=
          { s with messages := s.messages.push { info := cmd.info, severity := .error, text, code } }
        match s.loader m, s.checked.get? m with
        | none, _ => go' input base chars stop (err s!"unknown module {m}" ErrorCode.unknownModule) memo
        | some _, some none => go' input base chars stop (err s!"import cycle through {m}" ErrorCode.importCycle) memo
        | some src, done =>
          let srcChars := src.toList.toArray
          -- in isolation (unless already done in this run)
          let (isoErrs, checked, iso?, memo) : Array Msg × Std.HashMap Name (Option (Array Msg)) × Option (CommandState R) × Std.HashMap Name (CommandState R) := match done with
            | some (some errs) => (errs, s.checked, memo.get? m, memo)
            | _ =>
              let isolate (_ : Unit) :=
                let (iso, memo) := go' src base srcChars 0
                  { base with imported := m :: base.imported, messages := #[], module := m,
                              checked := s.checked.insert m none } memo
                (({ state := iso, errs := iso.messages.filter (·.severity == .error) } : Isolated R), iso.checked, memo)
              -- kept from an earlier run in this process, or elaborated (and kept)
              let (e, checked, memo) := match IsoCache.ref (R := R), isoKey base m with
                | some ref, some k => match isoGet ref k with
                  | some e => (e, s.checked, memo)
                  | none => let (e, checked, memo) := isolate (); (isoPut ref k e, checked, memo)
                | _, _ => isolate ()
              (e.errs, checked.insert m (some e.errs), some e.state, memo.insert m e.state)
          let s := { s with checked }
          let (inner, memo) := match iso? with
            -- (a pristine state may still list imports, of modules without commands; the
            -- isolated state may come from another run: the loader and headers are ours)
            | some iso => if s.pristine then ({ iso with checked, loader := s.loader, cHeaders := s.cHeaders, cSources := s.cSources,
                                                          imported := iso.imported.filter (!s.imported.contains ·) ++ s.imported }, memo) else
                go' src base srcChars 0 { s with imported := m :: s.imported, messages := #[], module := m } memo
            | none => go' src base srcChars 0 { s with imported := m :: s.imported, messages := #[], module := m } memo
          let errs := if isoErrs.isEmpty then inner.messages.filter (·.severity == .error) else isoErrs
          -- (a declaration this file already has is reported as it is, at the import)
          let msg : Msg := match errs.find? (·.code == "duplicate-declaration") with
            | some d => { info := cmd.info, severity := .error, text := d.text, code := d.code }
            | none => { info := cmd.info, severity := .error, code := ErrorCode.moduleErrors,
                        text := importErrorsText m src errs }
          let msgs := if errs.isEmpty then s.messages else s.messages.push msg
          -- (a module's warnings, such as an unchecked `builtin`, are shown at the import)
          let msgs := msgs ++ (inner.messages.filter (·.severity == .warning)).map fun w =>
            { info := cmd.info, severity := .warning, text := s!"module {m}: {w.render src}" }
          -- the info tree is positions in this file: keep only ours (and (11q) the import)
          -- (13m) the module's `local` notation stays in it
          let infos := if s.termInfo then s.infos.push (.importMod (cmd.getArg 1).info m) else s.infos
          go' input base chars stop { (inner.endModule s) with messages := msgs, module := s.module, infos } memo
      else go' input base chars stop (step chars cmd s) memo
    | .error e =>
      -- (13o) a keyword where a name was expected: which notation, from which module
      let e := e.explainKeywords s.tables (fun k => (s.kindSites[k]?).map (·.2))
      let msg := (e.render input).splitOn ": " |>.drop 1 |> ": ".intercalate
      go' input base chars (recoverPos chars (skipWs chars pos))
        { s with messages := s.messages.push { info := { start := e.pos, stop := e.pos },
                                                severity := .error, text := msg, code := ErrorCode.parseError } } memo

  /-- Elaborate one command, recording where the declarations it adds come from, and
  (11s) what they are and their doc comments. -/
  step (chars : Array Char) (cmd : Syntax) (s : CommandState R) : CommandState R :=
    let before := s.globals.order.size
    -- (11q) for the language server: the syntax the command uses, by where it was declared
    let s := if s.termInfo then { s with infos := s.infos ++ syntaxRefs s cmd } else s
    let s' := ((elabCommand cmd).run { s with pristine := false }).2
    let added := s'.globals.order.extract before s'.globals.order.size
    -- (a command macro's located output may have placed them already: keep that)
    { s' with declSites := added.foldl (fun m n => if m.contains n then m else m.insert n (cmd.info, s.module)) s'.declSites,
              declDocs := if added.isEmpty then s'.declDocs else declDocsOf chars cmd added s'.declDocs }

end Wiz
