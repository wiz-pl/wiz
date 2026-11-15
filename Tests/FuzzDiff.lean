import Tests.Elab
import Tests.Groups.Prop
import Tests.FalseFuzz

/-!
# A deterministic differential fuzzer for the Wiz pipelines (`fuzz-diff`)

The harness generates closed terms and whole programs from a **seed** and a **choice
sequence** (`Tests.Prop.Gen`), then asks the pipelines that exist today the same question:

* **kernel terms** — the Lean kernel (`Tests.Prop.accepts` / `wizNormal`) and the
  self-hosted kernel (`selfhost/Kernel.wiz`, run through `Tests.FalseFuzz.runKernel`).
  Both a verdict and, when the Lean kernel accepts, the normal form are compared;
* **programs** — the Lean frontend + C backend (`Build.runGlobal`), the self-hosted
  compiler + C backend (`selfhost/*.wiz` with the self-hosted runtime), and the Lean
  frontend's IR interpreter (`#run`).  The Lean→C run is the reference; Wiz→C and the
  interpreter must produce the same output.

A failing case is **shrunk** by shrinking its choice sequence (delta debugging over the
deterministic generator), and every generated case is cached in a TSV corpus keyed by
`kind seed index` so a run is reproducible even after the generator changes.

The fast PR subset is the `fuzz-diff` test group (`Tests/Groups/FuzzDiff.lean`): a small
fixed seed, kernel terms and Lean→C vs the interpreter.  The nightly run is
`scripts/fuzz-diff.sh --nightly`, which uses the date as the seed, adds Wiz→C, and
shrinks findings.  Neither run pushes anything.

Replay one case:

```
tests --fuzz-diff --replay term SEED INDEX CHOICE...
```
-/

set_option compiler.extract_closed false

open Wiz
open Tests.Prop
open Tests.FalseFuzz (Query runKernel norm feats)

namespace Tests.FuzzDiff

/-! ## Determinism and choice sequences -/

/-- The fixed seed of the fast PR subset.  Change it only with the checked-in corpus. -/
def fastSeed : Nat := 20261115

/-- A deterministic per-case random stream: the campaign seed and the case index. -/
def caseRnd (seed index : Nat) : Nat := lcg (lcg seed + index * 0x9E3779B1)

/-- The shape of a generated program. -/
inductive Focus where
  | nat | bool | list | option | pair | tree
  deriving DecidableEq, Repr, Inhabited

def Focus.label : Focus → String
  | .nat => "nat" | .bool => "bool" | .list => "list" | .option => "option"
  | .pair => "pair" | .tree => "tree"

/-- The interpreter handles these (the pair is a Σ and the IR has no `String.length`
native in the small corpus, so those are compiler-only). -/
def Focus.irOK : Focus → Bool
  | .pair => false
  | _ => true

/-! ## Term cases: the two kernels -/

/-- The closed types the term generator draws from.  They are all in
`MTm.globalDefs`/the shared world, so both kernels can judge the result. -/
def termTypes : Array Tm := #[
  .unit 0, .unit 1, .enum (Tests.Elab.MTm.labels 1), .enum (Tests.Elab.MTm.labels 2),
  .enum (Tests.Elab.MTm.labels 3),
  .empty 0, .empty 1, .const "Nat" [],
  .sigma "x" (.qlit .many) (.const "Nat" []) (.const "Nat" []) .hole,
  .pi "x" .default (.qlit .many) (.const "Nat" []) (.const "Nat" []) .hole,
  .eqTy (.const "Nat" []) (.const "Nat" [])]

/-- The world the term generator draws from: the shared differential world without sizes
(the size rules have pinned kernel differences, which are not this harness's target). -/
def fuzzWorld : World := { sharedWorld () with name := "fuzz-diff", sizes := false }

structure TermCase where
  seed : Nat
  index : Nat
  choices : Array Nat
  ty : Tm
  val : Tm
  deriving Inhabited

def TermCase.name (c : TermCase) : String := s!"term-{c.seed}-{c.index}"

/-- The shapes the fast kernel differential covers: no sizes, `ν`, casts, descriptions,
proofs or linear/erased binders.  Those have pinned kernel differences (`Tests/FalseFuzz`,
`Tests/Prop`); the compiler differential is their home.  Keeping the fast fragment narrow
is what makes a red run actionable rather than a re-run of the known list. -/
def fastFragment (t : Tm) : Bool :=
  let s := t.pretty []
  let has (p : String) : Bool := (s.splitOn p).length > 1
  (feats t).isEmpty && !has "(1 " && !has "(0 " && !has "prf " &&
    !has "ULift" && !has "ind " && !has "transp "

/-- Generate a value of a random closed type, retrying until the Lean kernel accepts the
annotation and the term is in the fast fragment.  The fuel can otherwise leave an
ill-typed stub; an ill-typed sample is still a useful rejection case, but we want normal
forms too. -/
partial def genTermSample (tries : Nat) : Gen (Tm × Tm) := do
  let ti ← choose termTypes.size
  let ty := termTypes.getD ti (.unit 0)
  let cx := mkCx fuzzWorld #[]
  let val := annotate cx (← genTm cx ty 3)
  if tries == 0 then return (.unit 1, .tt)
  else if fastFragment val && fastFragment ty && accepts fuzzWorld.g (.ann val ty) then
    return (ty, val)
  else genTermSample (tries - 1)

def genTermCase (seed index : Nat) : TermCase :=
  let (p, gs) := runGen #[] (some (caseRnd seed index)) (genTermSample 3)
  { seed, index, choices := gs.log.map (·.1), ty := p.1, val := p.2 }

/-- Rebuild a case from its choice sequence.  `none` when the sequence no longer replays
exactly (a generator change), so a stale corpus row is never silently trusted. -/
def replayTermCase (seed index : Nat) (choices : Array Nat) : Option TermCase :=
  let (p, gs) := runGen choices none (genTermSample 3)
  if gs.log.size != choices.size then none
  else some { seed, index, choices, ty := p.1, val := p.2 }

def TermCase.render (c : TermCase) : String :=
  s!"{c.val.pretty []} : {c.ty.pretty []}"

/-! ## Program cases: the compilers and the interpreter -/

/-- A small typed expression language.  Every constructor is typed by construction, so a
generated program is accepted by both frontends unless a backend has a bug. -/
inductive PTy where
  | nat | bool | list | option | pair
  deriving DecidableEq, Repr, Inhabited

def PTy.render : PTy → String
  | .nat => "Nat" | .bool => "Bool" | .list => "List Nat"
  | .option => "Option Nat" | .pair => "Nat × Bool"

/-- Count a value of the type down to `Nat` (the `out` of every generated program). -/
def countBool (e : String) : String := s!"(if ({e}) then 1 else 0)"
def countList (e : String) : String := s!"(sumL ({e}))"
def countOption (e : String) : String := s!"(let o : Option Nat := ({e}); match o with | .none => 0 | .some x => x)"
def countPair (e : String) : String := s!"(let p : Nat × Bool := ({e}); if p.2 then p.1 else 0)"

/-- Generate a typed expression at `depth`. -/
partial def genExpr (T : PTy) (depth : Nat) : Gen String := do
  let d := depth
  match T with
  | .nat =>
    if d == 0 then return toString (← choose 13)
    else match ← choose 11 with
    | 0 => return s!"Nat.add ({← genExpr .nat (d-1)}) ({← genExpr .nat (d-1)})"
    | 1 => return s!"Nat.mul ({← genExpr .nat (d-1)}) ({← genExpr .nat (d-1)})"
    | 2 => return s!"Nat.sub ({← genExpr .nat (d-1)}) ({← genExpr .nat (d-1)})"
    | 3 => return s!"Nat.mod ({← genExpr .nat (d-1)}) (Nat.succ ({← genExpr .nat (d-1)}))"
    | 4 => return s!"Nat.div ({← genExpr .nat (d-1)}) (Nat.succ ({← genExpr .nat (d-1)}))"
    | 5 => return s!"Nat.pred ({← genExpr .nat (d-1)})"
    | 6 => return s!"if ({← genExpr .bool (d-1)}) then ({← genExpr .nat (d-1)}) else ({← genExpr .nat (d-1)})"
    | 7 => do
        let n ← genExpr .nat (d-1)
        let a ← genExpr .nat (d-1)
        let b ← genExpr .nat (d-1)
        return s!"(let n : Nat := ({n}); match n with | .zero => ({a}) | .succ k => Nat.add k ({b}))"
    | 8 => return countBool (← genExpr .bool (d-1))
    | 9 => return countList (← genExpr .list (d-1))
    | _ => return countOption (← genExpr .option (d-1))
  | .bool =>
    if d == 0 then return if (← choose 2) == 0 then "Bool.true" else "Bool.false"
    else match ← choose 8 with
    | 0 => return s!"Nat.beq ({← genExpr .nat (d-1)}) ({← genExpr .nat (d-1)})"
    | 1 => return s!"Nat.lt ({← genExpr .nat (d-1)}) ({← genExpr .nat (d-1)})"
    | 2 => return s!"Bool.and ({← genExpr .bool (d-1)}) ({← genExpr .bool (d-1)})"
    | 3 => return s!"Bool.or ({← genExpr .bool (d-1)}) ({← genExpr .bool (d-1)})"
    | 4 => return s!"Bool.not ({← genExpr .bool (d-1)})"
    | 5 => return s!"if ({← genExpr .bool (d-1)}) then ({← genExpr .bool (d-1)}) else ({← genExpr .bool (d-1)})"
    | 6 =>
      let n ← genExpr .nat (d-1)
      let a ← genExpr .bool (d-1)
      let b ← genExpr .bool (d-1)
      return s!"(let n : Nat := ({n}); match n with | .zero => ({a}) | .succ k => Bool.or (Nat.beq k 0) ({b}))"
    | _ => return s!"Nat.lt ({← genExpr .nat (d-1)}) ({← genExpr .nat (d-1)})"
  | .list =>
    if d == 0 then return "(List.cons 0 (List.nil : List Nat))"
    else match ← choose 4 with
    | 0 => return s!"List.cons ({← genExpr .nat (d-1)}) ({← genExpr .list (d-1)})"
    | 1 => return s!"List.append ({← genExpr .list (d-1)}) ({← genExpr .list (d-1)})"
    | 2 =>
      let xs ← genExpr .list (d-1)
      let e ← genExpr .nat (d-1)
      return s!"(let xs : List Nat := ({xs}); match xs with | .nil => (List.nil : List Nat) | .cons x rest => List.cons ({e}) rest)"
    | _ => return "(List.nil : List Nat)"
  | .option =>
    if d == 0 then return "(Option.some 0)"
    else match ← choose 3 with
    | 0 => return s!"Option.some ({← genExpr .nat (d-1)})"
    | 1 => return "(Option.none : Option Nat)"
    | _ =>
      let o ← genExpr .option (d-1)
      let e ← genExpr .nat (d-1)
      return s!"(let o : Option Nat := ({o}); match o with | .none => (Option.some ({e})) | .some x => Option.some (Nat.add x ({e})))"
  | .pair =>
    if d == 0 then return "(0, .true)"
    else match ← choose 3 with
    | 0 => return s!"(({← genExpr .nat (d-1)}), ({← genExpr .bool (d-1)}))"
    | 1 =>
      let p ← genExpr .pair (d-1)
      return s!"(let p : Nat × Bool := ({p}); (Nat.add p.1 ({← genExpr .nat (d-1)}), Bool.or p.2 ({← genExpr .bool (d-1)})))"
    | _ =>
      let p ← genExpr .pair (d-1)
      return s!"(let q : Nat × Bool := ({p}); (q.1, q.2))" -- (projected; still exercises the Σ)

/-- A program of the given focus, with `out : Nat := …` and an IO `main`. -/
def programOf (_f : Focus) (body : String) : String :=
  -- (always defined: a `Nat` expression may count a list, and an unused definition is
  -- dropped by both compilers)
  "def sumL : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => Nat.add x (sumL xs)\n" ++
  body ++ "def main : IO Unit := IO.println (Nat.toString out)\n"

/-- The tree template: a recursive datatype, a builder and a fold. -/
def genTree : Gen String := do
  let k ← choose 5
  let base ← choose 10
  return s!"inductive Tree where\n  | leaf (n : Nat)\n  | node (l : Tree) (r : Tree)\n" ++
    s!"def mkT : Nat → Tree\n  | .zero => .leaf {base}\n  | .succ k => .node (mkT k) (mkT k)\n" ++
    s!"def sumT : Tree → Nat\n  | .leaf n => n\n  | .node l r => Nat.add (sumT l) (sumT r)\n" ++
    s!"def out : Nat := sumT (mkT {k})\n"

def genProgramSample : Gen (Focus × String) := do
  let fi ← choose 7
  let f : Focus := #[.nat, .nat, .bool, .list, .option, .pair, .tree].getD fi .nat
  let src ← match f with
  | .nat => do
      let e ← genExpr .nat 3
      pure (programOf .nat s!"def out : Nat := {e}\n")
  | .bool => do
      let e ← genExpr .bool 3
      pure (programOf .bool s!"def out : Nat := {countBool e}\n")
  | .list => do
      let e ← genExpr .list 3
      pure (programOf .list s!"def out : Nat := {countList e}\n")
  | .option => do
      let e ← genExpr .option 3
      pure (programOf .option s!"def out : Nat := {countOption e}\n")
  | .pair => do
      let e ← genExpr .pair 3
      pure (programOf .pair s!"def out : Nat := {countPair e}\n")
  | .tree => pure (programOf .tree (← genTree))
  pure (f, "import Prelude\nimport IO\n" ++ src)

structure ProgramCase where
  seed : Nat
  index : Nat
  choices : Array Nat
  focus : Focus
  source : String
  deriving Inhabited

def ProgramCase.name (c : ProgramCase) : String := s!"prog-{c.seed}-{c.index}-{c.focus.label}"
def ProgramCase.irExpr (c : ProgramCase) : Option String := if c.focus.irOK then some "out" else none

def genProgramCase (seed index : Nat) : ProgramCase :=
  let (p, gs) := runGen #[] (some (caseRnd seed index)) genProgramSample
  { seed, index, choices := gs.log.map (·.1), focus := p.1, source := p.2 }

def replayProgramCase (seed index : Nat) (choices : Array Nat) : Option ProgramCase :=
  let (p, gs) := runGen choices none genProgramSample
  if gs.log.size != choices.size then none
  else some { seed, index, choices, focus := p.1, source := p.2 }

/-! ## Corpus cache -/

structure Row where
  kind : String
  seed : Nat
  index : Nat
  choices : Array Nat
  deriving Inhabited, Repr

/-- A row (a function: a multiline structure literal is not accepted inside a `do`). -/
def mkRow (kind : String) (seed index : Nat) (choices : Array Nat) : Row :=
  { kind, seed, index, choices }

def escape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\t" "\\t" |>.replace "\n" "\\n"

def unescape (s : String) : String := Id.run do
  let mut out := ""
  let mut it := s.toList
  while let c :: rest := it do
    it := rest
    if c == '\\' then
      match it with
      | 'n' :: r => out := out.push '\n'; it := r
      | 't' :: r => out := out.push '\t'; it := r
      | 'r' :: r => out := out.push '\r'; it := r
      | '\\' :: r => out := out.push '\\'; it := r
      | _ => out := out.push '\\'
    else out := out.push c
  return out

def parseChoices (s : String) : Array Nat :=
  ((s.splitOn ",").filterMap fun x => x.toNat?).toArray

def renderChoices (cs : Array Nat) : String :=
  ",".intercalate (cs.toList.map toString)

def readRows (path : System.FilePath) : IO (Array Row) := do
  unless ← path.pathExists do return #[]
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").filterMap fun line =>
    if line.isEmpty || line.startsWith "#" then none
    else match line.splitOn "\t" with
      | [kind, seed, index, choices] =>
        some (mkRow kind (seed.toNat?.getD 0) (index.toNat?.getD 0)
          (parseChoices (unescape choices)))
      | _ => none
  return lines.toArray

def writeRows (path : System.FilePath) (rows : Array Row) : IO Unit := do
  if let some d := path.parent then IO.FS.createDirAll d
  let body := rows.foldl (fun acc r =>
    acc ++ String.intercalate "\t" [r.kind, toString r.seed, toString r.index,
      escape (renderChoices r.choices)] ++ "\n") ""
  IO.FS.writeFile path ("# Tests/FuzzDiff/corpus.tsv — fuzz-diff cases.\n" ++
    "# kind\tseed\tindex\tchoices (comma-separated; the deterministic generator's choices).\n" ++
    "# Regenerate deliberately with `tests --fuzz-diff --update-corpus`; review the diff.\n" ++ body)

/-- The first row for a case, from the checked-in corpus before the local cache. -/
def lookupChoices (rows : Array Row) (kind : String) (seed index : Nat) : Option (Array Nat) :=
  rows.find? (fun r => r.kind == kind && r.seed == seed && r.index == index) |>.map (·.choices)

/-! ## Running the pipelines -/

inductive Outcome where
  | ok (out : String)
  | rejected (msg : String)
  | skipped (why : String)
  deriving Repr

structure ProcResult where
  code : UInt32
  out : String
  err : String
  deriving Inhabited

def runTool (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (secs : Nat := 300) : IO ProcResult := do
  let out ← IO.Process.output
    { cmd := "timeout", args := #[toString secs, cmd] ++ args, cwd }
  pure { code := out.exitCode, out := out.stdout, err := out.stderr }

def noToolchain (e : String) : Option String :=
  if (e.splitOn "gmp.h").length > 1 then some "no GMP headers"
  else if (e.splitOn "gc.h").length > 1 then some "no Boehm GC headers"
  else if (e.splitOn "llc:").length > 1 then some "no LLVM `llc`"
  else if (e.splitOn "could not execute external process").length > 1 then some "no C toolchain"
  else if (e.splitOn "No such file").length > 1 then some "no C toolchain"
  else none

def frontendErrors (src : String) : IO (List String) := do
  let loader ← Tests.Elab.libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  pure ((s.messages.filter (·.severity == .error)).toList.map (·.text))

/-- The Lean frontend + C backend, run.  This is the reference output. -/
def runLeanC (src : String) : IO Outcome := do
  let errs ← frontendErrors src
  if !errs.isEmpty then return .rejected ("lean frontend: " ++ "\n".intercalate errs)
  let loader ← Tests.Elab.libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← Tests.toolchain) s "main" dir false (timeout := some 120) with
  | .ok out => pure (.ok out)
  | .error e =>
    match noToolchain e with
    | some why => pure (.skipped why)
    | none => pure (.rejected ("lean-c: " ++ e))

/-- An existing self-hosted compiler: `WIZ_FUZZ_COMPILER`, else built once from
`selfhost/*.wiz` and cached under `/tmp` by the **source** hash (unlike the test suite's
cache, which is keyed by the test binary's mtime, so editing this file does not rebuild
the compiler). -/
def wizCompiler : IO (Except String System.FilePath) := do
  if let some p ← IO.getEnv "WIZ_FUZZ_COMPILER" then
    if ← (System.FilePath.mk p).pathExists then return .ok (System.FilePath.mk p)
  let srcs ← Wiz.Selfhost.compilerFiles.mapM (fun f => IO.FS.readFile (System.FilePath.mk f))
  let prog := Wiz.Selfhost.compilerSource srcs
  let dir : System.FilePath := s!"/tmp/wiz-fuzz-compiler-{toString (hash prog)}"
  let exe := dir / "compiler"
  if ← exe.pathExists then return .ok exe
  IO.FS.createDirAll dir
  let loader ← Tests.Elab.libLoader
  let s := runFrontend (R := ZeroOneMany) prog { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map (fun m => m.render prog)
  unless errs.isEmpty do return .error s!"self-hosted compiler source: {"\n".intercalate errs.toList}"
  match Build.irProgram s "main" with
  | .error e => return .error e
  | .ok (decls, _) =>
    let tmp := dir / s!"compiler-{← IO.monoNanosNow}"
    match ← Build.compileC (← Tests.toolchain) (C.program decls true (Build.extraC s)) tmp with
    | .error e => return .error e
    | .ok () => IO.FS.rename tmp exe; return .ok exe

/-- The self-hosted compiler + C backend + the self-hosted runtime, run. -/
def runWizC (src : String) : IO Outcome := do
  let tc ← Tests.toolchain
  if tc.gcCflags.isEmpty then return .skipped "no Boehm GC (`--gc-cflags` is empty)"
  match ← wizCompiler with
  | .error e =>
    match noToolchain e with
    | some why => pure (.skipped why)
    | none => pure (.rejected ("self-hosted compiler: " ++ e))
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") src
    let comp ← runTool exe.toString #[] (some dir) 300
    if comp.code != 0 then
      return .rejected ("self-hosted frontend: " ++ comp.err)
    IO.FS.writeFile (dir / "out.c") comp.out
    let rt := (← IO.currentDir) / "selfhost"
    let prog := dir / "prog"
    let args := #["-O2", "-w", s!"-I{rt}"] ++ tc.gcCflags.toArray ++
      #[(dir / "out.c").toString, "-o", prog.toString] ++ tc.gcLdflags.toArray
    let cc ← runTool tc.cc args (some dir) 120
    if cc.code != 0 then
      match noToolchain cc.err with
      | some why => pure (.skipped why)
      | none => pure (.rejected ("wiz cc: " ++ cc.err))
    else
      let run ← runTool prog.toString #[] (some dir) 120
      if run.code != 0 then pure (.rejected s!"wiz program failed ({run.code}): {run.err}")
      else pure (.ok run.out)

/-- The Lean frontend's IR interpreter (`#run`). -/
def runIR (src expr : String) : IO Outcome := do
  let prog := src ++ "\n#run " ++ expr ++ "\n"
  let loader ← Tests.Elab.libLoader
  let s := runFrontend (R := ZeroOneMany) prog { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).toList.map (·.text)
  if !errs.isEmpty then return .rejected ("ir: " ++ "\n".intercalate errs)
  let infos := (s.messages.filter (·.severity == .info)).toList.map (·.text)
  if infos.isEmpty then return .rejected "ir: no result (the `#run` produced no info message)"
  pure (.ok ("\n".intercalate infos))

/-! ## Findings, statistics and the campaign -/

structure Finding where
  kind : String
  seed : Nat
  index : Nat
  choices : Array Nat
  focus : String := ""
  stage : String
  detail : String
  source : String := ""
  deriving Inhabited

/-- A finding (a function: a multiline structure literal is not accepted inside a `do`). -/
def mkFinding (kind : String) (seed index : Nat) (choices : Array Nat)
    (focus stage detail : String) (source : String := "") : Finding :=
  { kind, seed, index, choices, focus, stage, detail, source }

def Finding.replay (f : Finding) : String :=
  s!"tests --fuzz-diff --replay {f.kind} {f.seed} {f.index} {renderChoices f.choices}"

def Finding.render (f : Finding) : String :=
  s!"✗ {f.kind} {f.seed}/{f.index}{(if f.focus.isEmpty then "" else " (" ++ f.focus ++ ")")}: {f.stage}\n" ++
  s!"  {f.detail}\n  replay: {f.replay}" ++
  (if f.source.isEmpty then "" else "\n```\n" ++ f.source ++ "```")

structure Stats where
  terms : Nat := 0
  programs : Nat := 0
  kernelJudgments : Nat := 0
  kernelVerdictDiffs : Nat := 0
  kernelNfDiffs : Nat := 0
  leanC : Nat := 0
  wizC : Nat := 0
  ir : Nat := 0
  leanVsWiz : Nat := 0
  irVsC : Nat := 0
  invalid : Array String := #[]
  skipped : Array (String × String) := #[]
  findings : Array Finding := #[]
  deriving Inhabited

def Stats.addSkip (s : Stats) (stage why : String) : Stats :=
  if s.skipped.any (fun (a, _) => a == stage) then s
  else { s with skipped := s.skipped.push (stage, why) }

/-- One kernel query (a function: a multiline structure literal is not accepted in `do`). -/
def mkQuery (role : String) (seq : Array Nat) (m : Tests.Elab.MTm) (nf : Bool)
    (lean render : String) : Query :=
  { shape := .nu, role, seq, m, nf, lean, render, falseClaim := false }

/-- Compare the Lean and self-hosted kernels on one batch of term cases.  Returns one
`Option Finding` per case (`none` = agree); an empty result means `Kernel.wiz` could not
be run here.  The queries are batched: one Wiz program checks the whole batch. -/
def checkTermCases (cases : Array TermCase) (nf : Bool := true) : IO (Array (Option Finding) × Nat × Nat × Nat) := do
  let world := fuzzWorld
  let mut qs : Array Query := #[]
  let mut skipped : Array Nat := #[]
  for c in cases, ci in [0:cases.size] do
    let ann := .ann c.val c.ty
    let acc := accepts world.g ann
    match toM ann with
    | none => skipped := skipped.push ci
    | some m =>
      let tag := s!"{ci}:"
      qs := qs.push (mkQuery (tag ++ "verdict") c.choices m false
        (if acc then "ok" else "error") c.render)
      if acc && nf then
        qs := qs.push (mkQuery (tag ++ "nf") c.choices m true (wizNormal world.g m) c.render)
  if qs.isEmpty then return (#[], 0, 0, 0)
  let ans ← Tests.FalseFuzz.runKernel qs
  if ans.isEmpty then return (#[], 0, 0, 0)
  let mut verdictDiffs := 0
  let mut nfDiffs := 0
  let mut out : Array (Option Finding) := #[]
  for c in cases, ci in [0:cases.size] do
    if skipped.contains ci then out := out.push none
    else
      let mine := ans.filter fun (q, _) => (q.role.splitOn ":")[0]! == toString ci
      if mine.isEmpty then out := out.push none
      else
        let mut f : Option Finding := none
        for (q, got) in mine do
          if q.nf then
            if got != "error" && norm q.lean != norm got then
              nfDiffs := nfDiffs + 1
              if f.isNone then
                f := some (mkFinding "term" c.seed c.index c.choices "" "kernel normal form"
                  s!"Lean {oneLine q.lean}, Wiz {oneLine got}" c.render)
          else
            let la := q.lean == "ok"
            let wa := got != "error"
            if la != wa then
              verdictDiffs := verdictDiffs + 1
              if f.isNone then
                f := some (mkFinding "term" c.seed c.index c.choices "" "kernel verdict"
                  s!"Lean {q.lean}, Wiz {got}" c.render)
        out := out.push f
  return (out, verdictDiffs, nfDiffs, qs.size)
where
  oneLine (s : String) : String :=
    let s := s.replace "\n" "⏎"
    if s.length > 200 then s.take 200 |>.toString |>.append "…" else s

structure PipeCfg where
  wizC : Bool := false

/-- What one program's run exercised (a skip is not a pass). -/
structure ProgOut where
  findings : Array Finding := #[]
  leanC : Bool := false
  wizC : Bool := false
  ir : Bool := false
  skipped : Array (String × String) := #[]
  deriving Inhabited

/-- One program through the requested pipelines. -/
def evalProgram (cfg : PipeCfg) (pc : ProgramCase) : IO ProgOut := do
  let lean ← runLeanC pc.source
  match lean with
  | .skipped why => pure { skipped := #[("lean-c", why)] }
  | .rejected msg =>
    pure { leanC := true, findings := #[mkFinding "program" pc.seed pc.index pc.choices pc.focus.label
      "lean frontend rejected a generated program" msg pc.source] }
  | .ok out =>
    let mut po : ProgOut := { leanC := true }
    if cfg.wizC then
      match ← runWizC pc.source with
      | .skipped why => po := { po with skipped := po.skipped.push ("wiz-c", why) }
      | .rejected msg =>
        po := { po with wizC := true, findings := po.findings.push (mkFinding "program" pc.seed pc.index pc.choices pc.focus.label "Lean→C accepts, Wiz→C rejects" msg pc.source) }
      | .ok wout =>
        po := { po with wizC := true }
        if wout != out then
          po := { po with findings := po.findings.push (mkFinding "program" pc.seed pc.index pc.choices pc.focus.label "Lean→C vs Wiz→C" s!"Lean {repr out}, Wiz {repr wout}" pc.source) }
    if let some expr := pc.irExpr then
      match ← runIR pc.source expr with
      | .rejected msg =>
        po := { po with ir := true, findings := po.findings.push (mkFinding "program" pc.seed pc.index pc.choices pc.focus.label "compiled, IR rejects" msg pc.source) }
      | .skipped why => po := { po with skipped := po.skipped.push ("ir", why) }
      | .ok iout =>
        po := { po with ir := true }
        if iout.trimAscii.toString != out.trimAscii.toString then
          po := { po with findings := po.findings.push (mkFinding "program" pc.seed pc.index pc.choices pc.focus.label "IR interpreter vs compiled" s!"compiled {repr out}, IR {repr iout}" pc.source) }
    pure po

/-! ### Shrinking -/

def key (a : Array Nat) : Nat × Nat := (a.size, a.foldl (· + ·) 0)

def keyLt (a b : Array Nat) : Bool :=
  let (sa, xa) := key a; let (sb, xb) := key b
  sa < sb || (sa == sb && xa < xb)

/-- Plausible smaller choice sequences: drop runs of 1, 2, 4, … entries, zero an entry, or
halve an entry.  Duplicates and anything not strictly smaller are removed. -/
def candidates (a : Array Nat) : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := #[]
  let mut sizes : List Nat := [1, 2, 4, 8, 16, 32]
  for sz in sizes do
    for i in [0:a.size] do
      if i + sz <= a.size then
        out := out.push (a.extract 0 i ++ a.extract (i + sz) a.size)
  for i in [0:a.size] do
    out := out.push (a.set! i 0)
    out := out.push (a.set! i (a[i]! / 2))
  let mut seen : Array (Array Nat) := #[]
  for b in out do
    if keyLt b a && !seen.contains b then seen := seen.push b
  return seen.qsort (fun x y => keyLt x y)

/-- Delta-debug a choice sequence: keep the smallest sequence whose replayed case still
fails the same predicate.  `bad` is batched (a whole round is one kernel run, or a few
program builds). -/
partial def shrinkLoop {α : Type} (replay : Array Nat → Option α)
    (bad : Array α → IO (Array Bool)) (cur : Array Nat) (fuel : Nat) : IO (Array Nat) := do
  if fuel == 0 then return cur
  let cands := (candidates cur).filterMap fun c => (replay c).map (fun v => (c, v))
  if cands.isEmpty then return cur
  let flags ← bad (cands.map (·.2))
  if flags.isEmpty then return cur
  let mut chosen : Option (Array Nat) := none
  for ((c, _), ok) in cands.zip flags do
    if ok && chosen.isNone then chosen := some c
  match chosen with
  | none => return cur
  | some c =>
    if keyLt c cur then shrinkLoop replay bad c (fuel - 1)
    else return cur

def runProgramBatch (cfg : PipeCfg) (pcs : Array ProgramCase) : IO (Array Bool) := do
  let mut out : Array Bool := #[]
  for pc in pcs do
    let po ← evalProgram cfg pc
    out := out.push (!po.findings.isEmpty)
  return out

/-! ### The campaign -/

structure Config where
  seed : Nat := fastSeed
  terms : Nat := 0
  programs : Nat := 0
  wizC : Bool := true
  shrink : Bool := true
  /-- ask for normal forms too (the fast subset compares verdicts only: a normal form can
  be much more work than the check, and a verdict difference is the actionable signal) -/
  nf : Bool := true
  corpusPath : System.FilePath := "Tests/FuzzDiff/corpus.tsv"
  cachePath : Option System.FilePath := some ".lake/fuzz-diff/corpus-cache.tsv"
  updateCorpus : Bool := false
  replay : Option (String × Nat × Nat × Array Nat) := none

def rowFor (_cfg : Config) (rows : Array Row) (kind : String) (seed index : Nat) :
    Option (Array Nat) :=
  lookupChoices rows kind seed index

/-- Run the campaign.  `rows` is the merged corpus (checked-in first) used for replay;
the returned rows are the current run's cases (`kind seed index choices`). -/
def campaign (cfg : Config) (rows : Array Row) : IO (Stats × Array Row) := do
  let mut st : Stats := {}
  let mut fresh : Array Row := #[]
  let mut termCases : Array TermCase := #[]
  for i in [0:cfg.terms] do
    let freshCase := genTermCase cfg.seed i
    let c ← match rowFor cfg rows "term" cfg.seed i with
      | some choices =>
        match replayTermCase cfg.seed i choices with
        | some c => pure c
        | none =>
          st := { st with invalid := st.invalid.push s!"term {cfg.seed}/{i}: the corpus choices no longer replay" }
          pure freshCase
      | none => pure freshCase
    termCases := termCases.push c
    fresh := fresh.push (mkRow "term" cfg.seed i c.choices)
  -- kernel terms: one batch, then shrink each finding (also batched)
  if !termCases.isEmpty then
    let (checks, vd, nd, kj) ← checkTermCases termCases cfg.nf
    if checks.isEmpty then
      st := st.addSkip "kernel" "Kernel.wiz could not run (no toolchain)"
    else
      st := { st with terms := termCases.size, kernelVerdictDiffs := vd, kernelNfDiffs := nd, kernelJudgments := kj }
      for c in termCases, o in checks do
        if let some f := o then
          let mut fin : Finding := f
          if cfg.shrink then
            let small ← shrinkLoop (fun cs => replayTermCase cfg.seed c.index cs)
              (fun cs => do
                let (os, _, _, _) ← checkTermCases cs cfg.nf
                pure (os.map (·.isSome)))
              c.choices 8
            if keyLt small c.choices then
              if let some sc := replayTermCase cfg.seed c.index small then
                let (os, _, _, _) ← checkTermCases #[sc] cfg.nf
                match os[0]? with
                | some (some f') => fin := { f' with detail := f'.detail ++ " (shrunk)" }
                | _ => pure ()
          st := { st with findings := st.findings.push fin }
  -- programs
  if cfg.programs > 0 then
    for i in [0:cfg.programs] do
      let freshCase := genProgramCase cfg.seed i
      let c ← match rowFor cfg rows "program" cfg.seed i with
        | some choices =>
          match replayProgramCase cfg.seed i choices with
          | some c => pure c
          | none =>
            st := { st with invalid := st.invalid.push s!"program {cfg.seed}/{i}: the corpus choices no longer replay" }
            pure freshCase
        | none => pure freshCase
      fresh := fresh.push (mkRow "program" cfg.seed i c.choices)
      let po ← evalProgram { wizC := cfg.wizC } c
      st := { st with programs := st.programs + 1, leanC := st.leanC + (if po.leanC then 1 else 0), wizC := st.wizC + (if po.wizC then 1 else 0), ir := st.ir + (if po.ir then 1 else 0) }
      for (s, why) in po.skipped do st := st.addSkip s why
      let mut fin := po.findings
      if !po.findings.isEmpty && cfg.shrink then
        let small ← shrinkLoop (fun cs => replayProgramCase cfg.seed c.index cs)
          (runProgramBatch { wizC := cfg.wizC }) c.choices 8
        if keyLt small c.choices then
          if let some sc := replayProgramCase cfg.seed c.index small then
            let po' ← evalProgram { wizC := cfg.wizC } sc
            if !po'.findings.isEmpty then
              fin := po'.findings.map (fun f => ({ f with detail := f.detail ++ " (shrunk)" }))
      st := { st with findings := st.findings ++ fin }
  return (st, fresh)

/-! ## CLI -/

structure Args where
  cfg : Config := {}
  report : Option System.FilePath := none
  findings : Option System.FilePath := none
  strict : Bool := false
  help : Bool := false

def parseArgs (args : List String) : Except String Args := do
  let rec go (a : Args) : List String → Except String Args
    | [] => pure a
    | "--seed" :: n :: rest => go { a with cfg := { a.cfg with seed := n.toNat?.getD a.cfg.seed } } rest
    | "--terms" :: n :: rest => go { a with cfg := { a.cfg with terms := n.toNat?.getD a.cfg.terms } } rest
    | "--programs" :: n :: rest => go { a with cfg := { a.cfg with programs := n.toNat?.getD a.cfg.programs } } rest
    | "--count" :: n :: rest =>
      let k := n.toNat?.getD 4
      go { a with cfg := { a.cfg with terms := k, programs := k } } rest
    | "--kinds" :: ks :: rest => do
      let mut terms := false
      let mut programs := false
      for k in ks.splitOn "," do
        if k == "term" || k == "terms" then terms := true
        if k == "program" || k == "programs" then programs := true
      if !terms && !programs then throw "--kinds needs term and/or program"
      let cfg := a.cfg
      go { a with cfg := { cfg with terms := (if terms then max cfg.terms 4 else 0), programs := (if programs then max cfg.programs 4 else 0) } } rest
    | "--wiz" :: rest => go { a with cfg := { a.cfg with wizC := true } } rest
    | "--no-wiz" :: rest => go { a with cfg := { a.cfg with wizC := false } } rest
    | "--shrink" :: rest => go { a with cfg := { a.cfg with shrink := true } } rest
    | "--no-shrink" :: rest => go { a with cfg := { a.cfg with shrink := false } } rest
    | "--nf" :: rest => go { a with cfg := { a.cfg with nf := true } } rest
    | "--no-nf" :: rest => go { a with cfg := { a.cfg with nf := false } } rest
    | "--fast" :: rest =>
      go { a with cfg := { a.cfg with terms := 4, programs := 4, wizC := false, shrink := false, nf := false } } rest
    | "--full" :: rest =>
      go { a with cfg := { a.cfg with terms := 24, programs := 16, wizC := true, shrink := true, nf := true } } rest
    | "--corpus" :: f :: rest =>
      go { a with cfg := { a.cfg with corpusPath := System.FilePath.mk f } } rest
    | "--cache" :: f :: rest =>
      go { a with cfg := { a.cfg with cachePath := some (System.FilePath.mk f) } } rest
    | "--no-cache" :: rest => go { a with cfg := { a.cfg with cachePath := none } } rest
    | "--update-corpus" :: rest => go { a with cfg := { a.cfg with updateCorpus := true } } rest
    | "--report" :: f :: rest => go { a with report := some (System.FilePath.mk f) } rest
    | "--findings" :: f :: rest => go { a with findings := some (System.FilePath.mk f) } rest
    | "--strict" :: rest => go { a with strict := true } rest
    | "--help" :: _ => pure { a with help := true }
    | "--replay" :: kind :: seed :: index :: rest => do
      -- The replay command is terminal (`--replay KIND SEED INDEX CHOICE...`); a trailing
      -- `--wiz` opts into the self-hosted compiler (the default is no: it is expensive).
      let choices := rest.filter (fun x => !x.startsWith "--")
      let wiz := rest.contains "--wiz"
      let cs := parseChoices (",".intercalate choices)
      go { a with cfg := { a.cfg with wizC := wiz, replay := some (kind, seed.toNat?.getD 0, index.toNat?.getD 0, cs) } } []
    | a :: _ => throw s!"unknown argument to --fuzz-diff: {a}"
  go {} args

def renderReport (cfg : Config) (st : Stats) : String := Id.run do
  let mut out := s!"# fuzz-diff — seed {cfg.seed}\n\n"
  out := out ++ s!"Generated {st.terms} term cases and {st.programs} programs; " ++
    s!"{st.kernelJudgments} kernel judgments, {st.leanC} Lean→C runs, {st.wizC} Wiz→C runs, " ++
    s!"{st.ir} interpreter runs.\n\n"
  out := out ++ s!"Findings: {st.findings.size}.  Skipped: {st.skipped.size}.\n\n"
  if !st.invalid.isEmpty then
    out := out ++ "## Corpus errors\n\n"
    for w in st.invalid do out := out ++ s!"* {w}\n"
    out := out ++ "\n"
  if !st.skipped.isEmpty then
    out := out ++ "| stage | reason |\n|---|---|\n"
    for (s, why) in st.skipped do out := out ++ s!"| {s} | {why} |\n"
    out := out ++ "\n"
  if st.findings.isEmpty then
    out := out ++ "No differential failures.\n"
  else
    out := out ++ "## Findings\n\n"
    for f in st.findings do
      out := out ++ s!"### {f.kind} {f.seed}/{f.index}{(if f.focus.isEmpty then "" else " (" ++ f.focus ++ ")")}\n\n" ++
        s!"**{f.stage}** — {f.detail}\n\n```\n{f.source}\n```\n\nReplay: `{f.replay}`\n\n"
  out := out ++ "A skipped pipeline is not a pass (see `Tests/FuzzDiff/README.md`).\n"
  return out

def main (args : List String) : IO UInt32 := do
  -- a generated term that makes the evaluator panic must fail the case, not kill the
  -- driver; `Case.runHere` reports the exception and every other case still runs
  Wiz.exitOnPanic false
  let a ← match parseArgs args with
    | .ok a => pure a
    | .error e => IO.eprintln e; return 2
  if a.help then
    IO.println "usage: tests --fuzz-diff [--seed N] [--terms N] [--programs N] [--count N] \
[--kinds term,program] [--fast|--full] [--wiz|--no-wiz] [--shrink|--no-shrink] [--nf|--no-nf] \
[--corpus FILE] [--cache FILE|--no-cache] [--update-corpus] [--report FILE] [--findings FILE] \
[--strict] [--replay KIND SEED INDEX CHOICE...]"
    return 0
  let corpus ← readRows a.cfg.corpusPath
  let cache ← match a.cfg.cachePath with
    | some p => readRows p
    | none => pure #[]
  let rows := corpus ++ cache
  if let some (kind, seed, index, choices) := a.cfg.replay then
    if kind == "term" then
      match replayTermCase seed index choices with
      | none => IO.eprintln "the choices do not replay a term case"; return 2
      | some c =>
        let (checks, vd, nd, _) ← checkTermCases #[c] a.cfg.nf
        if checks.isEmpty then IO.eprintln "Kernel.wiz could not run (no toolchain)"; return 2
        IO.println s!"{c.render}\nverdict/nf differences: {vd} / {nd}"
        match checks[0]? with
        | some (some f) => IO.println f.render; return 1
        | _ => return 0
    else if kind == "program" then
      match replayProgramCase seed index choices with
      | none => IO.eprintln "the choices do not replay a program case"; return 2
      | some c =>
        let po ← evalProgram { wizC := a.cfg.wizC } c
        for f in po.findings do IO.println f.render
        return (if po.findings.isEmpty then 0 else 1)
    else IO.eprintln s!"unknown kind {kind} (term or program)"; return 2
  let (st, fresh) ← campaign a.cfg rows
  -- The counters in `Stats` are best-effort; the definitive tally is the generated/
  -- pipeline lines.  A skip is never a pass.
  IO.println (s!"\nfuzz-diff: seed {a.cfg.seed}; {st.terms} term cases, {st.programs} programs; " ++
    s!"{st.kernelJudgments} kernel judgments, {st.leanC} Lean→C, {st.wizC} Wiz→C, {st.ir} IR; " ++
    s!"{st.findings.size} findings; {st.skipped.size} skipped")
  for (stage, why) in st.skipped do IO.println s!"  ⊘ {stage}: {why}"
  for w in st.invalid do IO.println s!"  ✗ corpus: {w}"
  for f in st.findings do IO.println f.render
  if let some p := a.report then
    if let some d := p.parent then IO.FS.createDirAll d
    IO.FS.writeFile p (renderReport a.cfg st)
  if let some p := a.findings then
    if let some d := p.parent then IO.FS.createDirAll d
    let lines := st.findings.map fun f =>
      String.intercalate "\t" [f.kind, toString f.seed, toString f.index, escape (renderChoices f.choices),
        escape f.stage, escape f.detail, escape f.source]
    IO.FS.writeFile p ("# kind\tseed\tindex\tchoices\tstage\tdetail\tsource\n" ++
      "\n".intercalate lines.toList ++ (if lines.isEmpty then "" else "\n"))
  if a.cfg.updateCorpus then
    writeRows a.cfg.corpusPath fresh
    IO.println s!"wrote {a.cfg.corpusPath} ({fresh.size} rows)"
  else if let some p := a.cfg.cachePath then
    writeRows p fresh
  if !st.findings.isEmpty || !st.invalid.isEmpty then return 1
  if a.strict && !st.skipped.isEmpty then return 1
  return 0

/-! ## The fast PR subset (the `fuzz-diff` test group) -/

/-- The shrinker is part of the harness too: a sequence is bad exactly when it still
contains `3`, and the smallest such sequence is `[3]`. -/
def shrinkSelfTest : IO Unit := do
  let bad (cs : Array (Array Nat)) : IO (Array Bool) :=
    pure (cs.map fun c => c.contains 3)
  let small ← shrinkLoop (fun cs => some cs) bad #[1, 2, 3, 4, 5] 8
  unless small == #[3] do
    throw (IO.userError s!"the shrinker returned {small.toList}, expected [3]")

def fastTermCase : IO Unit := do
  Wiz.exitOnPanic false
  let corpus ← readRows (System.FilePath.mk "Tests/FuzzDiff/corpus.tsv")
  let cfg : Config := { seed := fastSeed, terms := 4, programs := 0, wizC := false, shrink := false, nf := false, cachePath := none }
  let (st, _) ← campaign cfg corpus
  if st.kernelJudgments == 0 then
    Tests.skip "Kernel.wiz could not run (no toolchain)"
    return
  unless st.invalid.isEmpty do
    throw (IO.userError s!"fuzz-diff: {st.invalid.size} corpus error(s): {"\n".intercalate st.invalid.toList}")
  unless st.findings.isEmpty do
    throw (IO.userError (s!"fuzz-diff: {st.findings.size} kernel finding(s):\n" ++
      "\n".intercalate (st.findings.toList.map Finding.render)))

def fastProgramCase : IO Unit := do
  Wiz.exitOnPanic false
  let corpus ← readRows (System.FilePath.mk "Tests/FuzzDiff/corpus.tsv")
  let cfg : Config := { seed := fastSeed, terms := 0, programs := 4, wizC := false, shrink := false, cachePath := none }
  let (st, _) ← campaign cfg corpus
  if st.leanC == 0 then
    Tests.skip "no C toolchain"
    return
  unless st.invalid.isEmpty do
    throw (IO.userError s!"fuzz-diff: {st.invalid.size} corpus error(s): {"\n".intercalate st.invalid.toList}")
  unless st.findings.isEmpty do
    throw (IO.userError (s!"fuzz-diff: {st.findings.size} program finding(s):\n" ++
      "\n".intercalate (st.findings.toList.map Finding.render)))

def replayCorpusCase : IO Unit := do
  Wiz.exitOnPanic false
  let rows ← readRows (System.FilePath.mk "Tests/FuzzDiff/corpus.tsv")
  let terms := rows.filter (·.kind == "term") |>.take 2
  let progs := rows.filter (·.kind == "program") |>.take 2
  if terms.isEmpty && progs.isEmpty then
    Tests.skip "no checked-in corpus"
    return
  -- (the fast term case already judges these: here we only check that the pinned choice
  -- sequences still replay, so a generator change is caught without a second Wiz build)
  for r in terms do
    match replayTermCase r.seed r.index r.choices with
    | none => throw (IO.userError s!"corpus term {r.seed}/{r.index} no longer replays")
    | some _ => pure ()
  for r in progs do
    match replayProgramCase r.seed r.index r.choices with
    | none => throw (IO.userError s!"corpus program {r.seed}/{r.index} no longer replays")
    | some c =>
      let po ← evalProgram { wizC := false } c
      if !po.findings.isEmpty then
        throw (IO.userError (s!"corpus program {r.seed}/{r.index} now differs:\n" ++
          "\n".intercalate (po.findings.toList.map Finding.render)))

end Tests.FuzzDiff
