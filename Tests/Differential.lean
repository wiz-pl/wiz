import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# The multi-pipeline differential harness (COMP-02, `docs/building.md`)

One small corpus is run through the pipelines that exist today:

* `lean-c`      — the Lean frontend, erasure, IR and C backend (`Build.build`, `llvm := false`);
* `lean-llvm`   — the same frontend, through LLVM (`Build.build`, `llvm := true`);
* `wiz-c-gc`    — the self-hosted compiler (`selfhost/*.wiz`), C with Boehm GC;
* `wiz-c-rc`    — the self-hosted compiler, C with reference counting (`--rc`);
* `ir-interp`   — the Lean frontend's `#run` (IR interpreter, `Wiz.Compiler.IRRun`).

The corpus covers arithmetic, data, IO, classes, FFI, exit codes, compile-time
diagnostics and generated code.  A pipeline that cannot run here (no `llc`, no Boehm GC,
no GMP, no C toolchain) is **skipped** with a reason; it is never counted as a pass.

`Tests/Differential/baseline.tsv` is the golden baseline: one row per case and pipeline,
with the verdict, the program's exit code, and the observed value (stdout for a run, the
normalized diagnostic for a reject, a hash of the normalized generated code for a
compile-only case).  Regenerate it deliberately with `scripts/differential.sh --update`.

The false-difference filters are deliberately small and explicit (see
`Tests/Differential/README.md`): program output is exact; diagnostics are compared by
message text (positions and temporary-directory paths stripped); generated code is
normalized by dropping the Lean runtime preamble (everything before
`/* ---- generated ---- */`), full-line comments and blank lines, then hashed.  There is
no cross-pipeline comparison of diagnostics (the two frontends word them differently);
each pipeline's exact message is pinned in the baseline.
-/

namespace Tests.Differential

/-- The five pipelines of COMP-02. -/
inductive Pipeline where
  | leanC
  | leanLLVM
  | wizGC
  | wizRC
  | irInterp
  deriving DecidableEq, Repr

def Pipeline.name : Pipeline → String
  | .leanC => "lean-c"
  | .leanLLVM => "lean-llvm"
  | .wizGC => "wiz-c-gc"
  | .wizRC => "wiz-c-rc"
  | .irInterp => "ir-interp"

def allPipelines : List Pipeline :=
  [.leanC, .leanLLVM, .wizGC, .wizRC, .irInterp]

/-- What a corpus case checks. -/
inductive Kind where
  /-- Build and run `main`; compare stdout and exit code. -/
  | run
  /-- The frontend/compiler must reject the source; pin its diagnostic. -/
  | reject
  /-- Generate code (C or LLVM) and compare a hash of its normalized text. -/
  | compileOnly
  deriving DecidableEq, Repr

/-- One corpus program.  `expected` is exact stdout (with its final newline) for `run`;
`irExpr` is the pure expression appended as `#run …` for the interpreter (absent when
the interpreter cannot run the case, e.g. an IO `main` or an extern call). -/
structure Spec where
  name : String
  src : String
  kind : Kind := .run
  expected : String := ""
  expectedExit : Nat := 0
  /-- A fragment every rejecting pipeline's diagnostic must mention; empty accepts any
  error.  Exact messages are pinned per pipeline in the baseline. -/
  expectedDiag : String := ""
  irExpr : Option String := none
  /-- Pipelines that this case cannot exercise, with an explicit reason. -/
  skip : List (Pipeline × String) := []
  deriving Inhabited

def skipReason (s : Spec) (p : Pipeline) : Option String :=
  (s.skip.find? (·.1 == p)).map (·.2)

/-! ## The corpus -/

def arithBig : String := "import IO
def fact : Nat → Nat
  | .zero => 1
  | .succ n => (.succ n) * fact n
def out : Nat := fact 20
def main : IO Unit := IO.println (Nat.toString out)
"

def arithOps : String := "import IO
def out : Nat :=
  100 / 7 + Nat.mod 100 7 + Nat.pow 3 10 + Nat.land 12 10 + Nat.lor 12 10 +
  Nat.xor 12 10 + Nat.shiftLeft 3 10 + Nat.shiftRight 1000 3 + Nat.log2 1025
def main : IO Unit := IO.println (Nat.toString out)
"

def dataList : String := "import IO
def range : Nat → List Nat → List Nat
  | .zero, acc => acc
  | .succ n, acc => range n (.cons n acc)
def mapL (f : Nat → Nat) : List Nat → List Nat
  | .nil => .nil
  | .cons x xs => .cons (f x) (mapL f xs)
def sum : List Nat → Nat
  | .nil => 0
  | .cons x xs => x + sum xs
def out : Nat := sum (mapL (fun x => x * x) (range 10 .nil))
def main : IO Unit := IO.println (Nat.toString out)
"

def dataTree : String := "import IO
inductive T where
  | leaf (n : Nat)
  | node (l : T) (r : T)
def sumT : T → Nat
  | .leaf n => n
  | .node l r => sumT l + sumT r
def t : T := T.node (T.node (T.leaf 1) (T.leaf 2)) (T.leaf 3)
def out : Nat := sumT t
def main : IO Unit := IO.println (Nat.toString out)
"

def dataArrayMap : String := "import Std
def out : Nat :=
  let a := Array.push (Array.push Array.empty 3) 4;
  let b := Array.set a 0 10;
  let m := StrMap.insert (StrMap.insert StrMap.empty (Str.ofString \"a\") 1) (Str.ofString \"b\") 2;
  Array.size a + Array.getD b 0 0 + StrMap.findD m (Str.ofString \"b\") 0 + StrMap.size m
def main : IO Unit := IO.println (Nat.toString out)
"

def dataString : String := "import IO
def strLen : String → Nat
  | .mk cs => List.length cs
def out : Nat := strLen (String.append \"hello\" \"world\")
def main : IO Unit := IO.println (Nat.toString out)
"

def ioSequence : String := "import IO
def out : Nat := 6 * 7
def main : IO Unit := do
  IO.println \"differential\";
  IO.println (Nat.toString out)
"

/-- Type classes are in the Lean frontend only (the self-hosted frontend does not have
`class`/`instance` yet), so the two Wiz pipelines skip this case explicitly. -/
def classes : String := "import IO
class Weight (A : Type) where
  weight : A → Nat
instance : Weight Nat where
  weight := fun n => n * 2
instance : Weight Bool where
  weight := fun b => if b then 1 else 0
def heavy (x : Nat) : Nat := Weight.weight x + Weight.weight Bool.true
def out : Nat := heavy 20
def main : IO Unit := IO.println (Nat.toString out)
"

def ffiStrlen : String := "import IO
extern \"strlen\" (header := \"string.h\") strlen : String → Nat
def out : Nat := strlen \"hello\"
def main : IO Unit := IO.println (Nat.toString out)
"

def exitCode : String := "import Prelude
import Sys
def main : IO Unit := do
  IO.println \"exit\";
  Process.exit 7
"

def errTypeMismatch : String := "import Prelude
def bad (A : Type) (a : A) : Type := a
"

def errUnknown : String := "import Prelude
def bad : Type := Nope
"

def errLinear : String := "import Prelude
def dup {A : Type} (f : A → A → A) (1 x : A) : A := f x x
"

/-- A compile-only program: the generated C and LLVM are compared (normalized) with the
baseline.  Running it is not part of the case (a pure `main` is fine for both backends,
but `wiz-c-gc`/`-rc` define their C entry point differently). -/
def compileStruct : String := "import Prelude
structure P where
  x : Nat
  y : Nat
def main : Nat := (P.mk 3 4).y + 1
"

def compileString : String := "import Prelude
def main : String := String.append \"a\" \"b\"
"

def corpus : List Spec := [
  { name := "arith-big", src := arithBig, expected := "2432902008176640000\n", irExpr := some "out" },
  { name := "arith-ops", src := arithOps, expected := "62300\n", irExpr := some "out" },
  { name := "data-list", src := dataList, expected := "285\n", irExpr := some "out" },
  { name := "data-tree", src := dataTree, expected := "6\n", irExpr := some "out" },
  { name := "data-array-map", src := dataArrayMap, expected := "16\n", irExpr := some "out",
    skip := [(.irInterp, "the IR interpreter has no Array/StrMap natives")] },
  { name := "data-string", src := dataString, expected := "10\n", irExpr := some "out" },
  { name := "io-sequence", src := ioSequence, expected := "differential\n42\n",
    skip := [(.irInterp, "the IR interpreter does not run an IO `main`")] },
  { name := "classes", src := classes, expected := "41\n", irExpr := some "out",
    skip := [(.wizGC, "the self-hosted frontend has no type classes"),
             (.wizRC, "the self-hosted frontend has no type classes")] },
  { name := "ffi-strlen", src := ffiStrlen, expected := "5\n",
    skip := [(.irInterp, "the IR interpreter cannot call a foreign function")] },
  { name := "exit-code", src := exitCode, expected := "exit\n", expectedExit := 7,
    skip := [(.irInterp, "the IR interpreter does not run an IO `main`")] },
  { name := "error-type-mismatch", src := errTypeMismatch, kind := .reject,
    expectedDiag := "type mismatch", skip := [(.irInterp, "rejected before the IR exists")] },
  { name := "error-unknown", src := errUnknown, kind := .reject,
    expectedDiag := "unknown identifier", skip := [(.irInterp, "rejected before the IR exists")] },
  { name := "error-linear", src := errLinear, kind := .reject,
    expectedDiag := "quantity", skip := [(.irInterp, "rejected before the IR exists")] },
  { name := "compile-struct", src := compileStruct, kind := .compileOnly },
  { name := "compile-string", src := compileString, kind := .compileOnly }
]

/-! ## Results and the baseline -/

inductive Verdict where
  | pass
  | skipped
  | diff
  deriving BEq, DecidableEq, Repr

def Verdict.name : Verdict → String
  | .pass => "pass"
  | .skipped => "skip"
  | .diff => "diff"

structure Result where
  caseName : String
  pipeline : Pipeline
  verdict : Verdict
  /-- stdout for a run, the normalized diagnostic for a reject, the normalized-code hash
  for a compile-only case, empty for a skip. -/
  observed : String := ""
  exit : Nat := 0
  note : String := ""
  /-- The normalized generated code, for saving on a compile-only diff. -/
  artifact : Option String := none

def Result.fail (c : Spec) (p : Pipeline) (note : String) : Result :=
  { caseName := c.name, pipeline := p, verdict := .diff, note }

def Result.skip (c : Spec) (p : Pipeline) (why : String) : Result :=
  { caseName := c.name, pipeline := p, verdict := .skipped, note := why }

/-- Backslashes and line/field separators in a baseline field. -/
def escape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\t" "\\t" |>.replace "\n" "\\n" |>.replace "\r" "\\r"

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

structure BaselineRow where
  caseName : String
  pipeline : String
  verdict : String
  exit : Nat
  observed : String
  note : String := ""

def baselinePath : System.FilePath := "Tests/Differential/baseline.tsv"

def readBaseline : IO (List BaselineRow) := do
  let text ← IO.FS.readFile baselinePath
  return (text.splitOn "\n").filterMap fun line =>
    if line.isEmpty || line.startsWith "#" then none
    else match line.splitOn "\t" with
      | [c, p, v, e, o, n] =>
        some { caseName := c, pipeline := p, verdict := v, exit := e.toNat?.getD 0,
               observed := unescape o, note := unescape n }
      | [c, p, v, e, o] =>
        some { caseName := c, pipeline := p, verdict := v, exit := e.toNat?.getD 0,
               observed := unescape o }
      | _ => none

def renderBaseline (rs : List Result) : String :=
  let rows := rs.map fun r =>
    String.intercalate "\t" [r.caseName, r.pipeline.name, r.verdict.name, toString r.exit,
      escape r.observed, escape r.note]
  "# Tests/Differential/baseline.tsv — golden baseline for the COMP-02 pipelines.\n" ++
  "# Regenerate deliberately with `scripts/differential.sh --update`; review the diff.\n" ++
  "# case\tpipeline\tverdict\texit\tobserved\tnote\n" ++
  "\n".intercalate rows ++ "\n"

/-- Compare one result with its baseline row.  A skip stays a skip whatever the baseline
says (a machine without `llc`/GC must skip cleanly); a baseline skip does not fail a
current pass (the toolchain became available). -/
def checkBaseline (rows : List BaselineRow) (r : Result) : Result :=
  if r.verdict == .skipped then r else
  match rows.find? (fun b => b.caseName == r.caseName && b.pipeline == r.pipeline.name) with
  | none => { r with verdict := .diff, note := "no baseline row (run scripts/differential.sh --update after review)" }
  | some b =>
    if b.verdict == "skip" then r
    else if b.verdict == r.verdict.name && b.exit == r.exit && b.observed == r.observed then r
    else
      let bs := s!"baseline {b.verdict} exit {b.exit}: {oneLine b.observed}"
      { r with verdict := .diff, note := if r.note.isEmpty then bs else s!"{r.note}; {bs}" }
where
  oneLine (s : String) : String :=
    let s := s.replace "\n" "⏎"
    if s.length > 160 then s.take 160 |>.toString |>.append "…" else s

/-! ## Running a pipeline -/

structure ToolOutput where
  code : UInt32
  stdout : String
  stderr : String

def runTool (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (secs : Nat := 300) : IO ToolOutput := do
  let out ← IO.Process.output
    { cmd := "timeout", args := #[toString secs, cmd] ++ args, cwd := cwd }
  pure { code := out.exitCode, stdout := out.stdout, stderr := out.stderr }

def noToolchain (e : String) : Option String :=
  if (e.splitOn "gmp.h").length > 1 then some "no GMP headers"
  else if (e.splitOn "llc").length > 1 then some "no LLVM `llc`"
  else if (e.splitOn "could not execute external process").length > 1 then some "no C toolchain"
  else if (e.splitOn "No such file").length > 1 then some "no C toolchain"
  else none

/-- Error messages are pinned by text, not position; a temporary directory that the
frontend happened to mention is replaced. -/
def normalizeDiagnostics (dir : System.FilePath) (msgs : List String) : String :=
  let msgs := msgs.map fun m =>
    let m := m.replace dir.toString "<tmp>"
    "\n".intercalate ((m.splitOn "\n").map (·.trimAscii.toString))
  "\n".intercalate msgs |>.trimAscii.toString

/-- Text normalization for generated code: full-line comments, blank lines and trailing
whitespace are dropped; nothing inside a line is rewritten (so string literals and
indentation stay meaningful). -/
def normalizeCode (s : String) : String :=
  let lines := (s.splitOn "\n").map fun l => (l.trimAscii.toString).replace "\t" "  "
  let keep (l : String) : Bool :=
    let t := l.trimAscii.toString
    !t.isEmpty && !t.startsWith "/*" && !t.startsWith ";" && !t.startsWith "//"
  "\n".intercalate (lines.filter keep)

def frontendErrors (sp : Spec) : IO (List String) := do
  let loader ← Tests.Elab.libLoader
  let s := runFrontend (R := ZeroOneMany) sp.src { trustedModule := Tests.libModule, loader }
  pure ((s.messages.filter (·.severity == .error)).toList.map (·.text))

/-- Lean C/LLVM: the same frontend and IR, two code generators. -/
def leanPipeline (sp : Spec) (llvm : Bool) : IO Result := do
  let p := if llvm then Pipeline.leanLLVM else Pipeline.leanC
  let loader ← Tests.Elab.libLoader
  let s := runFrontend (R := ZeroOneMany) sp.src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).toList.map (·.text)
  if sp.kind == .reject then
    if errs.isEmpty then return Result.fail sp p "accepted (expected a diagnostic)"
    let diag := normalizeDiagnostics (System.FilePath.mk "/tmp") errs
    if sp.expectedDiag != "" && (diag.splitOn sp.expectedDiag).length == 1 then
      return Result.fail sp p s!"diagnostic does not mention '{sp.expectedDiag}': {diag}"
    return { caseName := sp.name, pipeline := p, verdict := .pass, observed := diag }
  if !errs.isEmpty then
    return Result.fail sp p s!"frontend errors: {normalizeDiagnostics (System.FilePath.mk "/tmp") errs}"
  if sp.kind == .compileOnly then
    match Build.irProgram s "main" with
    | .error e => return Result.fail sp p s!"cannot generate IR: {e}"
    | .ok (decls, ty) =>
      let io := Build.isIO ty
      let code := if llvm then LLVM.program decls io false
        else
          let c := C.program decls io (Build.extraC s) s.globals.unboxStructs
          -- drop the runtime and glue: they are not this generator's output
          match c.splitOn "/* ---- generated ---- */" with
          | [_, generated] => generated
          | _ => c
      let norm := normalizeCode code
      if norm.trimAscii.isEmpty then return Result.fail sp p "generated no code"
      return { caseName := sp.name, pipeline := p, verdict := .pass,
               observed := toString (hash norm), artifact := some norm }
  let tc ← Tests.toolchain
  let dir ← IO.FS.createTempDir
  let exe := dir / "wiz_main"
  match ← Build.build tc s "main" exe llvm false with
  | .error e =>
    match noToolchain e with
    | some why => return Result.skip sp p why
    | none => return Result.fail sp p s!"build failed: {e}"
  | .ok _ =>
    let out ← runTool exe.toString #[] (some dir) 120
    if out.code == 124 then return Result.fail sp p "the program timed out"
    let note := if out.code.toNat == sp.expectedExit then "" else
      s!"expected exit {sp.expectedExit}, got {out.code.toNat}"
    if out.stdout != sp.expected then
      return { caseName := sp.name, pipeline := p, verdict := .diff, observed := out.stdout,
               exit := out.code.toNat,
               note := if note.isEmpty then s!"stdout differs: expected {repr sp.expected}" else note }
    if !note.isEmpty then
      return { caseName := sp.name, pipeline := p, verdict := .diff, observed := out.stdout,
               exit := out.code.toNat, note }
    return { caseName := sp.name, pipeline := p, verdict := .pass, observed := out.stdout,
             exit := out.code.toNat }

/-- The self-hosted compiler: generated C, then the self-hosted runtime in GC or RC mode. -/
def wizPipeline (sp : Spec) (rc : Bool) : IO Result := do
  let p := if rc then Pipeline.wizRC else Pipeline.wizGC
  let tc ← Tests.toolchain
  if !rc && tc.gcCflags.isEmpty then
    return Result.skip sp p "no Boehm GC (`--gc-cflags` is empty)"
  match ← Tests.Elab.selfhostCompiler with
  | .error e =>
    match noToolchain e with
    | some why => return Result.skip sp p why
    | none => return Result.fail sp p s!"cannot build the self-hosted compiler: {e}"
  | .ok exe =>
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / "input.wiz") sp.src
    let flags : Array String := if rc then #["--rc"] else #[]
    let comp ← runTool exe.toString flags (some dir) 300
    if comp.code != 0 then
      if sp.kind == .reject then
        let diag := normalizeDiagnostics dir ((comp.stderr.splitOn "\n").filter (·.startsWith "error"))
        if diag.isEmpty then return Result.fail sp p s!"failed without an `error` line: {comp.stderr}"
        if sp.expectedDiag != "" && (diag.splitOn sp.expectedDiag).length == 1 then
          return Result.fail sp p s!"diagnostic does not mention '{sp.expectedDiag}': {diag}"
        return { caseName := sp.name, pipeline := p, verdict := .pass, observed := diag }
      return Result.fail sp p s!"the self-hosted compiler failed ({comp.code}): {comp.stderr}"
    if sp.kind == .reject then return Result.fail sp p "accepted (expected a diagnostic)"
    if sp.kind == .compileOnly then
      let norm := normalizeCode comp.stdout
      if norm.trimAscii.isEmpty then return Result.fail sp p "generated no code"
      return { caseName := sp.name, pipeline := p, verdict := .pass,
               observed := toString (hash norm), artifact := some norm }
    let cf := dir / "out.c"
    IO.FS.writeFile cf comp.stdout
    let rt := (← IO.currentDir) / "selfhost"
    let prog := dir / "prog"
    let args := #["-O2", "-w", s!"-I{rt}"] ++
      (if rc then #[] else tc.gcCflags.toArray) ++
      #[cf.toString, "-o", prog.toString] ++
      (if rc then #[] else tc.gcLdflags.toArray)
    let cc ← runTool tc.cc args (some dir) 120
    if cc.code != 0 then
      if (cc.stderr.splitOn "gc.h").length > 1 then return Result.skip sp p "no Boehm GC headers"
      match noToolchain cc.stderr with
      | some w => return Result.skip sp p w
      | none => return Result.fail sp p s!"cc failed: {cc.stderr}"
    let out ← runTool prog.toString #[] (some dir) 120
    if out.code == 124 then return Result.fail sp p "the program timed out"
    let note := if out.code.toNat == sp.expectedExit then "" else
      s!"expected exit {sp.expectedExit}, got {out.code.toNat}"
    if out.stdout != sp.expected then
      return { caseName := sp.name, pipeline := p, verdict := .diff, observed := out.stdout,
               exit := out.code.toNat,
               note := if note.isEmpty then s!"stdout differs: expected {repr sp.expected}" else note }
    if !note.isEmpty then
      return { caseName := sp.name, pipeline := p, verdict := .diff, observed := out.stdout,
               exit := out.code.toNat, note }
    return { caseName := sp.name, pipeline := p, verdict := .pass, observed := out.stdout,
             exit := out.code.toNat }

/-- The IR interpreter (Lean's `#run`): the same source plus the case's pure expression. -/
def irPipeline (sp : Spec) : IO Result := do
  if let some why := skipReason sp .irInterp then return Result.skip sp .irInterp why
  let some expr := sp.irExpr
    | return Result.skip sp .irInterp "no pure expression for the interpreter"
  let src := sp.src ++ "\n#run " ++ expr ++ "\n"
  let loader ← Tests.Elab.libLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).toList.map (·.text)
  if sp.kind == .reject then
    if errs.isEmpty then return Result.fail sp .irInterp "accepted (expected a diagnostic)"
    let diag := normalizeDiagnostics (System.FilePath.mk "/tmp") errs
    if sp.expectedDiag != "" && (diag.splitOn sp.expectedDiag).length == 1 then
      return Result.fail sp .irInterp s!"diagnostic does not mention '{sp.expectedDiag}': {diag}"
    return { caseName := sp.name, pipeline := .irInterp, verdict := .pass, observed := diag }
  if !errs.isEmpty then
    return Result.fail sp .irInterp s!"errors: {normalizeDiagnostics (System.FilePath.mk "/tmp") errs}"
  let infos := (s.messages.filter (·.severity == .info)).toList.map (·.text)
  let value := "\n".intercalate infos
  if value != sp.expected.trimAscii.toString then
    return { caseName := sp.name, pipeline := .irInterp, verdict := .diff, observed := value,
             note := s!"expected {repr (sp.expected.trimAscii.toString)}" }
  return { caseName := sp.name, pipeline := .irInterp, verdict := .pass, observed := value }

def runCase (sp : Spec) (p : Pipeline) : IO Result :=
  if let some why := skipReason sp p then pure (Result.skip sp p why)
  else match p with
  | .leanC => leanPipeline sp false
  | .leanLLVM => leanPipeline sp true
  | .wizGC => wizPipeline sp false
  | .wizRC => wizPipeline sp true
  | .irInterp => irPipeline sp

/-! ## Reports -/

def Result.symbol (r : Result) : String :=
  match r.verdict with
  | .pass => "ok"
  | .skipped => "skip"
  | .diff => "DIFF"

def cell (s : String) : String :=
  let s := s.replace "\n" "⏎" |>.replace "|" "\\|"
  if s.length > 90 then s.take 90 |>.toString |>.append "…" else s

def renderReport (rs : List Result) : String := Id.run do
  let cases := corpus.filter fun c => rs.any (·.caseName == c.name)
  let p := rs.countP (·.verdict == .pass)
  let k := rs.countP (·.verdict == .skipped)
  let d := rs.countP (·.verdict == .diff)
  let mut out := "# Differential pipelines — report\n\n"
  out := out ++ s!"Corpus: {cases.length} programs × {allPipelines.length} pipelines; " ++
    s!"{p} passed, {k} skipped, {d} diff.\n\n"
  out := out ++ "| case | " ++ String.intercalate " | " (allPipelines.map (·.name)) ++ " |\n"
  out := out ++ "|---|" ++ String.join (allPipelines.map fun _ => "---|") ++ "\n"
  for c in cases do
    out := out ++ "| " ++ c.name ++ " | "
    for pipe in allPipelines do
      let v := match rs.find? (fun r => r.caseName == c.name && r.pipeline == pipe) with
        | some r => r.symbol
        | none => "—"
      out := out ++ v ++ " | "
    out := out ++ "\n"
  let problems := rs.filter fun r => r.verdict != .pass
  if !problems.isEmpty then
    out := out ++ "\n## Skips and diffs\n\n| case | pipeline | verdict | exit | note | observed |\n"
    out := out ++ "|---|---|---|---|---|---|\n"
    for r in problems do
      out := out ++ s!"| {r.caseName} | {r.pipeline.name} | {r.symbol} | {r.exit} | " ++
        s!"{cell r.note} | {cell r.observed} |\n"
  out := out ++ "\nExit codes and exact stdout are compared for runs; compile-time diagnostics " ++
    "are pinned per pipeline in the baseline; compile-only rows compare a hash of normalized " ++
    "generated code.  A skip is not a pass.\n"
  return out

/-! ## The command (`tests --differential`) -/

def parseArgs (args : List String) : IO (Bool × Option System.FilePath × List String × List String) := do
  let rec go (update : Bool) (report : Option System.FilePath) (cases pipes : List String)
      : List String → IO (Bool × Option System.FilePath × List String × List String)
    | [] => pure (update, report, cases.reverse, pipes.reverse)
    | "--update" :: rest => go true report cases pipes rest
    | "--report" :: f :: rest => go update (some (System.FilePath.mk f)) cases pipes rest
    | "--case" :: c :: rest => go update report (c :: cases) pipes rest
    | "--pipeline" :: p :: rest => go update report cases (p :: pipes) rest
    | a :: _ => throw (IO.userError s!"unknown argument to --differential: {a}")
  go false none [] [] args

def selected (cases pipes : List String) (sp : Spec) (p : Pipeline) : Bool :=
  (cases.isEmpty || cases.contains sp.name) && (pipes.isEmpty || pipes.contains p.name)

def main (args : List String) : IO UInt32 := do
  let (update, reportPath, onlyCases, onlyPipes) ← parseArgs args
  if update && (!onlyCases.isEmpty || !onlyPipes.isEmpty) then
    throw (IO.userError "--update needs the whole corpus (drop --case/--pipeline)")
  let rows ← if update then pure [] else readBaseline
  let selectedCorpus := corpus.filter fun c =>
    onlyCases.isEmpty || onlyCases.contains c.name
  let selectedPipes := allPipelines.filter fun p =>
    onlyPipes.isEmpty || onlyPipes.contains p.name
  let mut raw : List Result := []
  for sp in selectedCorpus do
    for p in selectedPipes do
      let r ← runCase sp p
      raw := raw ++ [r]
  let checked := if update then raw else raw.map (checkBaseline rows ·)
  let report := renderReport checked
  IO.print report
  if let some path := reportPath then
    if let some d := path.parent then IO.FS.createDirAll d
    IO.FS.writeFile path report
  if update then
    if let some d := baselinePath.parent then IO.FS.createDirAll d
    IO.FS.writeFile baselinePath (renderBaseline raw)
    IO.eprintln s!"wrote {baselinePath} ({raw.length} rows)"
  -- save generated code when a compile-only row differs, for a readable diff
  let dir : System.FilePath := ".lake/differential"
  for r in checked do
    if r.verdict == .diff then
      if let some art := r.artifact then
        IO.FS.createDirAll dir
        IO.FS.writeFile (dir / s!"{r.caseName}.{r.pipeline.name}.txt") art
  let bad := checked.filter (·.verdict == .diff)
  if bad.isEmpty then return 0
  IO.eprintln s!"\n{bad.length} differential row(s) differ"
  return 1

end Tests.Differential
