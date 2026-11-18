import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# `=selfhost-libdiff`: where replacement parity actually stands

The parity matrix (`wiz-notes/selfhost-parity.md`) counts features; this group measures
the library. For every `*.wiz` under `lib/` (and `scry/`) it runs **both** compilers on
the file as a root module and compares

* acceptance (does the frontend report an error at all),
* the first error's code,
* its span (file, line, column),
* its message text (whitespace-normalised), and
* the number of declarations the frontend produced for that file

and reports the first divergence. Files that both reject are counted apart from files
whose verdicts differ; the latter are the gap list, grouped by the construct the
self-hosted frontend is missing (`by`, `syntax`, `namespace`, …).

The host side runs the Lean frontend in a child process (`--libdiff-host FILE`, the same
`runFrontend` `wiz check` runs), so this process can bound it; the self-hosted side runs
the compiler binary the `selfhost` group builds (`selfhostCompiler`), `check FILE
--types`, whose info lines are the per-declaration reports.

The group never fails because of a gap: it measures. It fails only when the harness
itself cannot run (a toolchain problem is a skip, the way the `selfhost` group skips).

Usage (a work list, not a gate):

    tests --libdiff                          # every lib/ and scry/ file
    tests --libdiff --limit 10               # the first ten
    tests --libdiff --only lib/Hoare.wiz     # one file (repeatable)
    tests --libdiff --json                   # one JSON record per line
    tests --libdiff --baseline FILE          # write it, or diff against it
    tests --libdiff --jobs 3                 # three files at a time (capped by CPUs and memory)

`lake test -- '=selfhost-libdiff'` runs the sweep with the defaults (the driver's
`--jobs N`, capped as above) and writes the report to `.lake/libdiff/` (the harness hides
a passing case's output).
-/

/-- The module roots both toolchains resolve `import M` under, in order. The checkout's
`lib/` first (the toolchain library), then the package roots of `scry/`. -/
def libDiffRoots : List String :=
  ["lib", "drafts/feral/lib", "scry/src", "scry/gen", "scry", "scry/tests", "scry/tools"]

/-- Every `*.wiz` under `dir`, recursively. -/
partial def libDiffWalk (dir : System.FilePath) (acc : Array String) : IO (Array String) := do
  unless ← dir.pathExists do return acc
  let mut acc := acc
  for e in ← dir.readDir do
    if ← e.path.isDir then
      acc ← libDiffWalk e.path acc
    else if e.path.extension == some "wiz" then
      acc := acc.push e.path.toString
  pure acc

/-- Every `*.wiz` under `lib/` and `scry/`, sorted. -/
def libDiffFiles : IO (Array String) := do
  let all := (← libDiffWalk "lib" #[]) ++ (← libDiffWalk "scry" #[])
  pure (all.qsort (· < ·))

/-- The module a file's path names, for `--only`: `lib/Hdl/Uart.wiz` is `Hdl.Uart`. -/
def libDiffModule (file : String) : String :=
  let rel :=
    if file.startsWith "lib/" then (file.drop 4).toString
    else if file.startsWith "scry/src/" then (file.drop 9).toString
    else if file.startsWith "scry/gen/" then (file.drop 9).toString
    else if file.startsWith "scry/tests/" then (file.drop 11).toString
    else if file.startsWith "scry/tools/" then (file.drop 11).toString
    else if file.startsWith "scry/" then (file.drop 5).toString
    else file
  (rel.dropEnd 4).toString.replace "/" "."

/-- Does `--only ARG` pick `file`? A path, a path suffix, or the module name. -/
def libDiffPicks (arg file : String) : Bool :=
  arg == file || file.endsWith ("/" ++ arg) || arg == libDiffModule file || arg ++ ".wiz" == file

/-! ## A side's verdict -/

/-- One compiler's verdict on a file. `status` is `ok`, `timeout` or `crash` (a signal
or an allocation failure). -/
structure Side where
  accepted : Bool := false
  exitCode : UInt32 := 0
  errors : Nat := 0
  decls : Nat := 0
  /-- the first error's stable code (`""` if it has none) -/
  code : String := ""
  /-- the file the first error is in (the checked file, or an imported module) -/
  efile : String := ""
  line : Nat := 0
  col : Nat := 0
  msg : String := ""
  status : String := "ok"
  note : String := ""
  /-- the run's wall time (milliseconds), measured by the sweep -/
  ms : Nat := 0
  deriving Inhabited

def jsonOfSide (s : Side) : Lean.Json :=
  Lean.Json.mkObj [
    ("accepted", .bool s.accepted), ("exit", .num s.exitCode.toNat), ("errors", .num s.errors),
    ("decls", .num s.decls), ("code", .str s.code), ("file", .str s.efile),
    ("line", .num s.line), ("col", .num s.col), ("msg", .str s.msg),
    ("status", .str s.status), ("note", .str s.note), ("ms", .num s.ms)]

def jStr (j : Lean.Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def jNat (j : Lean.Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0

def jBool (j : Lean.Json) (k : String) : Bool := (j.getObjValAs? Bool k).toOption.getD false

def sideOfJson (j : Lean.Json) : Side :=
  { accepted := jBool j "accepted", exitCode := (jNat j "exit").toUInt32, errors := jNat j "errors",
    decls := jNat j "decls", code := jStr j "code", efile := jStr j "file",
    line := jNat j "line", col := jNat j "col", msg := jStr j "msg",
    status := (if (jStr j "status").isEmpty then "ok" else jStr j "status"), note := jStr j "note" }

/-! ## The host side (a child process of the sweep, so it can be bounded) -/

/-- The init state `Main.initState` builds for `wiz check`, with `libDiffRoots` as the
module roots (no cache: the sweep wants the frontend's own output, not a replay). -/
def libDiffHostState (file : String) (input : String) : IO (CommandState ZeroOneMany) := do
  let roots : List System.FilePath := libDiffRoots.map System.FilePath.mk
  let tc ← toolchain
  let closure ← Module.loadClosure roots input
  let lib : Std.HashMap Name String := closure.fold (fun m n (_, src) => m.insert n src) {}
  let headers ← Build.preprocessHeaders tc (String.join (input :: lib.values))
  let dir := (System.FilePath.mk file).parent.getD "."
  let sources ← Module.cSourceTable dir input closure
  let includes ← Module.includeTable dir input closure
  let own := Module.fromFirstRoot roots closure
  pure { loader := fun n => lib[n]?,
         cHeaders := fun h => headers[h]?,
         cSources := some (Module.cSourceResolver sources),
         includes := some (Module.includeResolver includes),
         trustedModule := fun n => own.contains n }

/-- The declarations the root file produced: the names `declSites` puts in module `""`
(minus a structure's constructors, fields and projections, which the source did not
declare), plus the file's `#check` info messages — the same count the self-hosted
frontend's `--types` report gives (one line per declaration and per `#check`). -/
def libDiffHostDecls (s : CommandState ZeroOneMany) : Nat :=
  let src : Name → Bool := fun n =>
    match s.declDocs.get? n with
    | none => true
    | some d => !(["constructor", "field", "auxiliary"].contains d.kind)
  let decls := (s.declSites.toList.filter fun (n, (_, m)) => m == "" && src n).length
  decls + (s.messages.filter (·.severity == .info)).size

/-- What the Lean frontend says about `file`: `--libdiff-host`'s body. -/
def libDiffHost (file : String) : IO Side := do
  let input ← IO.FS.readFile file
  let init ← libDiffHostState file input
  let s := runFrontend (R := ZeroOneMany) input init
  let errs := s.messages.filter (·.severity == .error)
  let lineCols (m : Msg) : Nat × Nat :=
    let (l, c) := lineCol input m.info.start
    (l + 1, c + 1)
  let first := errs[0]?
  pure { accepted := errs.isEmpty, exitCode := if errs.isEmpty then 0 else 1,
         errors := errs.size, decls := libDiffHostDecls s,
         code := first.map (ErrorCode.reported ·.code) |>.getD "",
         efile := if first.isSome then file else "",
         line := first.map (fun m => (lineCols m).1) |>.getD 0,
         col := first.map (fun m => (lineCols m).2) |>.getD 0,
         msg := first.map (·.text) |>.getD "" }

/-- `tests --libdiff-host FILE [toolchain flags]`: one JSON line, the host's verdict. -/
def libDiffHostMain (args : List String) : IO UInt32 := do
  let file := match args with
    | f :: _ => f
    | [] => ""
  if file.isEmpty then
    IO.eprintln "usage: tests --libdiff-host FILE"
    return 2
  let side ← try libDiffHost file
    catch e => pure ({ status := "crash", note := toString e } : Side)
  IO.println (Lean.Json.compress (jsonOfSide side))
  return 0

/-! ## The self-hosted side -/

/-- One diagnostic line of the self-hosted driver:
`file:line:col: severity: message [code]`. -/
structure LibDiag where
  file : String
  line : Nat
  col : Nat
  sev : String
  msg : String
  code : String

/-- Split a trailing ` [code]` off `s`. -/
def libDiffSplitCode (s : String) : String × String :=
  let parts := s.splitOn " ["
  match parts.reverse with
  | last :: revInit =>
    if last.endsWith "]" then
      (String.intercalate " [" revInit.reverse, (last.dropEnd 1).toString)
    else (s, "")
  | [] => (s, "")

def libDiffParseDiag (line : String) : Option LibDiag :=
  match line.splitOn ":" with
  | f :: ln :: cl :: rest =>
    match ln.trimAscii.toString.toNat?, cl.trimAscii.toString.toNat? with
    | some ln, some cl =>
      match rest with
      | sev :: msgParts =>
        let (msg, code) := libDiffSplitCode ((String.intercalate ":" msgParts).trimAscii.toString)
        some { file := f, line := ln, col := cl, sev := sev.trimAscii.toString, msg, code }
      | [] => none
    | _, _ => none
  | _ => none

/-- The declaration lines of the self-hosted `--types` report: its info lines for
`file`, without the projections (`T.f`) a structure also reports. -/
def libDiffSelfDecls (file : String) (diags : List LibDiag) : Nat :=
  (diags.filter fun d =>
    d.sev == "info" && d.file == file &&
      (let head := (d.msg.splitOn " : ").headD ""
       head.contains ' ' || !head.contains '.')).length

/-- Bounded run: a wall-clock limit (`timeout -k 5`) and, with `memMB > 0`, a
virtual-memory limit. -/
def libDiffRun (cmd : String) (args : Array String) (secs memMB : Nat) :
    IO (UInt32 × String × String) := do
  let limit := if memMB == 0 then "" else s!"ulimit -v {memMB * 1024} 2>/dev/null; "
  let script := s!"{limit}exec timeout -k 5 {secs} \"$0\" \"$@\""
  let out ← IO.Process.output
    { cmd := "sh", args := #["-c", script, cmd] ++ args, stdin := .null }
  pure (out.exitCode, out.stdout, out.stderr)

/-- `status` from a bounded run's exit code. 3 is the self-hosted runtime giving up
(`die`/`unreach` in selfhost/rt.c, `wiz_panic` in runtime/rt_core.inc): "out of memory"
when a `malloc` fails under the `ulimit -v` bound, or "applying a non-function". It
prints `wiz: REASON` and no diagnostics, so read as an exit status it looked like an
accepted file with no declarations (lib/BitVecAdd.wiz: "self ok (0 decls)"). -/
def libDiffStatus (code : UInt32) : String :=
  if code == 124 then "timeout"
  else if code == 137 || code == 139 || code == 3 then "crash"
  else "ok"

/-- The runtime's `wiz: REASON` line on stderr, if it gave up (exit 3). -/
def libDiffRuntimeNote (err : String) : String :=
  match (err.splitOn "\n").reverse.find? (·.startsWith "wiz: ") with
  | some l => (l.take 200).toString
  | none => ""

/-- Run the self-hosted compiler's `check FILE --types` and read its diagnostics. -/
def libDiffSelf (exe : System.FilePath) (file : String) (secs memMB : Nat)
    (cache : String) : IO Side := do
  let args : Array String :=
    #["check", file, "--types", "--cache", cache] ++
    (libDiffRoots.flatMap (fun r => ["-I", r])).toArray
  let (code, out, err) ← libDiffRun exe.toString args secs memMB
  let lines := out.splitOn "\n" ++ err.splitOn "\n"
  let diags := lines.filterMap libDiffParseDiag
  let errs := diags.filter (·.sev == "error")
  -- the first error in the file itself if there is one, else the first import error
  let first := (errs.find? (·.file == file)).orElse (fun _ => errs[0]?)
  pure { accepted := errs.isEmpty, exitCode := code, errors := errs.length,
         decls := libDiffSelfDecls file diags,
         code := first.map (·.code) |>.getD "",
         efile := first.map (·.file) |>.getD "",
         line := first.map (·.line) |>.getD 0,
         col := first.map (·.col) |>.getD 0,
         msg := first.map (·.msg) |>.getD "",
         status := libDiffStatus code,
         note := if libDiffStatus code == "crash" then libDiffRuntimeNote err else "" }

/-! ## Comparing the two -/

/-- Collapse whitespace, drop a trailing full stop: the text two frontends can
reasonably share. -/
def libDiffNormMsg (s : String) : String :=
  let ws := ((s.replace "\n" " ").splitOn " ").filter (· != "")
  let t := " ".intercalate ws
  if t.endsWith "." then (t.dropEnd 1).toString else t

/-- The friendly name of a missing construct, from the kind the self-hosted frontend
names in `unsupported command/syntax <kind>`. -/
def libDiffConstruct (k : String) : String :=
  let k := if k.startsWith "command." then (k.drop 8).toString
    else if k.startsWith "term." then (k.drop 5).toString
    else k
  match k with
  | "by" | "byTactic" => "by"
  | "syntax" => "syntax"
  | "macroRules" => "macro_rules"
  | "notation" => "notation"
  | "namespace" => "namespace"
  | "open" => "open"
  | "section" => "section"
  | "variable" => "variable"
  | "deriving" => "deriving"
  | "universe" => "universe"
  | "setOption" => "set_option"
  | "builtin" => "builtin"
  | "example" => "example"
  | "listLit" | "listCons" => "list literal"
  | "exists" => "exists"
  | "ir" => "ir"
  | "run" => "run"
  | "erase" => "erase"
  | k => k

/-- The construct an error is about, for the gap list: the kind the message names, else
a keyword the parser stopped at, else the error code. -/
def libDiffClassOf (s : Side) : String :=
  let m := libDiffNormMsg s.msg
  let after (p : String) : Option String :=
    if m.startsWith p then
      let rest := (m.drop p.length).toString
      some (libDiffConstruct ((rest.splitOn " ").headD rest))
    else none
  match after "unsupported syntax " with
  | some c => c
  | none =>
  match after "unsupported command " with
  | some c => c
  | none =>
    let keywords := ["by", "syntax", "macro_rules", "notation", "namespace", "open", "section",
      "variable", "deriving", "universe", "set_option", "builtin", "example"]
    match keywords.find? (fun k => (m.splitOn ("'" ++ k ++ "'")).length > 1) with
    | some k => k
    | none =>
      if s.code == "unknown-module" then "import"
      else if s.code == "parse-error" then "parse-error"
      else if s.code == "" then "other"
      else s.code

/-- What the comparison found. -/
structure LibRec where
  file : String
  host : Side
  self : Side
  /-- `ok`, `rejected` (both reject), `diverging` (the verdicts differ), `bounded`
  (a run hit the time or memory limit) -/
  verdict : String
  /-- `acceptance`, `code`, `span`, `message`, `decls`, `run`, or `""` (agreement) -/
  divergence : String
  /-- the missing construct, for a divergence and for a rejection -/
  klass : String
  note : String := ""
  deriving Inhabited

def libDiffCompare (file : String) (h s : Side) : LibRec :=
  let bounded := h.status != "ok" || s.status != "ok"
  let verdict :=
    if bounded then "bounded"
    else if h.accepted && s.accepted then if h.decls == s.decls then "ok" else "diverging"
    else if h.accepted != s.accepted then "diverging"
    else "rejected"
  let divergence :=
    if bounded then "run"
    else if h.accepted && s.accepted then (if h.decls == s.decls then "" else "decls")
    else if h.accepted != s.accepted then "acceptance"
    else if h.code != s.code then "code"
    else if h.line != s.line || h.col != s.col || (s.efile != "" && s.efile != file) then "span"
    else if libDiffNormMsg h.msg != libDiffNormMsg s.msg then "message"
    else ""
  let klass := if s.accepted then "" else libDiffClassOf s
  let note :=
    if bounded then
      (if h.status != "ok" then s!"host {h.status}" else "") ++
      (if s.status != "ok" then (if h.status != "ok" then "; " else "") ++ s!"self {s.status}" ++
        (if s.note.isEmpty then "" else s!" ({s.note})") else "")
    else if !s.accepted && s.efile != "" && s.efile != file then s!"in {s.efile}"
    else ""
  { file, host := h, self := s, verdict, divergence, klass, note }

def jsonOfRec (r : LibRec) : Lean.Json :=
  Lean.Json.mkObj [
    ("file", .str r.file), ("module", .str (libDiffModule r.file)),
    ("scope", .str (if r.file.startsWith "lib/" then "lib" else "scry")),
    ("verdict", .str r.verdict), ("divergence", .str r.divergence),
    ("class", .str r.klass), ("note", .str r.note),
    ("host", jsonOfSide r.host), ("self", jsonOfSide r.self)]

/-! ## The sweep and the report -/

/-- The sweep's knobs. -/
structure LibDiffOpts where
  limit : Nat := 0
  only : List String := []
  json : Bool := false
  baseline : Option String := none
  hostSecs : Nat := 60
  selfSecs : Nat := 120
  memMB : Nat := 4096
  /-- how many files to check at once: 0 is auto (`libDiffAsked`: the CPUs minus one,
  capped by the free memory at `memMB` per file); an explicit `--jobs N` (or the
  driver's `--jobs N`) overrides it -/
  jobs : Nat := 0
  deriving Inhabited

/-- A record as one line of the report: verdict, the two sides, and the first divergence. -/
def libDiffRender (r : LibRec) : String :=
  let h := r.host
  let s := r.self
  let tag := match r.verdict with
    | "ok" => "ok     "
    | "rejected" => "reject "
    | "diverging" => "DIVERGE"
    | "bounded" => "BOUNDED"
    | v => v
  let hostTex := if h.accepted then s!"host ok ({h.decls} decls)" else s!"host error [{h.code}]"
  let selfTex := if s.accepted then s!"self ok ({s.decls} decls)" else
    s!"self error [{s.code}] {s.line}:{s.col} {(s.msg.take 100).toString}"
  s!"{tag} {r.file}\t{hostTex} / {selfTex}" ++
    (if r.divergence.isEmpty then "" else s!"\t(first divergence: {r.divergence})") ++
    (if r.klass.isEmpty then "" else s!"\t({r.klass})") ++
    (if r.note.isEmpty then "" else s!"\t[{r.note}]")

/-- One file through both compilers: the host child (`self` with `--libdiff-host FILE`,
which is this binary) and the self-hosted compiler `exe`, each with its own bound, and
their wall times. -/
def libDiffFile (o : LibDiffOpts) (self : String) (flags : Array String)
    (exe : System.FilePath) (cache : String) (file : String) : IO LibRec := do
  let t0 ← IO.monoMsNow
  -- the host child is Lean itself (whose runtime reserves address space): it gets the
  -- time bound, and the heavy job's memory cap, not a ulimit
  let h : Side ← match ← libDiffRun self (#["--libdiff-host", file] ++ flags) o.hostSecs 0 with
    | (c, out, err) =>
      if libDiffStatus c != "ok" then
        pure ({ status := libDiffStatus c, exitCode := c, note := (err.trimAscii.toString.take 200).toString } : Side)
      else match (out.splitOn "\n").findSome? (fun l => (Lean.Json.parse l).toOption) with
        | some j => pure (sideOfJson j)
        | none => pure ({ status := "crash", note := s!"no host record: {(err.take 200).toString}" } : Side)
  let t1 ← IO.monoMsNow
  let s ← libDiffSelf exe file o.selfSecs o.memMB cache
  let t2 ← IO.monoMsNow
  pure (libDiffCompare file { h with ms := t1 - t0 } { s with ms := t2 - t1 })

/-! ## Checking files at once (`--jobs N`)

The sweep is one case (it builds the self-hosted compiler once, which takes minutes), so
it is split inside the case: N workers take the files off one list, each file exactly
once, and the records come back in the files' order, so the report, the verdicts and the
baseline signatures are those of a sequential sweep. Each file keeps its own bounds (the
time bounds start when its run starts, never while it waits), so what can change a
verdict is the machine being oversubscribed: the workers are capped by the CPUs and by
the free memory at `memMB` per file (`libDiffWorkers`), and a worker starts its next
file only while that much memory is free (`libDiffFreeMiB`) or no other file is running. -/

/-- Memory this process may still use, in MiB: the least of `MemAvailable` and, for
each cgroup it is in that has a `memory.max` (a heavy job's scope, a container), that
limit minus its `memory.current`. `none` if none of them can be read. -/
def libDiffFreeMiB : IO (Option Nat) := do
  let mut best : Option Nat := none
  let lower (b : Option Nat) (v : Nat) : Option Nat := some (match b with | some x => min x v | none => v)
  let readNat (f : String) : IO (Option Nat) := do
    try pure (← IO.FS.readFile f).trimAscii.toString.toNat? catch _ => pure none
  try
    for l in (← IO.FS.readFile "/proc/meminfo").splitOn "\n" do
      if l.startsWith "MemAvailable:" then
        match (((l.drop 13).toString.trimAscii.toString.splitOn " ").head?).bind String.toNat? with
        | some kb => best := lower best (kb / 1024)
        | none => pure ()
  catch _ => pure ()
  try
    for l in (← IO.FS.readFile "/proc/self/cgroup").splitOn "\n" do
      if l.startsWith "0::" then
        let parts := ((l.drop 3).toString.splitOn "/").filter (· != "")
        for k in [0:parts.length + 1] do
          let dir := "/sys/fs/cgroup/" ++ "/".intercalate (parts.take k)
          match ← readNat (dir ++ "/memory.max"), ← readNat (dir ++ "/memory.current") with
          | some mx, some cur => best := lower best ((mx - cur) / 1048576)
          | _, _ => pure ()
  catch _ => pure ()
  pure best

/-- The CPUs this process may run on (`nproc`, which honours the affinity mask); 1 if
that cannot be run. -/
def libDiffCpus : IO Nat := do
  try
    let out ← IO.Process.output { cmd := "nproc", stdin := .null }
    pure (max 1 (out.stdout.trimAscii.toString.toNat?.getD 1))
  catch _ => pure 1

/-- How many files the sweep asks for: `0` is auto, the CPUs minus one (the driver and
the host child still need a core); an explicit count is used as it is. -/
def libDiffAsked (jobs cpus : Nat) : Nat :=
  if jobs == 0 then max 1 (cpus - 1) else jobs

/-- How many files the sweep checks at once: what was asked for, but no more than the
CPUs (a file's bound is wall-clock time, so an oversubscribed machine would turn slow
files into `bounded` ones) and no more than the free memory holds at `memMB` per file
(the self-hosted run's bound; unknown free memory means one); at least 1. -/
def libDiffWorkers (asked cpus : Nat) (freeMiB : Option Nat) (memMB : Nat) : Nat :=
  let byMem := match freeMiB with
    | some f => if memMB == 0 then asked else f / memMB
    | none => 1
  max 1 (min asked (min cpus byMem))

partial def libDiffWaitSlot {α : Type} (slots : IO.Ref (Array (Option (Except IO.Error α))))
    (i : Nat) : IO (Except IO.Error α) := do
  match (← slots.get)[i]? with
  | some (some r) => pure r
  | _ => IO.sleep 50; libDiffWaitSlot slots i

/-- Run `work i w` for every `i < n`, each exactly once, with `jobs` workers (`w` is
the worker's 0-based slot), and give the results to `emit` in index order as they
become available. A worker starts an item only when no other item is running or
`canStart` says so (it asks again every second). An exception stops the workers from
taking new items and is rethrown, in index order, once the running items have finished.
With one worker it is a plain loop. -/
partial def libDiffPool {α : Type} (n jobs : Nat) (canStart : IO Bool)
    (work : Nat → Nat → IO α) (emit : Nat → α → IO Unit) : IO (Array α) := do
  if jobs ≤ 1 || n ≤ 1 then
    let mut out := #[]
    for i in [0:n] do
      let a ← work i 0
      emit i a
      out := out.push a
    return out
  let next ← IO.mkRef (0 : Nat)
  let active ← IO.mkRef (0 : Nat)
  let slots ← IO.mkRef (Array.replicate n (none : Option (Except IO.Error α)))
  let rec admit : IO Unit := do
    if (← active.get) == 0 || (← canStart) then active.modify (· + 1)
    else IO.sleep 1000; admit
  let worker (w : Nat) : IO Unit := do
    let mut go := true
    while go do
      let i ← next.modifyGet fun k => (k, k + 1)
      if i ≥ n then
        go := false
      else
        admit
        let r ← (work i w).toBaseIO
        active.modify (· - 1)
        slots.modify (·.set! i (some r))
  let tasks ← (List.range (min jobs n)).mapM fun w => IO.asTask (worker w) .dedicated
  let mut out := #[]
  for i in [0:n] do
    match ← libDiffWaitSlot slots i with
    | .ok a =>
      emit i a
      out := out.push a
    | .error e =>
      next.set n
      for t in tasks do
        let _ ← IO.wait t
      throw e
  for t in tasks do
    let _ ← IO.wait t
  return out

/-- Every second until `stop` is set, and every `every` seconds of it (counted from
`start`, a `monoMsNow`), `tell` the line `line` makes of the seconds elapsed. -/
partial def libDiffHeartbeat (stop : IO.Ref Bool) (every start next : Nat)
    (line : Nat → IO String) (tell : String → IO Unit) : IO Unit := do
  if ← stop.get then return
  IO.sleep 1000
  let secs := ((← IO.monoMsNow) - start) / 1000
  if secs ≥ next then
    unless ← stop.get do tell (← line secs)
    libDiffHeartbeat stop every start (next + every) line tell
  else libDiffHeartbeat stop every start next line tell

/-- A file's progress line, as it finishes: how many are done, its verdict, the file, and
the seconds its two runs took. -/
def libDiffProgressLine (done total : Nat) (r : LibRec) : String :=
  s!"libdiff [{done}/{total}] {r.verdict} {r.file} {showMs (r.host.ms + r.self.ms)} s " ++
    s!"(host {showMs r.host.ms} s, self {showMs r.self.ms} s)"

/-- Run both compilers over the selected files, `libDiffWorkers` at a time; the records,
and the number of workers. `none` when the self-hosted compiler could not be built for a
toolchain reason (the caller skips). With `tell` (the group passes the harness's
`progress`), it also reports where it is: the compiler build, one line per file as it
finishes (in the order they finish), a heartbeat every 60 s, and the counts at the end.
These lines only report; the records and verdicts are the same without them. -/
def libDiffSweep (o : LibDiffOpts) (say : String → IO Unit)
    (tell : Option (String → IO Unit) := none) : IO (Option (Array LibRec × Nat)) := do
  let tell' : String → IO Unit := fun l => match tell with | some t => t l | none => pure ()
  let all ← libDiffFiles
  let picked := all.filter fun f =>
    (o.only.isEmpty || o.only.any (libDiffPicks · f)) && f.endsWith ".wiz"
  let picked := if o.limit == 0 then picked else picked.take o.limit
  let t0 ← IO.monoMsNow
  tell' s!"libdiff: building the self-hosted compiler ({picked.size} files to check)"
  match ← selfhostCompiler with
  | .error e =>
    tell' s!"libdiff: no self-hosted compiler after {showMs ((← IO.monoMsNow) - t0)} s"
    if (e.splitOn "gmp.h").length > 1 then return none else throw (IO.userError e)
  | .ok exe =>
    let self ← IO.appPath
    let flags := (← flagsRef.get).toArray
    let cpus ← libDiffCpus
    let workers := libDiffWorkers (libDiffAsked o.jobs cpus) cpus (← libDiffFreeMiB) o.memMB
    let canStart : IO Bool := do
      match ← libDiffFreeMiB with
      | some f => pure (f ≥ o.memMB)
      | none => pure false
    -- each worker has its own self-hosted compiler cache: two workers writing one
    -- cache can read each other's half-written module records (the errors differ)
    let cache (w : Nat) : String := s!"/tmp/wiz-libdiff-cache-{w}"
    let start ← IO.monoMsNow
    tell' s!"libdiff: compiler ready ({showMs (start - t0)} s); {picked.size} files, {workers} at a time"
    let done ← IO.mkRef (0 : Nat)
    let stop ← IO.mkRef false
    let beat ← if tell.isSome then
        some <$> IO.asTask (libDiffHeartbeat stop 60 start 60 (fun secs => do
          let free := match ← libDiffFreeMiB with | some f => s!"{f} MiB" | none => "unknown"
          pure s!"libdiff: {← done.get}/{picked.size} files done, {secs} s elapsed (free memory {free})")
          tell') Task.Priority.dedicated
      else pure none
    let finish : IO Unit := do
      stop.set true
      if let some t := beat then
        let _ ← IO.wait t
    let recs ← tryFinally
        (libDiffPool picked.size workers canStart
          (fun i w => do
            let r ← libDiffFile o self.toString flags exe (cache w) picked[i]!
            if tell.isSome then
              let d ← done.modifyGet fun k => (k + 1, k + 1)
              tell' (libDiffProgressLine d picked.size r)
            pure r)
          (fun _ r => if o.json then IO.println (Lean.Json.compress (jsonOfRec r)) else say (libDiffRender r)))
        finish
    unless recs.size == picked.size && (recs.map (·.file)) == picked do
      throw (IO.userError s!"selfhost-libdiff: {recs.size} records for {picked.size} files")
    let count (v : String) : Nat := (recs.filter (·.verdict == v)).size
    let (ok, rej, div) := (count "ok", count "rejected", count "diverging")
    tell' (s!"libdiff: done, {recs.size} files in {showMs ((← IO.monoMsNow) - start)} s " ++
      s!"(compiler {showMs (start - t0)} s): ok {ok} rejected {rej} diverging {div} " ++
      s!"bounded {recs.size - ok - rej - div}")
    pure (some (recs, workers))

/-- The counts the summary prints. -/
structure LibSummary where
  ok : Nat := 0
  rejected : Nat := 0
  diverging : Nat := 0
  bounded : Nat := 0
  sameCode : Nat := 0
  sameSpan : Nat := 0
  sameMsg : Nat := 0
  hostOkSelfErr : Nat := 0
  hostErrSelfOk : Nat := 0
  /-- (class, files) for the differing verdicts, most first -/
  byConstruct : List (String × Nat) := []
  /-- (class, files) for both-rejected files -/
  byCode : List (String × Nat) := []
  /-- (file, class, message) for the differing verdicts -/
  blockers : List (String × String × String) := []
  /-- the slowest host and self-hosted runs: (milliseconds, file) -/
  slowHost : Nat × String := (0, "")
  slowSelf : Nat × String := (0, "")

def libDiffCount (xs : List String) : List (String × Nat) :=
  let counts := xs.foldl (fun m x => m.insert x (m.getD x 0 + 1)) ({} : Std.HashMap String Nat)
  let arr := counts.toList.toArray.qsort fun a b =>
    if a.2 != b.2 then a.2 > b.2 else a.1 < b.1
  arr.toList

def libDiffStep (s : LibSummary) (r : LibRec) : LibSummary :=
  match r.verdict with
  | "ok" => { s with ok := s.ok + 1 }
  | "rejected" =>
    let s := { s with rejected := s.rejected + 1 }
    match r.divergence with
    | "" => { s with sameCode := s.sameCode + 1, sameSpan := s.sameSpan + 1, sameMsg := s.sameMsg + 1 }
    | "span" => { s with sameCode := s.sameCode + 1 }
    | "message" => { s with sameCode := s.sameCode + 1, sameSpan := s.sameSpan + 1 }
    | _ => s
  | "diverging" =>
    let s := { s with diverging := s.diverging + 1 }
    if r.host.accepted && !r.self.accepted then { s with hostOkSelfErr := s.hostOkSelfErr + 1 }
    else if !r.host.accepted && r.self.accepted then { s with hostErrSelfOk := s.hostErrSelfOk + 1 }
    else s
  | _ => { s with bounded := s.bounded + 1 }

def libDiffSummarize (recs : Array LibRec) : LibSummary :=
  let s := recs.foldl libDiffStep {}
  let gaps := recs.filter (fun r => r.verdict == "diverging" && r.host.accepted && !r.self.accepted)
  let rejects := recs.filter (fun r => r.verdict == "rejected")
  let byConstruct := libDiffCount (gaps.toList.map (·.klass))
  -- the work list: the most common missing construct first, then the file name
  let rank (k : String) : Nat :=
    match byConstruct.find? (fun (k', _) => k' == k) with
    | some (_, n) => n
    | none => 0
  let entries := gaps.toList.map (fun r => (r.file, r.klass, (r.self.msg.take 110).toString))
  let blockers := (entries.toArray.qsort fun (f1, k1, _) (f2, k2, _) =>
    if rank k1 != rank k2 then (rank k2).blt (rank k1) else f1 < f2).toList
  { s with
    byConstruct := byConstruct,
    byCode := libDiffCount (rejects.toList.map (·.self.code)),
    blockers := blockers,
    slowHost := recs.foldl (fun m r => if r.host.ms > m.1 then (r.host.ms, r.file) else m) (0, ""),
    slowSelf := recs.foldl (fun m r => if r.self.ms > m.1 then (r.self.ms, r.file) else m) (0, "") }

/-- `s` padded with spaces on the right. -/
def libDiffPad (s : String) (n : Nat) : String := s ++ "".pushn ' ' (n - s.length)

def libDiffSummaryText (s : LibSummary) : String :=
  let lines := [
    s!"  ok          {s.ok}",
    s!"  rejected    {s.rejected}   (both reject; {s.sameCode} same code, {s.sameSpan} same span, {s.sameMsg} same message)",
    s!"  diverging   {s.diverging}   (host accepts, self rejects: {s.hostOkSelfErr}; host rejects, self accepts: {s.hostErrSelfOk})",
    s!"  bounded     {s.bounded}   (a run hit its time or memory bound)"]
  let byC := if s.byConstruct.isEmpty then [] else
    "\nby missing construct (files whose verdicts differ):" ::
      s.byConstruct.map (fun (k, n) => s!"  {libDiffPad k 24}{n}")
  let byE := if s.byCode.isEmpty then [] else
    "\nby error class (both reject):" ::
      s.byCode.map (fun (k, n) => s!"  {libDiffPad (if k.isEmpty then "(no code)" else k) 24}{n}")
  let top := if s.blockers.isEmpty then [] else
    "\ntop 10 blockers (host accepts, self-hosted frontend rejects):" ::
      (s.blockers.take 10).zipIdx.map (fun ((f, k, m), i) => s!"  {i + 1}. {f}\t{k}\t{m}")
  let slow := if s.slowHost.1 == 0 && s.slowSelf.1 == 0 then [] else
    [s!"  slowest     host {showMs s.slowHost.1} s ({s.slowHost.2}); self {showMs s.slowSelf.1} s ({s.slowSelf.2})"]
  String.intercalate "\n" (lines ++ slow ++ byC ++ byE ++ top)

/-- The signature a baseline stores per file: the parts progress is measured in. -/
def libDiffSig (r : LibRec) : String :=
  s!"{r.verdict}/{r.divergence}/{r.klass}"

/-- How a file stands against a baseline signature. -/
def libDiffDelta (before after : String) : String :=
  let ok (s : String) : Bool := s.startsWith "ok/"
  if before == "" then "new"
  else if before == after then "same"
  else if !ok before && ok after then "fixed"
  else if ok before && !ok after then "regressed"
  else "changed"

/-- The baseline diff: `fixed`, `regressed`, `changed`, `new`, `same`. -/
def libDiffBaselineText (before : Std.HashMap String String) (recs : Array LibRec) : String := Id.run do
  let mut counts : Std.HashMap String Nat := {}
  for r in recs do
    let d := libDiffDelta (before.getD r.file "") (libDiffSig r)
    counts := counts.insert d (counts.getD d 0 + 1)
  let order := ["fixed", "regressed", "changed", "new", "same"]
  let lines := order.filterMap fun k =>
    match counts.get? k with
    | some n => if n == 0 then none else some s!"  {libDiffPad k 10}{n}"
    | none => none
  let details := recs.toList.filterMap fun r =>
    let b := before.getD r.file ""
    let d := libDiffDelta b (libDiffSig r)
    if d == "fixed" then some s!"  fixed: {r.file} (was {b}, now {libDiffSig r})"
    else if d == "regressed" then some s!"  REGRESSED: {r.file} (was {b}, now {libDiffSig r})"
    else if d == "changed" then some s!"  changed: {r.file} ({b} → {libDiffSig r})"
    else none
  return String.intercalate "\n" (("vs baseline:" :: lines) ++ details)

/-- A baseline is JSON lines, one per file; read the `file` and `sig` of each. -/
def libDiffReadBaseline (f : String) : IO (Std.HashMap String String) := do
  let mut m : Std.HashMap String String := {}
  unless ← (System.FilePath.mk f).pathExists do return m
  for line in (← IO.FS.readFile f).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match Lean.Json.parse line with
    | .ok j => m := m.insert (jStr j "file") (jStr j "sig")
    | .error _ => pure ()
  return m

/-! ## The command line (`tests --libdiff …`) -/

def libDiffParseOptsGo (o : LibDiffOpts) : List String → Except String LibDiffOpts
  | [] => pure o
  | "--limit" :: n :: r =>
    match n.toNat? with
    | some k => libDiffParseOptsGo { o with limit := k } r
    | none => throw s!"--limit needs a number, not {n}"
  | "--only" :: f :: r => libDiffParseOptsGo { o with only := o.only ++ [f] } r
  | "--json" :: r => libDiffParseOptsGo { o with json := true } r
  | "--baseline" :: f :: r => libDiffParseOptsGo { o with baseline := some f } r
  | "--timeout" :: n :: r =>
    match n.toNat? with
    | some k => libDiffParseOptsGo { o with hostSecs := k, selfSecs := k } r
    | none => throw s!"--timeout needs a number of seconds, not {n}"
  | "--host-timeout" :: n :: r =>
    match n.toNat? with
    | some k => libDiffParseOptsGo { o with hostSecs := k } r
    | none => throw s!"--host-timeout needs a number of seconds, not {n}"
  | "--self-timeout" :: n :: r =>
    match n.toNat? with
    | some k => libDiffParseOptsGo { o with selfSecs := k } r
    | none => throw s!"--self-timeout needs a number of seconds, not {n}"
  | "--mem" :: n :: r =>
    match n.toNat? with
    | some k => libDiffParseOptsGo { o with memMB := k } r
    | none => throw s!"--mem needs megabytes, not {n}"
  | "--jobs" :: n :: r =>
    match n.toNat? with
    | some k => if k > 0 then libDiffParseOptsGo { o with jobs := k } r
      else throw "--jobs needs a count of at least 1"
    | none => throw s!"--jobs needs a count, not {n}"
  | a :: _ => throw s!"unknown argument {a}\nusage: tests --libdiff [--limit N] [--only FILE]… [--json] [--baseline FILE] [--jobs N]"

def libDiffParseOpts (args : List String) : Except String LibDiffOpts :=
  libDiffParseOptsGo {} args

def libDiffMain (args : List String) : IO UInt32 := do
  match libDiffParseOpts args with
  | .error e => IO.eprintln e; return 2
  | .ok o => do
    -- `--libdiff --jobs N` is the explicit control; else the driver's `--jobs N` (the
    -- CI shard's "jobs"); else auto (0: the CPUs minus one, capped by memory)
    let o ← if o.jobs != 0 then pure o else
      match ← caseJobsGiven with
      | true => do pure { o with jobs := ← caseJobs }
      | false => pure o
    -- the baseline as it was before this run: writing a new one is not comparing to it
    let before ← match o.baseline with
      | none => pure ({} : Std.HashMap String String)
      | some f => libDiffReadBaseline f
    let existed ← match o.baseline with
      | none => pure true
      | some f => (System.FilePath.mk f).pathExists
    let start ← IO.monoMsNow
    let res ← libDiffSweep o fun line => IO.println line
    let some (recs, workers) := res | do
      IO.eprintln "selfhost-libdiff: no self-hosted compiler (no C toolchain: --gc-cflags)"
      return 3
    let sum := libDiffSummarize recs
    if o.json then
      IO.println (Lean.Json.compress (Lean.Json.mkObj [
        ("summary", Lean.Json.mkObj [
          ("files", .num recs.size), ("ok", .num sum.ok), ("rejected", .num sum.rejected),
          ("diverging", .num sum.diverging), ("bounded", .num sum.bounded),
          ("host_ok_self_error", .num sum.hostOkSelfErr), ("host_error_self_ok", .num sum.hostErrSelfOk),
          ("by_construct", Lean.Json.mkObj (sum.byConstruct.map (fun (k, n) => (k, .num n)))),
          ("by_code", Lean.Json.mkObj (sum.byCode.map (fun (k, n) => (k, .num n)))),
          ("seconds", .num ((← IO.monoMsNow) - start)), ("workers", .num workers)])]))
    else
      IO.println s!"\n── selfhost-libdiff: {recs.size} files ({showMs ((← IO.monoMsNow) - start)} s, {workers} at a time)"
      IO.println (libDiffSummaryText sum)
    if let some f := o.baseline then
      unless o.json do IO.println ""
      if existed then
        unless o.json do IO.println (libDiffBaselineText before recs)
      else do
        let text := String.intercalate "\n" (recs.toList.map fun r =>
          Lean.Json.compress (Lean.Json.mkObj [("file", .str r.file), ("sig", .str (libDiffSig r))]))
        IO.FS.writeFile f (text ++ "\n")
        unless o.json do IO.println s!"baseline written: {f} ({recs.size} files)"
    pure 0

/-! ## The group -/

/-- The report the group leaves behind (its own output is hidden when it passes). -/
def libDiffWriteReport (recs : Array LibRec) (sum : LibSummary) : IO Unit := do
  let dir : System.FilePath := ".lake/libdiff"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "records.jsonl")
    (String.intercalate "\n" (recs.toList.map fun r => Lean.Json.compress (jsonOfRec r)) ++ "\n")
  IO.FS.writeFile (dir / "summary.txt")
    (s!"{recs.size} files\n" ++ libDiffSummaryText sum ++ "\n")

def libDiffGroup : Group where
  name := "selfhost-libdiff"
  exercise := "replacement parity: lib/ and scry/ through both compilers"
  shard := "selfhost"
  cases := [
    { name := "the library through both compilers: the parity gap list", run := fun _ => do
        -- `--libdiff --jobs N` / the driver's `--jobs N` when it was given (so CI's
        -- shard may set it, and `--jobs 1` is the serial control); else auto
        let cj ← caseJobs
        let given ← caseJobsGiven
        let o : LibDiffOpts := { jobs := if given then cj else 0 }
        let say := fun (_ : String) => pure ()
        -- the per-file lines, a heartbeat and the counts reach the CI log while it runs
        match ← libDiffSweep o say (some progress) with
        | none => skip "no C toolchain (no self-hosted compiler)"
        | some (recs, workers) =>
          let sum := libDiffSummarize recs
          libDiffWriteReport recs sum
          note s!"libdiff files={recs.size} ok={sum.ok} rejected={sum.rejected} diverging={sum.diverging} bounded={sum.bounded} workers={workers}"
          note s!"libdiff slowest host={showMs sum.slowHost.1}s/{o.hostSecs}s ({sum.slowHost.2}) self={showMs sum.slowSelf.1}s/{o.selfSecs}s ({sum.slowSelf.2})" },
    { name := "the sweep's worker pool: every file exactly once, results in order, any worker count", run := fun _ => do
        for jobs in [1, 2, 3, 8, 40] do
          let n := 17
          let seen ← IO.mkRef #[]
          let workers ← IO.mkRef #[]
          let out ← libDiffPool n jobs (pure true)
            (fun i w => do
              check (w < max 1 (min jobs n)) "a worker id is out of range"
              workers.modify (·.push w)
              pure (i * i))
            (fun i a => do
              checkEq (i * i) a
              seen.modify (·.push i))
          checkEq ((List.range n).map (fun i => i * i)) out.toList
          checkEq (List.range n) (← seen.get).toList
          check ((← workers.get).size == n) "not every item ran" },
    { name := "the sweep's workers: as asked (or auto), but no more than the CPUs and the free memory hold", run := fun _ => do
        checkEq 3 (libDiffAsked 0 4)
        checkEq 1 (libDiffAsked 0 1)
        checkEq 1 (libDiffAsked 1 4)
        checkEq 4 (libDiffAsked 4 4)
        checkEq 1 (libDiffWorkers 1 32 (some 16384) 4096)
        checkEq 4 (libDiffWorkers 8 32 (some 16384) 4096)
        -- 16 GiB with the driver and the OS already using some: 3 files, not 4
        checkEq 3 (libDiffWorkers 8 32 (some 15360) 4096)
        checkEq 2 (libDiffWorkers 8 2 (some 16384) 4096)
        checkEq 1 (libDiffWorkers 8 32 (some 4095) 4096)
        checkEq 1 (libDiffWorkers 8 32 none 4096)
        checkEq 8 (libDiffWorkers 8 32 (some 16384) 0) },
    { name := "a self-hosted run that exits 3 (the runtime gave up) is bounded, with its reason; not accepted", run := fun _ => do
        checkEq "crash" (libDiffStatus 3)
        checkEq "ok" (libDiffStatus 1)
        checkEq "wiz: out of memory" (libDiffRuntimeNote "partial\nwiz: out of memory\n")
        let h : Side := { accepted := true, decls := 30 }
        let s : Side := { accepted := true, exitCode := 3, status := libDiffStatus 3,
                          note := libDiffRuntimeNote "wiz: out of memory\n" }
        let r := libDiffCompare "lib/BitVecAdd.wiz" h s
        checkEq "bounded" r.verdict
        checkEq "run" r.divergence
        checkEq "self crash (wiz: out of memory)" r.note },
    { name := "the sweep's worker pool: no files, and an exception is rethrown once the running files finish", run := fun _ => do
        for n in [0, 1, 5, 17] do
          for jobs in [1, 2, 3, 8, 40] do
            let seen ← IO.mkRef (Array.replicate n 0)
            let emitted ← IO.mkRef (#[] : Array Nat)
            let out ← libDiffPool n jobs (pure true)
              (fun i _ => do IO.sleep (UInt32.ofNat (i % 3)); seen.modify (fun a => a.modify i (· + 1)); pure (i * 10))
              (fun i _ => emitted.modify (·.push i))
            checkEq (Array.replicate n 1) (← seen.get)
            checkEq ((Array.range n).map (· * 10)) out
            checkEq (Array.range n) (← emitted.get)
        -- an exception is rethrown, after the running items finish
        let threw ← try
            let _ ← libDiffPool 6 3 (pure true) (fun i _ => if i == 4 then throw (IO.userError "boom") else pure i) (fun _ _ => pure ())
            pure false
          catch _ => pure true
        check threw "the pool swallowed a worker's exception" },
    { name := "the sweep's workers: as asked, but no more than the CPUs and the free memory hold", run := fun _ => do
        checkEq 1 (libDiffWorkers 1 4 (some 16000) 4096)
        checkEq 3 (libDiffWorkers 3 4 (some 16000) 4096)
        checkEq 3 (libDiffWorkers 8 4 (some 14000) 4096)  -- memory: 14000 / 4096
        checkEq 2 (libDiffWorkers 8 2 (some 64000) 4096)  -- CPUs
        checkEq 1 (libDiffWorkers 3 4 (some 6000) 4096)   -- a heavy job declared 7G
        checkEq 1 (libDiffWorkers 3 4 (some 100) 4096)    -- never 0
        checkEq 1 (libDiffWorkers 3 4 none 4096)          -- free memory unknown: one
        checkEq 3 (libDiffWorkers 3 4 (some 100) 0) },    -- no memory bound
    { name := "a sweep at three workers gives a sequential sweep's records, exit 3 (the runtime gave up) included", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let rx : IO.AccessRight := { read := true, execution := true }
        let host := dir / "host.sh"
        IO.FS.writeFile host "#!/bin/sh\necho '{\"accepted\":true,\"decls\":2}'\n"
        let selfExe := dir / "self.sh"
        IO.FS.writeFile selfExe (String.intercalate "\n" [
          "#!/bin/sh",
          "case \"$2\" in",
          "  *oom*) echo partial; echo 'wiz: out of memory' >&2; exit 3;;",
          "  *bad*) echo \"$2:3:1: error: unknown identifier X [unknown-identifier]\"; exit 1;;",
          "  *) echo \"$2:1:1: info: a : Nat\"; echo \"$2:2:1: info: b : Nat\";;",
          "esac", ""])
        for f in [host, selfExe] do
          IO.setAccessRights f { user := { rx with write := true }, group := rx, other := rx }
        let files := #["a.wiz", "b-bad.wiz", "c-oom.wiz", "d.wiz", "e-bad.wiz", "f.wiz", "g-oom.wiz"]
        let o : LibDiffOpts := {}
        let run (jobs : Nat) : IO (Array LibRec) :=
          libDiffPool files.size jobs (pure true)
            (fun i _ => libDiffFile o host.toString #[] selfExe "/tmp/wiz-libdiff-test-cache" files[i]!)
            (fun _ _ => pure ())
        let seq ← run 1
        let par ← run 3
        IO.FS.removeDirAll dir
        let sig (r : LibRec) := s!"{r.file} {libDiffSig r} {r.note} {r.self.exitCode}"
        checkEq (seq.map sig) (par.map sig)
        checkEq (files.toList) (par.toList.map (·.file))
        let oom := par.filter (·.file.endsWith "-oom.wiz")
        checkEq 2 oom.size
        for r in oom do
          checkEq "bounded" r.verdict
          checkEq "self crash (wiz: out of memory)" r.note
          check (!r.self.accepted || r.self.status == "crash") "an exit 3 counted as accepted"
        checkEq ["ok", "diverging", "bounded", "ok", "diverging", "ok", "bounded"] (par.toList.map (·.verdict)) }
  ]

builtin_initialize registerGroup libDiffGroup

end Tests.Elab
