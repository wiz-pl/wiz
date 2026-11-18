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

The group never fails because of a gap: it measures. A compiler that *dies* (a signal,
or a runtime give-up that is not the declared memory limit) is not a gap but a failure,
counted apart from `bounded`; the sweep case fails on a death, on no file reaching a
verdict, and on `scry/tests/ReplPrelude.wiz` (accepted by both with one declaration)
not being `ok`. A toolchain problem is a skip, the way the `selfhost` group skips.

Usage (a work list, not a gate):

    tests --libdiff                          # every lib/ and scry/ file
    tests --libdiff --limit 10               # the first ten
    tests --libdiff --only lib/Hoare.wiz     # one file (repeatable)
    tests --libdiff --json                   # one JSON record per line
    tests --libdiff --baseline FILE          # write it, or diff against it

`lake test -- '=selfhost-libdiff'` runs the sweep with the defaults and writes the report
to `.lake/libdiff/` (the harness hides a passing case's output).
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

/-- One compiler's verdict on a file. `status` is `ok`, a declared bound (`timeout`,
`memory`), or `died` (a signal or a runtime give-up that is not the memory limit). -/
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
  deriving Inhabited

def jsonOfSide (s : Side) : Lean.Json :=
  Lean.Json.mkObj [
    ("accepted", .bool s.accepted), ("exit", .num s.exitCode.toNat), ("errors", .num s.errors),
    ("decls", .num s.decls), ("code", .str s.code), ("file", .str s.efile),
    ("line", .num s.line), ("col", .num s.col), ("msg", .str s.msg),
    ("status", .str s.status), ("note", .str s.note)]

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
    catch e => pure ({ status := "died", note := toString e } : Side)
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

/-- The declaration lines of the self-hosted `--types` report: every info line for
`file`. A dotted name is an ordinary declaration (`BitVec.add`, `Scry.Foo.bar`), not a
projection: the self-hosted frontend prints no line for a structure's fields or
projections (the host's `libDiffHostDecls` excludes those too), so dropping names with a
`.` dropped `Nat.repr`, `BitVec.add`, … and made the counts disagree for 114 of the 117
`lib` files. (Projection lines do appear, at 1:1, only in a graph that failed to load,
where the file is rejected anyway.) -/
def libDiffSelfDecls (file : String) (diags : List LibDiag) : Nat :=
  (diags.filter fun d => d.sev == "info" && d.file == file).length

/-- Bounded run: a wall-clock limit (`timeout -k 5`) and, with `memMB > 0`, a
virtual-memory limit. -/
def libDiffRun (cmd : String) (args : Array String) (secs memMB : Nat) :
    IO (UInt32 × String × String) := do
  let limit := if memMB == 0 then "" else s!"ulimit -v {memMB * 1024} 2>/dev/null; "
  let script := s!"{limit}exec timeout -k 5 {secs} \"$0\" \"$@\""
  let out ← IO.Process.output
    { cmd := "sh", args := #["-c", script, cmd] ++ args, stdin := .null }
  pure (out.exitCode, out.stdout, out.stderr)

/-- The runtime's `wiz: REASON` line on stderr, if it gave up (exit 3). -/
def libDiffRuntimeNote (err : String) : String :=
  match (err.splitOn "\n").reverse.find? (·.startsWith "wiz: ") with
  | some l => (l.take 200).toString
  | none => ""

/-- `status` from a bounded run's exit code and stderr.
`timeout`/`memory` are the *declared* limits: `124`, or `137` after `timeout -k`'s kill;
exit 3 with the runtime's `wiz: out of memory` is the `ulimit -v` bound. Those are a
bound, not a verdict.
`died` is the compiler dying: a signal (`139` segfault, `134` abort), exit 3 for another
`wiz:` reason (`applying a non-function`), or any other non-0/non-1 exit. A death is a
failure; the old code put it in `bounded`.
`ok`: 0 (accepted) or 1 (diagnostics). -/
def libDiffStatus (code : UInt32) (err : String := "") : String :=
  if code == 124 || code == 137 then "timeout"
  else if code == 3 then
    if (libDiffRuntimeNote err).contains "out of memory" then "memory" else "died"
  else if code == 0 || code == 1 then "ok"
  else "died"

/-- The reason a run did not reach a verdict: the runtime's `wiz:` line, else the exit
code for a signal; a declared time bound has no note (the limit is the reason). -/
def libDiffRunNote (code : UInt32) (err : String) : String :=
  let why := libDiffRuntimeNote err
  if !why.isEmpty then why
  else if code == 124 || code == 137 then ""
  else s!"exit {code}"

/-- Run the self-hosted compiler's `check FILE --types` and read its diagnostics. -/
def libDiffSelf (exe : System.FilePath) (file : String) (secs memMB : Nat) : IO Side := do
  let args : Array String :=
    #["check", file, "--types", "--cache", "/tmp/wiz-libdiff-cache"] ++
    (libDiffRoots.flatMap (fun r => ["-I", r])).toArray
  let (code, out, err) ← libDiffRun exe.toString args secs memMB
  let lines := out.splitOn "\n" ++ err.splitOn "\n"
  let diags := lines.filterMap libDiffParseDiag
  let errs := diags.filter (·.sev == "error")
  -- the first error in the file itself if there is one, else the first import error
  let first := (errs.find? (·.file == file)).orElse (fun _ => errs[0]?)
  let status := libDiffStatus code err
  pure { accepted := errs.isEmpty, exitCode := code, errors := errs.length,
         decls := libDiffSelfDecls file diags,
         code := first.map (·.code) |>.getD "",
         efile := first.map (·.file) |>.getD "",
         line := first.map (·.line) |>.getD 0,
         col := first.map (·.col) |>.getD 0,
         msg := first.map (·.msg) |>.getD "",
         status,
         note := if status == "ok" || status == "timeout" then "" else libDiffRunNote code err }

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
  (a run hit the declared time or memory limit), or `died` (a compiler died: a failure) -/
  verdict : String
  /-- `acceptance`, `code`, `span`, `message`, `decls`, `run`, `died`, or `""` (agreement) -/
  divergence : String
  /-- the missing construct, for a divergence and for a rejection -/
  klass : String
  note : String := ""
  deriving Inhabited

def libDiffCompare (file : String) (h s : Side) : LibRec :=
  let bound := fun (x : Side) => x.status == "timeout" || x.status == "memory"
  let died := h.status == "died" || s.status == "died"
  let bounded := bound h || bound s
  let verdict :=
    if died then "died"
    else if bounded then "bounded"
    else if h.accepted && s.accepted then if h.decls == s.decls then "ok" else "diverging"
    else if h.accepted != s.accepted then "diverging"
    else "rejected"
  let divergence :=
    if died then "died"
    else if bounded then "run"
    else if h.accepted && s.accepted then (if h.decls == s.decls then "" else "decls")
    else if h.accepted != s.accepted then "acceptance"
    else if h.code != s.code then "code"
    else if h.line != s.line || h.col != s.col || (s.efile != "" && s.efile != file) then "span"
    else if libDiffNormMsg h.msg != libDiffNormMsg s.msg then "message"
    else ""
  let klass := if s.accepted then "" else libDiffClassOf s
  -- a bound or a death on either side, named with its reason
  let runSide (side : String) (x : Side) : String :=
    if x.status == "ok" then "" else
      s!"{side} {x.status}" ++ (if x.note.isEmpty then "" else s!" ({x.note})")
  let hn := runSide "host" h
  let sn := runSide "self" s
  let note :=
    if died || bounded then
      (if hn.isEmpty then "" else hn) ++
      (if sn.isEmpty then "" else (if hn.isEmpty then "" else "; ") ++ sn)
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
    | "died" => "DIED   "
    | v => v
  let hostTex := if h.accepted then s!"host ok ({h.decls} decls)" else s!"host error [{h.code}]"
  let selfTex := if s.accepted then s!"self ok ({s.decls} decls)" else
    s!"self error [{s.code}] {s.line}:{s.col} {(s.msg.take 100).toString}"
  s!"{tag} {r.file}\t{hostTex} / {selfTex}" ++
    (if r.divergence.isEmpty then "" else s!"\t(first divergence: {r.divergence})") ++
    (if r.klass.isEmpty then "" else s!"\t({r.klass})") ++
    (if r.note.isEmpty then "" else s!"\t[{r.note}]")

/-- Run both compilers over the selected files. `none` when the self-hosted compiler
could not be built for a toolchain reason (the caller skips). -/
def libDiffSweep (o : LibDiffOpts) (say : String → IO Unit) : IO (Option (Array LibRec)) := do
  let all ← libDiffFiles
  let picked := all.filter fun f =>
    (o.only.isEmpty || o.only.any (libDiffPicks · f)) && f.endsWith ".wiz"
  let picked := if o.limit == 0 then picked else picked.take o.limit
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then return none else throw (IO.userError e)
  | .ok exe =>
    let self ← IO.appPath
    let flags := (← flagsRef.get).toArray
    let mut recs : Array LibRec := #[]
    for file in picked do
      -- the host child is Lean itself (whose runtime reserves address space): it gets
      -- the time bound, and the heavy job's memory cap, not a ulimit
      let h : Side ← match ← libDiffRun self.toString (#["--libdiff-host", file] ++ flags) o.hostSecs 0 with
        | (c, out, err) =>
          let st := libDiffStatus c err
          if st != "ok" then
            pure ({ status := st, exitCode := c,
                    note := if st == "timeout" then "" else libDiffRunNote c err } : Side)
          else match (out.splitOn "\n").findSome? (fun l => (Lean.Json.parse l).toOption) with
            | some j => pure (sideOfJson j)
            | none => pure ({ status := "died", note := s!"no host record: {(err.take 200).toString}" } : Side)
      let s ← libDiffSelf exe file o.selfSecs o.memMB
      let r := libDiffCompare file h s
      recs := recs.push r
      if o.json then
        IO.println (Lean.Json.compress (jsonOfRec r))
      else
        say (libDiffRender r)
    pure (some recs)

/-- The counts the summary prints. -/
structure LibSummary where
  ok : Nat := 0
  rejected : Nat := 0
  diverging : Nat := 0
  bounded : Nat := 0
  /-- the compiler died (not a bound: a failure) -/
  died : Nat := 0
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
  | "died" => { s with died := s.died + 1 }
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
    blockers := blockers }

/-- `s` padded with spaces on the right. -/
def libDiffPad (s : String) (n : Nat) : String := s ++ "".pushn ' ' (n - s.length)

def libDiffSummaryText (s : LibSummary) : String :=
  let lines := [
    s!"  ok          {s.ok}",
    s!"  rejected    {s.rejected}   (both reject; {s.sameCode} same code, {s.sameSpan} same span, {s.sameMsg} same message)",
    s!"  diverging   {s.diverging}   (host accepts, self rejects: {s.hostOkSelfErr}; host rejects, self accepts: {s.hostErrSelfOk})",
    s!"  bounded     {s.bounded}   (a run hit its declared time or memory bound)",
    s!"  died        {s.died}   (a compiler died: a failure, not a gap)"]
  let byC := if s.byConstruct.isEmpty then [] else
    "\nby missing construct (files whose verdicts differ):" ::
      s.byConstruct.map (fun (k, n) => s!"  {libDiffPad k 24}{n}")
  let byE := if s.byCode.isEmpty then [] else
    "\nby error class (both reject):" ::
      s.byCode.map (fun (k, n) => s!"  {libDiffPad (if k.isEmpty then "(no code)" else k) 24}{n}")
  let top := if s.blockers.isEmpty then [] else
    "\ntop 10 blockers (host accepts, self-hosted frontend rejects):" ::
      (s.blockers.take 10).zipIdx.map (fun ((f, k, m), i) => s!"  {i + 1}. {f}\t{k}\t{m}")
  String.intercalate "\n" (lines ++ byC ++ byE ++ top)

/-- The signature a baseline stores per file: the parts progress is measured in. -/
def libDiffSig (r : LibRec) : String :=
  s!"{r.verdict}/{r.divergence}/{r.klass}"

/-- How a file stands against a baseline signature. -/
def libDiffDelta (before after : String) : String :=
  let ok (s : String) : Bool := s.startsWith "ok/"
  if before == after then "same"
  -- a compiler death is a regression even when the file was not `ok` before: it is a
  -- failure, not a parity gap the baseline may absorb
  else if after.startsWith "died/" then "regressed"
  else if before == "" then "new"
  else if !ok before && ok after then "fixed"
  else if ok before && !ok after then "regressed"
  else "changed"

/-- The records whose signature differs from the baseline (`fixed`, `regressed`,
`changed` or `new`): what makes the `--baseline` gate fail. A missing baseline is the
update path, so it was already written and this is not called for it. -/
def libDiffChanged (before : Std.HashMap String String) (recs : Array LibRec) : List LibRec :=
  recs.toList.filter fun r => libDiffDelta (before.getD r.file "") (libDiffSig r) != "same"

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
  | a :: _ => throw s!"unknown argument {a}\nusage: tests --libdiff [--limit N] [--only FILE]… [--json] [--baseline FILE]"

def libDiffParseOpts (args : List String) : Except String LibDiffOpts :=
  libDiffParseOptsGo {} args

def libDiffMain (args : List String) : IO UInt32 := do
  match libDiffParseOpts args with
  | .error e => IO.eprintln e; return 2
  | .ok o => do
    -- the baseline as it was before this run: writing a new one is not comparing to it
    let before ← match o.baseline with
      | none => pure ({} : Std.HashMap String String)
      | some f => libDiffReadBaseline f
    let existed ← match o.baseline with
      | none => pure true
      | some f => (System.FilePath.mk f).pathExists
    let start ← IO.monoMsNow
    let res ← libDiffSweep o fun line => IO.println line
    let some recs := res | do
      IO.eprintln "selfhost-libdiff: no self-hosted compiler (no C toolchain: --gc-cflags)"
      return 3
    let sum := libDiffSummarize recs
    if o.json then
      IO.println (Lean.Json.compress (Lean.Json.mkObj [
        ("summary", Lean.Json.mkObj [
          ("files", .num recs.size), ("ok", .num sum.ok), ("rejected", .num sum.rejected),
          ("diverging", .num sum.diverging), ("bounded", .num sum.bounded),
          ("died", .num sum.died),
          ("host_ok_self_error", .num sum.hostOkSelfErr), ("host_error_self_ok", .num sum.hostErrSelfOk),
          ("by_construct", Lean.Json.mkObj (sum.byConstruct.map (fun (k, n) => (k, .num n)))),
          ("by_code", Lean.Json.mkObj (sum.byCode.map (fun (k, n) => (k, .num n)))),
          ("seconds", .num ((← IO.monoMsNow) - start))])]))
    else
      IO.println s!"\n── selfhost-libdiff: {recs.size} files ({showMs ((← IO.monoMsNow) - start)} s)"
      IO.println (libDiffSummaryText sum)
    if let some f := o.baseline then
      unless o.json do IO.println ""
      if existed then
        unless o.json do IO.println (libDiffBaselineText before recs)
        -- The gate: a stored baseline that no longer matches is a failure. Updating it
        -- is the missing-baseline path (remove the file, run again), so a green run
        -- always means "the signatures are the ones recorded".
        let changed := libDiffChanged before recs
        unless changed.isEmpty do
          IO.eprintln s!"selfhost-libdiff: {changed.length} file(s) differ from the baseline {f}"
          IO.eprintln s!"  update: rm {f} && tests --libdiff --baseline {f}"
          return 1
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
        let o : LibDiffOpts := {}
        let say := fun (_ : String) => pure ()
        match ← libDiffSweep o say with
        | none => skip "no C toolchain (no self-hosted compiler)"
        | some recs =>
          let sum := libDiffSummarize recs
          libDiffWriteReport recs sum
          note s!"libdiff files={recs.size} ok={sum.ok} rejected={sum.rejected} diverging={sum.diverging} bounded={sum.bounded} died={sum.died}"
          -- The case is not only a report: a compiler that died, or a sweep that
          -- decided nothing, is a harness failure. (`--baseline`'s non-empty diff is
          -- enforced by libDiffMain and its own case below.)
          check (sum.died == 0) s!"the self-hosted compiler died on {sum.died} file(s); see .lake/libdiff/records.jsonl"
          check (sum.ok + sum.rejected + sum.diverging > 0)
            "no file reached a verdict (every run was bounded or died)"
          -- A parity measurement whose `ok` bucket is unreachable measures nothing.
          -- `scry/tests/ReplPrelude.wiz` is the smallest real module in the sweep and
          -- both compilers accept it with one declaration: it must be `ok` (not bounded,
          -- not diverging). The `lib/` side of the same check is
          -- `lib/BitVecAdd.wiz`, whose declarations are all dotted; the old filter made
          -- it `self ok (0 decls)` and the unit case below pins that count.
          check (sum.ok > 0) "no file is accepted by both compilers"
          match recs.find? (·.file == "scry/tests/ReplPrelude.wiz") with
          | none => throw (IO.userError "scry/tests/ReplPrelude.wiz is missing from the sweep")
          | some r =>
            check (r.verdict == "ok")
              s!"scry/tests/ReplPrelude.wiz: expected ok (both compilers accept it with one declaration), got {r.verdict}/{r.divergence} ({r.host.decls} vs {r.self.decls} declarations)" },
    { name := "--baseline: any difference from a stored baseline fails; an identical one does not", run := fun _ => do
        let recOf (file verdict diverg klass : String) : LibRec :=
          { file, host := {}, self := {}, verdict, divergence := diverg, klass }
        let before : Std.HashMap String String :=
          (({} : Std.HashMap String String).insert "lib/A.wiz" "ok//").insert "lib/B.wiz" "rejected/code/by"
        checkEq 0 (libDiffChanged before #[recOf "lib/A.wiz" "ok" "" ""]).length
        checkEq 1 (libDiffChanged before #[recOf "lib/A.wiz" "diverging" "acceptance" "by"]).length
        -- progress is a difference too: it must be recorded, not hidden by a green run
        checkEq 1 (libDiffChanged before #[recOf "lib/B.wiz" "ok" "" ""]).length
        checkEq 1 (libDiffChanged before #[recOf "lib/C.wiz" "ok" "" ""]).length
        -- a death is a regression, even for a file that was not `ok` before
        checkEq "regressed" (libDiffDelta "rejected/code/by" "died/died/")
        checkEq "regressed" (libDiffDelta "" "died/died/")
        checkEq "same" (libDiffDelta "died/died/" "died/died/") },
    { name := "dotted names (`BitVec.add`, a module path) count as declarations, not projections", run := fun _ => do
        let d (file sev msg : String) : LibDiag := { file, line := 1, col := 1, sev, msg, code := "" }
        checkEq 3 (libDiffSelfDecls "f.wiz" [
          d "f.wiz" "info" "BitVec.add : (x : Nat) → Nat",
          d "f.wiz" "info" "Scry.Foo.bar : Nat",
          d "f.wiz" "info" "plain : Nat"])
        checkEq 0 (libDiffSelfDecls "f.wiz" [d "other.wiz" "info" "x : Nat"]) },
    { name := "a compiler death is `died` (a failure); only the declared limits are `bounded`", run := fun _ => do
        checkEq "died" (libDiffStatus 3)
        checkEq "died" (libDiffStatus 139)
        checkEq "died" (libDiffStatus 134)
        checkEq "died" (libDiffStatus 2)
        checkEq "ok" (libDiffStatus 0)
        checkEq "ok" (libDiffStatus 1)
        checkEq "timeout" (libDiffStatus 124)
        checkEq "timeout" (libDiffStatus 137)
        checkEq "memory" (libDiffStatus 3 "partial\nwiz: out of memory\n")
        checkEq "died" (libDiffStatus 3 "wiz: applying a non-function\n")
        checkEq "wiz: out of memory" (libDiffRuntimeNote "partial\nwiz: out of memory\n")
        let h : Side := { accepted := true, decls := 30 }
        -- the declared memory bound: `bounded`, with the runtime's reason
        let mem : Side := { accepted := true, exitCode := 3, status := libDiffStatus 3 "wiz: out of memory\n",
                            note := libDiffRunNote 3 "wiz: out of memory\n" }
        let r := libDiffCompare "lib/BitVecAdd.wiz" h mem
        checkEq "bounded" r.verdict
        checkEq "run" r.divergence
        checkEq "self memory (wiz: out of memory)" r.note
        -- a death has its own verdict, so the summary and the group fail on it
        let dead : Side := { accepted := false, exitCode := 139, status := libDiffStatus 139,
                             note := libDiffRunNote 139 "" }
        let d := libDiffCompare "lib/BitVecAdd.wiz" h dead
        checkEq "died" d.verdict
        checkEq "died" d.divergence
        checkEq "self died (exit 139)" d.note }
  ]

builtin_initialize registerGroup libDiffGroup

end Tests.Elab
