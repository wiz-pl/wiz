import Grail.Test
import Grail.Selfhost
import Grail.Exec
import Grail.Command

/-!
# The build graph and its scheduler (stage 23g)

`grail build` turns the targets into a graph of **nodes** (`check F`, `build F`
(check, IR and C of an executable's source, in one job), `ir F`, `obj F`, `link E`,
`test F`, the steps of the bootstrap check), each with the nodes it depends on:
`obj F` on `build F`, …, `link E` on `obj F`, a check on the checks of the package
modules it imports, a `run` test on its executable. A node's key is computed
only once its dependencies are done (an object's key hashes the C text its `c` node
wrote), by the scheduler, in its own process, cheaply; a node whose output directory
`.grail/build/<key>/` exists is up to date.

The rest are **jobs**, run from a ready queue, at most `-j N` at a time, each as a
separate process (`<self> --grail-job JOB TOOLCHAIN-FLAGS`, or the C compiler directly)
under a supervisor (`Grail/Exec.lean`, 23k), which kills the job's whole process group
when its time is up or grail dies. Command targets (23i, `Grail/Command.lean`) are jobs
too. A job
writes into a temporary directory that the scheduler renames into place when the job
succeeds. A failed job is reported, and the nodes that depend on it are skipped; the
others still run (a test is the exception: it runs anyway, its output being the error).

The report is deterministic: each node's output is buffered and printed in the graph's
order (dependencies first, then the targets' order) as soon as everything before it is
done, so `-j 1` and `-j 8` print the same.
-/

namespace Grail
open Wiz Cache

/-- (9f) `link.txt`, beside `main.c`: one line per `link_c` file (`src PATH`) and
`link_lib` library (`lib NAME`). -/
def renderLink (l : Build.Link) : String :=
  String.join (l.sources.toList.map (s!"src {·}\n")) ++ String.join (l.libs.toList.map (s!"lib {·}\n"))

def readLink (f : System.FilePath) : IO Build.Link := do
  if !(← f.pathExists) then return {}
  let mut l : Build.Link := {}
  for line in (← IO.FS.readFile f).splitOn "\n" do
    if line.startsWith "src " then l := { l with sources := l.sources.push (line.drop 4).toString }
    else if line.startsWith "lib " then l := { l with libs := l.libs.push (line.drop 4).toString }
  pure l

/-- What a node of the build graph does. -/
inductive Action where
  | check (file : String)
  /-- check, lower and emit the C of a standalone source, in one job (it is elaborated
  once: `check`, `ir` and `c` as three jobs elaborated it three times) -/
  | build (file : String)
  | ir (file : String)
  | obj (file : String)
  /-- link the executable `name`; `bin`: install it as `.grail/bin/<name>` -/
  | link (name file : String) (bin : Bool)
  | test (file : String)
  /-- generate the self-hosted program `role` (`Grail/Selfhost.lean`) -/
  | source (role : String)
  | self1 | stage2 | self2 | fixpoint
  /-- (23i) a command target: its tools (an `exe` tool by the position of its link among
  the node's dependencies) and inputs (one another command makes: by its position) -/
  | command (c : Command) (tools : Array (Tool × Option Nat)) (inputs : Array (String × Option Nat))
  deriving Inhabited

structure Node where
  label : String
  action : Action
  deps : Array Nat
  /-- runs even when a dependency failed (a test, whose output is then the error) -/
  tolerant : Bool := false
  deriving Inhabited

structure Graph where
  nodes : Array Node := #[]
  ids : Std.HashMap String Nat := {}
  /-- nodes being added: an import cycle isn't followed (the check reports it) -/
  pending : Std.HashSet String := {}

abbrev GraphM := StateT Graph IO

/-- The node `label`, made by `mk` (its action, dependencies, tolerance) unless it exists.
Nodes are numbered after their dependencies. -/
def GraphM.add (label : String) (mk : GraphM (Action × Array Nat × Bool)) : GraphM (Option Nat) := do
  if let some i := (← get).ids[label]? then return some i
  if (← get).pending.contains label then return none
  modify fun g => { g with pending := g.pending.insert label }
  let (action, deps, tolerant) ← mk
  modify fun g => { g with nodes := g.nodes.push { label, action, deps, tolerant },
                           ids := g.ids.insert label g.nodes.size, pending := g.pending.erase label }
  return some ((← get).nodes.size - 1)

/-- The package file that module `m` is, under the root of one of the `lib` targets. -/
def libFileOf (dir : System.FilePath) (libs : List String) (m : Name) : IO (Option String) := do
  for root in libs do
    let rel := (System.FilePath.mk root / Module.relPath m).toString
    if ← (dir / rel).pathExists then return some rel
  return none

/-- `check F`, after the checks of the package modules `F` imports and `extra`. -/
partial def addCheck (dir : System.FilePath) (libs : List String) (file : String) (extra : Array Nat := #[]) :
    GraphM (Option Nat) :=
  GraphM.add s!"check {file}" do
    let mut deps := extra
    if ← (dir / file).pathExists then
      for m in Module.importsOf (← IO.FS.readFile (dir / file)) do
        if let some f ← libFileOf dir libs m then
          if f != file then
            if let some i ← addCheck dir libs f then deps := deps.push i
    pure (.check file, deps, false)

/-- The check nodes `F` depends on: those of the package modules it imports, and
`extra`. `F` itself is not checked. -/
def addCheckImports (dir : System.FilePath) (libs : List String) (file : String)
    (extra : Array Nat := #[]) : GraphM (Array Nat) := do
  let mut deps := extra
  if ← (dir / file).pathExists then
    for m in Module.importsOf (← IO.FS.readFile (dir / file)) do
      if let some f ← libFileOf dir libs m then
        if f != file then
          if let some i ← addCheck dir libs f then deps := deps.push i
  pure deps

/-- `src → obj → link` for the executable `name` from `file`'s `main`, where `src` makes
`file`'s C (`build`, or `ir` for a file already checked as a module). -/
def addLinkFrom (name file : String) (bin : Bool) (src : Nat) : GraphM (Option Nat) := do
  let some o ← GraphM.add s!"obj {file}" (pure (.obj file, #[src], false)) | return none
  -- (the link reads the `link_c` files and libraries that `src` lists)
  GraphM.add s!"link {name}" (pure (.link name file bin, #[o, src], false))

/-- `build → obj → link` for the executable `name` from `file`'s `main`: one job checks
`file` and emits its IR and C (the source is elaborated once, not once per job). A file
that is already checked as a package module keeps its check job, and `ir` (which also
emits the C) follows it. -/
def addLink (dir : System.FilePath) (libs : List String) (name file : String) (bin : Bool)
    (extra : Array Nat := #[]) : GraphM (Option Nat) := do
  if let some ck := (← get).ids[s!"check {file}"]? then
    let some ir ← GraphM.add s!"ir {file}" (pure (.ir file, #[ck], false)) | return none
    return ← addLinkFrom name file bin ir
  let deps ← addCheckImports dir libs file extra
  let some b ← GraphM.add s!"build {file}" (pure (.build file, deps, false)) | return none
  addLinkFrom name file bin b

def testExe (file : String) : String := s!"test-{hash file}"

def addTest (dir : System.FilePath) (libs : List String) (file : String) : GraphM (Option Nat) := do
  let deps ← match TestKind.ofSource (← IO.FS.readFile (dir / file)) with
    | .ok .run => pure (← addLink dir libs (testExe file) file false).toArray
    | _ => pure #[]
  GraphM.add s!"test {file}" (pure (.test file, deps, true))

def addSelfhost (dir : System.FilePath) (libs : List String) (name role : String) : GraphM (List Nat) := do
  let source (role : String) := GraphM.add s!"generate {role}.wiz" (pure (.source role, #[], false))
  match role with
  | "checker" | "compiler" =>
    let some s ← source role | return []
    pure (← addLink dir libs name (genFile role) true #[s]).toList
  | "bootstrap" =>
    let some s ← source "compiler" | return []
    let some l ← addLink dir libs "selfhost-stage1" (genFile "compiler") false #[s] | return []
    let some k1 ← GraphM.add "stage 1 compiles the toolchain (self1.c)" (pure (.self1, #[l, s], false)) | return []
    let some k2 ← GraphM.add "stage 2: cc self1.c with selfhost/rt.c" (pure (.stage2, #[k1], false)) | return []
    let some k3 ← GraphM.add "stage 2 compiles the toolchain (self2.c)" (pure (.self2, #[k2, s], false)) | return []
    pure (← GraphM.add "fixpoint" (pure (.fixpoint, #[k1, k3], false))).toList
  | _ => throw (IO.userError s!"unknown self-hosted target {role} (checker, compiler, bootstrap)")

/-- (23i) A command, after what makes its inputs and its `exe` tools. -/
partial def addCommand (dir : System.FilePath) (libs : List String) (all : List Target) (c : Command) :
    GraphM (Option Nat) := do
  let r ← GraphM.add s!"command {c.name}" do
    let mut deps : Array Nat := #[]
    let mut tools := #[]
    for t in c.tool :: c.uses do
      match t with
      | .path _ => tools := tools.push (t, none)
      | .exe n =>
        let some file := all.findSome? fun | .exe m f => if m == n then some f else none | _ => none
          | throw (IO.userError s!"command {c.name}: no exe target {n}")
        let some l ← addLink dir libs n file true | throw (IO.userError s!"command {c.name}: a cycle through exe {n}")
        tools := tools.push (t, some deps.size)
        deps := deps.push l
    let mut inputs := #[]
    for i in c.inputs do
      match producerOf all i with
      | some p =>
        let some k ← addCommand dir libs all p
          | throw (IO.userError s!"command {c.name}: a cycle through command {p.name} (input {i})")
        inputs := inputs.push (i, some deps.size)
        deps := deps.push k
      | none => inputs := inputs.push (i, none)
    pure (.command c tools inputs, deps, false)
  pure r

def addTarget (dir : System.FilePath) (libs : List String) (all : List Target := []) : Target → GraphM (List Nat)
  | .check _ f => do pure (← addCheck dir libs f).toList
  | .lib _ root => do
    let mut ids := #[]
    for (m, _) in ← Module.listRoot (dir / root) do
      if let some i ← addCheck dir libs (System.FilePath.mk root / Module.relPath m).toString then ids := ids.push i
    pure ids.toList
  | .exe n f => do pure (← addLink dir libs n f true).toList
  -- `grail test`
  | .tests _ _ => pure []
  | .selfhost n role => addSelfhost dir libs n role
  | .command c => do pure (← addCommand dir libs all c).toList

def libsOf (ts : List Target) : List String := ts.filterMap fun | .lib _ r => some r | _ => none

/-! ## Running nodes -/

/-- A finished node: its key and output directory. -/
structure Done where
  key : UInt64
  out : System.FilePath
  deriving Inhabited

/-- What a job's end means: success (and whether to record the output), and its report. -/
structure Finish where
  res : Except String Unit
  record : Bool := true
  log : String := ""

inductive How where
  /-- a grail job process: `(KIND ARGS…)` -/
  | grail (job : Sx)
  /-- a command, given the output directory -/
  | cmd (cmd : String) (args : System.FilePath → Array String)
  /-- (23i) a command target's program: its arguments, working directory and
  environment, given the job's directory -/
  | command (cmd : String) (args : System.FilePath → Array String) (cwd : System.FilePath → System.FilePath)
      (env : List (String × String))
  /-- in the scheduler's process (cheap: writing a generated file) -/
  | here (act : System.FilePath → IO (Except String Unit))

/-- A job: its key, how it runs, and its time limit. -/
structure Job where
  key : UInt64
  how : How
  timeoutMs : Nat
  /-- run even if the output exists -/
  force : Bool := false
  /-- judges the job's end (by default: its exit code, and its output is the report) -/
  finish : Option (Outcome → System.FilePath → IO Finish) := none
  /-- after success, up to date (`true`) or run: installs, and more report -/
  onOk : Bool → System.FilePath → IO String := fun _ _ => pure ""
  /-- before it runs, given its directory (a command's output directories) -/
  setup : System.FilePath → IO Unit := fun _ => pure ()

/-- A node whose dependencies are done: finished already, failed, or a job. -/
inductive Prep where
  | done (d : Done) (log : String := "")
  | fail (msg : String) (log : String := "")
  | job (j : Job)
  deriving Inhabited

def Runner.outDir (r : Runner) (key : UInt64) : System.FilePath := r.ctx.grailDir / "build" / hex key

def Runner.jobSx (r : Runner) (out : System.FilePath) (job : Sx) : Sx :=
  node "job" [str r.ctx.dir.toString, str r.ctx.std.toString, str (toString r.ctx.binId.toNat),
    list (r.ctx.libRoots.map (str ·.toString)), str out.toString, job]

def indent (s : String) : String :=
  "  " ++ (s.trimAsciiEnd.toString.replace "\n" "\n  ")

/-- The test results of a `grail test` run, by file. -/
abbrev TestResults := IO.Ref (Std.HashMap String TestResult)

/-- Compare a test's actual output with the expected one. -/
def Runner.judgeTest (r : Runner) (file : String) (update : Bool) (results : TestResults)
    (actual : Except String String) : IO Finish := do
  let (expFile, expected) ← expectedOf r.ctx.dir file
  -- (a pass is recorded under the key of the expected output it was compared with: with
  -- `--update`, only if that didn't change)
  let report (res : TestResult) (record : Bool := !update) : IO Finish := do
    results.modify (·.insert file res)
    let log := if res.ok then s!"  ✓ {file}{if res.message.isEmpty then "" else s!" ({res.message})"}\n"
      else s!"  ✗ {file}\n      {res.message}\n"
    pure { res := if res.ok then .ok () else .error res.message, record := res.ok && record, log }
  match actual with
  | .error e => report { file, ok := false, message := e }
  | .ok actual =>
  if update then
    if expected != some actual then IO.FS.writeFile expFile actual
    return ← report { file, ok := true, message := if expected == some actual then "" else "updated" }
      (record := expected == some actual)
  match expected with
  | none => report { file, ok := false, message := s!"no {expFile} (grail test --update writes it)" }
  | some e =>
    if e != actual then
      let note := TestKind.defaultNote (← IO.FS.readFile (r.ctx.dir / file))
      report { file, ok := false, message := firstDifference e actual ++ note }
    else report { file, ok := true }

/-- (23i) A command whose dependencies are done: its key, and the job that runs it. -/
def Runner.prepCommand (r : Runner) (c : Command) (tools : Array (Tool × Option Nat))
    (inputs : Array (String × Option Nat)) (d : Nat → Done) : IO Prep := do
  let cwd ← IO.currentDir
  let abs (p : System.FilePath) : System.FilePath := if p.isAbsolute then p else cwd / p
  let pkgAbs := abs r.ctx.dir
  -- the tools: what runs, and identities
  let mut ids := #[]
  let mut exe := ""
  for (t, pos) in tools do
    let (run, id) ← match t, pos with
      | .exe n, some i => pure ((abs ((d i).out / n)).toString, s!"exe {n} {(d i).key.toNat}")
      | .path n, _ => match ← r.resolveTool n with
        | .ok x => pure x
        | .error e => return .fail s!"command {c.name}: {e}"
      | .exe n, none => return .fail s!"command {c.name}: no link for {n}"
    if exe.isEmpty then exe := run
    ids := ids.push id
  -- the inputs: what made them, or their contents
  let mut ins := #[]
  for (i, pos) in inputs do
    match pos with
    | some k => ins := ins.push s!"{i} from {(d k).key.toNat}"
    | none =>
      let f := r.ctx.dir / i
      if !(← f.pathExists) then return .fail s!"command {c.name}: the input {i} does not exist, and no target makes it"
      ins := ins.push s!"{i} {(← hashPath f).toNat}"
  let key := mixHash (hash "command") (hash (toString [toString (repr { c with name := "" }), toString ids.toList, toString ins.toList]))
  let label := s!"command {c.name}"
  pure (.job {
    key, timeoutMs := r.timeoutMs, force := c.phony,
    setup := fun tmp => prepareOutputs c (abs tmp / "out"),
    how := .command exe (fun tmp => renderArgs c pkgAbs (abs tmp / "out"))
      (fun tmp => if c.inOutDir then abs tmp / "out" else pkgAbs) c.env,
    finish := some fun o tmp => do
      let logText := (if c.stdout.isSome then "" else o.stdout) ++ o.stderr
      IO.FS.writeFile (tmp / "log.txt") logText
      let logDir := r.ctx.grailDir / "log"
      let logFile := logDir / s!"{c.name}.txt"
      let shown := if r.ctx.dir.toString == "." then s!".grail/log/{c.name}.txt" else logFile.toString
      let failed (msg : String) : IO Finish := do
        IO.FS.createDirAll logDir
        IO.FS.writeFile logFile logText
        pure { res := .error s!"{msg}\n(the whole log: {shown})" }
      if o.code != 0 then
        return ← failed (describeExit o.code r.timeoutMs ++
          (if logText.trimAscii.isEmpty then ", and printed nothing" else s!"; the end of its output:\n{tailLines logText}"))
      if let some p := c.stdout then IO.FS.writeFile (tmp / "out" / p) o.stdout
      if let .error e ← checkOutputs c (tmp / "out") then return ← failed e
      pure { res := .ok (), record := !c.phony,
             log := s!"[{label}]\n" ++ (if c.phony then o.stdout ++ o.stderr else "") },
    onOk := fun _ out => do
      if !c.phony then installOutputs r c out
      pure "" })

/-- Prepare a node whose dependencies are done (`deps`, in the node's order; only a
tolerant node sees failed ones). -/
def Runner.prep (r : Runner) (update : Bool) (results : TestResults) (n : Node)
    (deps : Array (Except String Done)) : IO Prep := do
  let d (i : Nat) : Done := match deps[i]? with | some (.ok d) => d | _ => default
  let tc := r.ctx.tc
  match n.action with
  | .check file => pure (.job { key := ← r.checkKey file, how := .grail (node "check" [str file]), timeoutMs := r.timeoutMs })
  | .build file => pure (.job { key := mixHash (hash "build") (← r.checkKey file), how := .grail (node "build" [str file]), timeoutMs := r.timeoutMs })
  -- (`ir` also writes the C: its key is new, so an old `ir` directory (without main.c) is not reused)
  | .ir file => pure (.job { key := mixHash (hash "ir+c") (d 0).key, how := .grail (node "ir" [str file]), timeoutMs := r.timeoutMs })
  | .obj _ =>
    let cFile := (d 0).out / "main.c"
    let cText ← IO.FS.readFile cFile
    let key := mixHash (hash "obj") (hash (toString [cText, tc.cc, " ".intercalate tc.cflags]))
    pure (.job {
      key := key, timeoutMs := r.timeoutMs, how := .cmd tc.cc fun out =>
      #["-O2", "-w", "-c", "-o", (out / "main.o").toString, cFile.toString] ++ tc.cflags.toArray })
  | .link name _ bin =>
    let o := d 0
    -- (9f) the `link_c` files (compiled here, with `cflags`) and `link_lib` libraries
    let link ← readLink ((d 1).out / "link.txt")
    let mut contents : Array String := #[]
    for f in link.sources do
      contents := contents.push (← try pure (toString (hash (← IO.FS.readBinFile f))) catch _ => pure "missing")
    let srcArgs := if link.sources.isEmpty then #[] else #["-O2", "-w"] ++ link.sources ++ tc.cflags.toArray
    let key := mixHash (hash "link") (hash (toString [toString o.key, tc.cc, " ".intercalate tc.ldflags, " ".intercalate tc.libs,
      " ".intercalate tc.gmp, toString link.sources.toList, toString contents.toList, toString link.libs.toList,
      if link.sources.isEmpty then "" else " ".intercalate tc.cflags]))
    pure (.job {
      key := key, timeoutMs := r.timeoutMs,
      how := .cmd tc.cc fun out =>
        #["-o", (out / name).toString, (o.out / "main.o").toString] ++ srcArgs ++ tc.gmp.toArray ++
          tc.ldflags.toArray ++ tc.libs.toArray ++ link.libFlags,
      onOk := fun _ out => do
        if bin then install (out / name) (r.ctx.grailDir / "bin" / name)
        pure "" })
  | .test file =>
    let kind ← match TestKind.ofSource (← IO.FS.readFile (r.ctx.dir / file)) with
      | .ok k => pure k
      | .error e =>
        let f ← r.judgeTest file update results (.error e)
        return .fail e f.log
    let (_, expected) ← expectedOf r.ctx.dir file
    let key ← r.testKey file kind expected
    -- (9f) a `run` test also depends on its executable's link (its `link_c` files' contents)
    let key := if kind == .run then mixHash key (d 0).key else key
    let force := update || expected.isNone
    let onOk (cached : Bool) (_ : System.FilePath) : IO String := do
      if !cached then return ""
      results.modify (·.insert file { file, ok := true, cached := true })
      pure s!"  ✓ {file}\n"
    -- a dependency failed (the test's program doesn't check or build): a failed test,
    -- with or without `--update`, and nothing is recorded
    if let some (.error e) := deps.find? (· matches .error _) then
      let msg := s!"its program does not build: {e.trimAsciiEnd.toString}"
      let f ← r.judgeTest file update results (.error msg)
      return .fail msg f.log
    let exe := if kind == .run then ((d 0).out / testExe file).toString else ""
    pure (.job {
      key := key, timeoutMs := r.testTimeoutMs, force := force, onOk := onOk,
      how := .grail (node "test" [str file, str kind.name, str exe]),
      finish := some fun o out => do
        if o.code == 124 then r.judgeTest file update results (.error s!"timed out after {secs r.testTimeoutMs} s")
        -- (exit 1: the test failed, its message on stderr; else the process died)
        else if o.code == 1 && !o.stderr.trimAscii.isEmpty then r.judgeTest file update results (.error o.stderr.trimAsciiEnd.toString)
        else if o.code != 0 then r.judgeTest file update results (.error s!"the test's process failed: {failureMessage o r.testTimeoutMs}")
        else r.judgeTest file update results (.ok (← IO.FS.readFile (out / "actual"))) })
  | .source role =>
    let (prog, self) ← r.selfhostSources role
    let key := mixHash (hash "selfhost-source") (hash (toString [role, toString r.ctx.binId, prog]))
    pure (.job {
      key := key, timeoutMs := r.timeoutMs,
      how := .here fun out => do
        IO.FS.writeFile (out / s!"{role}.wiz") prog
        IO.FS.writeFile (out / "self.wiz") self
        pure (.ok ()),
      onOk := fun _ out => do
        install (out / s!"{role}.wiz") (r.ctx.dir / genFile role)
        install (out / "self.wiz") (r.ctx.dir / genSelf role)
        pure "" })
  | .self1 =>
    let stage1 := (d 0).out / "selfhost-stage1"
    let input := r.ctx.dir / genSelf "compiler"
    let self ← IO.FS.readFile input
    let key := mixHash (hash "self1") (hash (toString [toString (hash (← IO.FS.readBinFile stage1)), self]))
    pure (.job { key := key, timeoutMs := r.timeoutMs, how := .grail (node "run-on" [str stage1.toString, str input.toString, str "self1.c"]) })
  | .stage2 =>
    let self1 := (d 0).out / "self1.c"
    let rt ← IO.FS.readFile (r.ctx.dir / "selfhost" / "rt.c")
    let key := mixHash (hash "stage2 -O2") (hash (toString [← IO.FS.readFile self1, rt, tc.cc,
      " ".intercalate tc.gcCflags, " ".intercalate tc.gcLdflags]))
    let rtDir ← IO.FS.realPath (r.ctx.dir / "selfhost")
    pure (.job {
      key := key, timeoutMs := r.timeoutMs, how := .cmd tc.cc fun out =>
      #["-O2", "-w", s!"-I{rtDir}"] ++ tc.gcCflags.toArray ++
        #[self1.toString, "-o", (out / "stage2").toString] ++ tc.gcLdflags.toArray })
  | .self2 =>
    let input := r.ctx.dir / genSelf "compiler"
    let key := mixHash (hash "self2") (hash (toString [toString (d 0).key, ← IO.FS.readFile input]))
    pure (.job { key := key, timeoutMs := r.timeoutMs, how := .grail (node "run-on" [str ((d 0).out / "stage2").toString, str input.toString, str "self2.c"]) })
  | .command c tools inputs => r.prepCommand c tools inputs (d ·)
  | .fixpoint =>
    let self1 ← IO.FS.readFile ((d 0).out / "self1.c")
    let self2 ← IO.FS.readFile ((d 1).out / "self2.c")
    if self1 == self2 then
      pure (.done default s!"fixpoint: stage-1 C = stage-2 C ({self1.utf8ByteSize} bytes)\n")
    else pure (.fail s!"no fixpoint: {firstDiff self1 self2}")

/-- A node's state in the scheduler. -/
inductive Res where
  | ok (d : Done)
  /-- failed, or skipped because `root` failed -/
  | bad (msg : String) (root : String)

structure Sched where
  res : Array (Option Res)
  started : Array Bool
  /-- each node's report (stdout, stderr), printed in order -/
  logs : Array (Option (String × String))
  next : Nat := 0
  /-- ready jobs, in the graph's order -/
  queue : Array (Nat × Job) := #[]
  running : Std.HashMap Nat (System.FilePath × Job) := {}
  tasks : List (Task (Nat × Except IO.Error Outcome)) := []

def Runner.stat (r : Runner) (f : Stats → Stats) : IO Unit := r.stats.modify f

/-- Run the graph: every node, dependencies first, jobs `r.jobs` at a time. -/
partial def Runner.schedule (r : Runner) (g : Graph)
    (prep : Node → Array (Except String Done) → IO Prep) : IO (Array (Option Res)) := do
  let n := g.nodes.size
  let st ← IO.mkRef ({ res := .replicate n none, started := .replicate n false, logs := .replicate n none } : Sched)
  let finishNode (i : Nat) (res : Res) (out err : String) : IO Unit :=
    st.modify fun s => { s with res := s.res.set! i (some res), logs := s.logs.set! i (some (out, err)) }
  let failNode (i : Nat) (msg log : String) : IO Unit := do
    r.stat fun s => { s with failed := s.failed + 1 }
    let label := g.nodes[i]!.label
    if log.isEmpty then finishNode i (.bad msg label) "" s!"✗ {label}\n{indent msg}\n"
    else finishNode i (.bad msg label) log ""
  -- a job ended: judge it, then rename its directory into place
  let complete (i : Nat) (o : Outcome) : IO Unit := do
    let some (tmp, j) := (← st.get).running[i]? | return
    st.modify fun s => { s with running := s.running.erase i }
    let key := j.key
    let label := g.nodes[i]!.label
    let fin ← try
        match j.finish with
        | some f => f o tmp
        | none =>
          if o.code == 0 then pure { res := .ok (), log := s!"[{label}]\n{o.stdout}" }
          else pure { res := .error (failureMessage o j.timeoutMs) }
      catch e => pure { res := .error (toString e) }
    match fin.res with
    | .ok () =>
      let out := r.outDir key
      if fin.record then
        IO.FS.createDirAll (r.ctx.grailDir / "build")
        try IO.FS.rename tmp out
        catch _ => IO.FS.removeDirAll tmp   -- someone else made it first
      else IO.FS.removeDirAll tmp
      r.stat fun s => { s with ran := s.ran + 1 }
      let extra ← try j.onOk false out catch e => pure s!"{e}\n"
      finishNode i (.ok { key, out }) (fin.log ++ extra) ""
    | .error e =>
      if ← tmp.pathExists then IO.FS.removeDirAll tmp
      failNode i e fin.log
  -- start a ready job (a `here` job runs to the end)
  let start (i : Nat) (j : Job) : IO Unit := do
    let ms := j.timeoutMs
    let tmp := r.ctx.grailDir / "tmp" / s!"{hex j.key}-{← IO.Process.getPID}-{← IO.monoNanosNow}"
    IO.FS.createDirAll tmp
    st.modify fun s => { s with running := s.running.insert i (tmp, j) }
    match j.how with
    | .here act =>
      let res ← try act tmp catch e => pure (.error (toString e))
      complete i (match res with
        | .ok () => { code := 0, stdout := "", stderr := "" }
        | .error e => { code := 1, stdout := "", stderr := e })
    | .grail job =>
      let args := #["--grail-job", (r.jobSx tmp job).render] ++ r.ctx.tc.toFlags.toArray
      let t ← IO.asTask (prio := .dedicated) (runSupervised r.self ms r.self.toString args)
      st.modify fun s => { s with tasks := t.map (i, ·) :: s.tasks }
    | .cmd cmd args =>
      let t ← IO.asTask (prio := .dedicated) (runSupervised r.self ms cmd (args tmp))
      st.modify fun s => { s with tasks := t.map (i, ·) :: s.tasks }
    | .command cmd args cwd env =>
      let t ← IO.asTask (prio := .dedicated) do
        try
          j.setup tmp
          runSupervised r.self ms cmd (args tmp) (some (cwd tmp)) env
        catch e => pure ({ code := 127, stdout := "", stderr := toString e } : Outcome)
      st.modify fun s => { s with tasks := t.map (i, ·) :: s.tasks }
  -- a node whose dependencies are done
  let ready (i : Nat) : IO Unit := do
    let nd := g.nodes[i]!
    let s ← st.get
    let deps := nd.deps.map fun j => match s.res[j]! with
      | some (.ok d) => (Except.ok d, "")
      | some (.bad m root) => (.error m, root)
      | none => (.error "", "")
    if !nd.tolerant then
      if let some (_, root) := deps.find? (·.1 matches .error _) then
        r.stat fun s => { s with skipped := s.skipped + 1 }
        let msg := match deps.find? (·.1 matches .error _) with | some (.error m, _) => m | _ => ""
        finishNode i (.bad msg root) "" s!"- {nd.label}: skipped ({root} failed)\n"
        return
    let p ← try prep nd (deps.map (·.1)) catch e => pure (.fail (toString e))
    match p with
    | .done d log => finishNode i (.ok d) log ""
    | .fail msg log => failNode i msg log
    | .job j =>
      let out := r.outDir j.key
      if !j.force && (← out.pathExists) then
        r.stat fun s => { s with upToDate := s.upToDate + 1 }
        let extra ← try j.onOk true out catch e => pure s!"{e}\n"
        finishNode i (.ok { key := j.key, out }) extra ""
      else st.modify fun s => { s with queue := s.queue.push (i, j) }
  let emit : IO Unit := do
    repeat
      let s ← st.get
      match s.logs[s.next]? with
      | some (some (o, e)) =>
        r.out o; r.err e
        st.set { s with next := s.next + 1 }
      | _ => break
  repeat
    -- every node whose dependencies are done is prepared
    let mut progress := true
    while progress do
      progress := false
      for i in [0:n] do
        let s ← st.get
        if !s.started[i]! && g.nodes[i]!.deps.all (s.res[·]!.isSome) then
          st.modify fun s => { s with started := s.started.set! i true }
          ready i
          progress := true
    -- start jobs
    let mut ranHere := false
    repeat
      let s ← st.get
      if s.queue.isEmpty || s.tasks.length ≥ max 1 r.jobs then break
      let some (i, j) := s.queue[0]? | break
      st.set { s with queue := s.queue.extract 1 s.queue.size }
      if j.how matches .here _ then ranHere := true
      start i j
    emit
    let s ← st.get
    match s.tasks with
    | [] => if !ranHere && s.queue.isEmpty then break
    | t :: ts =>
      let ((i, o), rest) ← IO.waitAny' (t :: ts)
      st.modify fun s => { s with tasks := rest }
      complete i (match o with
        | .ok o => o
        | .error e => { code := 127, stdout := "", stderr := toString e })
  emit
  pure (← st.get).res

/-- Build these targets (of a package with targets `all`); false if anything failed. -/
def Runner.build (r : Runner) (all targets : List Target) : IO Bool := do
  let g ← try
      if let .error e := checkCommands all then throw (IO.userError e)
      let (_, g) ← (targets.forM fun t => do let _ ← addTarget r.ctx.dir (libsOf all) all t).run {}
      pure g
    catch e => r.err s!"{e}\n"; return false
  -- (23i) outputs an earlier build installed that no command declares now
  r.out (← removeStale r.ctx all)
  let res ← r.schedule g (r.prep false (← IO.mkRef {}))
  pure (res.all (· matches some (.ok _)))

/-- (23j) `grail run TARGET -- ARGS`: build what TARGET needs, then run it with `extra`
appended, its stdio grail's own (not captured), in the package directory, in grail's
process group (so Ctrl-C reaches it). A command run this way is not recorded: its
outputs are written at their paths in the package, and its stdout is not redirected.
Returns its exit code (128+N if it died of signal N). -/
def Runner.runTarget (r : Runner) (all : List Target) (t : Target) (extra : Array String) : IO UInt32 := do
  let cwd ← IO.currentDir
  let pkgAbs := if r.ctx.dir.isAbsolute then r.ctx.dir else cwd / r.ctx.dir
  let exeTarget (n : String) : Option Target := all.find? fun | .exe m _ => m == n | _ => false
  let bin (n : String) : System.FilePath := pkgAbs / ".grail" / "bin" / n
  let spawn (cmd : String) (args : Array String) (env : List (String × String)) : IO UInt32 := do
    let child ← try IO.Process.spawn { cmd, args, cwd := pkgAbs, env := env.toArray.map fun (k, v) => (k, some v) }
      catch e => r.err s!"{cmd}: {e}\n"; return 127
    child.wait
  match t with
  | .exe n _ =>
    unless ← r.build all [t] do return 1
    spawn (bin n).toString extra []
  | .command c =>
    let mut needs : List Target := []
    for tool in c.tool :: c.uses do
      if let .exe n := tool then
        match exeTarget n with
        | some e => needs := needs ++ [e]
        | none => r.err s!"command {c.name}: no exe target {n}\n"; return 1
    for i in c.inputs do
      if let some p := producerOf all i then needs := needs ++ [.command p]
    unless ← r.build all needs do return 1
    let exe ← match c.tool with
      | .exe n => pure (bin n).toString
      | .path n => match ← r.resolveTool n with
        | .ok (run, _) => pure run
        | .error e => r.err s!"{e}\n"; return 127
    for i in c.inputs do
      unless (producerOf all i).isSome || (← (r.ctx.dir / i).pathExists) do
        r.err s!"command {c.name}: the input {i} does not exist, and no target makes it\n"; return 1
    prepareOutputs c pkgAbs
    spawn exe (renderArgs { c with inOutDir := false } pkgAbs pkgAbs ++ extra) c.env
  | _ => r.err s!"grail run: {t.name} is not an exe or a command target\n"; pure 2

/-- Run the tests of these targets whose path contains one of `filters` (all, if none). -/
def Runner.tests (r : Runner) (targets : List Target) (filters : List String) (update : Bool) :
    IO (Array TestResult) := do
  let mut files := #[]
  for t in targets do
    if let .tests _ root := t then
      for f in ← testFiles r.ctx.dir root do
        if filters.isEmpty || filters.any (fun p => (f.splitOn p).length > 1) then files := files.push f
  let (_, g) ← (files.forM fun f => do let _ ← addTest r.ctx.dir (libsOf targets) f).run {}
  let results : TestResults ← IO.mkRef {}
  let res ← r.schedule g (r.prep update results)
  let got ← results.get
  pure (files.map fun f => match got[f]? with
    | some t => t
    | none =>
      let msg := match g.ids[s!"test {f}"]? >>= (res[·]?) with
        | some (some (.bad m _)) => m
        | _ => "did not run"
      { file := f, ok := false, message := msg })

/-! ## A job, in its own process -/

/-- The IR, C and link text of a checked program. One job writes all three, so a file
is elaborated once instead of once per job. -/
def writeCode (out : System.FilePath) (s : CommandState ZeroOneMany) : IO (Except String Unit) :=
  match mainDecls s with
  | .error e => pure (.error e)
  | .ok (ds, io) => do
    IO.FS.writeFile (out / "main.ir") ("\n".intercalate (ds.toList.map (·.toString)))
    IO.FS.writeFile (out / "main.c") (C.program ds io (Build.extraC s) s.globals.unboxStructs)
    IO.FS.writeFile (out / "link.txt") (renderLink (Build.linkOf s))
    pure (.ok ())

/-- Run one job (`(KIND ARGS…)`), writing into `out`. -/
def Runner.runJob (r : Runner) (out : System.FilePath) : Sx → IO (Except String Unit)
  | .l #[.a "check", .a file] => do
    let l ← r.load file
    let s ← r.elab file
    let msgs := render file l s
    if hasErrors s then return .error msgs
    IO.print msgs
    IO.FS.writeFile (out / "messages.txt") msgs
    pure (.ok ())
  -- (`build`: check, IR and C of a standalone source; `ir`: the same for a file that is
  -- already checked as a package module)
  | .l #[.a "build", .a file] => do
    let l ← r.load file
    let s ← r.elab file
    let msgs := render file l s
    if hasErrors s then return .error msgs
    IO.print msgs
    IO.FS.writeFile (out / "messages.txt") msgs
    writeCode out s
  | .l #[.a "ir", .a file] => do writeCode out (← r.elab file)
  | .l #[.a "run-on", .a exe, .a input, .a file] => do
    runOn exe (← IO.FS.readFile input) out file
  | .l #[.a "test", .a file, .a kind, .a exe] => do
    let kind := if kind == "run" then TestKind.run else .check
    -- a program that times out or fails is a failed test, not an output (`--update`
    -- must not record it)
    match ← r.testOutput file kind exe with
    | .ok a => IO.FS.writeFile (out / "actual") a; pure (.ok ())
    | .error e => pure (.error e)
  | x => pure (.error s!"unknown job {x.render}")

/-- `<self> --grail-job JOB TOOLCHAIN-FLAGS`: `JOB` is `(job DIR STD BINID (ROOTS…) OUT (KIND ARGS…))`.
Exit code 0 when the job succeeded; its report on stdout, its error on stderr. -/
def jobMain (tc : Toolchain) (arg : String) : IO UInt32 := do
  let some (.l #[.a "job", .a dir, .a std, .a bin, .l roots, .a out, job]) := Sx.parse arg
    | IO.eprintln s!"bad job {arg}"; return 2
  let r : Runner := { ctx := { dir, std, tc, binId := bin.toNat!.toUInt64,
                               libRoots := roots.toList.filterMap fun x => (atom? x).map System.FilePath.mk },
                      stats := ← IO.mkRef {}, memo := ← IO.mkRef {} }
  match ← (try r.runJob out job catch e => pure (.error (toString e))) with
  | .ok () => pure 0
  | .error e => IO.eprint e; pure 1

end Grail
