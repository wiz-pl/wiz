import Wiz
import Tests.Harness

/-!
# The rejection corpus

A helper for the group `reject` (`Tests/Groups/Reject.lean`): programs that the elaborator
must turn down, with the diagnostic class and the place it is reported. Each rejection is
checked three ways:

* in process (`frontend`, a cached `runFrontend`), for the error's `code` and the source text its span covers;
* through `wiz check` (`cli := true`, one or two cases per class), so the program really
  makes the compiler exit nonzero (an accepted neighbour must leave it zero). Running
  `wiz check` on every case costs about a second each (it reads the library from cache),
  so the group pins the exit code on representatives and checks the class and span of
  every program here. Both paths run the same frontend;
* for a `panic`: a `panic!` aborts the case's process (`Wiz.exitOnPanic` in
  `Tests/Main.lean`), and the command line's output must not mention one either.

A program that is currently accepted but should not be is an `xfail`: its case records
the reason (a `Tests.note`, so it shows in `--timings`) and fails once the elaborator
starts rejecting it, which is when it moves to `rejected`.
-/

namespace Tests.Reject

open Wiz

initialize libRef : IO.Ref (Std.HashMap Name String) ← IO.mkRef ({} : Std.HashMap Name String)

/-- The toolchain's modules, read once in this process. -/
def libModules : IO (Std.HashMap Name String) := do
  let m ← libRef.get
  if !m.isEmpty then return m
  let mods ← Module.loadAll ["lib"]
  let mut t : Std.HashMap Name String := {}
  for (n, (_, text)) in mods.toList do t := t.insert n text
  libRef.set t
  pure t

/-- The frontend's state for a program: `lib/`, plus the given modules (path → text). -/
def stateFor (extra : List (Name × String) := []) : IO (CommandState ZeroOneMany) := do
  let mut table ← libModules
  for (n, text) in extra do table := table.insert n text
  pure { loader := fun m => table[m]?, trustedModule := Tests.libModule }

/-- A cache the group's cases share: the first one elaborates the library, the rest
deserialize it (`wiz check` uses the same cache path in a run, one process per case). -/
def cacheDir : System.FilePath := "/tmp/wiz-reject-corpus-cache"

/-- The frontend's result for a program, through the shared cache. -/
def frontend (src : String) (extra : List (Name × String) := []) : IO (CommandState ZeroOneMany) := do
  IO.FS.createDirAll cacheDir
  let (s, _) ← Cache.elaborateCached (some cacheDir) [] src (← stateFor extra) 0
  pure s

/-- The source text under a message's span. -/
def spanText (src : String) (m : Msg) : String :=
  let cs := src.toList.toArray
  let a := min m.info.start cs.size
  let b := min m.info.stop cs.size
  if b <= a then "" else String.ofList (cs.extract a b).toList

/-- Whether the message's span points at `frag`: the span contains it, or (a parser
error's zero-width span, at the offending token) the text from the span's start begins
with it. -/
def spanPointsAt (src : String) (m : Msg) (frag : String) : Bool :=
  if (spanText src m).contains frag then true
  else if !(spanText src m).isEmpty then false
  else
    let cs := src.toList.toArray
    let a := min m.info.start cs.size
    (String.ofList (cs.extract a cs.size).toList).startsWith frag

def codeMatches (want : Option String) (m : Msg) : Bool :=
  match want with
  | some c => m.code == c
  | none => m.code == ""

def describe (src : String) (m : Msg) : String :=
  let code := if m.code.isEmpty then "(no code)" else m.code
  s!"  [{code}] at {m.info.start}..{m.info.stop} {repr (spanText src m)}: {m.text}"

/-- Fail if a diagnostic mentions a panic. (`Wiz.exitOnPanic` already turns a real
`panic!` into a failed case; this also catches one that reached a message.) -/
def noPanic (msgs : Array Msg) : IO Unit := do
  for m in msgs do
    if m.text.toLower.contains "panic" then
      throw (IO.userError s!"a panic in a diagnostic: {m.text}")

/-- The `wiz` binary next to the tests binary (or Lake's), if there is one. -/
def wizBinary : IO (Option System.FilePath) := do
  let app ← IO.appPath
  let candidates : List System.FilePath :=
    [(app.parent.getD ".") / "wiz", System.FilePath.mk ".lake/build/bin/wiz"]
  for c in candidates do
    if ← c.pathExists then return some c
  return none

/-- Write the program (and its modules) to a fresh directory and run `wiz check` on it:
`wantReject` says whether the compiler must exit nonzero. -/
def cliCheck (src : String) (extra : List (Name × String)) (wantReject : Bool) : IO Unit := do
  let some wiz ← wizBinary | skip "no wiz binary"
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "main.wiz") src
  for (n, text) in extra do
    let p := dir / Module.relPath n
    if let some d := p.parent then IO.FS.createDirAll d
    IO.FS.writeFile p text
  IO.FS.createDirAll cacheDir
  let out ← IO.Process.output
    { cmd := wiz.toString,
      args := #["check", (dir / "main.wiz").toString, "-I", dir.toString, "--cache", cacheDir.toString] }
  let output := out.stdout ++ out.stderr
  if output.toLower.contains "panic" then
    throw (IO.userError s!"wiz check panicked:\n{output}")
  if wantReject then
    unless out.exitCode != 0 do
      throw (IO.userError s!"wiz check accepted a program that must be rejected (exit 0):\n{output}")
  else
    unless out.exitCode == 0 do
      throw (IO.userError s!"wiz check rejected a program that must stay accepted (exit {out.exitCode}):\n{output}")

/-- Elaborate in process and check that an error with the given class (code; `none` is
"no code") and span is reported. -/
def checkRejection (src : String) (extra : List (Name × String))
    (code : Option String) (span : String) (text : String) : IO Unit := do
  let s ← frontend src extra
  noPanic s.messages
  let errs := s.messages.filter (·.severity == .error)
  if errs.isEmpty then
    throw (IO.userError s!"accepted a program that must be rejected:\n{src}")
  let ok := errs.any fun m =>
    codeMatches code m && spanPointsAt src m span && (text.isEmpty || m.text.contains text)
  unless ok do
    let want := match code with | some c => c | none => "(no code)"
    throw (IO.userError
      s!"no error with code {want}, span at {repr span}, text {repr text}.\nAll errors:\n{"\n".intercalate (errs.toList.map (describe src))}")

/-- A program that must be rejected: `code` is the expected stable error code (`none`:
an error that has no code yet), `span` text the diagnostic must point at, and `text` a
fragment of the message (to pin down errors that share a code or have none). -/
def rejected (name src : String) (code : Option String) (span : String)
    (text : String := "") (extra : List (Name × String) := []) (cli : Bool := false) : Case where
  name := name
  run := fun _ => do
    checkRejection src extra code span text
    if cli then cliCheck src extra true

/-- A neighbour that must stay accepted: no error in process, and (with `cli`) `wiz check`
exits 0. -/
def accepted (name src : String) (extra : List (Name × String) := [])
    (cli : Bool := false) : Case where
  name := name
  run := fun _ => do
    let s ← frontend src extra
    noPanic s.messages
    let errs := (s.messages.filter (·.severity == .error)).map fun m => describe src m
    unless errs.isEmpty do
      throw (IO.userError s!"rejected a program that must stay accepted:\n{"\n".intercalate errs.toList}")
    if cli then cliCheck src extra false

/-- A program that should be rejected but is currently accepted: an `xfail`, with the
reason in a test note. It fails when the elaborator starts rejecting it, so the case
moves to `rejected` (or the reason is revisited). -/
def xfail (name src : String) (reason : String) (extra : List (Name × String) := [])
    (cli : Bool := true) : Case where
  name := name
  run := fun _ => do
    let s ← frontend src extra
    noPanic s.messages
    let errs := (s.messages.filter (·.severity == .error)).map fun m => describe src m
    unless errs.isEmpty do
      throw (IO.userError
        s!"xfail case is now rejected (promote it to `rejected`): {reason}\n{"\n".intercalate errs.toList}")
    Tests.note s!"xfail: {reason}"
    if cli then cliCheck src extra false

end Tests.Reject
