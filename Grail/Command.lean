import Grail.Build
import Grail.Exec

/-!
# Command targets (stage 23i)

A command target runs a program (`Tool.path`: found on `PATH`; `Tool.exe`: an `exe`
target of the package) with declared inputs and outputs, as a node of the build graph
(`Grail/Graph.lean`). This file has what is particular to them:

* **edges**: an input that is another command's declared output (or lies under its
  declared output directory) depends on that command; an `exe` tool depends on its link;
* **the key**: the command's description (tool reference, argument parts, inputs,
  outputs, environment, working directory), the tool's identity (`Runner.resolveTool`),
  and each input's producer key or content hash (`hashPath`);
* **outputs**: written under `<job dir>/out/`, checked (each declared one exists,
  nothing else was made there), renamed into the store with the job's directory, and
  **installed** at their paths in the package (`installOutputs`), recorded in
  `.grail/installed` so that `grail clean` and later builds can remove what grail put
  there (`removeStale`, `cleanInstalled`).
-/

namespace Grail
open Wiz Cache

/-- `./a//b/` → `a/b` -/
def normPath (p : String) : String :=
  let parts := (p.splitOn "/").filter fun s => !s.isEmpty && s != "."
  "/".intercalate parts

/-- Is `p` the path `o` or under it? -/
def pathUnder (p o : String) : Bool :=
  let p := normPath p
  let o := normPath o
  p == o || p.startsWith (o ++ "/")

def commandsOf (all : List Target) : List Command :=
  all.filterMap fun | .command c => some c | _ => none

/-- The command whose declared output `p` is (or lies under). -/
def producerOf (all : List Target) (p : String) : Option Command :=
  (commandsOf all).find? fun c => c.outputPaths.any (pathUnder p ·)

/-- Each output belongs to one command, inside the package, and outside `.grail/`. -/
def checkCommands (all : List Target) : Except String Unit := do
  let mut seen : List (String × String) := []
  for c in commandsOf all do
    for o in c.outputPaths do
      if o.startsWith "/" || (o.splitOn "/").contains ".." || normPath o == "" then
        throw s!"command {c.name}: the output {o} is not a path inside the package"
      if pathUnder o ".grail" then throw s!"command {c.name}: the output {o} is inside .grail/"
      for (q, other) in seen do
        if normPath q == normPath o then
          throw s!"commands {other} and {c.name} both declare the output {o}"
        if pathUnder o q || pathUnder q o then
          throw s!"the output {o} of {c.name} and the output {q} of {other} are inside one another"
      seen := seen ++ [(o, c.name)]
    for i in c.inputs do
      if c.outputPaths.any (pathUnder i ·) then throw s!"command {c.name}: {i} is both an input and an output"

/-- Every file under a directory, by path relative to it, sorted. -/
partial def treeFiles (root : System.FilePath) (rel : String := "") : IO (Array String) := do
  let mut out := #[]
  for e in ← (if rel.isEmpty then root else root / rel).readDir do
    let r := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
    if ← e.path.isDir then out := out ++ (← treeFiles root r) else out := out.push r
  pure (out.qsort (· < ·))

/-- A file's or directory's contents, as a hash (a directory: every file's path and contents). -/
def hashPath (p : System.FilePath) : IO UInt64 := do
  if ← p.isDir then
    let mut k := hash "dir"
    for f in ← treeFiles p do
      k := mixHash k (mixHash (hash f) (hash (← IO.FS.readBinFile (p / f))))
    pure k
  else pure (hash (← IO.FS.readBinFile p))

/-- A program by name: the path it is run by (`PATH` is searched for a bare name; a name
with a `/` is relative to the package), and its identity: its real path (symlinks
followed) and the hash of that file. Memoised per run. -/
def Runner.resolveTool (r : Runner) (name : String) : IO (Except String (String × String)) := do
  if let some t := (← r.memo.get).tools[name]? then return t
  let found : Option System.FilePath ← do
    if name.contains '/' then
      let p : System.FilePath := if name.startsWith "/" then name else r.ctx.dir / name
      pure (if ← p.pathExists then some p else none)
    else
      let path := (← IO.getEnv "PATH").getD ""
      let mut hit := none
      for d in path.splitOn ":" do
        if d.isEmpty then continue
        let p := System.FilePath.mk d / name
        if (← p.pathExists) && !(← p.isDir) then hit := some p; break
      pure hit
  let res ← match found with
    | none => pure (.error s!"{name}: not found{if name.contains '/' then "" else " on PATH"}")
    | some p =>
      try
        let real ← IO.FS.realPath p
        pure (.ok (p.toString, s!"{real} {hash (← IO.FS.readBinFile real)}"))
      catch e => pure (.error s!"{name}: {e}")
  r.memo.modify fun m => { m with tools := m.tools.insert name res }
  pure res

/-- The argv of a command: inputs as written (absolute when it runs in its output
directory), outputs under `outRoot`. -/
def renderArgs (c : Command) (pkgAbs outRoot : System.FilePath) : Array String :=
  c.args.toArray.map fun parts => String.join (parts.map fun
    | .text s => s
    | .input p => if c.inOutDir then (pkgAbs / p).toString else p
    | .output p => (outRoot / p).toString)

/-- Create the parents of a command's output files and its output directories. -/
def prepareOutputs (c : Command) (outRoot : System.FilePath) : IO Unit := do
  IO.FS.createDirAll outRoot
  for (p, dir) in c.outputs do
    if dir then IO.FS.createDirAll (outRoot / p)
    else if let some d := (outRoot / p).parent then IO.FS.createDirAll d
  if let some p := c.stdout then
    if let some d := (outRoot / p).parent then IO.FS.createDirAll d

/-- After the command: every declared output exists, and nothing undeclared was made
under the output directory. -/
def checkOutputs (c : Command) (outRoot : System.FilePath) : IO (Except String Unit) := do
  let mut errs := #[]
  for (p, dir) in c.outputs do
    let f := outRoot / p
    if dir then
      unless ← f.isDir do errs := errs.push s!"the declared output directory {p} was not made"
    else if !(← f.pathExists) then errs := errs.push s!"the declared output {p} was not made"
    else if ← f.isDir then errs := errs.push s!"the declared output file {p} is a directory (declare it with Command.makesDir)"
  if ← outRoot.pathExists then
    for f in ← treeFiles outRoot do
      unless c.outputPaths.any (pathUnder f ·) do
        errs := errs.push s!"{f} was made in the output directory but is not a declared output (Command.makes or Command.makesDir)"
  pure (if errs.isEmpty then .ok () else .error ("\n".intercalate errs.toList))

/-! ## Output manifests and cache validity (23p)

A command's key covers its description and its inputs; its result is the directory
`.grail/build/<key>/`. A directory that merely exists is not enough: a later build also
checks that the declared outputs are still there and have the hashes written beside
them (`outputs.txt`), so a deleted or edited store output makes the command run again.
An entry from before this file existed (no `outputs.txt`) is still accepted if every
declared output is present, so an existing cache keeps working.
-/

/-- `outputs.txt`, beside a command job's `out/` directory. -/
def outputManifest (jobDir : System.FilePath) : System.FilePath := jobDir / "outputs.txt"

/-- The declared outputs, by path, and whether each is a directory (23p). -/
def outputKind (c : Command) (p : String) : Bool :=
  c.outputs.any fun (q, dir) => dir && normPath q == normPath p

/-- The manifest of a command's `out/` directory: `file PATH HASH` for every file and
`dir PATH` for every declared output directory (a directory's files are each listed).
Sorted, so it is stable. -/
def renderOutputManifest (c : Command) (outRoot : System.FilePath) : IO String := do
  let mut lines : List String := []
  for p in c.outputPaths do
    let p := normPath p
    if outputKind c p then
      lines := lines ++ [s!"dir {p}"]
      for f in ← treeFiles (outRoot / p) do
        let rel := normPath (p ++ "/" ++ f)
        let h := hash (← IO.FS.readBinFile (outRoot / p / f))
        lines := lines ++ [s!"file {rel} {h.toNat}"]
    else
      let h := hash (← IO.FS.readBinFile (outRoot / p))
      lines := lines ++ [s!"file {p} {h.toNat}"]
  pure (String.join ((lines.mergeSort (· < ·)).map (· ++ "\n")))

/-- Write a command's output manifest into its job directory, before the directory is
renamed into the store. -/
def writeOutputManifest (c : Command) (jobDir : System.FilePath) : IO Unit := do
  let text ← renderOutputManifest c (jobDir / "out")
  IO.FS.writeFile (outputManifest jobDir) text

/-- Are all of a command's declared outputs present under `outRoot`, with the right kind? -/
def outputsPresent (c : Command) (outRoot : System.FilePath) : IO Bool := do
  for p in c.outputPaths do
    let f := outRoot / p
    if outputKind c p then
      unless ← f.isDir do return false
    else
      unless (← f.pathExists) && !(← f.isDir) do return false
  pure true

/-- Is a stored command result still valid (23p)? Its manifest must list every declared
output and every listed file must still have the hash it was written with. An entry
without a manifest (an older grail) is valid when its declared outputs are present. -/
def checkOutputManifest (c : Command) (jobDir : System.FilePath) : IO Bool := do
  let outRoot := jobDir / "out"
  let manifest := outputManifest jobDir
  if !(← manifest.pathExists) then return ← outputsPresent c outRoot
  let mut files : Std.HashMap String Nat := {}
  let mut dirs : Std.HashSet String := {}
  for line in (← IO.FS.readFile manifest).splitOn "\n" do
    match line.splitOn " " with
    | ["file", p, h] =>
      if let some h := h.toNat? then files := files.insert p h
    | ["dir", p] => dirs := dirs.insert p
    | _ => pure ()
  -- every declared output is covered by the manifest
  for p in c.outputPaths do
    let p := normPath p
    if outputKind c p then
      unless dirs.contains p do return false
    else
      unless files.contains p do return false
  -- and every listed entry still exists with its hash
  for (p, h) in files.toList do
    let f := outRoot / p
    unless (← f.pathExists) && !(← f.isDir) do return false
    let got := hash (← IO.FS.readBinFile f)
    unless got.toNat == h do return false
  for p in dirs.toList do
    unless ← (outRoot / p).isDir do return false
  pure true

/-! ## Installed outputs -/

def installedFile (c : Ctx) : System.FilePath := c.grailDir / "installed"

/-- `.grail/installed`: each file grail installed in the package, with the hash of what it wrote. -/
def readInstalled (c : Ctx) : IO (Std.HashMap String UInt64) := do
  let f := installedFile c
  if !(← f.pathExists) then return {}
  let mut m := {}
  for l in (← IO.FS.readFile f).splitOn "\n" do
    if let [p, h] := l.splitOn "\t" then
      if let some h := h.toNat? then m := m.insert p h.toUInt64
  pure m

def writeInstalled (c : Ctx) (m : Std.HashMap String UInt64) : IO Unit := do
  let lines := m.toList.map (fun (p, h) => s!"{p}\t{h.toNat}") |>.toArray.qsort (· < ·)
  IO.FS.createDirAll c.grailDir
  let tmp := (installedFile c).toString ++ s!".tmp{← IO.Process.getPID}"
  IO.FS.writeFile tmp (String.join (lines.toList.map (· ++ "\n")))
  IO.FS.rename tmp (installedFile c)

/-- Copy a file if its content or its executable bit differs: mode 755 if the command
made it executable (by its owner), 644 otherwise. -/
def installData (src dst : System.FilePath) : IO Unit := do
  let new ← IO.FS.readBinFile src
  let exec ← isExecutable src
  if ← dst.pathExists then
    if !(← dst.isDir) then
      if (← IO.FS.readBinFile dst) == new && (← isExecutable dst) == exec then return
    else IO.FS.removeDirAll dst
  if let some d := dst.parent then IO.FS.createDirAll d
  let tmp := dst.toString ++ s!".tmp{← IO.Process.getPID}"
  IO.FS.writeBinFile tmp new
  let r : IO.AccessRight := { read := true }
  let rx : IO.AccessRight := { read := true, execution := true }
  IO.setAccessRights tmp (if exec then { user := { read := true, write := true, execution := true }, group := rx, other := rx }
    else { user := { read := true, write := true }, group := r, other := r })
  IO.FS.rename tmp dst

/-- Install a command's outputs (from the store directory `out`) at their paths in the
package; a directory output replaces the package's directory as a whole. -/
def installOutputs (r : Runner) (c : Command) (out : System.FilePath) : IO Unit := do
  let mut inst ← readInstalled r.ctx
  for p in c.outputPaths do
    let src := out / "out" / p
    let dst := r.ctx.dir / p
    if ← src.isDir then
      let files ← treeFiles src
      if ← dst.pathExists then
        if ← dst.isDir then
          for f in ← treeFiles dst do
            unless files.contains f do
              IO.FS.removeFile (dst / f)
              inst := inst.erase (normPath (p ++ "/" ++ f))
        else IO.FS.removeFile dst
      IO.FS.createDirAll dst
      for f in files do
        installData (src / f) (dst / f)
        inst := inst.insert (normPath (p ++ "/" ++ f)) (hash (← IO.FS.readBinFile (src / f)))
    else
      installData src dst
      inst := inst.insert (normPath p) (hash (← IO.FS.readBinFile src))
  writeInstalled r.ctx inst

/-- Files grail installed that no command of the package declares any more: removed if
they are as grail left them, kept (and named) if they were changed since; `grail clean`
does the same for every installed file. Returns the report. -/
def removeInstalled (c : Ctx) (keep : String → Bool) (why : String) : IO String := do
  let inst ← readInstalled c
  if inst.isEmpty then return ""
  let mut report := ""
  let mut left := inst
  for (p, h) in inst.toList do
    if keep p then continue
    let f := c.dir / p
    left := left.erase p
    if !(← f.pathExists) then continue
    if (← hashPath f) == h then
      IO.FS.removeFile f
      report := report ++ s!"removed {p} ({why})\n"
    else report := report ++ s!"kept {p}: changed since grail installed it\n"
  if left.size != inst.size then writeInstalled c left
  pure report

def removeStale (c : Ctx) (all : List Target) : IO String :=
  removeInstalled c (fun p => (commandsOf all).any fun cmd => cmd.outputPaths.any (pathUnder p ·))
    "installed by an earlier build; no target makes it any more"

def cleanInstalled (c : Ctx) : IO String := removeInstalled c (fun _ => false) "installed by grail"

end Grail
