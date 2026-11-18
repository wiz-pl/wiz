import Tests.Harness
import Wiz
import Grail
import Tests.Elab

/-!
Stage 23: modules by path (23b), per-module cache keys and atomic writes (23c), and
grail, the build tool (23d).

The helpers that several of these groups (or other modules) use. Each group is a module
of its own, `Tests/Groups/Grail*.lean`, which registers it (see `Tests/Harness.lean`,
`registerGroup`); a helper only one group uses lives in that group's module.
-/

namespace Tests.Grail
open Wiz Tests

/-- A fresh directory with these files in it. -/
def mkTree (files : List (String × String)) : IO System.FilePath := do
  let dir ← IO.FS.createTempDir
  for (p, text) in files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  pure dir

def loaderOf (m : Std.HashMap Name (System.FilePath × String)) : Name → Option String := fun n => (m[n]?).map (·.2)

/-- Every file under `dir`, as (path relative to `root`, modification time, hash of the
contents), sorted by path: a read-only cache must leave this unchanged. The contents are
read as bytes (a `.wizr` region is not UTF-8). -/
partial def snapshotAt (root dir : System.FilePath) : IO (List (String × String × UInt64)) := do
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← snapshotAt root e.path)
    else
      let md ← e.path.metadata
      let bytes ← IO.FS.readBinFile e.path
      let rel := (e.path.toString.drop root.toString.length).toString
      out := out ++ [(rel, s!"{md.modified.sec}.{md.modified.nsec}", hash bytes.toList)]
  pure out

def snapshot (dir : System.FilePath) : IO (List (String × String × UInt64)) := do
  pure ((← snapshotAt dir dir).mergeSort (fun a b => a.1 < b.1))

/-- The `.wizr` module regions in a cache directory. -/
def regionFiles (cache : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← cache.readDir
  pure (entries.filter (fun e => e.fileName.endsWith ".wizr") |>.map (·.path))

/-- The per-module output manifests in a cache directory. -/
def manifestFiles (cache : System.FilePath) : IO (Array System.FilePath) := do
  let d := cache / "manifest.d"
  if !(← d.pathExists) then return #[]
  let entries ← d.readDir
  pure (entries.filter (fun e => e.fileName.endsWith ".wizmf") |>.map (·.path))

/-- The manifest file for module `name` in a cache directory. -/
def manifestFor (cache : System.FilePath) (name : String) : IO (Option System.FilePath) := do
  for f in ← manifestFiles cache do
    let text ← IO.FS.readFile f
    if let some m := Cache.parseManifest text then
      if toString m.module == name then return some f
  pure none

/-- Set a file's modification time (`touch -d`), for the pruning tests. -/
def touchAgo (f : System.FilePath) (when : String) : IO Unit := do
  let o ← IO.Process.output { cmd := "touch", args := #["-d", when, f.toString] }
  if o.exitCode != 0 then throw (IO.userError s!"touch -d {when} {f}: {o.exitCode} {o.stderr}")

/-- Flip one byte in `f` (by default the middle): a same-size corruption no header or tag
would catch. Returns the index flipped. -/
def flipByte (f : System.FilePath) (i : Nat := 0) : IO Nat := do
  let b ← IO.FS.readBinFile f
  if b.size == 0 then throw (IO.userError s!"{f} is empty")
  let j := min (if i == 0 then b.size / 2 else i) (b.size - 1)
  IO.FS.writeBinFile f (b.set! j (b.get! j ^^^ 0xff))
  pure j

/-- A small library: `Data.Two` (in a subdirectory) imports `Prelude`; `Use` imports it. -/
def libFiles : List (String × String) :=
  [("Data/Two.wiz", "import Prelude\ndef two : Nat := 2\n"),
   ("Use.wiz", "import Data.Two\ndef four : Nat := two + two\n"),
   ("Other.wiz", "import Prelude\ndef one : Nat := 1\n")]

/-- The binary id of the grail the tests run: this test driver (its jobs run as
`<this test driver> --grail-job …`), by its hash, so a rebuilt driver doesn't reuse a
package's `.grail/build` from an older one. -/
def binId (tc : Toolchain) : IO UInt64 := Cache.binaryId tc.cacheDir

/-- The toolchain with the package's settings (and the machine's, from
`grail.local.wiz`) applied, as `grail` itself does: `grail.wiz` has `Package.set "libs"
"-lm"`, and a test that runs a program must link it the same way. An unknown setting is
ignored here (the CLI reports it); the harness is not the build tool. -/
def withSettings (tc : Toolchain) (pkg : Grail.Package) (machine : List (String × String)) :
    IO Toolchain := do
  let mut tc := tc
  for (k, v) in pkg.settings ++ machine do
    match tc.set k v with
    | some t => tc := t
    | none => pure ()
  pure tc

/-- A runner for a package directory; its jobs run as `<this test driver> --grail-job …`,
and its report goes to `log`. -/
def runner (dir : System.FilePath) (tc : Toolchain) (pkg : Grail.Package) (jobs : Nat := 1)
    (log : IO.Ref String) : IO Grail.Runner := do
  pure { ctx := { dir, std := "lib", tc, binId := ← binId tc, libRoots := Grail.libRootsOf dir pkg.targets },
         stats := ← IO.mkRef {}, memo := ← IO.mkRef {}, jobs, self := ← IO.appPath,
         out := fun s => log.modify (· ++ s), err := fun s => log.modify (· ++ s) }

/-- Run grail's build on a package directory; also returns the report. -/
def buildLog (dir : System.FilePath) (tc : Toolchain) (only : List String := []) (jobs : Nat := 1)
    (timeoutMs : Option Nat := none) : IO (Grail.Stats × Bool × String) := do
  match ← Grail.readConfig tc (← binId tc) "lib" dir with
  | .error e => throw (IO.userError e)
  | .ok (pkg, machine) =>
    let tc ← withSettings tc pkg machine
    let log ← IO.mkRef ""
    let r ← runner dir tc pkg jobs log
    let r := { r with timeoutMs := timeoutMs.getD r.timeoutMs }
    let ok ← r.build pkg.targets (pkg.targets.filter fun t => only.isEmpty || only.contains t.name)
    pure (← r.stats.get, ok, ← log.get)

def build (dir : System.FilePath) (tc : Toolchain) (only : List String := []) (jobs : Nat := 1) : IO (Grail.Stats × Bool) := do
  let (s, ok, _) ← buildLog dir tc only jobs
  pure (s, ok)

/-- The names in a package's `.grail/build`, sorted. -/
def buildDirs (dir : System.FilePath) : IO (List String) := do
  let entries ← (dir / ".grail" / "build").readDir
  pure (entries.map (·.fileName)).toList.mergeSort

/-- Run git in `dir` (with an identity, for commits); fails the test if git fails. -/
def gitIn (dir : System.FilePath) (args : List String) : IO String := do
  let o ← IO.Process.output {
    cmd := "git", cwd := dir,
    args := #["-c", "user.name=grail", "-c", "user.email=grail@example.com", "-c", "init.defaultBranch=main",
              "-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false"] ++ args.toArray }
  if o.exitCode != 0 then throw (IO.userError s!"git {args}: {o.stderr}")
  pure o.stdout.trimAscii.toString

/-- Run a command in `dir`; its trimmed stdout. Fails if it fails. -/
def runIn (dir : System.FilePath) (cmd : String) (args : List String) : IO String := do
  let o ← IO.Process.output { cmd, args := args.toArray, cwd := dir }
  if o.exitCode != 0 then throw (IO.userError s!"{cmd} {args}: {o.stderr}")
  pure o.stdout.trimAscii.toString

/-- A package's archive (`NAME-VERSION/` under a tarball) and its sha256. -/
def tarballOf (dir : System.FilePath) (name version : String) (files : List (String × String)) :
    IO (System.FilePath × String) := do
  let work ← mkTree (files.map fun (p, c) => (s!"{name}-{version}/{p}", c))
  let out := dir / s!"{name}-{version}.tar.gz"
  let _ ← runIn work "tar" ["-czf", out.toString, s!"{name}-{version}"]
  let sha := ((← runIn dir "sha256sum" [out.toString]).splitOn " ").head!
  pure (out, sha)

/-- A package directory with an index, a fetched archive and a lock: `greet` 1.2.0,
whose module the app imports. -/
def registryTree : IO (System.FilePath × System.FilePath × String × Toolchain) := do
  let root ← IO.FS.createTempDir
  let idx := root / "index"
  IO.FS.createDirAll idx
  let cache := root / "cache"
  let (tar, sha) ← tarballOf root "greet" "1.2.0"
    [("grail.wiz", "import Grail\ndef package : Package := Package.new \"greet\"\n  |> Package.version \"1.2.0\"\n  |> Package.toolchain \">=0.1.0\"\n  |> Package.lib \"greet\" \"src\"\n"),
     ("src/Greet/Hello.wiz", "import Prelude\ndef hello : Nat := 41\n")]
  IO.FS.writeFile (idx / "greet.sexpr")
    s!"(index (package \"greet\" (version \"1.2.0\" (source \"file://{tar}\") (sha256 \"{sha}\") (toolchain \">=0.1.0\") (deps))))\n"
  let dir ← mkTree [
    ("grail.wiz", s!"import Grail\ndef package : Package := Package.new \"app\"\n  |> Package.set \"index\" \"{idx}\"\n  |> Package.require \"greet\" \"^1\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
    ("app.wiz", "import Greet.Hello\n#eval hello + 1\n")]
  pure (root, dir, sha, { cacheDir := some cache })

/-- Run `grail test` in-process on a package directory. `filters` are the same path
substrings `grail test FILTER` takes (all the tests of the targets if empty), so a case
can run the tests of a name range without copying the package. -/
def runTests (dir : System.FilePath) (tc : Toolchain) (update : Bool := false)
    (testTimeoutMs : Option Nat := none) (filters : List String := []) :
    IO (Array Grail.TestResult × Grail.Stats) := do
  let std : System.FilePath := "lib"
  match ← Grail.readConfig tc 7 std dir with
  | .error e => throw (IO.userError e)
  | .ok (pkg, machine) =>
    let tc ← withSettings tc pkg machine
    let r ← runner dir tc pkg 2 (← IO.mkRef "")
    let r := { r with testTimeoutMs := testTimeoutMs.getD r.testTimeoutMs }
    let res ← r.tests pkg.targets filters update
    pure (res, ← r.stats.get)

def cmdTc : IO Toolchain := do pure { cacheDir := some (← IO.FS.createTempDir) }

def has (log needle : String) : Bool := (log.splitOn needle).length > 1

/-- Empty: the groups register themselves (`Tests/Groups/Grail*.lean`). `Tests/Main.lean`
still concatenates this list until the older modules move to `registerGroup`. -/
def groups : List Group := []

end Tests.Grail
