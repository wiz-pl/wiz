import Grail.Config

/-!
# Jobs (stages 23d, 23g)

A **job** has a key, computed from its inputs before it runs, and an output directory
`.grail/build/<key>/`. A job whose directory exists is up to date and doesn't run; a job
that runs writes into a temporary directory that is renamed into place when it
succeeds, so an interrupted build leaves nothing half-written. Keys:

* `check F`: the file's key (`Cache.moduleKey`: its text, headers, and its imports'
  keys, transitively), mixed with `binId` (this grail binary: elaborator and backends);
* `build F` from `check F`'s key: one job that checks `F` and writes its IR, C and
  link text (elaborating it once, not once per job); `ir F` is the same C job for a
  file that is already checked as a package module;
* `obj F` from the text of `main.c` and the compiler and `cflags`;
* `link E` from `obj F` and the compiler and `ldflags`, and (9f) the `link_c` files (their
  paths and contents: the link compiles them, with `cflags`) and `link_lib` libraries,
  which `c F` lists in `link.txt`.

So editing a module reruns the checks of the files that import it, and an edit that
doesn't change the generated C stops at `obj`. The jobs form a graph (`Grail/Graph.lean`)
whose ready jobs run as separate processes, up to `-j N` at a time.
-/

namespace Grail
open Wiz

structure Ctx where
  /-- the package directory -/
  dir : System.FilePath
  /-- the standard library (`lib/`) -/
  std : System.FilePath
  tc : Toolchain
  /-- identifies this grail binary -/
  binId : UInt64
  /-- the roots of the package's `lib` targets: their modules can be imported -/
  libRoots : List System.FilePath := []

def Ctx.roots (c : Ctx) : List System.FilePath := [c.std, c.dir] ++ c.libRoots ++ c.tc.searchPath

def libRootsOf (dir : System.FilePath) (ts : List Target) : List System.FilePath :=
  ts.filterMap fun | .lib _ r => some (dir / r) | _ => none
def Ctx.grailDir (c : Ctx) : System.FilePath := c.dir / ".grail"

structure Stats where
  ran : Nat := 0
  upToDate : Nat := 0
  failed : Nat := 0
  /-- not run because a job they depend on failed -/
  skipped : Nat := 0

def hex (k : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 k.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- A file's elaborated state and its loaded form, made at most once per run. -/
structure Memo where
  loaded : Std.HashMap String Loaded := {}
  states : Std.HashMap String (CommandState ZeroOneMany) := {}
  /-- (23i) a command's program by name: the path it runs by, and its identity -/
  tools : Std.HashMap String (Except String (String × String)) := {}

structure Runner where
  ctx : Ctx
  stats : IO.Ref Stats
  memo : IO.Ref Memo
  /-- where the build's report goes (stdout and stderr), in a fixed order -/
  out : String → IO Unit := IO.print
  err : String → IO Unit := IO.eprint
  /-- how many jobs run at once -/
  jobs : Nat := 1
  /-- the program that runs a job (`<self> --grail-job …`): grail, or the test driver -/
  self : System.FilePath := "grail"
  /-- a job's time limit, in milliseconds; tests have their own -/
  timeoutMs : Nat := 1800000
  testTimeoutMs : Nat := 300000

def Runner.load (r : Runner) (file : String) : IO Loaded := do
  if let some l := (← r.memo.get).loaded[file]? then return l
  let path := r.ctx.dir / file
  let l ← Grail.load r.ctx.tc r.ctx.roots r.ctx.binId (← IO.FS.readFile path) (path.parent.getD r.ctx.dir)
  r.memo.modify fun m => { m with loaded := m.loaded.insert file l }
  pure l

def Runner.elab (r : Runner) (file : String) : IO (CommandState ZeroOneMany) := do
  if let some s := (← r.memo.get).states[file]? then return s
  let s ← elaborate r.ctx.tc r.ctx.binId (← r.load file)
  r.memo.modify fun m => { m with states := m.states.insert file s }
  pure s

/-- The key of `check F`. -/
def Runner.checkKey (r : Runner) (file : String) : IO UInt64 := do
  pure (mixHash (hash "check") (mixHash r.ctx.binId (← r.load file).key))

/-- `main`'s IR, and whether it is an `IO` program. -/
def mainDecls (s : CommandState ZeroOneMany) : Except String (Array IR.Decl × Bool) := do
  let (ds, ty) ← Build.irProgram s "main"
  pure (ds, Build.isIO ty)

def run (cmd : String) (args : Array String) : IO (Except String Unit) := do
  try
    let o ← IO.Process.output { cmd, args }
    pure (if o.exitCode == 0 then .ok () else .error s!"{cmd} failed:\n{o.stderr}")
  catch e => pure (.error s!"{cmd}: {e}")

/-- Copy a file if its content differs. -/
def install (src dst : System.FilePath) : IO Unit := do
  let new ← IO.FS.readBinFile src
  if ← dst.pathExists then
    if (← IO.FS.readBinFile dst) == new then return
  if let some d := dst.parent then IO.FS.createDirAll d
  let tmp := dst.toString ++ s!".tmp{← IO.Process.getPID}"
  IO.FS.writeBinFile tmp new
  IO.setAccessRights tmp { user := { read := true, write := true, execution := true },
                           group := { read := true, execution := true }, other := { read := true, execution := true } }
  IO.FS.rename tmp dst

end Grail
