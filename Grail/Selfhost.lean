import Grail.Build

/-!
# The self-hosted toolchain as targets (stage 23e)

`selfhost NAME ROLE` targets build the self-hosted programs from `selfhost/*.wiz`:

* `checker`: the self-hosted frontend (reads `input.wiz`, prints what it makes of it);
* `compiler`: the frontend and backend (reads `input.wiz`, prints C);
* `bootstrap`: the fixpoint check of `scripts/fixpoint.sh`, in its mode (`bootstrapMode`,
  reference counting). Stage 1 (the compiler, built by the Lean `wiz`) compiles the
  toolchain to C (`self1.c`); that C, compiled with `selfhost/rt.c` (no collector), is
  stage 2, which compiles the toolchain again (`self2.c`). The two must be equal, and
  stage 2 must free every object.

Each step is a job (`Grail/Graph.lean`): the generated source (keyed by the
`selfhost/*.wiz` texts — the tables are `selfhost/Tables.wiz`, so this binary only names
them — installed as `.grail/gen/ROLE.wiz`), then the executable as for any `exe`, then
`self1.c` (keyed by the stage-1 binary, its input and the mode), stage 2 (by `self1.c`,
`rt.c` and the compiler) and `self2.c`. Run again, the check runs nothing
unless something it depends on changed.
-/

namespace Grail
open Wiz

/-- The program for `role` (`checker` or `compiler`), and the toolchain as an input
(`self.wiz`). -/
def Runner.selfhostSources (r : Runner) (role : String) : IO (String × String) := do
  let files := if role == "checker" then Selfhost.checkerFiles else Selfhost.compilerFiles
  let srcs ← files.mapM fun (f : String) => IO.FS.readFile (r.ctx.dir / f)
  let prog := if role == "checker" then Selfhost.checkerSource srcs else Selfhost.compilerSource srcs
  pure (prog, Selfhost.selfSource srcs)

/-- Where the generated program for `role` is installed, relative to the package. -/
def genFile (role : String) : String := s!".grail/gen/{role}.wiz"
def genSelf (role : String) : String := s!".grail/gen/{role}-self.wiz"

/-- The backend mode of the `bootstrap` target's stages: reference counting, as
`scripts/fixpoint.sh` (since R1) and the release. -/
def bootstrapMode : String := "--rc"

/-- Run `exe` with `args` in a fresh directory with `input` as `input.wiz`; its output
goes to `file`. -/
def runOn (exe : System.FilePath) (input : String) (out : System.FilePath) (file : String)
    (args : Array String := #[]) : IO (Except String Unit) := do
  let exe ← IO.FS.realPath exe  -- it runs in another directory
  let work := out / "work"
  IO.FS.createDirAll work
  IO.FS.writeFile (work / "input.wiz") input
  let o ← IO.Process.output { cmd := exe.toString, args := args, cwd := work }
  IO.FS.removeDirAll work
  if o.exitCode != 0 then return .error s!"{exe} failed ({o.exitCode}): {o.stderr.take 2000}"
  IO.FS.writeFile (out / file) o.stdout
  pure (.ok ())

/-- The first line where stage 1's and stage 2's C differ. -/
def firstDiff (a b : String) : String := Id.run do
  let as := a.splitOn "\n"
  let bs := b.splitOn "\n"
  for i in [0:max as.length bs.length] do
    if as[i]? != bs[i]? then
      return s!"line {i + 1}: stage 1 {(as[i]?.getD "<end>").take 200} / stage 2 {(bs[i]?.getD "<end>").take 200}"
  pure "(equal)"

end Grail
