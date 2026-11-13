import Grail.Elab

/-!
# Build files

`grail.wiz` is a Wiz file that imports `Grail` (`lib/Grail.wiz`) and defines
`package : Package`; the uncommitted `grail.local.wiz` may define `settings : Settings`
(this machine's compiler flags). grail elaborates the file, evaluates
`Package.render package` (an S-expression) in the interpreter, and reads it back.
-/

namespace Grail
open Wiz

/-- (23i) What a command runs: a program found on `PATH` (or a path), or an `exe` target. -/
inductive Tool where
  | path (name : String)
  | exe (target : String)
  deriving Repr, Inhabited, BEq

/-- A piece of an argument. -/
inductive Part where
  | text (s : String)
  | input (path : String)
  | output (path : String)
  deriving Repr, Inhabited, BEq

/-- A command target (23i), its steps folded. -/
structure Command where
  name : String
  tool : Tool
  args : List (List Part) := []
  /-- every declared input, in order (argument inputs too) -/
  inputs : List String := []
  /-- declared output files and directories (`true`: a directory) -/
  outputs : List (String × Bool) := []
  stdout : Option String := none
  env : List (String × String) := []
  inOutDir : Bool := false
  uses : List Tool := []
  phony : Bool := false
  manual : Bool := false
  deriving Repr, Inhabited, BEq

def Command.outputPaths (c : Command) : List String :=
  c.outputs.map (·.1) ++ c.stdout.toList

inductive Target where
  | lib (name : String) (root : String)
  | check (name : String) (file : String)
  | exe (name : String) (file : String)
  /-- every `.wiz` file under a directory is a test, its expected output beside it -/
  | tests (name : String) (root : String)
  /-- the self-hosted toolchain: `checker`, `compiler`, or the `bootstrap` check -/
  | selfhost (name : String) (role : String)
  /-- an external command with declared inputs and outputs (23i) -/
  | command (c : Command)
  deriving Repr, Inhabited, BEq

def Target.name : Target → String
  | .lib n _ | .check n _ | .exe n _ | .tests n _ | .selfhost n _ => n
  | .command c => c.name

/-- Built by `grail build` without naming it? Not the bootstrap check (it takes minutes),
nor phony or manual commands. -/
def Target.isDefault : Target → Bool
  | .selfhost _ "bootstrap" => false
  | .command c => !c.phony && !c.manual
  | _ => true

/-- A package from git (stage 23h, `Grail/Deps.lean`) -/
structure Dep where
  name : String
  url : String
  rev : String
  deriving Repr, Inhabited, BEq

/-- (23m) A package from the registry: its name and version requirement -/
structure Req where
  name : String
  req : String
  deriving Repr, Inhabited, BEq

structure Package where
  name : String
  targets : List Target
  settings : List (String × String)
  deps : List Dep := []
  /-- (23m) this package's version ("" when it has none) -/
  version : String := ""
  /-- (23m) the toolchain it was tested with (a version requirement) -/
  toolchain : String := ""
  /-- (23m) registry dependencies -/
  requires : List Req := []
  deriving Repr, Inhabited

open Cache in
def decodeSettings (x : Sx) : Except String (List (String × String)) := do
  let some xs := items? x | throw "settings: expected a list"
  xs.toList.drop 1 |>.mapM fun
    | .l #[.a "set", .a k, .a v] => pure (k, v)
    | _ => throw "settings: expected (set key value)"

open Cache in
def decodeTool : Sx → Except String Tool
  | .l #[.a "path", .a n] => pure (.path n)
  | .l #[.a "exe", .a n] => pure (.exe n)
  | t => throw s!"bad tool {t.render}"

open Cache in
def decodeCommand (name : String) (tool : Sx) (steps : Sx) : Except String Command := do
  let some ss := items? steps | throw "command: expected a list of steps"
  let mut c : Command := { name, tool := ← decodeTool tool }
  let addOut (c : Command) (p : String) (dir : Bool) : Command :=
    if c.outputs.any (·.1 == p) then c else { c with outputs := c.outputs ++ [(p, dir)] }
  let addIn (c : Command) (p : String) : Command :=
    if c.inputs.contains p then c else { c with inputs := c.inputs ++ [p] }
  for st in ss.toList.drop 1 do
    match st with
    | .l #[.a "arg", ps] =>
      let some ps := items? ps | throw "arg: expected a list of parts"
      let parts ← ps.toList.drop 1 |>.mapM fun
        | .l #[.a "text", .a s] => pure (Part.text s)
        | .l #[.a "in", .a p] => pure (.input p)
        | .l #[.a "out", .a p] => pure (.output p)
        | x => throw s!"bad argument part {x.render}"
      c := { c with args := c.args ++ [parts] }
      for p in parts do
        match p with
        | .input f => c := addIn c f
        | .output f => c := addOut c f false
        | .text _ => pure ()
    | .l #[.a "input", .a p] => c := addIn c p
    | .l #[.a "output", .a p] => c := addOut c p false
    | .l #[.a "dir", .a p] =>
      -- (an output part of the same path, before or after, names the directory)
      c := if c.outputs.any (·.1 == p) then { c with outputs := c.outputs.map fun (q, d) => (q, d || q == p) }
        else addOut c p true
    | .l #[.a "stdout", .a p] => c := { c with stdout := some p }
    | .l #[.a "env", .a k, .a v] => c := { c with env := c.env ++ [(k, v)] }
    | .l #[.a "in-out-dir"] => c := { c with inOutDir := true }
    | .l #[.a "uses", t] => c := { c with uses := c.uses ++ [← decodeTool t] }
    | .l #[.a "phony"] => c := { c with phony := true }
    | .l #[.a "manual"] => c := { c with manual := true }
    | x => throw s!"command {name}: unknown step {x.render}"
  if c.phony && !c.outputPaths.isEmpty then
    throw s!"command {name}: a phony command has no outputs (it is never recorded)"
  pure c

open Cache in
def decodePackage (x : Sx) : Except String Package := do
  -- (23m) the last three fields (version, toolchain, requires) are optional, so a
  -- manifest written for an older grail still decodes
  let .l xs := x | throw "expected (package name targets settings deps)"
  let (name, ts, ss, ds, extra) ← match xs with
    | #[.a "package", .a name, ts, ss, ds] => pure (name, ts, ss, ds, #[])
    | #[.a "package", .a name, ts, ss, ds, v, tc, rs] => pure (name, ts, ss, ds, #[v, tc, rs])
    | _ => throw "expected (package name targets settings deps [version toolchain requires])"
  let some ts := items? ts | throw "targets: expected a list"
  let targets ← ts.toList.drop 1 |>.mapM fun
    | .l #[.a "lib", .a n, .a r] => pure (Target.lib n r)
    | .l #[.a "check", .a n, .a f] => pure (.check n f)
    | .l #[.a "exe", .a n, .a f] => pure (.exe n f)
    | .l #[.a "tests", .a n, .a r] => pure (.tests n r)
    | .l #[.a "selfhost", .a n, .a r] => pure (.selfhost n r)
    | .l #[.a "command", .a n, tool, steps] => return .command (← decodeCommand n tool steps)
    | t => throw s!"unknown target {t.render}"
  -- (23i) one target per name: `grail build NAME` names one thing
  let mut seen : List String := []
  for t in targets do
    if seen.contains t.name then throw s!"two targets are called {t.name}"
    seen := t.name :: seen
  let some ds := items? ds | throw "deps: expected a list"
  let deps ← ds.toList.drop 1 |>.mapM fun
    | .l #[.a "dep", .a name, .a url, .a rev] => pure { name, url, rev : Dep }
    | d => throw s!"bad dependency {d.render}"
  let (version, toolchain, requires) ← match extra with
    | #[] => pure ("", "", [])
    | #[.a v, .a tc, rs] =>
      let some rs := items? rs | throw "requires: expected a list"
      let requires ← rs.toList.drop 1 |>.mapM fun
        | .l #[.a "require", .a n, .a r] => pure { name := n, req := r : Req }
        | r => throw s!"bad requirement {r.render}"
      pure (v, tc, requires)
    | _ => throw "expected (package name targets settings deps version toolchain requires)"
  pure { name, targets, settings := ← decodeSettings ss, deps, version, toolchain, requires }

/-- Evaluate `expr` (a `String`) in the build file `path`. -/
def evalBuildFile (tc : Toolchain) (salt : UInt64) (roots : List System.FilePath) (path : System.FilePath)
    (expr : String) : IO (Except String Cache.Sx) := do
  let src := (← IO.FS.readFile path) ++ s!"\ndef grailOut : String := {expr}\n"
  let l ← load tc roots salt src (path.parent.getD ".")
  let s ← elaborate tc salt l
  if hasErrors s then return .error (render path.toString l s)
  match evalString s "grailOut" with
  | .error e => pure (.error s!"{path}: {e}")
  | .ok str => match Cache.Sx.parse str with
    | some x => pure (.ok x)
    | none => pure (.error s!"{path}: could not read {str}")

/-- Read `grail.wiz` (and `grail.local.wiz`, if there is one) in `dir`. -/
def readConfig (tc : Toolchain) (salt : UInt64) (std dir : System.FilePath) :
    IO (Except String (Package × List (String × String))) := do
  let roots := [std, dir]
  let file := dir / "grail.wiz"
  unless ← file.pathExists do return .error s!"no {file}"
  let pkg ← match ← evalBuildFile tc salt roots file "Package.render package" with
    | .error e => return .error e
    | .ok x => match decodePackage x with
      | .error e => return .error s!"{file}: {e}"
      | .ok p => pure p
  let localFile := dir / "grail.local.wiz"
  if !(← localFile.pathExists) then return .ok (pkg, [])
  match ← evalBuildFile tc salt roots localFile "Settings.render settings" with
  | .error e => pure (.error e)
  | .ok x => match decodeSettings x with
    | .error e => pure (.error s!"{localFile}: {e}")
    | .ok ss => pure (.ok (pkg, ss))

end Grail
