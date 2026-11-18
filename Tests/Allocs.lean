import Wiz

set_option compiler.extract_closed false

open Wiz

namespace Tests.Allocs

/-- `tests --allocs FILE ENTRY… [--ir NAME…]`: a measuring tool, not a test. Loads FILE
(imports from `lib/` and `drafts/rust/lib/`) and prints, for each ENTRY, the number of
objects the optimised IR allocates computing it on the checked heap (`#run`'s
interpreter). An ENTRY `name : T := e` is appended to the file as a definition first.
With `--ir`, prints the optimised IR of each NAME and of the functions lifted from it. -/
def allocsMain (args : List String) : IO UInt32 := do
  let file :: rest := args | IO.eprintln "usage"; return 2
  let (entries, irs) := match rest.span (· != "--ir") with
    | (e, _ :: i) => (e, i)
    | (e, []) => (e, [])
  let mut m : List (Name × String) := []
  for dir in ["lib", "drafts/rust/lib"] do
    for e in ← System.FilePath.readDir dir do
      if e.path.extension == some "wiz" then
        m := (e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
  let src ← IO.FS.readFile file
  let extra := "\n" ++ String.intercalate "\n" ((entries.filter (·.contains ':')).map fun e =>
    let parts := e.splitOn ":="
    s!"def {parts[0]!.trimAscii} := {parts[1]!.trimAscii}")
  let src := src ++ extra
  let s := runFrontend (R := ZeroOneMany) src { loader := fun n => m.lookup n }
  for msg in s.messages do
    if msg.severity == .error then IO.eprintln (msg.render src)
  for e in entries do
    let n : Name := ((e.splitOn ":=")[0]!.splitOn ":")[0]!.trimAscii.toString
    let r : Except String (RVal × Nat) := do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      let decls ← IR.lowerProgram code (.global n)
      IR.runProgram (decls.map (·.optimize))
    match r with
    | .ok (_, a) => IO.println s!"{n}: {a} allocations"
    | .error err => IO.println s!"{n}: error {err}"
  for n in irs do
    let r : Except String (Array IR.Decl) := do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n)
    match r with
    | .ok ds =>
      for d in ds do
        if d.name.startsWith n then IO.println d.optimize.toString
    | .error err => IO.println s!"{n}: error {err}"
  return 0

end Tests.Allocs
