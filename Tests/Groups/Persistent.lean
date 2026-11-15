import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Persistent maps and sets (`lib/PMap.wiz`): `examples/persistent.wiz` checks
persistence, the BST invariant, sorted `toList`, round trips, a differential test against
`U64Map`, the expected laws, structural sharing, sets and a generic key type, returning 0
when all hold. `examples/persistent-bench.wiz` with no arguments prints the checksums of
its three modes (the persistent tree, `U64Map`'s list model and the native `U64Map`),
which must agree. -/
def persistentGroup : Group where
  name := "persistent"
  exercise := "persistent data structures: lib/PMap.wiz (PMap, PSet), examples/persistent.wiz"
  cases := [
    { name := "the model (#eval) passes every check", run := fun _ => do
        let src ← IO.FS.readFile "examples/persistent.wiz"
        okLibs (src ++ "\n#eval main\n") ["0"] },
    { name := "compiled (C) passes every check", run := fun _ => do
        let src ← IO.FS.readFile "examples/persistent.wiz"
        cRunLibs src "0" },
    { name := "compiled (LLVM) passes every check", run := fun _ => do
        let src ← IO.FS.readFile "examples/persistent.wiz"
        cRunLibs src "0" (llvm := true) },
    { name := "the benchmark: the tree, U64Map's model and the native U64Map agree", run := fun _ => do
        let src ← IO.FS.readFile "examples/persistent-bench.wiz"
        cRunLibs src "86477693 86477693 86477693\n" }
  ]

builtin_initialize registerGroup persistentGroup

end Tests.Elab
