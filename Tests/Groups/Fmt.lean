import Wiz
import Tests.Harness

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# `wiz fmt` gate

A fixed, small corpus that must format idempotently and whose reprint must parse with the
same tables. It runs as `lake test -- '=fmt'` (the `fmt` group). The formatter's own
`--self-test` fixtures (`Wiz/Format.lean`) cover the constructs; this group keeps the
formatter honest on real files, including comments and the layout-sensitive constructs in
the library and the tour.

The files are read from the checkout's `lib/`, `examples/` (Lake runs tests from the
repository root). Each file is formatted twice: the second run must leave the first
reprint exactly as it is, and neither run may refuse a command.
-/

namespace Tests.Fmt

/-- The gate's fixed corpus: small files with different constructs (imports, deriving,
tactics, structures, implicit binders, comments). Hdl files are left out: importing
`Hdl.Core` makes a case take half a minute, which is not a fast gate. -/
def corpus : List String := [
  "lib/Logic.wiz",
  "lib/Text.wiz",
  "lib/Vec.wiz",
  "examples/tactics.wiz",
  "examples/tour/03-structures.wiz",
  "examples/tour/06-proofs.wiz"
]

/-- The frontend state for `path`: the toolchain's `lib/` and the file's own directory as
module roots, so imports and `syntax` declarations are the ones the file really sees. -/
def initial (path : String) (src : String) : IO (CommandState ZeroOneMany) := do
  let root := (System.FilePath.mk path).parent.getD "."
  let mods ← Module.loadClosure ["lib", root] src
  pure { loader := fun m => (mods[m]?).map (·.2), trustedModule := Tests.libModule }

def fail (path what : String) (why : Array String) : IO Unit :=
  throw (IO.userError s!"{path}: {what}: {" ".intercalate why.toList}")

/-- Format `path`; the reprint must parse and be a fixed point. -/
def checkFile (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  let once := Fmt.run (← initial path src) src {}
  unless once.errors.isEmpty do fail path "the file does not parse" once.errors
  unless once.refused.isEmpty do fail path "a command was refused" once.refused
  let twice := Fmt.run (← initial path once.text) once.text {}
  unless twice.errors.isEmpty do fail path "the reprint does not parse" twice.errors
  unless twice.refused.isEmpty do fail path "the reprint has a refused command" twice.refused
  checkEq once.text twice.text

def group : Group where
  name := "fmt"
  exercise := "11aa: wiz fmt gate (idempotence and reparse)"
  cases := corpus.map fun path => { name := path, run := fun _ => checkFile path }

builtin_initialize registerGroup group

end Tests.Fmt
