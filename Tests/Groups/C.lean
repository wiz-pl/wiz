import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (15k) A program large enough to split by hand: 64 definitions whose calls cross
translation-unit boundaries. -/
def splitSrc : String :=
  "import Prelude\n" ++
  String.join ((List.range 64).map fun i => s!"def sf{i} : Nat := {i} * 3\n") ++
  "\ndef main : Nat := " ++
  String.intercalate " + " ((List.range 64).map fun i => s!"sf{i}") ++ "\n"

/-- (15k) The same program compiled as four C units (the split path): the result and the
generated code must be the single-unit ones. -/
def splitCase : Case :=
  { name := "a C program in four translation units", run := fun _ => cRun splitSrc "6048" false 4 }

def cGroup : Group where
  name := "c"
  exercise := "Exercise 8.2"
  cases := nativeCases false ++ [splitCase]

builtin_initialize registerGroup cGroup

end Tests.Elab
