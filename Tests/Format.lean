import Wiz
import Tests.Harness

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# Tests for `wiz fmt` (11aa)

The formatter is run on fragments with the builtin tables (no library: fast), and its
output is checked: canonical layout, comments kept, and formatting again changes
nothing (idempotence). A refused command keeps its text and says why.
-/

namespace Tests.Format

/-- Format a fragment from the initial state (the builtin grammar only). -/
def fmt (input : String) (width : Nat := 100) : IO String := do
  let r := Fmt.run ({} : CommandState ZeroOneMany) input { width }
  unless r.errors.isEmpty do
    throw (IO.userError s!"parse error: {" ".intercalate r.errors.toList}")
  unless r.refused.isEmpty do
    throw (IO.userError s!"refused: {" ".intercalate r.refused.toList}")
  pure r.text

def formats (input expected : String) : IO Unit := do
  let out ← fmt input
  checkEq expected out

/-- The output, formatted again, is the same. -/
def idempotent (input : String) : IO Unit := do
  let once ← fmt input
  let twice ← fmt once
  checkEq once twice

def group : Group where
  name := "format"
  exercise := "11aa: wiz fmt"
  cases := [
    { name := "spacing is normalised, structure kept",
      run := fun _ => formats "def  id (x : Nat) : Nat :=  x\n" "def id (x : Nat) : Nat := x\n" },
    { name := "a long body breaks after `:=` at 2",
      run := fun _ => formats
        "def f : Nat := Nat.add (Nat.add (Nat.add 1 2) (Nat.add 3 4)) (Nat.add (Nat.add 5 6) (Nat.add 7 8)) Nat.mul\n"
        "def f : Nat :=\n  Nat.add (Nat.add (Nat.add 1 2) (Nat.add 3 4)) (Nat.add (Nat.add 5 6) (Nat.add 7 8)) Nat.mul\n" },
    { name := "match: alternatives at 2, nested at 4",
      run := fun _ => formats
        "def f (b : Bool) : Nat := match b with\n| .true => match b with | .true => 1 | .false => 2\n| .false => 3\n"
        "def f (b : Bool) : Nat := match b with\n  | .true => match b with\n    | .true => 1\n    | .false => 2\n  | .false => 3\n" },
    { name := "inductive: constructors and `deriving` at 2",
      run := fun _ => formats
        "inductive Foo where\n| a\n| b (n : Nat)\nderiving BEq\n"
        "inductive Foo where\n  | a\n  | b (n : Nat)\n  deriving BEq\n" },
    { name := "equations: alternatives at 2",
      run := fun _ => formats
        "def f : Nat → Nat\n| .zero => .zero\n| .succ n => n\n"
        "def f : Nat → Nat\n  | .zero => .zero\n  | .succ n => n\n" },
    { name := "let: a chain, one `let` per line",
      run := fun _ => formats
        "def f : Nat := let x := 1; let y := 2; x\n"
        "def f : Nat :=\n  let x := 1;\n  let y := 2;\n  x\n" },
    { name := "comments: on their own line and trailing",
      run := fun _ => formats
        "-- about f\ndef f : Nat :=\n    let x := 1; -- one\n    -- more\n    x\n"
        "-- about f\ndef f : Nat :=\n  let x := 1; -- one\n  -- more\n  x\n" },
    { name := "comments between commands and blank lines are kept",
      run := fun _ => formats
        "def a : Nat := 1\n\n-- two\ndef b : Nat := 2\n"
        "def a : Nat := 1\n\n-- two\ndef b : Nat := 2\n" },
    { name := "user syntax is formatted from its grammar",
      run := fun _ => formats
        "infixl:10 \" |> \" => f\ndef g (a b : Nat) : Nat := a |> b\n"
        "infixl:10 \" |> \" => f\ndef g (a b : Nat) : Nat := a |> b\n" },
    { name := "idempotent: defs, matches, lets, comments",
      run := fun _ => idempotent
        "-- c\ndef f (b : Bool) : Nat :=\n match b with\n | .true => let x := 1; x\n | .false => 0\n\ninductive T where\n | mk\n" },
    { name := "a fragment that does not parse is reported, not formatted",
      run := fun _ => do
        let r := Fmt.run ({} : CommandState ZeroOneMany) "def (\n" {}
        check (!r.errors.isEmpty) "expected a parse error" },
    { name := "--width changes where lines break, and the result is still idempotent",
      run := fun _ => idempotent
        "def f (a b : Nat) : Nat := Nat.add (Nat.add a b) (Nat.add a b)\n" },
    { name := "a shorter width breaks the body",
      run := fun _ => do
        checkEq "def f (a b : Nat) : Nat :=\n  Nat.add (Nat.add a b) (Nat.add a b)\n"
          (← fmt "def f (a b : Nat) : Nat := Nat.add (Nat.add a b) (Nat.add a b)\n" 40) }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. -/
def groups : List Group := [group]

end Tests.Format
