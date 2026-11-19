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

/-- `--check`'s two answers: an unformatted input is changed, and a formatted one is
left exactly as it is (which is what makes the driver exit 0). -/
def checkMode (unformatted formatted : String) : IO Unit := do
  formats unformatted formatted
  check (formatted != unformatted) "the input should have needed formatting"
  formats formatted formatted

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
    { name := "mutual: members at 2 and `end` at 0",
      run := fun _ => formats
        "mutual\npartial def even : Nat → Bool\n| .zero => .true\n| .succ n => odd n\npartial def odd : Nat → Bool\n| .zero => .false\n| .succ n => even n\nend\n"
        "mutual\n  partial def even : Nat → Bool\n    | .zero => .true\n    | .succ n => odd n\n  partial def odd : Nat → Bool\n    | .zero => .false\n    | .succ n => even n\nend\n" },
    { name := "let: a chain, one `let` per line",
      run := fun _ => formats
        "def f : Nat := let x := 1; let y := 2; x\n"
        "def f : Nat :=\n  let x := 1;\n  let y := 2;\n  x\n" },
    { name := "let: the body starts a line even without a `;`",
      run := fun _ => do
        let input := "def bind (x : Nat) (g : Nat → Nat) : Nat := fun s =>\n  let r := x\n  g r\n"
        let expected := "def bind (x : Nat) (g : Nat → Nat) : Nat :=\n  fun s =>\n    let r := x\n    g r\n"
        formats input expected
        idempotent input },
    { name := "let: a parenthesised match as the value is idempotent",
      run := fun _ => idempotent
        "inductive T where\n  | a\n  | b\n\ndef f (t : T) : Nat :=\n  match t with\n  | .a => 0\n  | .b =>\n    let x := (match t with\n      | .a => 1\n      | .b => 2);\n    x\n" },
    { name := "comments: a trailing comment does not leave a blank line",
      run := fun _ => formats
        "def f (x : Nat) : Nat :=\n  -- before let\n  let y := x -- after value\n  -- before body\n  y -- after body\n"
        "def f (x : Nat) : Nat :=\n  -- before let\n  let y := x -- after value\n  -- before body\n  y -- after body\n" },
    { name := "comments: match and tactic comments stay with their construct",
      run := fun _ => do
        let input := "def h (b : Bool) : Nat :=\n  match b with\n  | .true => 1 -- true\n  | .false => 2 -- false\n"
        idempotent input
        let out ← fmt input
        check (out.contains "-- true" && out.contains "-- false") "a trailing comment was lost" },
    { name := "strings keep comment markers and escapes",
      run := fun _ => formats
        "def s : String := \"a -- not a comment /- nor this -/ b\\n\"\n"
        "def s : String := \"a -- not a comment /- nor this -/ b\\n\"\n" },
    { name := "attributes, implicit binders and long applications are kept",
      run := fun _ => do
        idempotent
          "def f : Nat := 1\nattribute [inline] f\ndef im {α : Type} [Inhabited α] (x : α) : α := x\ndef long : Nat := Nat.add (Nat.add (Nat.add 1 2) (Nat.add 3 4)) (Nat.add (Nat.add 5 6) (Nat.add 7 8))\n" },
    { name := "--self-test fixtures are idempotent and keep their comments",
      run := fun _ => do
        let bad := Fmt.selfTest
        check bad.isEmpty (" ".intercalate bad.toList) },
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
          (← fmt "def f (a b : Nat) : Nat := Nat.add (Nat.add a b) (Nat.add a b)\n" 40) },
    { name := "calc at Nat: steps line up under the first relation",
      run := fun _ => do
        let input := "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\ndef t (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=\n    calc a ≤ b := h1\n         _ < c := h2\n         _ = d := h3\n"
        let expected := "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\ndef t (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=\n  calc a ≤ b := h1\n       _ < c := h2\n       _ = d := h3\n"
        formats input expected
        idempotent input },
    { name := "calc at Int: a named hypothesis and a longer chain",
      run := fun _ => do
        let input := "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\n\ndef t (a b c d : Int) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=\n  calc a ≤ b := h1\n       _ < c := h2\n       _ = d := h3\n\ndef u (n : Int) (h : n ≤ n) : n ≤ n :=\n    calc n ≤ n := h\n         _ ≤ n := h\n"
        let expected := "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\n\ndef t (a b c d : Int) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=\n  calc a ≤ b := h1\n       _ < c := h2\n       _ = d := h3\n\ndef u (n : Int) (h : n ≤ n) : n ≤ n :=\n  calc n ≤ n := h\n       _ ≤ n := h\n"
        formats input expected
        idempotent input },
    { name := "calc nested in a `by` block: steps align under its own first relation",
      run := fun _ => do
        let input := "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\nsyntax \"exact\" term : tactic\n\ndef t (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d := by\n  exact calc a ≤ b := h1\n             _ < c := h2\n             _ = d := h3\n"
        let expected := "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\nsyntax \"exact\" term : tactic\n\ndef t (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=\n  by\n  exact calc a ≤ b := h1\n             _ < c := h2\n             _ = d := h3\n"
        formats input expected
        idempotent input },
    { name := "calc keeps comments: before the block, between steps, and trailing",
      run := fun _ => do
        let input := "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\n\ndef t (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=\n    -- the chain\n    calc a ≤ b := h1 -- first\n         -- middle\n         _ < c := h2\n         _ = d := h3 -- last\n"
        let expected := "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\n\ndef t (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=\n  -- the chain\n  calc a ≤ b := h1 -- first\n       -- middle\n       _ < c := h2\n       _ = d := h3 -- last\n"
        formats input expected
        idempotent input },
    { name := "--check: a formatted calc is unchanged, an unformatted one differs",
      run := fun _ => checkMode
        "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\ndef t (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a < c :=\n    calc a ≤ b := h1\n         _ < c := h2\n"
        "infix:50 \" ≤ \" => Nat.le\ninfix:50 \" < \" => Nat.lt\ndef t (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a < c :=\n  calc a ≤ b := h1\n       _ < c := h2\n" }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. -/
def groups : List Group := [group]

end Tests.Format
