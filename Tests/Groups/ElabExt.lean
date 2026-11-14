import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! User-defined term elaborators (`attribute [elab k] f`, stage 6h): a Wiz function
`f : TermElab` (`Syntax → TacticM Unit`) elaborates a term of the syntax kind `k`. The
host makes a hole at the expected type, runs `f` with that hole as its only goal, and
accepts the term only if `f` closes the goal. -/

/-- `twice t` is elaborated by a Wiz function to `2 * t`. (The numeral `2` is built as
the term syntax `2`: `term.num` over a `num` node.) The registration is left to the
caller, so that a test can make it `local`. -/
def twiceDefs : String := "def twoSyntax : Syntax := Syntax.mkNode \"term.num\" (.cons (Syntax.mkNode \"num\" (.cons (.atom \"2\") .nil)) .nil)
syntax (name := twice) \"twice\" term : term
def twiceElab : TermElab := fun stx => do
  g ← TacticM.mainGoal;
  TacticM.exact g (Syntax.mkApp (Syntax.mkVar \"Nat.mul\") (.cons twoSyntax (.cons (Syntax.getArg stx 1) .nil)))
"

def twicePrelude : String := "import Prelude\n" ++ twiceDefs ++
  "attribute [elab term.twice] twiceElab\n"

/-- Run `main` with the modules `mods` importable (`lib/Prelude.wiz` is `Prelude`): every
message as `severity: text`, as `msgsLib` does. -/
def elabExtModules (mods : List (String × String)) (main : String) : IO (Array String) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else (mods.find? (·.1 == m)).map (·.2)
  let s := runFrontend (R := ZeroOneMany) main { loader, trustedModule := Tests.libModule }
  pure (s.messages.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}")

/-- A term elaborator that sees the expected type: `boolOf t` is `t`, but only at `Bool`. -/
def boolOfPrelude : String := "import Prelude
syntax (name := boolOf) \"boolOf\" term : term
def boolOfElab : TermElab := fun stx => do
  g ← TacticM.mainGoal;
  ty ← TacticM.goalType g;
  if Expr.isAppOf \"Bool\" ty then TacticM.exact g (Syntax.getArg stx 1)
  else TacticM.fail \"boolOf: the expected type is not Bool\"
attribute [elab term.boolOf] boolOfElab
"

def elabExtGroup : Group where
  name := "elab-ext"
  exercise := "stage 6: term elaborators written in Wiz"
  cases := [
    -- the elaborator builds `2 * x`, which is elaborated and checked as usual
    { name := "twice: an elaborator builds 2 * x", run := fun _ =>
        okLib (twicePrelude ++ "def k : Nat := twice 21\n#eval k\n#check twice 21") ["42", "42 : Nat"] },
    { name := "the term it assigned is checked by the kernel (#print axioms)", run := fun _ =>
        okLib (twicePrelude ++ "def k : Nat := twice 21\n#print axioms k")
          ["'k' does not depend on any axioms"] },
    -- a typed, dependent example: the element type comes from the expected type
    { name := "a dependent example: List.nil at the expected element type", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := nilOf) \"nilOf\" : term\n" ++
          "def nilOfElab : TermElab := fun _ => do\n  g ← TacticM.mainGoal;\n" ++
          "  TacticM.exact g (Syntax.mkVar \"List.nil\")\n" ++
          "attribute [elab term.nilOf] nilOfElab\n" ++
          "def ns : List Nat := nilOf\n#eval List.length ns\n#check (nilOf : List Bool)")
          ["0", ".nil : List Bool"] },
    -- the expected type is what the Wiz function sees (goalType)
    { name := "the elaborator sees the expected type (boolOf at Bool)", run := fun _ =>
        okLib (boolOfPrelude ++ "def b : Bool := boolOf Bool.true\n#eval b") [".true"] },
    { name := "and rejects the wrong expected type", run := fun _ =>
        failsLib (boolOfPrelude ++ "def n : Nat := boolOf Bool.true")
          "boolOf: the expected type is not Bool" },
    -- a function that fails, and one that leaves the goal open
    { name := "a term elaborator that fails is an error naming it", run := fun _ =>
        failsLib ("import Prelude\nsyntax (name := boom) \"boom\" : term\n" ++
          "def boomElab : TermElab := fun _ => TacticM.fail \"boom: nothing here\"\n" ++
          "attribute [elab term.boom] boomElab\ndef x : Nat := boom")
          "the term elaborator boomElab (for term.boom) failed: boom: nothing here" },
    { name := "a term elaborator that leaves the goal open is rejected", run := fun _ =>
        failsLib ("import Prelude\nsyntax (name := noop) \"noop\" : term\n" ++
          "def noopElab : TermElab := fun _ => TacticM.pure ()\n" ++
          "attribute [elab term.noop] noopElab\ndef x : Nat := noop")
          "the term elaborator noopElab (for term.noop) did not close the goal:\n⊢ Nat" },
    -- the dispatch does not take other syntax kinds
    { name := "a syntax kind with no elaborator falls through to macros and terms", run := fun _ =>
        okLib (twicePrelude ++ "syntax (name := seven) \"seven\" : term\nmacro_rules\n" ++
          "  | `(term| seven) => `(term| 7)\n#eval seven\n#eval 1 + 2") ["7", "3"] },
    -- macro expansion runs before the elaborator (documented order)
    { name := "macro expansion runs before the term elaborator", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := both) \"both!\" : term\nmacro_rules\n" ++
          "  | `(term| both!) => `(term| 9)\n" ++
          "def bothElab : TermElab := fun _ => TacticM.fail \"the elab ran, not the macro\"\n" ++
          "attribute [elab term.both] bothElab\n#eval both!") ["9"] },
    -- the registries are separate: a tactic is not a term elaborator, and vice versa
    { name := "a tactic registered for a term kind is not a term elaborator", run := fun _ =>
        failsLib ("import Prelude\nsyntax (name := foo) \"foo\" : term\n" ++
          "def fooTac : Tactic := fun _ => TacticM.fail \"not a term elaborator\"\n" ++
          "attribute [tactic term.foo] fooTac\ndef x : Nat := foo")
          "the syntax term.foo has no meaning" },
    { name := "a term elaborator registered for a tactic kind is not a tactic", run := fun _ =>
        failsLib ("import Prelude\nsyntax (name := bar) \"bar\" : tactic\n" ++
          "def barElab : TermElab := fun _ => TacticM.pure ()\n" ++
          "attribute [elab tactic.bar] barElab\ndef y : Nat := by bar")
          "the tactic syntax tactic.bar has no meaning" },
    -- registration checks the function's type
    { name := "attribute [elab] rejects a function of the wrong type", run := fun _ =>
        failsLib ("import Prelude\ndef idNat (n : Nat) : Nat := n\n" ++
          "attribute [elab term.idNat] idNat")
          "is not a term elaborator (a `Syntax → TacticM Unit`)" },
    { name := "the long spelling [term_elab] is accepted", run := fun _ =>
        okLib ("import Prelude\n" ++ twiceDefs ++
          "attribute [term_elab term.twice] twiceElab\ndef k : Nat := twice 21\n#eval k") ["42"] },
    -- a registration reaches the modules an import loads, unless it is `local`
    { name := "an elab registration reaches the importer", run := fun _ => do
        let ms ← elabExtModules
          [("ElabDefs", "import Prelude\n" ++ twiceDefs ++ "attribute [elab term.twice] twiceElab\n")]
          "import Prelude\nimport ElabDefs\ndef k : Nat := twice 21\n#eval k"
        checkEq ["info: 42"] ms.toList },
    { name := "a local elab registration ends with its module", run := fun _ => do
        let ms ← elabExtModules
          [("ElabDefs", "import Prelude\n" ++ twiceDefs ++
            "local attribute [elab term.twice] twiceElab\ndef inside : Nat := twice 21\n")]
          "import Prelude\nimport ElabDefs\ndef k : Nat := twice 21"
        let errs := ms.filter (·.startsWith "error:")
        checkEq 1 errs.size
        unless (errs[0]!.splitOn "the syntax term.twice has no meaning").length > 1 do
          throw (IO.userError s!"the local registration was not dropped:\n{errs[0]!}") }
  ]

builtin_initialize registerGroup elabExtGroup

end Tests.Elab
