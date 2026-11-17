import Tests.Groups.SelfHost

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! # `selfhost-macro`: A12, notation and macros in the self-hosted frontend

The forms are counted in `lib/**/*.wiz` (78 files, including `lib/Hdl/`; a declaration
at the start of a line, comments skipped, 2026-11-15 at `24218ce4`):

| form                    | declarations | files |
|-------------------------|-------------:|------:|
| `syntax`                | 123 | 13 |
| `attribute [tactic …]`  |  37 |  5 |
| `macro_rules`           |  27 |  5 |
| `infix` (plain)         |  18 |  4 |
| `infixr`                |  17 |  8 |
| `infixl`                |  13 |  3 |
| `declare_syntax_cat`    |  14 |  3 |
| `attribute [macro …]`   |  11 |  6 |
| `notation`              |   9 |  4 |
| `app_unexpander`        |   6 |  5 |
| `attribute [app_unexpander …]` | 2 | 1 |
| `prefix` / `postfix`    |   0 | 0 (the host has no such commands) |
| `macro` (declaration)   |   0 | 0 (the host has only `macro_rules`) |

17 files use one of these forms (15 without the plain infix operators). By target
category, the `syntax` rules are `tactic` 39, `term` 19, `doSeq` 9, `command` 3,
`exBinder` 2 and 49 Feral DSL categories (`lib/Feral.wiz`).

The self-hosted frontend implements `notation`, `infixl`/`infixr`/`infix`,
`declare_syntax_cat` + `syntax` (with `(name := …)`, priorities, the `stx` item grammar
and the meta parsers), `macro_rules` (quotations, `$x`, hygiene; the host has no
repetition) and command macros written as `macro_rules`. The cases below are
differential: the same source is checked by the Lean frontend (`selfhostSameNats`
compares its `#eval` with the Wiz-hosted `#reduce`) and by the Wiz-hosted one, and a
program is compiled and run by both toolchains.

`attribute [macro …]`/`[tactic …]` register a *function* the host executes at
elaboration time (e.g. `ListLit.expand`, `Ex.binderMacro`, ring reification, Feral);
the self-hosted frontend checks that the function exists and records nothing, because it
has no elaborator-time evaluator yet. That is A12's remaining half, together with
printing (`app_unexpander` is accepted but `#check` still prints kernel terms, not
notation) — see the A12 note in `docs/stages/21-bootstrap.md`. The last cases pin the
difference with `selfhostVerdicts`: the host rejects a function of the wrong type and an
unexpander whose pattern is not an application, while the self-hosted frontend accepts
them.

The cases are differential where both frontends can run the result: `selfhostSameNats`
compares the Lean frontend's `#eval` with the self-hosted `#reduce`, `selfhostAgrees`
compares verdicts, `ioRun`/`selfhostCompileRun` compare a compiled program's output, and
`selfhostCheckFile` pins the self-hosted output. -/

/-- `#check` (and, for the self-hosted frontend, `#reduce`) of macro-generated terms:
same declarations, and `selfhostSameNats` compares what both frontends compute. -/
def macroNotationHeader : String :=
  "def inc (n : Nat) : Nat := n + 1\n" ++
  "notation:max \"⌜\" P \"⌝\" => inc P\n" ++
  "def sub2 (a b : Nat) : Nat := Nat.sub a b\n" ++
  "infixl:65 \" − \" => sub2\n" ++
  "infixr:65 \" ⊖ \" => sub2\n" ++
  "notation:65 a:65 \" ⊕ \" b:66 => Nat.add a b\n" ++
  "def leftA : Nat := 10 − 3 − 2\ndef rightA : Nat := 10 ⊖ 3 ⊖ 2\n" ++
  "def prec : Nat := 1 ⊕ 2 * 3\ndef nested : Nat := ⌜1 + 2⌝\n" ++
  -- a postfix notation: an argument first, so the rule is trailing (the host's
  -- `notationRule`); this used to be a leading rule and overflowed the parser
  "def dbl (n : Nat) : Nat := Nat.mul n 2\n" ++
  "notation:max P \" !\" => dbl P\ndef postfix : Nat := 5 !\n" ++
  -- a prefix notation with an explicit argument precedence (`lib/Prelude.wiz`'s `~~~`
  -- and `!`, `lib/Logic.wiz`'s `¬`)
  "def neg (n : Nat) : Nat := Nat.sub 5 n\n" ++
  "notation:max \"~\" a:max => neg a\ndef prfx : Nat := ~3\n"

/-- A `syntax` rule, a `macro_rules` rule with pattern variables, hygiene, a declared
category with a rule of its own, and a command macro. -/
def macroRulesHeader : String :=
  "syntax:lead (name := unlessE) \"unless \" term \" then \" term \" else \" term : term\n" ++
  "macro_rules\n  | `(term| unless $c then $t else $e) => `(term| match $c with | .true => $e | .false => $t)\n" ++
  "def pick (b : Bool) (x y : Nat) : Nat := unless b then x else y\n" ++
  "syntax:lead (name := underE) \"under \" term : term\n" ++
  "macro_rules\n  | `(term| under $e) => `(term| let y := 3; $e + y)\n" ++
  "def hyg (y : Nat) : Nat := under (y + 1)\n" ++
  "declare_syntax_cat idx\n" ++
  "syntax (name := idxNum) \"⟨\" num \"⟩\" : idx\n" ++
  "syntax:lead (name := getIdx) \"get \" idx : term\n" ++
  "macro_rules\n  | `(term| get $i) => `(term| $i)\n" ++
  "macro_rules\n  | `(idx| ⟨7⟩) => `(term| 70)\n" ++
  "def seven : Nat := get ⟨7⟩\n" ++
  "syntax (name := defOne) \"def_one \" ident : command\n" ++
  "macro_rules\n  | `(command| def_one $x) => `(command| def $x : Nat := 1)\n" ++
  "def_one one\n"

/-- The same program, compiled and run by the Lean toolchain and by the Wiz-hosted one
(`ioRun`/`selfhostCompileRun`): the desugared terms must compute the same output. -/
def macroProgram : String :=
  "import Prelude\nimport IO\n" ++ macroNotationHeader ++ macroRulesHeader ++
  "def main : IO Unit := do\n" ++
  "  IO.println (Nat.toString (leftA + rightA + prec + nested));\n" ++
  "  IO.println (Nat.toString (pick .true 1 2));\n" ++
  "  IO.println (Nat.toString (pick .false 1 2));\n" ++
  "  IO.println (Nat.toString (hyg 5));\n" ++
  "  IO.println (Nat.toString (seven + one))\n"

def macroProgramExpected : String := "25\n2\n1\n9\n71\n"

/-- The macro layer's diagnostics, pinned: a rule must be two quotations, and a syntax
rule needs a declared category. -/
def macroErrors : String :=
  "import Prelude\n" ++
  "macro_rules\n  | 5 => 6\n" ++
  "syntax \"x\" : nope\n" ++
  "attribute [macro term.getIdx] nope\n" ++
  "def a : Nat := 1\n"

def macroErrorsExpected : String :=
  "error: a macro rule is `| `(cat| pattern) => `(cat| template)`\n" ++
  "error: unknown syntax category nope\n" ++
  "error: unknown declaration nope\n" ++
  "a : Nat\n"

/-- A macro file's declarations as the self-hosted frontend prints them. -/
def macroDecls : String :=
  "import Prelude\n" ++ macroNotationHeader ++
  "notation:max \"⟨⟨\" P \"⟩⟩\" => Nat.mul P 2\n" ++
  "def m : Nat := ⟨⟨3⟩⟩\n" ++
  "#check leftA\n#check rightA\n#check prec\n#check nested\n#check m\n"

def macroDeclsExpected : String :=
  "inc : (x0 : Nat) → Nat\n" ++
  "sub2 : (x0 : Nat) → (x1 : Nat) → Nat\n" ++
  "leftA : Nat\nrightA : Nat\nprec : Nat\nnested : Nat\n" ++
  "dbl : (x0 : Nat) → Nat\npostfix : Nat\n" ++
  "neg : (x0 : Nat) → Nat\nprfx : Nat\n" ++
  "m : Nat\nNat\nNat\nNat\nNat\nNat\n"

/-- Printing-notation declarations the host accepts too (`app_unexpander`'s printing
is part of A12's remaining half; the declarations are parsed and checked). -/
def macroPrinting : String :=
  "def f (n : Nat) : Nat := n\n" ++
  "app_unexpander f\n  | `(term| $h $a) => `(term| f $a)\n" ++
  "set_option pp.notation false\n"

/-- `attribute [macro …]`/`[tactic …]` accept a declared function (the host also checks
it has type `Macro`/`Tactic` and runs it; the self-hosted frontend cannot run it yet). -/
def macroRegistrations : String :=
  "import Prelude\n" ++
  "def f (n : Nat) : Nat := n\n" ++
  "attribute [macro term.getIdx] f\n" ++
  "attribute [tactic tactic.xsimpl] f\n" ++
  "def a : Nat := 1\n"

/-- Both frontends accept `src`; unlike `selfhostAgrees`, a self-hosted **parse** error
(the frontend prefixes it `parse`) counts as a rejection. -/
def selfhostAccepts (src : String) : IO Unit := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"the Lean frontend rejects:\n{"\n".intercalate errs.toList}")
  let some out ← selfhostOutput src | return
  let bad := (out.splitOn "\n").find? (fun l => l.startsWith "error" || l.startsWith "parse")
  match bad with
  | some l => throw (IO.userError s!"the self-hosted frontend rejects: {l}\n{out}")
  | none => pure ()

/-- `syntax` rules for the `tactic` category: 39 of `lib/`'s 123 `syntax` rules target
`tactic` (the largest target), and declaring one must work even though `by` is A13. The
last two declarations are the item grammar `lib/` uses: `sepBy(ident, ",")`, `term`, a
`tactic` reference, and a declared category with `(keywords := …)` (accepted; the scope's
words are not tracked, see the stage note). -/
def macroTacticSyntax : String :=
  "syntax (name := xsimplE) \"xsimpl\" : tactic\n" ++
  "syntax (name := xappE) \"xapp\" \"[\" sepBy(ident, \",\") \"]\" term : tactic\n" ++
  "syntax:lead (name := xletE) \"xlet\" ident \":=\" term \";\" tactic : tactic\n" ++
  "declare_syntax_cat hclause (keywords := hkw)\n" ++
  "syntax (name := reqE) \"requires\" \"(\" term \")\" : hclause\n" ++
  "def a : Nat := 1\n"

/-- A `syntax` rule whose items are a `sepBy(term, \",\")` (a `null` node in the tree),
and a macro rule that matches it and splices both elements. -/
def macroSyntaxItems : String :=
  "def add2 (a b : Nat) : Nat := Nat.add a b\n" ++
  "syntax:lead (name := pairE) \"pair\" \"(\" sepBy(term, \",\") \")\" : term\n" ++
  "macro_rules\n  | `(term| pair($a, $b)) => `(term| add2 $a $b)\n" ++
  "def p : Nat := pair(1, 2)\n"

/-- A second `infixl` on a token the Prelude already uses: the host makes a fresh kind
(`term.+_1`) and the later rule wins (`ParserTables` ties go to the declaration later).
Uses `Nat.sub` so the two readings differ (`3 + 1` is 4 with the Prelude's `+`, 2 here). -/
def macroInfixOverride : String :=
  "def sub2 (a b : Nat) : Nat := Nat.sub a b\n" ++
  "infixl:65 \" + \" => sub2\n"

/-- `infix` (neither left nor right) gives both operands `p + 1`, so a chain at the same
precedence does not parse; both frontends reject it. -/
def macroInfixHeader : String :=
  "def same (a b : Nat) : Nat := a\n" ++
  "infix:20 \" ? \" => same\n"

def selfhostMacroGroup : Group where
  name := "selfhost-macro"
  exercise := "Stage 19b; A12"
  cases := [
    { name := "notation, infixl, infixr and precedence desugar as the Lean frontend does (A12)", run := fun _ =>
        selfhostSameNats macroNotationHeader [
          ("10 − 3 − 2", 5), ("10 ⊖ 3 ⊖ 2", 9), ("1 ⊕ 2 * 3", 7), ("⌜1 + 2⌝", 4),
          ("⌜⌜3⌝⌝", 5), ("nested", 4), ("leftA + rightA + prec + nested", 25),
          ("postfix", 10), ("5 ! !", 20), ("~3", 2), ("~ ~3", 3),
          ("leftA + rightA + prec + nested + postfix + prfx", 37)] },
    { name := "macro_rules: pattern variables, hygiene, a declared category and a command macro (A12)", run := fun _ =>
        selfhostSameNats macroRulesHeader [
          ("pick .true 1 2", 2), ("pick .false 1 2", 1),
          ("hyg 5", 9),          -- hygiene: without it a template binder captures `y`
          ("seven", 70), ("one", 1)] },
    { name := "a macro's diagnostics: malformed rules and unknown categories (A12)", run := fun _ =>
        selfhostCheckFile macroErrors macroErrorsExpected },
    { name := "a macro file's declarations in the self-hosted frontend (A12)", run := fun _ =>
        selfhostCheckFile macroDecls macroDeclsExpected },
    { name := "app_unexpander and set_option pp.notation are accepted by both frontends (A12)", run := fun _ =>
        selfhostAccepts ("import Prelude\n" ++ macroPrinting) },
    { name := "attribute [macro] and [tactic] registrations are accepted, their function is not run (A12)", run := fun _ =>
        selfhostCheckFile macroRegistrations "f : (x0 : Nat) → Nat\na : Nat\n" },
    { name := "syntax rules for the `tactic` category and a `(keywords := …)` category are accepted by both frontends (A12)", run := fun _ =>
        selfhostAccepts ("import Prelude\n" ++ macroTacticSyntax) },
    { name := "a `sepBy` syntax item and the macro rule that matches and splices it (A12)", run := fun _ =>
        selfhostSameNats macroSyntaxItems [("p", 3)] },
    { name := "a second `infixl` on the Prelude's `+` gets a fresh kind and the later rule wins, as in the Lean frontend (A12)", run := fun _ =>
        selfhostSameNats macroInfixOverride [("3 + 1", 2)] },
    { name := "`infix` (non-associative) chains do not parse in either frontend (A12)", run := fun _ => do
        -- `selfhostAgrees` counts lines starting with "error" as the self-hosted
        -- frontend's diagnostics; a parse error starts with "parse", so check here.
        let src := "import Prelude\n" ++ macroInfixHeader ++ "#check (1 ? 2 ? 3)\n"
        let loader ← preludeLoader
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
        unless !(s.messages.filter (·.severity == .error)).isEmpty do
          throw (IO.userError "the Lean frontend accepts a non-associative chain:\n1 ? 2 ? 3")
        let some out ← selfhostOutput src | return
        let bad := (out.splitOn "\n").any (fun l => l.startsWith "error" || l.startsWith "parse")
        unless bad do throw (IO.userError s!"the self-hosted frontend accepts a non-associative chain:\n{out}") },
    { name := "A12's remaining half, pinned: a macro/tactic function's type is not checked (the self-hosted frontend cannot run it) (A12)", run := fun _ =>
        selfhostVerdicts "def f (n : Nat) : Nat := n\n" [
          ("attribute [macro term.foo] f", false, true),
          ("attribute [tactic tactic.xsimpl] f", false, true)] },
    { name := "A12's remaining half, pinned: an unexpander's pattern is unchecked (printing is not ported) (A12)", run := fun _ =>
        selfhostVerdicts "def f (n : Nat) : Nat := n\n" [
          ("app_unexpander f\n  | `(term| 5) => `(term| f 0)", false, true)] },
    { name := "macro-generated programs compile and run the same in both toolchains (A12)", run := fun _ => do
        ioRun macroProgram macroProgramExpected
        selfhostCompileRun macroProgram macroProgramExpected }
  ]

builtin_initialize registerGroup selfhostMacroGroup

end Tests.Elab
