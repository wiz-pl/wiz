import Tests.Elab

open Wiz

/-!
# 11ad: `ward`, the linter

`wiz lint`'s checks (`Wiz.Lint`) are properties of the text and of the info tree, so a
case gives the source (and the modules it imports) and reads the findings back. The
last three cases run the built `wiz` binary: the exit status with and without `--deny`,
the JSON document, and standard input.
-/

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Ward

abbrev R := ZeroOneMany

/-- Lint `src` as a file that imports `Prelude` and `mods` (`module → source`). -/
def lint (src : String) (mods : List (String × String) := []) (opts : Lint.Options := {}) :
    IO (Array Lint.Diag) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let init : CommandState R :=
    { trustedModule := Tests.libModule, termInfo := true,
      loader := fun m => if m == "Prelude" then some prelude else mods.lookup m }
  let s := runFrontend src init
  pure (Lint.run opts src s)

def warnings (ds : Array Lint.Diag) : Array Lint.Diag := ds.filter (·.severity == .warning)

def rules (ds : Array Lint.Diag) : List String := (warnings ds).toList.map (·.rule)

/-- The findings of `rule`, in order. -/
def of (ds : Array Lint.Diag) (rule : String) : Array Lint.Diag :=
  (warnings ds).filter (·.rule == rule)

def has (ms : Array String) (frag : String) : Bool := ms.any fun m => (m.splitOn frag).length > 1

def messages (ds : Array Lint.Diag) : Array String := (warnings ds).map (·.message)

/-- `wiz`'s path, as `Tests/Doc.lean` has it. -/
def wiz : IO String := do pure (← IO.FS.realPath ".lake/build/bin/wiz").toString

structure Run where
  code : UInt32
  out : String
  err : String

def runLint (args : List String) : IO Run := do
  let o ← IO.Process.output { cmd := ← wiz, args := args.toArray }
  pure { code := o.exitCode, out := o.stdout, err := o.stderr }

def wardGroup : Group where
  name := "ward"
  parallel := true
  exercise := "Stage 11ad"
  cases := [
    { name := "a clean file has no findings", run := fun _ => do
        let src := "import Prelude\n\ndef double (n : Nat) : Nat := n + n\n\ndef four : Nat := double 2\n"
        let ds ← lint src
        check ds.isEmpty s!"findings: {ds.toList.map (·.rule)}" },

    { name := "style: tabs, trailing whitespace, CRLF, long lines", run := fun _ => do
        let src := "import Prelude\n\ndef a : Nat :=\t1   \ndef b : Nat := 1\r\n" ++
          "def c : Nat := 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1\n"
        let ds ← lint src (opts := { maxLine := 40 })
        checkEq ["style.tabs", "style.trailing-whitespace", "style.crlf", "style.line-length"] (rules ds)
        -- a tab is not also trailing whitespace; CRLF is reported once
        checkEq 4 ds.size
        checkEq 1 (of ds "style.crlf").size
        -- --max-line 0 turns the length rule off
        check ((rules (← lint src (opts := { maxLine := 0 }))).filter (· == "style.line-length")).isEmpty
          "--max-line 0 still reports a long line" },

    { name := "sorry and axiom declarations are warnings", run := fun _ => do
        let src := "import Prelude\n\naxiom cheat : Nat\n\ndef bad : Nat := sorry\n"
        let ds ← lint src
        checkEq ["axiom", "sorry"] (rules ds)
        check (has (messages ds) "'cheat' is an axiom") s!"{messages ds}"
        check (has (messages ds) "'sorry' is not checked") s!"{messages ds}"
        -- the elaborator's own error is there too (Wiz has no sorry), and counts as one
        check (ds.any fun d => d.severity == .error && d.rule == "unknown-identifier") "no error at `sorry`" },

    { name := "a comment or string that says sorry is not a finding", run := fun _ => do
        let src := "import Prelude\n\n-- sorry in a comment\n/-\n  sorry, nested /- sorry -/\n-/\ndef s : String := \"sorry\"\n"
        check (rules (← lint src)).isEmpty s!"{rules (← lint src)}" },

    { name := "shadowed binders: an enclosing binder and a visible global", run := fun _ => do
        let src := "import Prelude\n\n" ++
          "def f (n : Nat) : Nat :=\n  let n := n\n  n\n\n" ++
          "def g (pipe : Nat) : Nat := pipe\n\n" ++
          "def h (x : Nat) : Nat := fun (x : Nat) => x\n\n" ++
          "def k (n : Nat) : Nat := n\n"
        let ds ← lint src
        checkEq ["shadowed-binder", "shadowed-binder", "shadowed-binder"] (rules ds)
        check (has (messages ds) "binder 'n' shadows an enclosing binder") s!"{messages ds}"
        check (has (messages ds) "binder 'pipe' shadows the global 'pipe'") s!"{messages ds}"
        check (has (messages ds) "binder 'x' shadows an enclosing binder") s!"{messages ds}" },

    { name := "inside a match alternative nothing is guessed (the branch context is shared)", run := fun _ => do
        let src := "import Prelude\n\ninductive T where\n  | a\n  | b (n : Nat)\n\n" ++
          "def f (t : T) (n : Nat) : Nat := match t with\n  | .a => n\n  | .b n => n\n\n" ++
          "def g (t : T) (n : Nat) : Nat := match t with\n  | n => n\n"
        let ds ← lint src
        -- the pattern variables are not checked, and the branch context's `n`s (the
        -- field's, the earlier alternative's) do not leak into warnings
        check (rules ds).isEmpty s!"{rules ds}" },

    { name := "a binder named like the declaration being made is not a shadow", run := fun _ => do
        let src := "import Prelude\n\ndef f (f : Nat) : Nat := f\n"
        check (rules (← lint src)).isEmpty s!"{rules (← lint src)}" },

    { name := "unused imports and a duplicate import", run := fun _ => do
        let a := "import Prelude\ndef fromA : Nat := 7\n"
        let b := "import Prelude\ndef fromB : Nat := 8\n"
        let src := "import Prelude\nimport M.A\nimport M.B\n\ndef x : Nat := fromA\n"
        let ds ← lint src [("M.A", a), ("M.B", b)]
        checkEq ["unused-import"] (rules ds)
        check (has (messages ds) "module M.B is imported but nothing") s!"{messages ds}"
        -- the same module twice: a duplicate (the first is the one reported unused)
        let ds ← lint "import Prelude\nimport M.A\nimport M.A\ndef x : Nat := 1\n" [("M.A", a)]
        checkEq ["unused-import", "duplicate-import"] (rules ds) },

    { name := "an import that only brings another module's name is kept", run := fun _ => do
        let a := "import Prelude\ndef fromA : Nat := 7\n"
        let b := "import Prelude\nimport M.A\ndef fromB : Nat := fromA\n"
        -- `fromA` is M.A's, but M.B is the only import that brings it (imports are
        -- transitive), so M.B is needed
        let ds ← lint "import Prelude\nimport M.B\n\ndef x : Nat := fromA\n" [("M.A", a), ("M.B", b)]
        check (rules ds).isEmpty s!"{rules ds}"
        -- a string literal that is a global's exact name marks its module used (a tactic
        -- that builds the term by name)
        let ds ← lint "import Prelude\nimport M.A\n\ndef x : String := \"fromA\"\n" [("M.A", a)]
        check (rules ds).isEmpty s!"{rules ds}" },

    { name := "an import whose module has effects on its importers is never unused", run := fun _ => do
        check (Lint.effectfulImport "import Prelude\nbuiltin nat := Nat\n") "a builtin"
        check (Lint.effectfulImport "import Prelude\nsyntax \"twice\" term : term\n") "a syntax"
        check (Lint.effectfulImport "import Prelude\ninfix:65 \" ++ \" => Nat.add\n") "an infix"
        check (!Lint.effectfulImport "import Prelude\ndef helper : Nat := 1\n") "a plain module" },

    { name := "a file with an error gets no unused-import guess", run := fun _ => do
        let a := "import Prelude\ndef fromA : Nat := 7\n"
        let src := "import Prelude\nimport M.A\n\ndef x : Nat := true\n"
        check (rules (← lint src [("M.A", a)])).isEmpty s!"{rules (← lint src [("M.A", a)])}" },

    { name := "wiz lint: exit 0 on a warning, 1 with --deny", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let f := dir / "warn.wiz"
        IO.FS.writeFile f "import Prelude\ndef a : Nat := 1  \n"
        let r ← runLint ["lint", f.toString]
        checkEq 0 r.code
        check ((r.out.splitOn "[style.trailing-whitespace]").length > 1) r.out
        let r ← runLint ["lint", "--deny", f.toString]
        checkEq 1 r.code },

    { name := "wiz lint --json: one document, the rule and its position", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let f := dir / "warn.wiz"
        IO.FS.writeFile f "import Prelude\ndef a : Nat := 1  \n"
        let r ← runLint ["lint", "--json", f.toString]
        checkEq 0 r.code
        let some js := (Lean.Json.parse r.out).toOption | throw (IO.userError s!"not JSON: {r.out}")
        let diags := (js.getObjValAs? (Array Lean.Json) "diagnostics").toOption.getD #[]
        checkEq 1 diags.size
        let d := diags[0]!
        checkEq "style.trailing-whitespace" ((d.getObjValAs? String "rule").toOption.getD "")
        checkEq 2 ((d.getObjValAs? Nat "line").toOption.getD 0)
        checkEq 0 ((js.getObjValAs? Nat "errors").toOption.getD 1) },

    { name := "wiz lint -: standard input", run := fun _ => do
        let cmd := (← wiz) ++ " lint --json -"
        let o ← IO.Process.output { cmd := "sh", args := #["-c", s!"printf 'import Prelude\\ndef a : Nat := 1  \\n' | {cmd}"] }
        checkEq 0 o.exitCode
        check ((o.stdout.splitOn "\"style.trailing-whitespace\"").length > 1) o.stdout }
  ]

builtin_initialize registerGroup wardGroup

end Tests.Ward
