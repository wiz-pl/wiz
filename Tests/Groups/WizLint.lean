import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.WizLint

/-- Run a source with the lint pass on, with the library importable plus the pure
fixture module `LintPlain`. -/
def lintWith (path src : String) (publicRoots : List String := []) :
    IO (CommandState ZeroOneMany) := do
  let base ← Tests.libLoader
  let plain ← IO.FS.readFile "Tests/fixtures/lint/LintPlain.wiz"
  let loader m := if m == "LintPlain" then some plain else base m
  pure <| runFrontend src
    { trustedModule := Tests.libModule, loader, lintEnabled := true,
      lintPath := path, lintPublicRoots := publicRoots }

/-- The lint codes of a run, in message order. -/
def codes (s : CommandState ZeroOneMany) : List String :=
  (s.messages.filter fun m => m.code.startsWith "W").toList.map (·.code)

def noErrors (s : CommandState ZeroOneMany) : IO Unit := do
  let errs := s.messages.filter (·.severity == .error)
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors: {errs.map (·.text)}")

/-- The sibling `wiz` of this test driver. -/
def wizExe : IO String := do
  pure (← IO.FS.realPath ((← IO.appPath).parent.getD "." / "wiz")).toString

def runWiz (args : List String) : IO (UInt32 × String × String) := do
  let out ← IO.Process.output { cmd := ← wizExe, args := args.toArray }
  pure (out.exitCode, out.stdout, out.stderr)

def read (f : String) : IO String := IO.FS.readFile ("Tests/fixtures/lint/" ++ f)

def lintGroup : Group where
  name := "wiz-lint"
  exercise := "Wiz/Lint.lean (the in-compiler lint pass and the P0 rules)"
  parallel := true
  shard := "library"
  cases := [
    { name := "W101: an unused declaration parameter is a warning, and a used one is not", run := fun _ => do
        let s ← lintWith "Tests/fixtures/lint/w101.wiz" (← read "w101.wiz")
        noErrors s
        checkEq ["W101"] (codes s)
        let m := s.messages.find? (·.code == "W101")
        check (m.map (·.severity) == some .warning) "W101 must be a warning, not an error"
        check (m.map (·.text) == some "unused binding 'x'") s!"unexpected text: {m.map (·.text)}" },
    { name := "W102: an inner local that shadows an outer local is a hint", run := fun _ => do
        let s ← lintWith "Tests/fixtures/lint/w102.wiz" (← read "w102.wiz")
        noErrors s
        checkEq ["W102"] (codes s)
        check ((s.messages.find? (·.code == "W102")).map (·.severity) == some .info)
          "W102 must be a hint (info)" },
    { name := "W103: a discarded Result and Option are reported; do-propagation is not", run := fun _ => do
        let s ← lintWith "Tests/fixtures/lint/w103.wiz" (← read "w103.wiz")
        noErrors s
        checkEq ["W103", "W103"] (codes s) },
    { name := "W301: a public declaration without a doc is reported, a documented one is not", run := fun _ => do
        let s ← lintWith "Tests/fixtures/lint/w301.wiz" (← read "w301.wiz") ["Tests/fixtures/lint"]
        noErrors s
        checkEq ["W301"] (codes s)
        check ((s.messages.find? (·.code == "W301")).map (·.text)
          == some "public declaration 'undocumented' has no doc comment") "unexpected W301 message" },
    { name := "W302: an unused pure import is reported, a used one is not", run := fun _ => do
        let s ← lintWith "Tests/fixtures/lint/w302.wiz" (← read "w302.wiz")
        noErrors s
        checkEq ["W302"] (codes s)
        let clean ← lintWith "Tests/fixtures/lint/w302_clean.wiz" (← read "w302_clean.wiz")
        noErrors clean
        checkEq [] (codes clean) },
    { name := "the clean idioms are silent", run := fun _ => do
        let s ← lintWith "Tests/fixtures/lint/clean.wiz" (← read "clean.wiz")
        noErrors s
        checkEq [] (codes s) },
    { name := "lint is off by default: the same source has no W messages", run := fun _ => do
        let base ← Tests.libLoader
        let s := runFrontend (R := ZeroOneMany) (← read "w101.wiz")
          { trustedModule := Tests.libModule, loader := base }
        checkEq [] (codes s)
        check (!s.messages.any (·.severity == .warning)) "a default run emitted a warning" },
    { name := "suppression: a marker with a reason removes the finding, and a bad marker is an error", run := fun _ => do
        let suppressed := "import Prelude\n-- lint: allow W101 (kept for named callers)\ndef unusedParam (x : Nat) : Nat := 1\n"
        let s ← lintWith "Tests/fixtures/lint/suppressed.wiz" suppressed
        checkEq [] (codes s)
        noErrors s
        let noReason := "import Prelude\n-- lint: allow W101\ndef unusedParam (x : Nat) : Nat := 1\n"
        let s ← lintWith "Tests/fixtures/lint/no-reason.wiz" noReason
        check (s.messages.any fun m => m.severity == .error && (m.text.splitOn "needs a reason").length > 1)
          "a suppression without a reason must be an error"
        let unknown := "import Prelude\n-- lint: allow W999 (typo)\ndef unusedParam (x : Nat) : Nat := 1\n"
        let s ← lintWith "Tests/fixtures/lint/unknown.wiz" unknown
        check (s.messages.any fun m => m.severity == .error && (m.text.splitOn "unknown code").length > 1)
          "an unknown suppression code must be an error" },
    { name := "wiz lint --json carries the W code and the warning severity", run := fun _ => do
        let (code, out, err) ← runWiz ["lint", "Tests/fixtures/lint/w101.wiz", "--json"]
        checkEq 0 code
        check (err.isEmpty) s!"unexpected stderr: {err}"
        check ((out.splitOn "\"code\":\"W101\"").length > 1) s!"no W101 in --json: {out}"
        check ((out.splitOn "\"severity\":\"warning\"").length > 1) s!"not a warning in --json: {out}"
        check ((out.splitOn "\"severity\":\"error\"").length == 1) s!"a W finding is an error: {out}" },
    { name := "every registered rule id is in docs/error-codes.md", run := fun _ => do
        let doc ← IO.FS.readFile "docs/error-codes.md"
        for r in Lint.registry (R := ZeroOneMany) do
          check ((doc.splitOn r.id).length > 1) s!"{r.id} is not in docs/error-codes.md" }
  ]

builtin_initialize registerGroup lintGroup

end Tests.WizLint
