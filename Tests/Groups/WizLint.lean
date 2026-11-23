import Tests.Elab
import Tests.Grail

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.WizLint

/-- Run a source with the lint pass on, with the library importable plus the pure
fixture module `LintPlain`. -/
def lintWith (path src : String) (publicRoots : List String := [])
    (sets : Array LintPackageSet := #[]) (enabled : List String := []) :
    IO (CommandState ZeroOneMany) := do
  let base ← Tests.libLoader
  let plain ← IO.FS.readFile "Tests/fixtures/lint/LintPlain.wiz"
  let loader m := if m == "LintPlain" then some plain else base m
  pure <| runFrontend src
    { trustedModule := Tests.libModule, loader, lintEnabled := true,
      lintPath := path, lintPublicRoots := publicRoots,
      lintPackageSets := sets, lintSets := enabled }

/-- Elaborate a package lint module and run the registry's checks on it. -/
def loadSet (file : String) : IO (Except String LintPackageSet) := do
  let base ← Tests.libLoader
  let src ← IO.FS.readFile ("Tests/fixtures/lint-pkg/" ++ file)
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := base }
  pure (Lint.loadPackageSet s)

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

/-- Elaborate a package lint module at `dir / module` and run the registry's checks
(the package test's counterpart of `loadSet`, which reads the committed fixtures). -/
def loadSetAt (dir : System.FilePath) (module : String) : IO (Except String LintPackageSet) := do
  let base ← Tests.libLoader
  let src ← IO.FS.readFile (dir / module)
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := base }
  pure (Lint.loadPackageSet s)

/-- A package tree: a manifest that declares `sets` (`Package.lintSet NAME MODULE`), a
`lint.conf`, and the modules themselves. -/
def pkgTree (sets : List (String × String)) (conf : String)
    (files : List (String × String)) : IO System.FilePath := do
  let manifest := "import Grail\ndef package : Package := Package.new \"p\"\n  |> Package.lib \"p\" \"src\"\n" ++
    String.join (sets.map fun (n, m) => s!"  |> Package.lintSet \"{n}\" \"{m}\"\n")
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "grail.wiz") manifest
  IO.FS.writeFile (dir / "lint.conf") conf
  for (p, text) in files do
    let f := dir / p
    IO.FS.createDirAll (f.parent.getD dir)
    IO.FS.writeFile f text
  pure dir

/-- Run `Tests/fixtures/lint/TypedProbe.wiz`'s `probe` on a view. -/
def runProbe (view : String) : IO (Except String String) := do
  let base ← Tests.libLoader
  let src ← IO.FS.readFile "Tests/fixtures/lint/TypedProbe.wiz"
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := base }
  let errs := s.messages.filter (fun m => m.severity == .error)
  unless errs.isEmpty do
    return .error s!"the typed probe did not elaborate: {errs.map (·.text)}"
  match compileReachable s.globals s.builtins ["probe"] with
  | .error e => pure (.error (Wiz.kernelRejected "probe" e))
  | .ok code => pure (.ok ((Lint.callRunner code "probe" view).getD "<not a string>"))

def lintGroup : Group where
  name := "wiz-lint"
  exercise := "Wiz/Lint.lean (the in-compiler pass, the P0 rules, and the package lint ABI)"
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
    { name := "a package lint set fires only when the consumer enables it", run := fun _ => do
        let set ← match ← loadSet "Lints.wiz" with
          | Except.ok s => pure s
          | Except.error e => throw (IO.userError s!"the good fixture package lint set was refused: {e}")
        check (set.name == "fixture") s!"unexpected set name: {set.name}"
        check (set.rules.toList.map (·.code) == ["W501"]) s!"unexpected rules: {set.rules.toList.map (·.code)}"
        let src := "import Prelude\ndef rawThing : Nat := 1\n"
        let on ← lintWith "Tests/fixtures/lint-pkg/target.wiz" src
          (sets := #[set]) (enabled := ["fixture"])
        noErrors on
        checkEq ["W501"] (codes on)
        check ((on.messages.find? (·.code == "W501")).map (·.text) == some "a raw declaration")
          "the package rule's text did not survive the view round-trip"
        let off ← lintWith "Tests/fixtures/lint-pkg/target.wiz" src (sets := #[set]) (enabled := [])
        checkEq [] (codes off) },
    { name := "a package rule with an undeclared capability is refused", run := fun _ => do
        match ← loadSet "BadCapability.wiz" with
        | Except.ok _ => throw (IO.userError "a set whose rule needs an undeclared capability was accepted")
        | Except.error e =>
          check ((e.splitOn "spans").length > 1) s!"the refusal does not name the capability: {e}" },
    { name := "a package rule whose closure reaches a trust source is refused", run := fun _ => do
        match ← loadSet "BadTrust.wiz" with
        | Except.ok _ => throw (IO.userError "a set whose rule reaches an axiom was accepted")
        | Except.error e =>
          check ((e.splitOn "trust").length > 1 || (e.splitOn "trustMe").length > 1)
            s!"the refusal does not name the trust source: {e}" },
    { name := "wiz lint --package-lint --set runs the package rule", run := fun _ => do
        let (code, out, err) ← runWiz
          ["lint", "Tests/fixtures/lint-pkg/target.wiz",
           "--package-lint", "Tests/fixtures/lint-pkg/Lints.wiz", "--set", "fixture"]
        checkEq 0 code
        check (err.isEmpty) s!"unexpected stderr: {err}"
        check ((out.splitOn "[W501]").length > 1) s!"the package rule did not fire: {out}"
        let (code2, out2, _) ← runWiz
          ["lint", "Tests/fixtures/lint-pkg/target.wiz",
           "--package-lint", "Tests/fixtures/lint-pkg/Lints.wiz"]
        checkEq 0 code2
        check ((out2.splitOn "[W501]").length == 1) s!"the package rule ran without --set: {out2}" },
    { name := "wiz lint --json carries the W code and the warning severity", run := fun _ => do
        let (code, out, err) ← runWiz ["lint", "Tests/fixtures/lint/w101.wiz", "--json"]
        checkEq 0 code
        check (err.isEmpty) s!"unexpected stderr: {err}"
        check ((out.splitOn "\"code\":\"W101\"").length > 1) s!"no W101 in --json: {out}"
        check ((out.splitOn "\"severity\":\"warning\"").length > 1) s!"not a warning in --json: {out}"
        check ((out.splitOn "\"severity\":\"error\"").length == 1) s!"a W finding is an error: {out}" },
    { name := "the typed lib/Lint.wiz mirrors the registry and parses the view", run := fun _ => do
        let view : Lint.CommandView :=
          { capabilities := [.decl, .spans, .facts], module := "M", path := "t.wiz",
            kind := "def", name := "rawThing",
            span := some { start := 3, stop := 9 },
            decls := #[{ name := "rawThing", kind := "def", isPublic := true, hasDoc := true }],
            binders := #[{ name := "x", used := true, depth := 0 }],
            messages := #[{ severity := "warning", code := "W101", start := 1, stop := 2, text := "m" }] }
        match ← runProbe view.render with
        | .error e => throw (IO.userError e)
        | .ok out =>
          checkEq ("decl,spans,imports,globals,messages,facts,info,tactics,kernelTerm,sourceText|" ++
            "decl=true,spans=true,imports=true,globals=true,messages=true,facts=true," ++
            "info=false,tactics=false,kernelTerm=false,sourceText=false|" ++
            "correctness,performance,api,maintainability,ecosystem|off,hint,warning,error|" ++
            "declaration,module,workspace|facts|3,9|rawThing!|W101|7\t9\ta#1\tmsg|pkg|ok") out },
    { name := "a rule written against lib/Lint.wiz fires from the typed view", run := fun _ => do
        let set ← match ← loadSet "Typed.wiz" with
          | Except.ok s => pure s
          | Except.error e => throw (IO.userError s!"the typed fixture set was refused: {e}")
        let src := "import Prelude\ndef rawThing : Nat := 1\n"
        let on ← lintWith "Tests/fixtures/lint-pkg/target.wiz" src
          (sets := #[set]) (enabled := ["typed"])
        noErrors on
        checkEq ["W503"] (codes on)
        check ((on.messages.find? (·.code == "W503")).map (·.text)
          == some "typed declaration 'rawThing' (0 binder(s))")
          s!"the typed rule's text did not survive: {on.messages.map (·.text)}" },
    { name := "a manifest lint set loads; lint.conf names it and refuses an undeclared name", run := fun _ => do
        let lints ← IO.FS.readFile "Tests/fixtures/lint-pkg/Lints.wiz"
        let tc ← toolchain
        let dir ← pkgTree [("fixture", "lint/Lints.wiz")]
          "set fixture\npublic-roots lint\n" [("lint/Lints.wiz", lints)]
        let binId ← Grail.binaryId tc.cacheDir
        match ← Grail.readConfig tc binId "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, _) =>
          checkEq ["fixture"] (pkg.lintSets.map (·.name))
          match ← Grail.readLintPolicy dir pkg with
          | .error e => throw (IO.userError e)
          | .ok conf =>
            checkEq [("fixture", "lint/Lints.wiz")] conf.sets
            checkEq ["lint"] conf.publicRoots
            checkEq (some ("fixture", "lint/Lints.wiz"))
              ((conf.sets.find? fun p => p.1 == "fixture"))
            match ← loadSetAt dir "lint/Lints.wiz" with
            | .ok set => checkEq ["W501"] (set.rules.toList.map (·.code))
            | .error e => throw (IO.userError s!"the declared set was refused: {e}")
        IO.FS.writeFile (dir / "lint.conf") "set nope\n"
        match ← Grail.readConfig tc binId "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, _) =>
          match ← Grail.readLintPolicy dir pkg with
          | .ok _ => throw (IO.userError "lint.conf enabled a set the manifest does not declare")
          | .error e =>
            check ((e.splitOn "nope").length > 1) s!"the refusal does not name the set: {e}"
            check ((e.splitOn "Package.lintSet").length > 1)
              s!"the refusal does not say where to declare the set: {e}" },
    { name := "a package lint set with an unknown capability is refused when it loads", run := fun _ => do
        let bad ← IO.FS.readFile "Tests/fixtures/lint-pkg/BadCapability.wiz"
        let tc ← toolchain
        let dir ← pkgTree [("bad", "lint/BadCapability.wiz")] "set bad\n"
          [("lint/BadCapability.wiz", bad)]
        let binId ← Grail.binaryId tc.cacheDir
        match ← Grail.readConfig tc binId "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, _) =>
          match ← Grail.readLintPolicy dir pkg with
          | .error e => throw (IO.userError s!"the manifest's own set was refused: {e}")
          | .ok conf =>
            checkEq [("bad", "lint/BadCapability.wiz")] conf.sets
            match ← loadSetAt dir "lint/BadCapability.wiz" with
            | .ok _ => throw (IO.userError "a set whose rule reads an undeclared capability was accepted")
            | .error e =>
              check ((e.splitOn "spans").length > 1) s!"the refusal does not name the capability: {e}" },
    { name := "baseline: write, rerun clean, then one new entry after a finding changes", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let file := dir / "w101.wiz"
        let baseline := dir / "lint-baseline.tsv"
        IO.FS.writeFile file "import Prelude\ndef unusedParam (x : Nat) : Nat := 1\n"
        let (c1, _, e1) ← runWiz ["lint", file.toString, "--lint-baseline-write", baseline.toString]
        checkEq 0 c1
        check ((e1.splitOn "wrote 1 finding").length > 1) s!"write output: {e1}"
        let text ← IO.FS.readFile baseline
        check ((text.splitOn "W101").length > 1) s!"no W101 key: {text}"
        check ((text.splitOn "unusedParam#0").length > 1) s!"the anchor is not in the key: {text}"
        check (text.startsWith "# wiz-lint baseline") s!"no header: {text}"
        let (c2, out2, e2) ← runWiz ["lint", file.toString, "--lint-baseline", baseline.toString]
        checkEq 0 c2
        check ((e2.splitOn "no new findings").length > 1) s!"diff output: {e2}"
        check ((out2.splitOn "[W101]").length == 1) s!"a baselined finding was printed: {out2}"
        -- the finding's declaration name changes, so its stable key does: one new entry
        IO.FS.writeFile file "import Prelude\ndef unusedOther (x : Nat) : Nat := 1\n"
        let (c3, out3, e3) ← runWiz ["lint", file.toString, "--lint-baseline", baseline.toString]
        checkEq 1 c3
        check ((e3.splitOn "1 new finding").length > 1) s!"diff count: {e3}"
        check ((out3.splitOn "[W101]").length == 2) s!"the new finding was not the only one printed: {out3}"
        -- a missing baseline is a clear failure, not a silent pass
        let (c4, _, e4) ← runWiz ["lint", file.toString, "--lint-baseline", (dir / "absent.tsv").toString]
        checkEq 3 c4
        check ((e4.splitOn "cannot read the baseline").length > 1) s!"missing baseline: {e4}" },
    { name := "every registered rule id is in docs/error-codes.md", run := fun _ => do
        let doc ← IO.FS.readFile "docs/error-codes.md"
        for r in Lint.registry (R := ZeroOneMany) do
          check ((doc.splitOn r.id).length > 1) s!"{r.id} is not in docs/error-codes.md" }
  ]

builtin_initialize registerGroup lintGroup

end Tests.WizLint
