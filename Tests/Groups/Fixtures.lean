import Tests.Elab
import Tests.Groups.FfiStruct
import Tests.Groups.GrailDeps
import Tests.Groups.GrailE2E
import Tests.Groups.ScryProject
import Tests.Groups.SelfHost
import Tests.Groups.SelfhostCli
import Tests.Groups.SelfhostCliDiff

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# `=fixtures`: the generated Wiz sources elaborate without their long cases

The suite builds Wiz programs from Lean strings and embeds them in cases. Some of those
cases spend minutes (or, for `=scry-project`, fifteen) before the program is even
elaborated, so a source string that stops parsing or stops matching the elaborator is
found late and in a case whose name is about something else. This group is the fast,
named place: it calls the *same source builders* and the *same frontend helper*
(`elabTree`/`elabTreeRoots`, which the cases use) and only checks the elaboration
messages. Nothing is code-generated, compiled to C or run, and no toolchain is needed:
`structFiles` and friends only `link_c` files that are in the tree, `divSrc` names a
system header but does not preprocess it, and the CLI fixtures do not build.

The static half of the gate is `scripts/check-fixtures.py` (`.github/workflows/ci.yml`,
job `docs_style`): it checks every `.expected` anchor against the current source and every
grail test's marker against its `.expected` beside it. It needs no build either.

What is deliberately *not* duplicated here: the short cases that already elaborate their
own inline program (`=ffi`, `=ffi-structs`, most of `=selfhost`) and the docs fences
(`scripts/check-docs-examples.py`, job `docs_examples`, which run the real `wiz`). The
lane's inventory is `wiz-notes/test-fixtures.md`.

A missing dependency is reported, never skipped silently: the scry driver needs the C#
grammar out-link (`nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp`),
and `skipMissing` fails unless the run explicitly allows missing dependencies. -/

/-- The elaboration errors of `files`, compiled as `elabTree` (or `elabTreeRoots`) does.
The temporary tree is removed; nothing is built or run. -/
def fixtureErrors (files : List (String × String)) (roots : List String := [])
    (trustNative : Bool := false) : IO (Array String) := do
  let (s, src, dir) ← if roots.isEmpty then elabTree files trustNative
    else elabTreeRoots roots files trustNative
  let errs := (s.messages.filter (·.severity == .error)).map (·.render src)
  IO.FS.removeDirAll dir
  pure errs

def fixtureShows (name : String) (errs : Array String) : String :=
  s!"{name}: {errs.size} elaboration error(s):\n  " ++ "\n  ".intercalate errs.toList

/-- `files` (a fixture's source builder output) must elaborate without an error. -/
def fixtureCompiles (name : String) (files : List (String × String)) (roots : List String := [])
    (trustNative : Bool := false) : IO Unit := do
  let errs ← fixtureErrors files roots trustNative
  unless errs.isEmpty do throw (IO.userError (fixtureShows name errs))

/-- A negative fixture must still fail, and the error must mention `fragment`. -/
def fixtureFails (name fragment : String) (files : List (String × String))
    (trustNative : Bool := false) : IO Unit := do
  let errs ← fixtureErrors files [] trustNative
  check (!errs.isEmpty) s!"{name}: expected an elaboration error, but it elaborated cleanly"
  unless errs.any (fun e => (e.splitOn fragment).length > 1) do
    throw (IO.userError (s!"{name}: no error mentions '{fragment}':\n  "
      ++ "\n  ".intercalate errs.toList))

/-- Run `build` with a generated C header, under a fresh directory removed afterwards
(`structDeepProgram` and `structArrayProgram` take their header's path). -/
def withHeader (header : String) (build : String → IO Unit) : IO Unit := do
  let dir ← IO.FS.createTempDir
  let h := dir / "fixture.h"
  IO.FS.writeFile h header
  try build h.toString finally IO.FS.removeDirAll dir

/-- A manifest must still be a Wiz program that evaluates to a `Package`
(`Grail.readConfig`, the same entry point `grail update`/`build` use). -/
def fixtureManifest (name : String) (manifest : String) : IO Unit := do
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "grail.wiz") manifest
  let tc ← toolchain
  let r ← Grail.readConfig tc (← Tests.Grail.binId tc) "lib" dir
  IO.FS.removeDirAll dir
  match r with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"{name}: {e}")

/-- The checked-in fate-index package manifests (`Tests/fixtures/fate-index/sources/*`),
discovered rather than listed: a new fixture package is parsed without an edit here. -/
def fixtureFateManifests : IO Unit := do
  let dir : System.FilePath := "Tests/fixtures/fate-index/sources"
  let mut n := 0
  for e in ← dir.readDir do
    let f := e.path / "grail.wiz"
    if ← f.pathExists then
      fixtureManifest f.toString (← IO.FS.readFile f)
      n := n + 1
  check (n > 0) s!"no package manifests under {dir}"

/-- (The scry driver imports `Scry.NativeLink`, whose `link_c` names this out-link; a
fresh checkout has it only after `nix build .#tree-sitter-c-sharp`.) -/
def scryGrammarPresent : IO Bool :=
  (System.FilePath.mk "scry/native/tree-sitter-c-sharp/src/parser.c").pathExists

def scryProjectFixture : IO Unit := do
  unless ← scryGrammarPresent do
    -- `skipMissing` fails by default and is a reported, allow-listed skip under
    -- `--allow-missing-deps`; it never passes silently.
    skipMissing "scry's C# grammar out-link (nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp)"
    return
  let tc ← toolchain
  fixtureCompiles "scryProjectSource" [("main.wiz", scryProjectSource tc.cc)]
    ["scry/src", "scry/gen"]

def structFixtures : IO Unit := do
  fixtureCompiles "structFiles" structFiles
  fixtureCompiles "unboxStructFiles" unboxStructFiles

def structDeepFixtures : IO Unit := do
  withHeader structDeepHeader fun h =>
    fixtureCompiles "structDeepProgram" [("main.wiz", structDeepProgram h)]
  withHeader structArrayHeader fun h =>
    fixtureCompiles "structArrayProgram" [("main.wiz", structArrayProgram h)]

def cliFixtures : IO Unit := do
  -- `elabTree` elaborates the file called `main.wiz`; the fixture's own name in its
  -- selfhost case (`good.wiz`) does not matter to the frontend.
  fixtureCompiles "cliGood" [("main.wiz", cliGood)]
  fixtureCompiles "cliHello" [("main.wiz", cliHello)]
  -- `native_refl` is accepted only with `--trust-native`, as the selfhost CLI runs it
  fixtureCompiles "cliNativeRefl" [("main.wiz", cliNativeRefl)] (trustNative := true)
  fixtureCompiles "cliNativeReflMain" [("main.wiz", cliNativeReflMain)] (trustNative := true)

def cliNegativeFixtures : IO Unit := do
  fixtureFails "cliBad" "unknown identifier 'nope'" [("main.wiz", cliBad)]
  fixtureFails "cliBadModule" "unknown identifier 'nope'" [("main.wiz", cliBadModule)]

def ffiStructFixture : IO Unit :=
  fixtureCompiles "divSrc" [("main.wiz", divSrc)]

def grailManifests : IO Unit := do
  -- the two builders the Grail dependency/e2e cases write into tarballs/trees
  fixtureManifest "depPkg" ((Tests.Grail.depPkg "git+file:///tmp/fixture" "v1").head!.2)
  fixtureManifest "e2eLibManifest" (Tests.Grail.e2eLibManifest "fixture-lib")
  fixtureManifest "e2eAppManifest"
    (Tests.Grail.e2eAppManifest "file:///tmp/fixture-index" "/tmp/fixture-base")
  fixtureFateManifests

def fixturesGroup : Group where
  name := "fixtures"
  exercise := "the generated Wiz sources: compile-only"
  parallel := true
  shard := "library"
  cases := [
    { name := "scry-project: scryProjectSource elaborates (no project build or analysis)",
      run := fun _ => scryProjectFixture },
    { name := "selfhost: structFiles and unboxStructFiles elaborate", run := fun _ => structFixtures },
    { name := "selfhost: structDeepProgram and structArrayProgram elaborate",
      run := fun _ => structDeepFixtures },
    { name := "selfhost-cli: cliGood, cliHello and the --trust-native refl fixtures elaborate",
      run := fun _ => cliFixtures },
    { name := "selfhost-cli: cliBad and cliBadModule still fail at their unknown identifier",
      run := fun _ => cliNegativeFixtures },
    { name := "ffi-structs: divSrc elaborates", run := fun _ => ffiStructFixture },
    { name := "control: a broken fixture string is reported with the fixture's name",
      run := fun _ =>
        fixtureFails "control/fixture" "unknown identifier 'nope'"
          [("main.wiz", "import Prelude\ndef broken : Nat := nope\n")] },
    { name := "grail: the dependency/e2e manifests and the fate-index packages parse",
      run := fun _ => grailManifests }
  ]

builtin_initialize registerGroup fixturesGroup

end Tests.Elab
