import Tests.Elab

open Wiz

/-!
# 11ad: `wiz lint`'s machine-readable output

`wiz lint --format sarif` (`Wiz.Sarif`) and `--format json` are the outputs a CI job or
a code-scanning service reads. The cases here check the SARIF document's required keys,
its rule descriptors and levels, relative artifact URIs, a file that does not parse, the
exit status with and without `--deny`, and one golden document; the last case checks that
`--format text` is unchanged.

The in-process cases call `Wiz.Lint.run` and `Wiz.Sarif` directly; the CLI cases run the
built `wiz` binary with the same temporary directories the `ward` group uses.
-/

set_option compiler.extract_closed false

namespace Tests.LintSarif

abbrev R := ZeroOneMany

/-- Lint `src` as a file that imports `Prelude`, as the `ward` group does. -/
def lint (src : String) : IO (Array Lint.Diag) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let init : CommandState R :=
    { trustedModule := Tests.libModule, termInfo := true,
      loader := fun m => if m == "Prelude" then some prelude else none }
  let s := runFrontend src init
  pure (Lint.run {} src s)

/-- `wiz`'s path, as `Tests/Groups/Ward.lean` has it. -/
def wiz : IO String := do pure (← IO.FS.realPath ".lake/build/bin/wiz").toString

structure Run where
  code : UInt32
  out : String
  err : String

def runLint (args : List String) (cwd : Option System.FilePath := none) : IO Run := do
  let o ← IO.Process.output { cmd := ← wiz, args := args.toArray, cwd }
  pure { code := o.exitCode, out := o.stdout, err := o.stderr }

def parseJson (out : String) : IO Lean.Json :=
  match Lean.Json.parse out with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"not JSON ({e}): {out}")

/-! ## JSON accessors (each `get…?` returns an `Except`, so `.toOption`) -/

def field (j : Lean.Json) (k : String) : Option Lean.Json := (j.getObjVal? k).toOption

def sfield (j : Lean.Json) (k : String) : Option String :=
  (j.getObjValAs? String k).toOption

def nfield (j : Lean.Json) (k : String) : Option Nat :=
  (j.getObjValAs? Nat k).toOption

def afield (j : Lean.Json) (k : String) : Array Lean.Json :=
  ((field j k).bind fun v => (v.getArr?).toOption).getD #[]

/-- The first location of a result. -/
def firstLocation (r : Lean.Json) : Option Lean.Json :=
  (field r "locations").bind fun l =>
    ((l.getArr?.toOption).bind fun a => a[0]?)

def physical (r : Lean.Json) : Option Lean.Json :=
  (firstLocation r).bind fun loc => field loc "physicalLocation"

/-- The `artifactLocation.uri` of a result. -/
def locationUri (r : Lean.Json) : String :=
  ((physical r).bind fun p => field p "artifactLocation").bind (sfield · "uri") |>.getD ""

/-- The `artifactLocation.uriBaseId` of a result. -/
def locationBaseId (r : Lean.Json) : String :=
  ((physical r).bind fun p => field p "artifactLocation").bind (sfield · "uriBaseId")
    |>.getD ""

/-- The `region` of a result. -/
def locationRegion (r : Lean.Json) : Lean.Json :=
  ((physical r).bind fun p => field p "region").getD .null

/-- The one run of a SARIF document. -/
def theRun (js : Lean.Json) : IO Lean.Json := do
  let runs := afield js "runs"
  checkEq 1 runs.size
  pure runs[0]!

def results (js : Lean.Json) : IO (Array Lean.Json) := do
  pure (afield (← theRun js) "results")

def driver (js : Lean.Json) : IO Lean.Json := do
  pure (field (← theRun js) "tool" |>.bind (fun t => field t "driver") |>.getD (.null))

def ruleIds (js : Lean.Json) : IO (Array String) := do
  pure ((afield (← driver js) "rules").map fun r => (sfield r "id").getD "")

/-- The golden document for `goldenSrc` below, with the current tool version. -/
def golden : String :=
  "{\"$schema\":\"https://docs.oasis-open.org/sarif/sarif/v2.1.0/os/schemas/sarif-schema-2.1.0.json\"," ++
  "\"runs\":[{\"artifacts\":[{\"location\":{\"uri\":\"golden.wiz\",\"uriBaseId\":\"%SRCROOT%\"}}]," ++
  "\"columnKind\":\"utf16CodeUnits\",\"results\":[{\"level\":\"warning\",\"locations\":[{\"physicalLocation\":" ++
  "{\"artifactLocation\":{\"uri\":\"golden.wiz\",\"uriBaseId\":\"%SRCROOT%\"},\"region\":{\"endColumn\":" ++
  "19,\"endLine\":2,\"startColumn\":17,\"startLine\":2}}}],\"message\":{\"text\":\"trailing whitespace\"}," ++
  "\"partialFingerprints\":{\"primaryLocationLineHash\":\"eabb5929b217c410\",\"wizlint/v1\":\"a7c7d043b29ad8d9\"}," ++
  "\"ruleId\":\"wizlint/style/trailing-whitespace\",\"ruleIndex\":1}],\"tool\":{\"driver\":{\"informationUri\":" ++
  "\"https://github.com/wiz-pl/wiz\",\"name\":\"wiz\",\"rules\":[{\"defaultConfiguration\":{\"level\":" ++
  "\"warning\"},\"id\":\"wizlint/style/tabs\",\"name\":\"tab\",\"shortDescription\":{\"text\":" ++
  "\"a tab in indentation or alignment\"}},{\"defaultConfiguration\":{\"level\":\"warning\"}," ++
  "\"id\":\"wizlint/style/trailing-whitespace\",\"name\":\"trailing-whitespace\",\"shortDescription\":" ++
  "{\"text\":\"spaces or tabs at the end of a line\"}},{\"defaultConfiguration\":{\"level\":\"warning\"}," ++
  "\"id\":\"wizlint/style/crlf\",\"name\":\"crlf\",\"shortDescription\":{\"text\":\"a CRLF line ending\"}}," ++
  "{\"defaultConfiguration\":{\"level\":\"warning\"},\"id\":\"wizlint/style/line-length\",\"name\":" ++
  "\"line-length\",\"shortDescription\":{\"text\":\"a line longer than the configured maximum\"}}," ++
  "{\"defaultConfiguration\":{\"level\":\"warning\"},\"id\":\"wizlint/hygiene/sorry\",\"name\":" ++
  "\"sorry\",\"shortDescription\":{\"text\":\"the identifier sorry or admit (Wiz does not check it)\"}}," ++
  "{\"defaultConfiguration\":{\"level\":\"warning\"},\"id\":\"wizlint/hygiene/axiom\",\"name\":" ++
  "\"axiom\",\"shortDescription\":{\"text\":\"an axiom declared in this file\"}},{\"defaultConfiguration\":" ++
  "{\"level\":\"warning\"},\"id\":\"wizlint/hygiene/shadowed-binder\",\"name\":\"shadowed-binder\"," ++
  "\"shortDescription\":{\"text\":\"a binder that shadows an enclosing binder or a visible global\"}}," ++
  "{\"defaultConfiguration\":{\"level\":\"warning\"},\"id\":\"wizlint/imports/unused-import\"," ++
  "\"name\":\"unused-import\",\"shortDescription\":{\"text\":\"an import that nothing in this file needs\"}}," ++
  "{\"defaultConfiguration\":{\"level\":\"warning\"},\"id\":\"wizlint/imports/duplicate-import\"," ++
  "\"name\":\"duplicate-import\",\"shortDescription\":{\"text\":\"the same module imported twice\"}}]," ++
  "\"version\":\"0.1.0-dev\"}}}],\"version\":\"2.1.0\"}"

/-- The source the golden document is rendered from. -/
def goldenSrc : String := "import Prelude\ndef a : Nat := 1  \ndef b : Nat := 2\n"

def lintSarifGroup : Group where
  name := "lint-sarif"
  parallel := true
  exercise := "Stage 11ad"

  cases := [
    { name := "SARIF: schema, version, driver and a location", run := fun _ => do
        let ds ← lint "import Prelude\ndef a : Nat := 1  \n"
        let js := Sarif.toJson "fixture.wiz" "import Prelude\ndef a : Nat := 1  \n" ds
        checkEq "2.1.0" ((sfield js "version").getD "")
        check ((sfield js "$schema").getD "" |>.endsWith "sarif-schema-2.1.0.json")
          s!"schema: {sfield js "$schema"}"
        let d ← driver js
        checkEq "wiz" ((sfield d "name").getD "")
        checkEq Wiz.version ((sfield d "version").getD "")
        checkEq "https://github.com/wiz-pl/wiz" ((sfield d "informationUri").getD "")
        checkEq "utf16CodeUnits" ((sfield (← theRun js) "columnKind").getD "")
        -- one artifact, the same relative location a result names, under %SRCROOT%
        let arts := afield (← theRun js) "artifacts"
        checkEq 1 arts.size
        checkEq "fixture.wiz"
          ((field arts[0]! "location").bind (sfield · "uri") |>.getD "")
        checkEq "%SRCROOT%"
          ((field arts[0]! "location").bind (sfield · "uriBaseId") |>.getD "")
        -- the rule table is stable: every lint rule has a namespaced descriptor, in a
        -- fixed order
        let ids ← ruleIds js
        checkEq #["wizlint/style/tabs", "wizlint/style/trailing-whitespace",
                  "wizlint/style/crlf", "wizlint/style/line-length",
                  "wizlint/hygiene/sorry", "wizlint/hygiene/axiom",
                  "wizlint/hygiene/shadowed-binder", "wizlint/imports/unused-import",
                  "wizlint/imports/duplicate-import"] ids
        let rs ← results js
        checkEq 1 rs.size
        let r := rs[0]!
        checkEq "wizlint/style/trailing-whitespace" ((sfield r "ruleId").getD "")
        checkEq "warning" ((sfield r "level").getD "")
        checkEq 1 ((nfield r "ruleIndex").getD 100)
        checkEq "trailing whitespace" (((field r "message").bind (sfield · "text")).getD "")
        checkEq "fixture.wiz" (locationUri r)
        checkEq "%SRCROOT%" (locationBaseId r)
        let region := locationRegion r
        checkEq 2 ((nfield region "startLine").getD 0)
        checkEq 17 ((nfield region "startColumn").getD 0)
        checkEq 2 ((nfield region "endLine").getD 0)
        checkEq 19 ((nfield region "endColumn").getD 0)
        let fps := (field r "partialFingerprints").getD .null
        check ((field fps Sarif.fingerprintKey).isSome) "no primaryLocationLineHash"
        check ((field fps Sarif.compositeFingerprintKey).isSome) "no wizlint/v1" },

    { name := "SARIF: several rules and severities, ruleIndex agrees", run := fun _ => do
        let src := "import Prelude\naxiom cheat : Nat\ndef bad : Nat := sorry\n"
        let ds ← lint src
        let js := Sarif.toJson "multi.wiz" src ds
        let ids ← ruleIds js
        check (ids.contains "wizlint/hygiene/axiom") s!"rules: {ids}"
        check (ids.contains "wizlint/hygiene/sorry") s!"rules: {ids}"
        -- an elaboration error has its own code as its rule id, with a descriptor
        check (ids.contains "wizlint/elaborator/unknown-identifier") s!"rules: {ids}"
        let rs ← results js
        let levels := rs.map fun r => (sfield r "level").getD ""
        check (levels.contains "error") s!"levels: {levels}"
        check (levels.contains "warning") s!"levels: {levels}"
        for r in rs do
          let id := (sfield r "ruleId").getD ""
          let i := (nfield r "ruleIndex").getD 1000
          check (i < ids.size) s!"ruleIndex {i} for {id}"
          checkEq id ids[i]!
        -- Wiz's `info` is SARIF's `note`
        checkEq "note" (Sarif.level .info)
        checkEq "error" (Sarif.level .error)
        checkEq "warning" (Sarif.level .warning) },

    { name := "SARIF: the artifact URI is relative to the invocation", run := fun _ => do
        let dir ← IO.FS.createTempDir
        IO.FS.writeFile (dir / "warn.wiz") "import Prelude\ndef a : Nat := 1  \n"
        let rel ← runLint ["lint", "--format", "sarif", "warn.wiz"] (cwd := some dir)
        checkEq 0 rel.code
        let js ← parseJson rel.out
        let r := (← results js)[0]!
        checkEq "warn.wiz" (locationUri r)
        -- an absolute path under the working directory is shortened too
        let abs ← runLint ["lint", "--format", "sarif", (dir / "warn.wiz").toString] (cwd := some dir)
        checkEq 0 abs.code
        let js ← parseJson abs.out
        let r := (← results js)[0]!
        checkEq "warn.wiz" (locationUri r) },

    { name := "SARIF: UTF-16 columns and stable fingerprints", run := fun _ => do
        -- a supplementary-plane character is two UTF-16 code units: the trailing
        -- whitespace starts at character column 5 but at UTF-16 column 6
        let src := "import Prelude\n-- 😀  \ndef a : Nat := 1\n"
        let ds ← lint src
        let js := Sarif.toJson "utf16.wiz" src ds
        let rs ← results js
        let some r := rs.find? fun r =>
            (sfield r "ruleId").getD "" == "wizlint/style/trailing-whitespace"
          | throw (IO.userError s!"no trailing-whitespace result: {rs}")
        let region := locationRegion r
        checkEq 2 ((nfield region "startLine").getD 0)
        checkEq 6 ((nfield region "startColumn").getD 0)
        checkEq 8 ((nfield region "endColumn").getD 0)
        -- the JSON's fingerprints are the two documented hashes
        let fps := (field r "partialFingerprints").getD .null
        let line := "-- 😀  "
        checkEq (Sarif.primaryLocationLineHash "wizlint/style/trailing-whitespace" line)
          ((field fps Sarif.fingerprintKey).bind (·.getStr?.toOption) |>.getD "")
        checkEq (Sarif.compositeFingerprint "wizlint/style/trailing-whitespace" "utf16.wiz" line)
          ((field fps Sarif.compositeFingerprintKey).bind (·.getStr?.toOption) |>.getD "")
        -- a whitespace-only edit keeps the primary line hash
        checkEq (Sarif.primaryLocationLineHash "wizlint/style/tabs" "def a := 1")
          (Sarif.primaryLocationLineHash "wizlint/style/tabs" "  def  a :=  1  ") },

    { name := "SARIF: a file that does not parse still reports, and exits 1", run := fun _ => do
        let dir ← IO.FS.createTempDir
        IO.FS.writeFile (dir / "bad.wiz") "import Prelude\ndef a : Nat :=\n"
        let r ← runLint ["lint", "--format", "sarif", "bad.wiz"] (cwd := some dir)
        checkEq 1 r.code
        let js ← parseJson r.out
        let rs ← results js
        check (rs.size > 0) "no result for the parse error"
        check (rs.any fun x => (sfield x "level").getD "" == "error") "no error result"
        let ids ← ruleIds js
        check (ids.contains "wizlint/elaborator/parse-error") s!"rules: {ids}" },

    { name := "--deny and the exit status: SARIF and JSON are written on failure", run := fun _ => do
        let dir ← IO.FS.createTempDir
        IO.FS.writeFile (dir / "warn.wiz") "import Prelude\ndef a : Nat := 1  \n"
        let ok ← runLint ["lint", "--format", "sarif", "warn.wiz"] (cwd := some dir)
        checkEq 0 ok.code
        check ((← results (← parseJson ok.out)).size > 0) "no result without --deny"
        let denied ← runLint ["lint", "--format", "sarif", "--deny", "warn.wiz"] (cwd := some dir)
        checkEq 1 denied.code
        check ((← results (← parseJson denied.out)).size > 0) "no SARIF with --deny"
        let json ← runLint ["lint", "--format", "json", "--deny", "warn.wiz"] (cwd := some dir)
        checkEq 1 json.code
        let js ← parseJson json.out
        let diags := afield js "diagnostics"
        checkEq 1 diags.size
        let span := (field diags[0]! "span").getD .null
        checkEq 2 ((nfield span "startLine").getD 0)
        checkEq 17 ((nfield span "startColumn").getD 0)
        -- `--json` is the older spelling of `--format json`
        let old ← runLint ["lint", "--json", "warn.wiz"] (cwd := some dir)
        checkEq 0 old.code
        checkEq json.out old.out
        -- an unknown format is a usage error
        let bad ← runLint ["lint", "--format", "yaml", "warn.wiz"] (cwd := some dir)
        checkEq 2 bad.code },

    { name := "the golden SARIF document is stable", run := fun _ => do
        let ds ← lint goldenSrc
        checkEq (golden.replace "0.1.0-dev" Wiz.version) (Sarif.render "golden.wiz" goldenSrc ds) },

    { name := "--format text (the default) is unchanged", run := fun _ => do
        let dir ← IO.FS.createTempDir
        IO.FS.writeFile (dir / "warn.wiz") "import Prelude\ndef a : Nat := 1  \n"
        let textual ← runLint ["lint", "warn.wiz"] (cwd := some dir)
        checkEq 0 textual.code
        check (textual.out.startsWith "warn.wiz:2:17: warning: trailing whitespace [style.trailing-whitespace]")
          textual.out
        check ((textual.err.splitOn "ward: 1 warning(s), 0 error(s)").length > 1) textual.err
        let explicit ← runLint ["lint", "--format", "text", "warn.wiz"] (cwd := some dir)
        checkEq textual.out explicit.out }
  ]

builtin_initialize registerGroup lintSarifGroup

end Tests.LintSarif
