import Tests.StcBridge

/-!
# `=stc-bridge`: the `MTm → F0.Tm` corpus and its report (CORE-1.2)

Runs the checked-in corpus (`Tests/data/stc-bridge/corpus.json`) through
`Tests.StcBridge.go`, compares the deterministic report with
`Tests/data/stc-bridge/report.txt`, and proves the failure path is not vacuous: one case
states a deliberately wrong expectation and requires the resulting failure to name the
class and case id.

The group is excluded from every CI shard until CORE-1.3 wires it into the `stc` job
(`.github/test-shard-exclusions.json`); run it with `lake test -- '=stc-bridge'`.

The report is checked in, so a translation change that moves a case fails twice: the
case's own class/id message, and the report line that changed.
-/

namespace Tests.StcBridge

open Tests (Group)

/-- The checked-in data, relative to the repository root (the test driver's cwd). -/
def dataDir : String := "Tests/data/stc-bridge"

def loadCorpus : IO (List CorpusClass) := do
  let text ← IO.FS.readFile s!"{dataDir}/corpus.json"
  match parseCorpus text with
  | .ok cs => pure cs
  | .error e => throw (IO.userError s!"stc-bridge: {dataDir}/corpus.json: {e}")

/-- The corpus report and the signature report, as the checked-in file spells them. -/
def goldenText (cs : List CorpusClass) : String :=
  (reportOf (CorpusClass.pairs cs)).render ++ "\n" ++
    (sigReport Tests.Elab.MTm.globalDefs).render "MTm.globalDefs" ++ "\n"

def group : Group where
  name := "stc-bridge"
  exercise := "CORE-1.2: the MTm → F0.Tm corpus and its per-class report"
  cases := [
    { name := "every case agrees with the translation and the checked-in report is current",
      run := fun _ => do
        let cs ← loadCorpus
        let rep := reportOf (CorpusClass.pairs cs)
        unless rep.failures.isEmpty do
          throw (IO.userError ("stc-bridge: case failures:\n" ++
            "\n".intercalate (rep.failures.map fun f => "  " ++ f.render)))
        let actual := goldenText cs
        let want ← IO.FS.readFile s!"{dataDir}/report.txt"
        unless actual == want do
          throw (IO.userError
            s!"stc-bridge: {dataDir}/report.txt is stale; the actual report is:\n{actual}") },
    { name := "a deliberately wrong expectation fails, naming the class and the case id",
      run := fun _ => do
        let cs ← loadCorpus
        match wrongExpectation cs with
        | .error e => throw (IO.userError s!"stc-bridge: {e}")
        | .ok f =>
          unless f.klass == Class.qty do
            throw (IO.userError
              s!"stc-bridge: the deliberate failure has class {f.klass.name}, not qty")
          let line := f.render
          unless (line.splitOn f.id).length > 1 do
            throw (IO.userError s!"stc-bridge: the failure does not name its case id: {line}")
          unless (line.splitOn "qty").length > 1 do
            throw (IO.userError s!"stc-bridge: the failure does not name its class: {line}")
          -- the exact line for the record; the driver only shows it if the case fails
          IO.println s!"stc-bridge: deliberate failure: {line}" } ]

end Tests.StcBridge
