import Wiz
import Tests.Harness
import Tests.Elab

/-!
# The `.cs` pipeline: C/C# parity and the real budget fields

`scry taint FILE.cs` and `scry taint FILE.c` run one analysis tail
(`Scry.analyzeLowered`). This group pins that:

* on two equivalent fixtures (the checked-in C `tests/fixtures/taint-unsafe.c` and
  `corpus/csharp/parity/taint-unsafe.cs`, whose sink is on the same line and column),
  the two frontends find the same rule and sink location and derive the same certificate
  status. The functions, messages and sink argument differ by language and are not
  compared (the rule pack names each language's source/sink);
* `--max-rounds` is honoured by both frontends: the report is `truncated`, names the
  bound it used, and carries a `scry/budget/summaries-incomplete` note — no placeholder
  `summaryRounds = 1` / `summaryComplete = true`;
* `--null-deref` is honoured by the `.cs` frontend: the nullness pass adds its
  `scry/memory/null-dereference` diagnostic.

The cases use checked-in `scry-cst` spills (the same boundary the existing C# tests use),
so they need the C toolchain for the one probe program but not the native parser. The probe
itself is `corpus/csharp/parity/pipeline-probe.wiz`, read at run time so a fixture change
does not need a Lean rebuild.
-/

open Wiz

namespace Tests.ScryCs

/-- One compiled probe for the whole group (a compile per case would be waste). The
probe imports the Scry package, so it uses `Tests.scryLoader` rather than `Elab.cRunLibs`
(whose loader serves only `lib/`). -/
def runProbe : IO Unit := do
  let src ← IO.FS.readFile "scry/corpus/csharp/parity/pipeline-probe.wiz"
  let loader ← Tests.scryLoader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← Tests.toolchain) s "main" dir false (timeout := some 1500) with
  | .ok out => checkEq "" out
  | .error e => if e.isToolchain then skip "no toolchain" else Elab.failRun e

def group : Group where
  name := "scry-cs"
  exercise := "scry .cs pipeline: C/C# parity, --max-rounds and --null-deref"
  parallel := true
  shard := "library"
  cases := [
    { name := "parity, budget fields and null-deref on checked-in spills", run := fun _ => runProbe }
  ]

builtin_initialize registerGroup group

end Tests.ScryCs
