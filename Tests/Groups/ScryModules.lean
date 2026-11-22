import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# The Scry modules that the analysis groups do not name

`scry-taint`, `scry-datalog` and friends go through `Scry.*`'s analysis entry points;
`Scry.Report` (pure HTML) and `Scry.Optics` (the read-only accessor layer) had no case
that reads them at all — `Scaling.allLibSource` only compiled them (the 2026-11-17
coverage audit, §2 and §7). `scry/tests/report-pure.wiz` exists but lives in the scry
package, whose `grail test` CI job is not in this tree, so its escaping and determinism
assertions were not run by anything here. This group runs both through the library
loader, so a change to either module runs the behavioural case.
-/

/-- `scry/src/Scry/Report.wiz`: the pure half of the HTML report. The assertions are the scry
package's own `scry/tests/report-pure.wiz` (XSS escaping, no remote resource, stable
bytes, anchors), evaluated through their definitions rather than by running `main`, so
no C toolchain is needed. `report-pure.expected` is the same list as the file's `check`
calls, kept here next to the case. -/
def scryReportCase : Case :=
  { name := "Scry.Report: HTML escaping, no remote resource, deterministic (scry/tests/report-pure.wiz)",
    run := fun _ => do
      let src ← IO.FS.readFile "scry/tests/report-pure.wiz"
      okLibs (src ++ "\n" ++
        "#eval Scry.htmlEscape \"<script>\"\n" ++
        "#eval Scry.htmlEscape \"a&b\\\"c'd\"\n" ++
        "#eval Scry.htmlEscape \"</style>\"\n" ++
        "#eval String.contains page \"<script\"\n" ++
        "#eval String.contains page \"&lt;script&gt;\"\n" ++
        "#eval String.contains page \"&lt;/style&gt;\"\n" ++
        "#eval String.contains page \"x&amp;y\"\n" ++
        "#eval String.contains page \"&quot;&lt;script&gt;\"\n" ++
        "#eval String.contains page \"class=\\\"sink\\\"\"\n" ++
        "#eval String.contains page \"step-tag\\\">1 source\"\n" ++
        "#eval String.contains page \"step-tag\\\">2 sink\"\n" ++
        "#eval String.contains page \"source &rarr; sink\"\n" ++
        "#eval String.contains page \"CWE-78 (T1)\"\n" ++
        "#eval String.contains page \"http://\"\n" ++
        "#eval String.contains page \"https://\"\n" ++
        "#eval String.eq page (Scry.renderReport (Scry.ReportMeta.mk \"scry test\" \"\") (.cons sourceFile .nil))\n")
        ["\"&lt;script&gt;\"", "\"a&amp;b&quot;c&#39;d\"", "\"&lt;/style&gt;\"",
         ".false", ".true", ".true", ".true", ".true", ".true", ".true", ".true",
         ".true", ".true", ".false", ".false", ".true"] }

/-- `scry/src/Scry/Optics.wiz`: the pure `Lens`/`Traversal` layer. The laws are proved in the
module; this evaluates them on a `Wil.Stmt`, so `get`, `set` and `over` actually run. -/
def scryOpticsCase : Case :=
  { name := "Scry.Optics: a statement's origin lens gets, sets and maps", run := fun _ =>
      okLibs ("import Scry.Optics\n" ++
        "def s : Wil.Stmt := .nop (Wil.Span.mk 1 2 3 4 5 6)\n" ++
        "def o : Wil.Span := Wil.Span.mk 7 8 9 10 11 12\n" ++
        "def bump (p : Wil.Span) : Wil.Span := Wil.Span.mk p.file (Nat.add p.start 10) p.stop p.node p.line p.col\n" ++
        "#eval (Scry.Lens.get Scry.Wil.stmtOriginL s).start\n" ++
        "#eval (Scry.Lens.get Scry.Wil.stmtOriginL (Scry.Lens.set Scry.Wil.stmtOriginL o s)).start\n" ++
        "#eval (Scry.Lens.get Scry.Wil.stmtOriginL (Scry.Lens.over Scry.Wil.stmtOriginL bump s)).start\n" ++
        "#eval (Scry.Lens.get Scry.Wil.stmtOriginL (Scry.Lens.over Scry.Wil.stmtOriginL (fun p => p) s)).stop\n" ++
        "#eval (Scry.Lens.get Scry.Wil.stmtOriginL (Scry.Lens.set Scry.Wil.stmtOriginL o s)).stop")
        ["2", "8", "12", "3", "9"] }

def scryModulesGroup : Group where
  name := "scry-modules"
  exercise := "S1/S4: scry/src/Scry/Report.wiz and scry/src/Scry/Optics.wiz"
  cases := [scryReportCase, scryOpticsCase]

builtin_initialize registerGroup scryModulesGroup

end Tests.Elab
