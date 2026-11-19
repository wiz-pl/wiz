import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-!
# The top-level examples

`examples/*.wiz` are the programs the stage documents and `docs/tour.md` point at. Most
were run by hand (`wiz check examples/foo.wiz`, `grail test` in the file's directory) but
a golden that no test reads cannot fail: a stale `.expected` was invisible, and a type
error in an example only showed up in `Scaling`'s sweep, which deliberately skipped
errors (item 3 of the 2026-11-17 coverage audit).

This module wires every top-level example into the same mechanism `examples/tour/` uses:
a package of its own holding one `examples/NAME.wiz` and its `.expected`, run by
`runTests` (the `grail test` runner) and required to pass. The `exampleFiles` case is the
registry: a new `examples/*.wiz` must be added to `goldenExamples`, `runExamples` or
`notRunExamples` (with a reason), and every `.expected` must belong to a run file, so a
golden cannot become dead again.

The golden files are `check` output (they include `#eval`/`#reduce` messages; no file
carries a `-- test: run` line), so they pin elaboration and the values examples print,
not a compiled run. `examples/words.wiz` is pinned in the kernel, both interpreters, C and
LLVM by its own case in the `word` group; `examples/plot.wiz` prints a deterministic SVG,
so its golden is `docs/assets/plot-example.svg`.
-/

/-- Every top-level example with a committed `.expected`, run through `grail test`. -/
def goldenExamples : List String :=
  ["church", "classes", "closed-table-bench", "data", "equality", "foreign", "fusion",
   "glue", "hdl-sim-bench", "import_c", "inductive", "macros", "match", "natives-bench",
   "pairs", "procmacro", "run", "sized", "streams", "syntax", "tactics", "words"]

/-- Examples run for their output rather than a `.expected` file: the golden lives
elsewhere and is named here. -/
def runExamples : List (String × String) :=
  [("plot", "its `main` prints the figure; the golden is docs/assets/plot-example.svg")]

/-- Examples deliberately not run, each with the reason. `exampleFiles` fails when a new
file is in none of the lists, so this is the only way to leave one unrun. -/
def notRunExamples : List (String × String) :=
  [("scry-datalog-bench",
    "a benchmark: `main` needs a `chain N`, `tc N` or `ins N` argument and prints elapsed milliseconds, so its output is not deterministic; it is run on demand (see the module doc)")]

/-- Examples another group reads and runs (the HDL, scry, natives and other groups). They
are listed here only so the registry can see that every top-level file has an owner; the
group that runs them stays the one that asserts their behaviour. -/
def coveredElsewhere : List String :=
  ["deriving", "effects", "hardware-tour", "hdl", "hdl-arb-n", "hdl-arty", "hdl-axi4",
   "hdl-bits", "hdl-bus", "hdl-bus-law", "hdl-cdc", "hdl-compose", "hdl-crc", "hdl-display",
   "hdl-gaps", "hdl-match", "hdl-mem", "hdl-mem-laws", "hdl-operators", "hdl-optic",
   "hdl-pipe", "hdl-prim", "hdl-protocols", "hdl-sim", "hdl-sim-theorem", "hdl-spi",
   "hdl-stream", "hdl-temporal", "hdl-uart-temporal", "hdl-verified", "hdl-verified-full",
   "hdl-verified-native", "intern", "io", "persistent", "persistent-bench", "resources",
   "rune-ddr", "rune-spi", "rune-uart", "scry-datalog-constprop", "scry-datalog-lattice",
   "scry-datalog-negation", "scry-datalog-samegen", "scry-datalog-store", "scry-datalog-tc",
   "scry-derivation", "scry-egraph-congruence", "scry-egraph-datalog", "scry-egraph-extract",
   "scry-egraph-fuel", "scry-egraph-rebuild", "scry-egraph-saturate", "std", "wordarray",
   "wordmap"]

/-- One example as `grail test` runs it: the file and its `.expected` in a package whose
tests root is `examples`, so the message paths are the repository's. -/
def goldenCase (name : String) : Case :=
  { name := s!"examples/{name}.wiz", run := fun _ => do
      let p := s!"examples/{name}"
      let dir ← mkTree [
        ("grail.wiz", "import Grail\ndef package : Package := Package.new \"examples\" |> Package.tests \"examples\" \"examples\"\n"),
        (p ++ ".wiz", ← IO.FS.readFile (p ++ ".wiz")),
        (p ++ ".expected", ← IO.FS.readFile (p ++ ".expected"))]
      let tc ← toolchain
      let tc : Toolchain := { tc with cacheDir := some (← tc.cacheDir.getDM IO.FS.createTempDir) }
      let (res, _) ← runTests dir tc
      checkEq 1 res.size
      for t in res do
        if !t.ok && ((t.message.splitOn "gmp.h").length > 1 ||
            (t.message.splitOn "was not preprocessed").length > 1) then
          skip "no C toolchain (cc) to preprocess an import_c header"; return
        check t.ok s!"{t.file}: {t.message}" }

/-- A Wiz string literal for `s` (`#eval` of a `String` compares the value). -/
def wizString (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\t' => "\\t"
    | c => c.toString) "" ++ "\""

/-- `examples/plot.wiz`: its pure `Plot.svg example` is the SVG that
`docs/assets/plot-example.svg` holds (the same bytes the documentation renders), so the
case evaluates and compares the strings (no C toolchain needed). -/
def plotCase : Case :=
  { name := "examples/plot.wiz", run := fun _ => do
      let src ← IO.FS.readFile "examples/plot.wiz"
      let svg ← IO.FS.readFile "docs/assets/plot-example.svg"
      Elab.okLibs (src ++ "\n#eval String.eq (Plot.svg example) " ++ wizString svg.trimAscii.toString ++ "\n")
        [".true"] }

/-- The registry: every `examples/*.wiz` is in exactly one list, and every `.expected`
has a file that is run. -/
def exampleFilesCase : Case :=
  { name := "every top-level example is run or listed with a reason; no dead golden", run := fun _ => do
      let mut wiz : List String := []
      let mut expected : List String := []
      for e in ← System.FilePath.readDir "examples" do
        if e.path.extension == some "wiz" then wiz := e.fileName :: wiz
        if e.path.extension == some "expected" then expected := e.fileName :: expected
      let owned := goldenExamples.map (· ++ ".wiz") ++ runExamples.map (fun (n, _) => n ++ ".wiz")
        ++ notRunExamples.map (fun (n, _) => n ++ ".wiz")
      let elsewhere := coveredElsewhere.map (· ++ ".wiz")
      let all := owned ++ elsewhere
      checkEq wiz.length all.length
      for f in wiz do
        check (all.contains f) s!"examples/{f} is run by no case and is not in notRunExamples"
      for f in owned do
        check (wiz.contains f) s!"{f} is in a list but examples/{f} does not exist"
      for f in elsewhere do
        check (wiz.contains f) s!"{f} is in coveredElsewhere but examples/{f} does not exist"
      let runNames := all.map fun f => f.dropEnd 4 |>.toString
      for f in expected do
        check (runNames.contains (f.dropEnd 9 |>.toString))
          s!"examples/{f} is a golden that no test reads"
      for n in goldenExamples do
        check (expected.contains (n ++ ".expected")) s!"examples/{n}.expected is missing" }

def exampleGroup : Group where
  name := "examples"
  exercise := "the stage documents' top-level examples (examples/*.wiz)"
  cases :=
    goldenExamples.map goldenCase ++ [plotCase, exampleFilesCase]

builtin_initialize registerGroup exampleGroup

end Tests.Grail
