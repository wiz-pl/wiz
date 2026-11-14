import Grail.Config

/-!
# `grail new`: package templates

`grail new NAME [--template lib|exe|hdl] [--dir DIR]` writes a small package that
builds, runs (where it has a program) and tests. Three templates:

* `lib`: a library under `src/` and golden tests under `tests/`;
* `exe` (the default): a library, an executable over `src/Main.wiz`, and golden tests;
* `hdl`: an HDL design, a program that prints its Verilog, board constraints, and the
  usual (manual) synthesis/flash commands, plus a simulation test.

Every template also writes a README with its exact tree and a `.gitignore` for
`.grail/` (and `build/` for `hdl`). `new` refuses a directory that is not empty and
checks the name, which becomes the package's name, its targets' names and the default
directory. See docs/stages/23-grail.md, 23o.
-/

namespace Grail
open Wiz

/-- A usable package name: a letter, then letters, digits, `_` or `-`, at most 64
characters. (It is the name in `grail.wiz` and its targets, the default directory and
the program's greeting.) -/
def validPackageName (name : String) : Bool :=
  let cs := name.toList
  !cs.isEmpty && cs.length ≤ 64 &&
  (match cs.head? with | some c => c.isAlpha | none => false) &&
  cs.all fun c => c.isAlpha || c.isDigit || c == '_' || c == '-'

/-- The package templates `grail new` writes. -/
inductive Template where
  | lib
  | exe
  | hdl
  deriving BEq, Repr, Inhabited

/-- A template's name on the command line (`--template`) and in messages. -/
def Template.name : Template → String
  | .lib => "lib"
  | .exe => "exe"
  | .hdl => "hdl"

/-- The templates the usage documents. -/
def Template.names : String := "lib, exe, hdl"

/-- Read a `--template` value. The long names are accepted as aliases. -/
def Template.ofName : String → Option Template
  | "lib" | "library" => some .lib
  | "exe" | "executable" => some .exe
  | "hdl" | "board" => some .hdl
  | _ => none

/-- A file's text from its lines, each ending in a newline. -/
def newFile (ls : List String) : String := "\n".intercalate ls ++ "\n"

/-- The generated `grail.wiz` for `exe`: a library over `src/`, an executable for
`src/Main.wiz` and the golden tests under `tests/`. -/
def newBuildFile (name : String) : String := newFile [
  "import Grail",
  "",
  "/-!",
  s!"# {name}",
  "",
  s!"`grail build` builds the library and the executable, `grail run {name}` runs it and",
  "`grail test` runs the tests under `tests/`. Add targets with `Package.lib`,",
  "`Package.exe`, `Package.tests` and `Package.command` (see lib/Grail.wiz).",
  "-/",
  "",
  "def package : Package :=",
  s!"  Package.new \"{name}\"",
  s!"    |> Package.lib \"{name}-lib\" \"src\"",
  s!"    |> Package.exe \"{name}\" \"src/Main.wiz\"",
  "    |> Package.tests \"tests\" \"tests\""]

/-- The generated `src/Main.wiz`: the smallest program. -/
def newMainFile (name : String) : String := newFile [
  "import Std",
  "",
  "/-- The program `grail run " ++ name ++ "` runs. -/",
  "def main : IO Unit := do",
  s!"  IO.println \"hello from {name}\""]

/-- The generated `tests/hello.wiz`: a `-- test: run` golden test. -/
def newTestFile (name : String) : String := newFile [
  "-- test: run",
  "-- A golden test: `grail test` runs `main` and compares its output with hello.expected.",
  "import Std",
  "",
  "def main : IO Unit := do",
  s!"  IO.println \"hello from {name}\""]

/-- The generated `grail.wiz` for `lib`: a library over `src/` and the golden tests
under `tests/`. -/
def newLibBuildFile (name : String) : String := newFile [
  "import Grail",
  "",
  "/-!",
  s!"# {name}",
  "",
  s!"`grail build` checks the library under `src/`; `grail test` builds and runs the",
  "golden tests under `tests/`. Add targets with `Package.lib`,",
  "`Package.exe`, `Package.tests` and `Package.command` (see lib/Grail.wiz).",
  "-/",
  "",
  "def package : Package :=",
  s!"  Package.new \"{name}\"",
  s!"    |> Package.lib \"{name}-lib\" \"src\"",
  s!"    |> Package.tests \"{name}-tests\" \"tests\""]

/-- The generated `src/Greeting.wiz`: the library's one definition. -/
def newGreetingFile (name : String) : String := newFile [
  "import Prelude",
  "",
  "/-- The library's greeting: what `tests/greeting.wiz` prints. -/",
  s!"def greeting : String := \"hello from {name}\""]

/-- The generated `tests/greeting.wiz`: a `-- test: run` golden test of the library. -/
def newLibTestFile : String := newFile [
  "-- test: run",
  "-- A golden test: `grail test` runs `main` and compares its output with greeting.expected.",
  "import Std",
  "import Greeting",
  "",
  "def main : IO Unit := do",
  "  IO.println greeting"]

/-- The generated `grail.wiz` for `hdl`: the design, a Verilog generator, the board
constraints and the synthesis pipeline (the external tools' commands are manual, so a
bare `grail build` needs none of them). -/
def newHdlBuildFile (name : String) : String := newFile [
  "import Grail",
  "",
  "/-!",
  s!"# {name}",
  "",
  "`grail build` checks the design under `src/`, builds the Verilog generator and",
  "writes `build/top.v`; `grail test` builds and runs the simulation test. The synthesis",
  "steps are manual: `grail build synth` (yosys), `place` (nextpnr-ice40), `pack`",
  "(icepack), and `grail build flash` (iceprog, phony) programs the board.",
  "-/",
  "",
  "def package : Package :=",
  s!"  Package.new \"{name}\"",
  "    |> Package.set \"libs\" \"-lm\"",
  s!"    |> Package.lib \"{name}-lib\" \"src\"",
  s!"    |> Package.exe \"{name}-verilog\" \"app/Verilog.wiz\"",
  s!"    |> Package.tests \"{name}-tests\" \"tests\"",
  "    |> Package.command (Command.new \"verilog\" (Tool.exe \"" ++ name ++ "-verilog\")",
  "         |> Command.stdout \"build/top.v\")",
  "    |> Package.command (Command.new \"synth\" (Tool.path \"yosys\")",
  "         |> Command.arg \"-q\" |> Command.arg \"-p\"",
  "         |> Command.parts [Part.text \"synth_ice40 -top top -json \", Part.output \"build/top.json\"]",
  "         |> Command.input \"build/top.v\" |> Command.needs \"board/pins.pcf\"",
  "         |> Command.manual)",
  "    |> Package.command (Command.new \"place\" (Tool.path \"nextpnr-ice40\")",
  "         |> Command.arg \"--hx1k\" |> Command.arg \"--package\" |> Command.arg \"tq144\"",
  "         |> Command.arg \"--json\" |> Command.input \"build/top.json\"",
  "         |> Command.arg \"--pcf\" |> Command.input \"board/pins.pcf\"",
  "         |> Command.arg \"--asc\" |> Command.output \"build/top.asc\"",
  "         |> Command.manual)",
  "    |> Package.command (Command.new \"pack\" (Tool.path \"icepack\")",
  "         |> Command.input \"build/top.asc\" |> Command.output \"build/top.bin\"",
  "         |> Command.manual)",
  "    |> Package.phony (Command.new \"flash\" (Tool.path \"iceprog\")",
  "         |> Command.input \"build/top.bin\")"]

/-- The generated `src/Counter.wiz`: a four-bit counter, the board's LEDs. -/
def newHdlCounterFile : String := newFile [
  "import Hdl.Core",
  "",
  "/-- The board's output: four LEDs showing the count. -/",
  "structure Count (r : HwTy → Type) where",
  "  count : r (HwTy.bits 4)",
  "  deriving Bundle",
  "",
  "/-- A four-bit counter: `count` is the value before this cycle's increment. -/",
  "def counter : Circuit (HwTy.bits 0) Count.code :=",
  "  Circuit.mk (HwTy.bits 4) (BitVec.ofNat 4 0)",
  "    (fun s _ => Hw.pair (Hw.add s (Hw.lit 4 1)) (Count.pack (Count.mk s)))"]

/-- The generated `app/Verilog.wiz`: print the design's Verilog (the `verilog` command
redirects it to `build/top.v`). -/
def newHdlVerilogFile : String := newFile [
  "import Std",
  "import Hdl.Core",
  "import Counter",
  "",
  "/-- Print the synthesizable Verilog for `counter`. -/",
  "def main : IO Unit :=",
  "  IO.print (Verilog.emit (Circuit.netlist \"top\" counter))"]

/-- The generated `board/pins.pcf`: iCEstick-like pin constraints for `clk` and the four
`count` bits. (Edit this for another board.) -/
def newHdlPinsFile : String := newFile [
  "-- Pin constraints for the `top` netlist (nextpnr-ice40's PCF format).",
  "-- These are iCEstick-like pins: edit them for your board.",
  "set_io clk 21",
  "set_io count[0] 99",
  "set_io count[1] 98",
  "set_io count[2] 97",
  "set_io count[3] 96"]

/-- The generated `tests/counter.wiz`: simulate three cycles and print their sum. -/
def newHdlTestFile : String := newFile [
  "-- test: run",
  "-- A golden test: three cycles of the counter sum to 0 + 1 + 2.",
  "import Std",
  "import Hdl.Core",
  "import Counter",
  "",
  "def main : IO Unit := do",
  "  IO.println (Hdl.show (Hdl.sum (Circuit.runPacked counter [0, 0, 0])))"]

/-- The generated README of a package, with its exact tree. -/
def newReadme (name : String) (template : Template) : String :=
  let (tree, how) : List String × List String := match template with
    | .lib => ([
        s!"{name}/",
        "  grail.wiz",
        "  src/Greeting.wiz",
        "  tests/greeting.wiz",
        "  tests/greeting.expected",
        "  README.md",
        "  .gitignore"], [
        "grail build        # check the library",
        "grail test         # build and run the golden test"])
    | .exe => ([
        s!"{name}/",
        "  grail.wiz",
        "  src/Main.wiz",
        "  tests/hello.wiz",
        "  tests/hello.expected",
        "  README.md",
        "  .gitignore"], [
        "grail build        # build the library and the executable",
        s!"grail run {name}   # run the executable",
        "grail test         # build and run the golden test"])
    | .hdl => ([
        s!"{name}/",
        "  grail.wiz",
        "  src/Counter.wiz",
        "  app/Verilog.wiz",
        "  board/pins.pcf",
        "  tests/counter.wiz",
        "  tests/counter.expected",
        "  README.md",
        "  .gitignore"], [
        "grail build        # check the design, build the Verilog generator, write build/top.v",
        "grail test         # build and run the simulation test",
        "grail build synth  # yosys: build/top.json (needs yosys)",
        "grail build place  # nextpnr-ice40: build/top.asc",
        "grail build pack   # icepack: build/top.bin",
        "grail build flash  # iceprog: program the board (phony)"])
  let intro := match template with
    | .lib => "A Wiz library made with `grail new --template lib`."
    | .exe => "A Wiz package made with `grail new`."
    | .hdl => "An HDL package made with `grail new --template hdl`."
  newFile ([
    s!"# {name}",
    "",
    intro,
    "",
    "Tree:",
    "",
    "```",
    ] ++ tree ++ [
    "```",
    "",
    "```sh"] ++ how ++ [
    "```",
    "",
    "`grail.wiz` is the build file: add targets (a `lib` per module root, an `exe` per",
    "program, `tests` per directory of golden tests, or a `command`) there.",
    "",
    "Machine settings (where GMP and the C compiler live) go in an uncommitted",
    "`grail.local.wiz`; `nix develop` writes one. `.grail/` is the build's store and is",
    "ignored by git."])

/-- The files (path, text) of one template. -/
def templateFiles (name : String) (template : Template) : List (String × String) :=
  match template with
  | .lib => [
      ("grail.wiz", newLibBuildFile name),
      ("src/Greeting.wiz", newGreetingFile name),
      ("tests/greeting.wiz", newLibTestFile),
      ("tests/greeting.expected", s!"hello from {name}\n"),
      ("README.md", newReadme name .lib),
      (".gitignore", ".grail/\n")]
  | .exe => [
      ("grail.wiz", newBuildFile name),
      ("src/Main.wiz", newMainFile name),
      ("tests/hello.wiz", newTestFile name),
      ("tests/hello.expected", s!"hello from {name}\n"),
      ("README.md", newReadme name .exe),
      (".gitignore", ".grail/\n")]
  | .hdl => [
      ("grail.wiz", newHdlBuildFile name),
      ("src/Counter.wiz", newHdlCounterFile),
      ("app/Verilog.wiz", newHdlVerilogFile),
      ("board/pins.pcf", newHdlPinsFile),
      ("tests/counter.wiz", newHdlTestFile),
      ("tests/counter.expected", "3\n"),
      ("README.md", newReadme name .hdl),
      (".gitignore", ".grail/\nbuild/\n")]

/-- Write the package `name` into `dir` with `template`. An existing empty directory is
used, anything else is refused (never overwritten). -/
def newPackage (name : String) (dir : System.FilePath) (template : Template := .exe) :
    IO (Except String Unit) := do
  unless validPackageName name do
    return .error s!"grail new: '{name}' is not a package name (a letter, then letters, digits, '_' or '-', at most 64)"
  if ← dir.pathExists then
    unless ← dir.isDir do
      return .error s!"grail new: {dir} exists and is not a directory"
    unless (← dir.readDir).isEmpty do
      return .error s!"grail new: {dir} is not empty (grail new never overwrites; pick another NAME or --dir)"
  IO.FS.createDirAll dir
  for (path, text) in templateFiles name template do
    let f := dir / path
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  return .ok ()

/-- What to run in a fresh package of this template. -/
def newAdvice (name : String) (template : Template) : String :=
  match template with
  | .lib => "grail build && grail test"
  | .exe => s!"grail build && grail run {name}"
  | .hdl => "grail build && grail test"

end Grail
