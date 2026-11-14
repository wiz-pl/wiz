import Grail.Config

/-!
# `grail new`: a minimal package

`grail new NAME [--dir DIR]` writes the smallest package that builds, runs and tests:
a `grail.wiz` with a `lib` target, an `exe` and a `tests` target, `src/Main.wiz`
(which imports `Std` and prints a line), a golden test under `tests/`, a README and a
`.gitignore` for `.grail/`. It refuses to write into a directory that is not empty and
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

/-- A file's text from its lines, each ending in a newline. -/
def newFile (ls : List String) : String := "\n".intercalate ls ++ "\n"

/-- The generated `grail.wiz`: a library over `src/`, an executable for `src/Main.wiz`
and the golden tests under `tests/`. -/
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

/-- The generated `README.md`. -/
def newReadme (name : String) : String := newFile [
  s!"# {name}",
  "",
  s!"A Wiz package made with `grail new`. `src/` is the library (`{name}-lib`) and",
  s!"`src/Main.wiz` its executable; `tests/` holds golden tests.",
  "",
  "```sh",
  "grail build        # build the library, the executable and the tests' programs",
  s!"grail run {name}   # run the executable",
  "grail test         # run the golden tests",
  "```",
  "",
  "`grail.wiz` is the build file: add targets (a `lib` per module root, an `exe` per",
  "program, `tests` per directory of golden tests, or a `command`) there.",
  "",
  "Machine settings (where GMP and the C compiler live) go in an uncommitted",
  "`grail.local.wiz`; `nix develop` writes one. `.grail/` is the build's store and is",
  "ignored by git."]

/-- Write the package `name` into `dir`. An existing empty directory is used, anything
else is refused (never overwritten). -/
def newPackage (name : String) (dir : System.FilePath) : IO (Except String Unit) := do
  unless validPackageName name do
    return .error s!"grail new: '{name}' is not a package name (a letter, then letters, digits, '_' or '-', at most 64)"
  if ← dir.pathExists then
    unless ← dir.isDir do
      return .error s!"grail new: {dir} exists and is not a directory"
    unless (← dir.readDir).isEmpty do
      return .error s!"grail new: {dir} is not empty (grail new never overwrites; pick another NAME or --dir)"
  IO.FS.createDirAll dir
  IO.FS.createDirAll (dir / "src")
  IO.FS.createDirAll (dir / "tests")
  IO.FS.writeFile (dir / "grail.wiz") (newBuildFile name)
  IO.FS.writeFile (dir / "src" / "Main.wiz") (newMainFile name)
  IO.FS.writeFile (dir / "tests" / "hello.wiz") (newTestFile name)
  IO.FS.writeFile (dir / "tests" / "hello.expected") s!"hello from {name}\n"
  IO.FS.writeFile (dir / "README.md") (newReadme name)
  IO.FS.writeFile (dir / ".gitignore") ".grail/\n"
  return .ok ()

end Grail
