import Tests.Harness

/-!
# `wiz test FILE` (stage 11ah)

The single-file test command: the `-- test:` directive (shared with grail's runner in
`Wiz/Test.lean`), the expected output beside the file or on the directive line, and the
`check`/`run` semantics of `wiz check`/`wiz run`.
-/

namespace Tests.WizTest
open Tests

/-- A fresh directory with these files in it. -/
def mkTree (files : List (String × String)) : IO System.FilePath := do
  let dir ← IO.FS.createTempDir
  for (p, text) in files do
    let f := dir / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  pure dir

def wizExe : IO String := do pure (← IO.FS.realPath ".lake/build/bin/wiz").toString

/-- Run this worktree's `wiz` in `dir`. -/
def runWiz (dir : System.FilePath) (args : List String) : IO IO.Process.Output := do
  IO.Process.output { cmd := ← wizExe, args := args.toArray, cwd := some dir }

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- A run test that failed because the machine has no C toolchain (the suite skips it:
a skipped case is not a pass). -/
def noToolchain (o : IO.Process.Output) : Bool :=
  ["gmp.h", "No such file", "not found", "failed to execute"].any (has o.stderr ·)

def group : Group where
  name := "wiz-test"
  exercise := "Stage 11ah"
  cases := [
    { name := "check is the default; FILE.expected is compared, and a missing one fails", run := fun _ => do
        let dir ← mkTree [("clean.wiz", "import Prelude\ndef x : Nat := 1\n"), ("clean.expected", ""),
                          ("info.wiz", "import Prelude\n#eval 1 + 1\n"), ("info.expected", "info.wiz:2:1: info: 2\n"),
                          ("noexp.wiz", "import Prelude\ndef y : Nat := 2\n"),
                          ("bad.wiz", "import Prelude\n#eval 1 + 1\n"), ("bad.expected", "wrong\n")]
        let o ← runWiz dir ["--no-cache", "test", "clean.wiz"]
        checkEq 0 o.exitCode
        checkEq "clean.wiz: passed (check)\n" o.stdout
        checkEq "" o.stderr
        let o ← runWiz dir ["--no-cache", "test", "info.wiz"]
        checkEq 0 o.exitCode
        checkEq "info.wiz: passed (check)\n" o.stdout
        let o ← runWiz dir ["--no-cache", "test", "noexp.wiz"]
        checkEq 1 o.exitCode
        check (has o.stderr "no noexp.expected") s!"stderr: {o.stderr}"
        let o ← runWiz dir ["--no-cache", "test", "bad.wiz"]
        checkEq 1 o.exitCode
        check (has o.stderr "bad.wiz: FAILED (check)") s!"stderr: {o.stderr}"
        check (has o.stderr "line 1:") s!"stderr: {o.stderr}"
        check (has o.stderr "expected: wrong") s!"stderr: {o.stderr}"
        check (has o.stderr "actual:   bad.wiz:2:1: info: 2") s!"stderr: {o.stderr}" },
    { name := "the directive carries the expected output, with escapes", run := fun _ => do
        let dir ← mkTree [
          ("inline.wiz", "-- test: check inline.wiz:3:1: info: 2\\n\nimport Prelude\n#eval 1 + 1\n"),
          ("two.wiz", "-- test: check a\\nb\\n\nimport Prelude\n#eval 1 + 1\n"),
          ("no.wiz", "-- test: check nope\nimport Prelude\n#eval 1 + 1\n")]
        let o ← runWiz dir ["--no-cache", "test", "inline.wiz"]
        checkEq 0 o.exitCode
        checkEq "inline.wiz: passed (check)\n" o.stdout
        -- `\n` splits the expected output over two lines
        let o ← runWiz dir ["--no-cache", "test", "two.wiz"]
        checkEq 1 o.exitCode
        check (has o.stderr "line 1:") s!"stderr: {o.stderr}"
        check (has o.stderr "expected: a") s!"stderr: {o.stderr}"
        check (has o.stderr "actual:   two.wiz:3:1: info: 2") s!"stderr: {o.stderr}"
        let o ← runWiz dir ["--no-cache", "test", "no.wiz"]
        checkEq 1 o.exitCode
        check (has o.stderr "line 1:") s!"stderr: {o.stderr}" },
    { name := "a malformed directive is a failed test; a missing file is a usage error", run := fun _ => do
        let dir ← mkTree [("bad.wiz", "-- test: frobnicate\n")]
        let o ← runWiz dir ["--no-cache", "test", "bad.wiz"]
        checkEq 1 o.exitCode
        check (has o.stderr "unknown test kind frobnicate (check, run)") s!"stderr: {o.stderr}"
        let o ← runWiz dir ["--no-cache", "test", "missing.wiz"]
        checkEq 2 o.exitCode
        check (has o.stderr "wiz test: no such file: missing.wiz") s!"stderr: {o.stderr}" },
    { name := "run: an IO program's output and a value read back, as wiz run prints them", run := fun _ => do
        let dir ← mkTree [
          ("hi.wiz", "-- test: run hi\\n\nimport IO\ndef main : IO Unit := IO.println \"hi\"\n"),
          ("value.wiz", "-- test: run\nimport Prelude\ndef main : Nat := 2 + 2\n"),
          ("value.expected", "4\n")]
        let flags := (← toolchain).toFlags
        let o ← runWiz dir (flags ++ ["--no-cache", "test", "hi.wiz"])
        if o.exitCode != 0 && noToolchain o then skip "no toolchain"; return
        checkEq 0 o.exitCode
        checkEq "hi.wiz: passed (run)\n" o.stdout
        let o ← runWiz dir (flags ++ ["--no-cache", "test", "value.wiz"])
        checkEq 0 o.exitCode
        checkEq "value.wiz: passed (run)\n" o.stdout },
    { name := "run: a program that exits nonzero fails, whatever the expected output", run := fun _ => do
        let dir ← mkTree [
          ("exit.wiz", "-- test: run before\\n\nimport IO\nimport Sys\n" ++
            "def main : IO Unit := do\n  IO.println \"before\";\n  Process.exit 1\n")]
        let o ← runWiz dir ((← toolchain).toFlags ++ ["--no-cache", "test", "exit.wiz"])
        if o.exitCode != 1 && noToolchain o then skip "no toolchain"; return
        checkEq 1 o.exitCode
        check (has o.stderr "exit.wiz: FAILED (run)") s!"stderr: {o.stderr}"
        check (has o.stderr "the program failed (1)") s!"stderr: {o.stderr}" }
  ]

-- (a new group also needs a shard in `.github/test-shards.json`)
builtin_initialize registerGroup group

end Tests.WizTest
