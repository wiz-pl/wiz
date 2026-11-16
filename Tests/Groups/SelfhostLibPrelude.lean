import Tests.Groups.SelfhostCliDiff

open Wiz

set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# The self-hosted backend on the library prelude (`--prelude-from-roots`)

With `--prelude-from-roots -I lib` the self-hosted toolchain checks a program against
the real `lib/Prelude.wiz` (and `IO`, `Std`) instead of its embedded prelude, and its
backend (`selfhost/Backend.wiz`, `libPrelude`) compiles what that prelude declares: the
`builtin` registrations are the runtime's natives, an `extern` of a native's name is
the native, `IO`'s pair is a `Σ` (`WIZ_IO_PAIR`), and only what `main` reaches is
compiled. Each case runs a program with the Lean-hosted `wiz run` (its own `lib`) and
with the self-hosted driver on the repository's `lib`, and compares the output and the
exit code; the error cases check that the self-hosted backend refuses what it can't
compile with a message naming it.
-/

/-- The driver's flags for the library prelude: the toolchain, then the roots. -/
def libPreludeArgs (shOpts : Array String) : IO (Array String) := do
  let lib := (← IO.currentDir) / "lib"
  pure (shOpts ++ #["--prelude-from-roots", "-I", lib.toString])

/-- `run` a program with both toolchains (the self-hosted one with `extra` after the
library prelude's flags) and compare the output and exit code with `want`. -/
def libPreludeRun (exe : System.FilePath) (shOpts : Array String) (prog want : String)
    (extra : Array String := #[]) : IO Unit := do
  let host ← cliDiffHost
  let tc ← cliDiffHostToolchain
  let sh ← libPreludeArgs shOpts
  let spec : CliDiffSpec := { files := #[("prog.wiz", prog)], args := #["run", "prog.wiz"]
                              hostArgs := tc, shArgs := sh ++ extra }
  let (h, s) ← cliDiffBoth host exe spec
  checkEq 0 h.code
  checkEq want h.out
  if s.code != 0 then throw (IO.userError s!"self-hosted run failed ({s.code}):\n{s.err}")
  checkEq want s.out

def libPreludeHello : String := "import IO
def main : IO Unit := do
  IO.println \"hello\";
  IO.println (Nat.toString (2 + 3 * 4));
  IO.println (Nat.toString (100 / 7 % 5))
"

def libPreludeData : String := "import IO
def sumTo : Nat → Nat
  | .zero => 0
  | .succ n => Nat.succ n + sumTo n
def xs : List Nat := List.cons 1 (List.cons 2 (List.cons 3 List.nil))
def main : IO Unit := do
  IO.println (String.append \"sum \" (Nat.toString (sumTo 100)));
  IO.println (Nat.toString (List.length (List.append xs xs)));
  IO.println (Nat.toString (Nat.land 12 10))
"

def libPreludeArgsProg : String := "import IO
def main : IO Unit := do
  args ← IO.args;
  IO.println (Nat.toString (List.length args))
"

def libPreludeStr : String := "import Std
def main : IO Unit := do
  IO.println (Str.toString (Str.append (Str.ofString \"ab\") (Str.ofString \"cd\")));
  IO.println (Nat.toString (Str.size (Str.ofString \"abcd\")));
  IO.println (Nat.toString (Str.byte (Str.ofString \"abcd\") 2))
"

/-- An `extern` of a runtime function the self-hosted runtime (`rt.c`) lacks. -/
def libPreludeMissing : String := "import IO
extern \"wiz_sys_errno\" myErrno : IO Nat
def main : IO Unit := do
  n ← myErrno;
  IO.println (Nat.toString n)
"

/-- An `extern` of a native's name whose shape is not the native's. -/
def libPreludeMismatch : String := "import Prelude
extern \"wiz_nat_show\" Nat.toString : Nat → Nat → String
def main : Nat := 0
"

/-- The 63-bit natives against the host's unbounded `Nat`: `2 ^ 64`, the bound
`Float64.ofNat`/`UInt64.ofNat` (lib/IO.wiz) compare with, and a `Float64.ofNat` that
takes the wrong branch because of it but happens to round to the same value. -/
def libPreludeWide : String := "import IO
def showB (x : Bool) : String := match x with
  | .true => \"true\"
  | .false => \"false\"
def main : IO Unit := do
  IO.println (Nat.toString (Nat.pow 2 64));
  IO.println (showB (Nat.lt 3 18446744073709551616));
  IO.println (Float64.toString (Float64.ofNat 3))
"

def libPreludeGroup : Group where
  name := "selfhost-lib-prelude"
  exercise := "stage 21 (A14): the self-hosted backend on lib/Prelude.wiz"
  shard := "selfhost"
  cases := [
    { name := "run: IO, numerals and the binop operators print as on the host", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some shOpts => withSelfhostCli fun exe =>
          libPreludeRun exe shOpts libPreludeHello "hello\n14\n4\n" },
    { name := "run: the same under reference counting (--rc)", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some shOpts => withSelfhostCli fun exe =>
          libPreludeRun exe shOpts libPreludeHello "hello\n14\n4\n" #["--rc"] },
    { name := "run: recursion, lists, strings and a native bit operation", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some shOpts => withSelfhostCli fun exe =>
          libPreludeRun exe shOpts libPreludeData "sum 5050\n6\n8\n" },
    { name := "run: IO.args (lib's IO.argsFrom over the natives)", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some shOpts => withSelfhostCli fun exe =>
          libPreludeRun exe shOpts libPreludeArgsProg "0\n" },
    { name := "run: Std's Str externs (the runtime's wiz_str_*)", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some shOpts => withSelfhostCli fun exe => do
          libPreludeRun exe shOpts libPreludeStr "abcd\n4\n99\n"
          libPreludeRun exe shOpts libPreludeStr "abcd\n4\n99\n" #["--rc"] },
    { name := "run: the 63-bit natives diverge from the host at 2^64 (pinned)", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some shOpts => withSelfhostCli fun exe => do
          let host ← cliDiffHost
          let tc ← cliDiffHostToolchain
          let sh ← libPreludeArgs shOpts
          let spec : CliDiffSpec := { files := #[("prog.wiz", libPreludeWide)], args := #["run", "prog.wiz"]
                                      hostArgs := tc, shArgs := sh }
          let (h, s) ← cliDiffBoth host exe spec
          checkEq 0 h.code
          checkEq 0 s.code
          -- A known divergence, asserted as it is (the case passes): the self-hosted
          -- runtime's Nat is a 63-bit word that wraps, so 2^64 is 0 and lib/IO's
          -- `Float64.ofNat`/`UInt64.ofNat` bound checks (`n < 2^64`) are false for every
          -- n; small values still agree by luck (an open issue, see the PR). When the
          -- runtime's numbers become unbounded, the second assertion fails: update it.
          let hl := h.out.splitOn "\n"
          let sl := s.out.splitOn "\n"
          checkEq ["18446744073709551616", "true"] (hl.take 2)
          checkEq ["0", "false"] (sl.take 2)
          checkEq (hl.drop 2) (sl.drop 2) },
    { name := "build: an extern of a wiz_ function rt.c lacks is an error naming it", run := fun _ => withSelfhostCli fun exe => do
        let sh ← libPreludeArgs #[]
        let dir ← cliDiffInit #[("prog.wiz", libPreludeMissing)]
        let s ← cliDiffExec exe dir sh #["build", "prog.wiz", "-o", "prog.c"]
        let c ← IO.FS.readFile (dir / "prog.c")
        cliCheck (s.err ++ c) "#error extern \"wiz_sys_errno\" myErrno: the self-hosted runtime (selfhost/rt.c) has no wiz_sys_errno" "the refusal" },
    { name := "build: an extern of a native's name with another shape is an error naming both", run := fun _ => withSelfhostCli fun exe => do
        let sh ← libPreludeArgs #[]
        let dir ← cliDiffInit #[("prog.wiz", libPreludeMismatch)]
        let s ← cliDiffExec exe dir sh #["build", "prog.wiz", "-o", "prog.c"]
        let c ← IO.FS.readFile (dir / "prog.c")
        cliCheck (s.err ++ c) "is the runtime's native Nat.toString of 1 argument" "the refusal" }
  ]

builtin_initialize registerGroup libPreludeGroup
