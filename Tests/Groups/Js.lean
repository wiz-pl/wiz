import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Is `node` on the PATH? The JS backend's smoke tests run the emitted module under it. -/
def jsNodeAvailable : IO Bool := do
  -- (`lake test` runs with Lean's LD_LIBRARY_PATH, whose libgcc shadows the system's for
  -- Node: run Node without it)
  try
    let out ← IO.Process.output { cmd := "node", args := #["--version"], env := #[("LD_LIBRARY_PATH", none)] }
    pure (out.exitCode == 0)
  catch _ => pure false

/-- The runtime shim the emitted module pastes in. A checkout has it at `web/`; a test
without it skips rather than pretends. -/
def jsRuntimeText : IO String := do
  let p : System.FilePath := "web" / "wiz-js-runtime.mjs"
  unless ← p.pathExists do throw (IO.userError "no web/wiz-js-runtime.mjs")
  IO.FS.readFile p

/-- Elaborate a source with the test library and compile `main` to an ES module. -/
def jsCompile (src : String) : IO (CommandState ZeroOneMany × Term ZeroOneMany × String) := do
  let s := runFrontend (R := ZeroOneMany) src { loader := ← libLoader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let (decls, ty) ← match Build.irProgram s "main" with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let runtime ← jsRuntimeText
  let text ← match Js.program runtime decls (Build.isIO ty) with
    | .ok t => pure t
    | .error e => throw (IO.userError e)
  -- the generated module is an ES module with a `main` export
  unless (text.splitOn "export function main").length > 1 do
    throw (IO.userError "the emitted module has no `main` export")
  pure (s, ty, text)

/-- Write a module to a scratch file and run it with Node; its standard output. -/
def jsRunText (text : String) : IO String := do
  let dir ← IO.FS.createTempDir
  let file := dir / "wiz_main.mjs"
  IO.FS.writeFile file text
  let out ← IO.Process.output
    { cmd := "node", args := #[file.toString], env := #[("LD_LIBRARY_PATH", none)] }
  if out.exitCode != 0 then
    throw (IO.userError s!"the JS program failed ({out.exitCode}): {out.stderr.take 1500}")
  pure out.stdout

/-- The interpreter's answer for `main`: append `#eval main` and take its one info
message. This is the oracle for a pure `main` (C/Wasm/JS must print the same tree). -/
def jsNative (src : String) : IO String := do
  let s := runFrontend (R := ZeroOneMany) (src ++ "\n#eval main\n")
    { loader := ← libLoader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let infos := (s.messages.toList.filter (·.severity == .info)).map (·.text)
  match infos with
  | [v] => pure v
  | _ => throw (IO.userError s!"the interpreter produced {infos.length} results: {infos}")

/-- A golden test: the emitted module and the interpreter run the same `main`, and their
results (read back with `main`'s type) must be equal. -/
def jsGolden (src : String) : IO Unit := do
  unless ← jsNodeAvailable do skip "no node"; return
  let expected ← jsNative src
  let (s, ty, text) ← jsCompile src
  let out ← jsRunText text
  match Build.parseValue out with
  | none => throw (IO.userError s!"could not read the result: {out}")
  | some v => checkEq expected (readback s.globals s.builtins (eval s.globals [] ty) v).pretty

/-- A pure result whose `#eval` cannot run (a native such as `UInt64`), against an
explicit expected value. -/
def jsRun (src expected : String) : IO Unit := do
  unless ← jsNodeAvailable do skip "no node"; return
  let (s, ty, text) ← jsCompile src
  let out ← jsRunText text
  match Build.parseValue out with
  | none => throw (IO.userError s!"could not read the result: {out}")
  | some v => checkEq expected (readback s.globals s.builtins (eval s.globals [] ty) v).pretty

/-- An `IO` program prints for itself; compare its standard output (the interpreter
cannot run the foreign functions). -/
def jsStdout (src expected : String) : IO Unit := do
  unless ← jsNodeAvailable do skip "no node"; return
  let (_, _, text) ← jsCompile src
  let out ← jsRunText text
  checkEq expected out

/-- The JS backend's error for a program, if it rejects it. -/
def jsError (src : String) : IO String := do
  let s := runFrontend (R := ZeroOneMany) src { loader := ← libLoader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let (decls, ty) ← match Build.irProgram s "main" with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let runtime ← jsRuntimeText
  match Js.program runtime decls (Build.isIO ty) with
  | .ok _ => throw (IO.userError "the JS backend accepted the program")
  | .error e => pure e

/-- The emitted module text, without running it (determinism and the runtime exports). -/
def jsEmit (src : String) : IO String := do
  let (_, _, text) ← jsCompile src
  pure text

/-- Build `main` through C (`wiz run`'s path) and through JS, and require the same
answer: the generic tree read back with `main`'s type for a pure `main`, and standard
output for an `IO` one. This is the acceptance comparison for the target. -/
def jsAgreesWithC (src : String) : IO Unit := do
  unless ← jsNodeAvailable do skip "no node"; return
  let s := runFrontend (R := ZeroOneMany) src { loader := ← libLoader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir with
  | .error e => if e.isToolchain then skip "no toolchain" else throw (IO.userError e.message)
  | .ok cOut =>
    match ← Build.runJsGlobal s "main" dir with
    | .error e => throw (IO.userError e)
    | .ok jsOut => checkEq cOut jsOut

/-- A source with every occurrence of `old` replaced by `new` (the broken-demo fixture). -/
def jsReplace (src old new : String) : String :=
  if old.isEmpty then src else String.intercalate new (src.splitOn old)

/-- Build `examples/js-loom/loom.wiz` (or a variant) and run it against the fake DOM:
the exit code, the harness's stdout and its stderr. -/
def jsLoomRun (src : String) : IO (UInt32 × String × String) := do
  let (_, _, text) ← jsCompile src
  let dir ← IO.FS.createTempDir
  let file := dir / "loom.mjs"
  IO.FS.writeFile file text
  let out ← IO.Process.output
    { cmd := "node", args := #["examples/js-loom/run.mjs", file.toString],
      env := #[("LD_LIBRARY_PATH", none)] }
  pure (out.exitCode, out.stdout, out.stderr)

def jsGroup : Group where
  name := "js"
  exercise := "Stage 8 (a JavaScript target)"
  parallel := true
  shard := "library"
  cases := [
    { name := "arithmetic and non-tail recursion (the interpreter is the oracle)", run := fun _ =>
        jsGolden ("import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\n" ++
          "def main : Nat := fact 12 + 7 * 9 - (Nat.pred 0)") },
    { name := "big integers, division and shifts", run := fun _ =>
        jsGolden ("import Prelude\ndef big : Nat := Nat.pow 3 50\n" ++
          "def l9 : List Nat := .cons (Nat.pow 0 0) .nil\n" ++
          "def l8 : List Nat := .cons (Nat.log2 0) l9\n" ++
          "def l7 : List Nat := .cons (Nat.log2 big) l8\n" ++
          "def l6 : List Nat := .cons (Nat.shiftRight big 40) l7\n" ++
          "def l5 : List Nat := .cons (Nat.shiftLeft 3 70) l6\n" ++
          "def l4 : List Nat := .cons (Nat.mod 100 0) l5\n" ++
          "def l3 : List Nat := .cons (Nat.div 100 7) l4\n" ++
          "def l2 : List Nat := .cons (Nat.mod big 1000007) l3\n" ++
          "def l1 : List Nat := .cons (Nat.div big 1000007) l2\n" ++
          "def main : List Nat := l1") },
    { name := "strings are code points (the interpreter is the oracle)", run := fun _ =>
        jsGolden ("import Prelude\nimport Text\ndef main : String := " ++
          "String.append \"hello, \" (String.append \"wörld\" \"!\")") },
    { name := "acceptance (pure): numbers, strings, lists, records, closures, match — JS and C agree", run := fun _ =>
        jsAgreesWithC ("import Prelude\nimport IO\nimport Text\nstructure Pair where\n" ++
          "  fst : Nat\n  snd : Nat\n" ++
          "def add (a : Nat) : Nat → Nat := fun b => a + b\n" ++
          "def mkList : Nat → List Nat\n  | .zero => .nil\n  | .succ k => .cons k (mkList k)\n" ++
          "def sumList : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sumList xs\n" ++
          "def classify (p : Pair) : Nat := match String.eq (Nat.toString p.fst) \"1\" with\n" ++
          "  | .true => p.snd\n  | .false => p.fst\n" ++
          "def main : Nat :=\n  let p := Pair.mk 1 2;\n  let xs := mkList 5;\n" ++
          "  add (sumList xs) (classify p) + List.length xs + " ++
          "List.length (String.chars (Nat.toString 42))") },
    { name := "acceptance (IO): do, IO.println, a closure and a match — JS and C print the same lines", run := fun _ =>
        jsAgreesWithC ("import Prelude\nimport IO\nimport Text\nstructure Pair where\n" ++
          "  fst : Nat\n  snd : Nat\n" ++
          "def add (a : Nat) : Nat → Nat := fun b => a + b\n" ++
          "def classify (p : Pair) : String := match String.eq (Nat.toString p.fst) \"1\" with\n" ++
          "  | .true => \"one\"\n  | .false => \"many\"\n" ++
          "def main : IO Unit := do\n  let p := Pair.mk 1 2;\n" ++
          "  let xs := List.cons (add 3 4) (List.cons (p.fst + 100) .nil);\n" ++
          "  IO.println (Nat.toString (List.length xs));\n" ++
          "  IO.println (classify p);\n" ++
          "  IO.println (match xs with | .nil => \"empty\" | .cons x _ => Nat.toString x)") },
    { name := "lists, structures and projections", run := fun _ =>
        jsGolden ("import Prelude\nstructure Pair where\n  fst : Nat\n  snd : Nat\n" ++
          "def mkList : Nat → List Nat\n  | .zero => .nil\n  | .succ k => .cons k (mkList k)\n" ++
          "def sumList : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sumList xs\n" ++
          "def bump (p : Pair) : Pair := Pair.mk (Nat.succ p.fst) (Nat.succ p.snd)\n" ++
          "def main : Nat := sumList (mkList 10) + (bump (Pair.mk 20 21)).fst + (bump (Pair.mk 20 21)).snd") },
    { name := "closures, partial and over-application", run := fun _ =>
        jsGolden ("import Prelude\ndef add3 (a b c : Nat) : Nat := a + b + c\n" ++
          "def apply2 (f : Nat → Nat) (x : Nat) : Nat := f (f x)\n" ++
          "def digits (x : Nat) : Nat → Nat := fun y => x * 10 + y\n" ++
          "def main : Nat := apply2 (add3 1 2) 10 + digits 4 5") },
    { name := "match, join points and a non-tail case", run := fun _ =>
        jsGolden ("import Prelude\ndef classify (n : Nat) : Nat := match n with\n" ++
          "  | .zero => 10\n  | .succ m => match m with\n    | .zero => 20\n    | .succ k => match k with\n" ++
          "      | .zero => 30\n      | .succ j => j + 40\n" ++
          "def g (n : Nat) : Nat := (match n with | .zero => 1 | .succ m => m) + 5\n" ++
          "def main : Nat := classify 7 + classify 0 + classify 1 + g 10") },
    { name := "mutual recursion and a deep self tail call (a loop, not JS stack)", run := fun _ =>
        jsRun ("import Prelude\nmutual\ndef even : Nat → Bool\n  | .zero => .true\n" ++
          "  | .succ n => odd n\ndef odd : Nat → Bool\n  | .zero => .false\n  | .succ n => even n\nend\n" ++
          "partial def countdown (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ k => countdown k (acc + 1)\n" ++
          "def main : Nat := (match even 1001 with | .true => 1 | .false => 0) + countdown 100000 0") "100000" },
    { name := "closed definitions are shared (CAF)", run := fun _ =>
        jsGolden "import Prelude\ndef c : Nat := 7 * 2\ndef main : Nat := c + c" },
    { name := "Int is the library's data type", run := fun _ =>
        jsGolden "import Int\ndef main : Int := (3 : Int) * (4 : Int) - 5" },
    { name := "Array is a JavaScript array (copy on set)", run := fun _ =>
        jsRun ("import Std\ndef arr : Array Nat := Array.push (Array.push (Array.empty) 1) 40\n" ++
          "def main : Nat := Array.getD arr 1 0 * 100 + Array.getD (Array.set arr 0 2) 0 0") "4002" },
    { name := "UInt64 wraps at 2^64 (a masked BigInt)", run := fun _ =>
        jsRun ("import IO\ndef main : Nat := UInt64.toNat (UInt64.add " ++
          "(UInt64.ofNat 18446744073709551615) (UInt64.ofNat 2))") "1" },
    { name := "UIntN is a masked BigInt at its width", run := fun _ =>
        jsRun ("import Word\ndef main : Nat := UIntN.toNat " ++
          "(UIntN.add (UIntN.ofNat 8 250) (UIntN.ofNat 8 10))") "4" },
    { name := "IO.println and IO.print (do, the world, wiz_io_*)", run := fun _ =>
        jsStdout ("import Prelude\nimport IO\ndef main : IO Unit := do\n  IO.println \"hello\";\n" ++
          "  IO.println (Nat.toString 42);\n  IO.print \"no newline\"") "hello\n42\nno newline" },
    { name := "the emitted module has the runtime entry points and a main export", run := fun _ => do
        let text ← jsEmit "import Prelude\ndef main : Nat := 1"
        check ((text.splitOn "export function wiz_nat_add").length > 1) "no wiz_nat_add"
        check ((text.splitOn "export function wizApply").length > 1) "no wizApply"
        check ((text.splitOn "export function main").length > 1) "no main export" },
    { name := "the emitted module is deterministic", run := fun _ => do
        let a ← jsEmit ("import Prelude\ndef c : List Nat := .cons 1 (.cons 2 .nil)\n" ++
          "partial def loop (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ k => loop k (acc + 1)\ndef main : Nat := loop 20 0 + (match c with | .nil => 0 | .cons x _ => x)")
        let b ← jsEmit ("import Prelude\ndef c : List Nat := .cons 1 (.cons 2 .nil)\n" ++
          "partial def loop (n acc : Nat) : Nat := match n with\n  | .zero => acc\n" ++
          "  | .succ k => loop k (acc + 1)\ndef main : Nat := loop 20 0 + (match c with | .nil => 0 | .cons x _ => x)")
        checkEq a b },
    { name := "IO.readFile is refused (no filesystem in this target)", run := fun _ => do
        let e ← jsError ("import Prelude\nimport IO\ndef main : IO Unit := do\n" ++
          "  s ← IO.readFile \"x\";\n  IO.println s")
        unless (e.splitOn "filesystem").length > 1 do throw (IO.userError e) },
    { name := "an unimplemented runtime native is refused by name", run := fun _ => do
        let e ← jsError ("import Prelude\nimport IO\nextern \"wiz_sys_getcwd\" cwd : IO String\n" ++
          "def main : IO String := cwd")
        unless (e.splitOn "no JavaScript runtime").length > 1 do throw (IO.userError e) },
    { name := "the build path writes OUT.mjs and runs it", run := fun _ => do
        unless ← jsNodeAvailable do skip "no node"; return
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef main : Nat := 6 * 7"
          { loader := ← libLoader, trustedModule := Tests.libModule }
        let dir ← IO.FS.createTempDir
        match ← Build.buildJs s "main" (dir / "out") with
        | .error e => throw (IO.userError e)
        | .ok _ =>
          let file := dir / "out.mjs"
          unless ← file.pathExists do throw (IO.userError "Build.buildJs did not write out.mjs")
          let out ← IO.Process.output
            { cmd := "node", args := #[file.toString], env := #[("LD_LIBRARY_PATH", none)] }
          checkEq "42" out.stdout.trimAscii.toString
          match ← Build.runJsGlobal s "main" dir with
          | .error e => throw (IO.userError e)
          | .ok v => checkEq "42" v },
    { name := "the Loom-shaped demo: mount, route, delegate and patch, in Wiz", run := fun _ => do
        unless ← jsNodeAvailable do skip "no node"; return
        let src ← IO.FS.readFile ("examples" / "js-loom" / "loom.wiz")
        let (code, stdout, stderr) ← jsLoomRun src
        if code != 0 then
          throw (IO.userError s!"the demo failed ({code}):\n{stdout}\n{stderr}")
        unless (stdout.splitOn "PASS loom demo").length > 1 do
          throw (IO.userError s!"no PASS line:\n{stdout}") },
    { name := "the Loom demo fails when its route is broken", run := fun _ => do
        unless ← jsNodeAvailable do skip "no node"; return
        let src ← IO.FS.readFile ("examples" / "js-loom" / "loom.wiz")
        -- `/` now routes to About: the first patch list is the wrong one, and the
        -- harness's assertion must say so
        let broken := jsReplace src "| .true => .home" "| .true => .about"
        check (broken != src) "the fixture did not contain the route branch"
        let (code, stdout, _) ← jsLoomRun broken
        if code == 0 then
          throw (IO.userError s!"the broken-route demo passed:\n{stdout}")
        unless (stdout.splitOn "FAIL loom demo").length > 1 do
          throw (IO.userError s!"the failure is not the demo's assertion:\n{stdout}") }
  ]

builtin_initialize registerGroup jsGroup

end Tests.Elab
