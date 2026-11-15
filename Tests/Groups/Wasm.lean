import Tests.Elab
import Wiz.Compiler.WasmValidate

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Is `node` on the PATH? The Wasm backend's smoke tests run the module under it. -/
def nodeAvailable : IO Bool := do
  -- (`lake test` runs with Lean's LD_LIBRARY_PATH, whose libgcc shadows the system's
  -- for Node: run Node without it)
  try
    let out ← IO.Process.output { cmd := "node", args := #["--version"], env := #[("LD_LIBRARY_PATH", none)] }
    pure (out.exitCode == 0)
  catch _ => pure false

/-- Elaborate a source with the test library and compile `main` to a Wasm module. The
module is checked by `Wiz.WasmValidate.validate` before it is returned, so a test sees
the same structural validation that `Build.compileWasm` does. -/
def wasmCompile (src : String) : IO (CommandState ZeroOneMany × Term ZeroOneMany × ByteArray) := do
  let s := runFrontend (R := ZeroOneMany) src { loader := ← libLoader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let (decls, ty) ← match Build.irProgram s "main" with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let bytes ← match Wasm.program decls (Build.isIO ty) with
    | .ok bytes => pure bytes
    | .error e => throw (IO.userError e)
  match WasmValidate.validate bytes with
  | .error e => throw (IO.userError s!"the Wasm module does not validate: {e}")
  | .ok () => pure ()
  -- (the module starts with the WebAssembly magic)
  unless bytes.size > 8 && bytes.toList.take 4 == [0x00, 0x61, 0x73, 0x6D] do
    throw (IO.userError "not a WebAssembly module")
  pure (s, ty, bytes)

/-- Run a module under Node with `web/wasm-host.mjs`; returns its stdout. -/
def wasmRunBytes (bytes : ByteArray) : IO String := do
  let host : System.FilePath := "web" / "wasm-host.mjs"
  let dir ← IO.FS.createTempDir
  let file := dir / "wiz_main.wasm"
  IO.FS.writeBinFile file bytes
  let out ← IO.Process.output
    { cmd := "node", args := #[host.toString, file.toString], env := #[("LD_LIBRARY_PATH", none)] }
  if out.exitCode != 0 then
    throw (IO.userError s!"the Wasm program failed ({out.exitCode}): {out.stderr.take 1500}")
  pure out.stdout

/-- Compile `main` with the Wasm backend, run it under Node with `web/wasm-host.mjs`,
and read its printed result back with `main`'s type (as `wiz run` does for C). -/
def wasmRun (src expected : String) : IO Unit := do
  unless ← nodeAvailable do skip "no node"; return
  let host : System.FilePath := "web" / "wasm-host.mjs"
  unless ← host.pathExists do skip "no web/wasm-host.mjs"; return
  let (s, ty, bytes) ← wasmCompile src
  let out ← wasmRunBytes bytes
  match Build.parseValue out with
  | none => throw (IO.userError s!"could not read the result: {out}")
  | some v => checkEq expected (readback s.globals s.builtins (eval s.globals [] ty) v).pretty

/-- The interpreter's answer for `main`: append `#eval main` and take its one info
message. This is the oracle for a golden test (the C backend's result is the same tree). -/
def wasmNative (src : String) : IO String := do
  let s := runFrontend (R := ZeroOneMany) (src ++ "\n#eval main\n")
    { loader := ← libLoader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let infos := (s.messages.toList.filter (·.severity == .info)).map (·.text)
  match infos with
  | [v] => pure v
  | _ => throw (IO.userError s!"the interpreter produced {infos.length} results: {infos}")

/-- A golden test: the Wasm module and the interpreter run the same `main`, and their
results (read back with `main`'s type) must be equal. -/
def wasmGolden (src : String) : IO Unit := do
  let expected ← wasmNative src
  wasmRun src expected

/-- A program that must fail at run time (a trap), with a fragment of the engine's
message. -/
def wasmTrap (src fragment : String) : IO Unit := do
  unless ← nodeAvailable do skip "no node"; return
  let host : System.FilePath := "web" / "wasm-host.mjs"
  unless ← host.pathExists do skip "no web/wasm-host.mjs"; return
  let (_, _, bytes) ← wasmCompile src
  let dir ← IO.FS.createTempDir
  let file := dir / "wiz_main.wasm"
  IO.FS.writeBinFile file bytes
  let out ← IO.Process.output
    { cmd := "node", args := #[host.toString, file.toString], env := #[("LD_LIBRARY_PATH", none)] }
  if out.exitCode == 0 then throw (IO.userError s!"the Wasm program did not trap: {out.stdout}")
  unless (out.stderr.splitOn fragment).length > 1 do
    throw (IO.userError s!"the trap does not mention '{fragment}': {out.stderr.take 1500}")

/-- A module whose entry is exactly `unreachable`: the engine must trap, and the host
must report it (not print a value). This is the trap path without a source-level
construct that Wiz's type system would reject. -/
def wasmTrapIr (fragment : String) : IO Unit := do
  unless ← nodeAvailable do skip "no node"; return
  let host : System.FilePath := "web" / "wasm-host.mjs"
  unless ← host.pathExists do skip "no web/wasm-host.mjs"; return
  let decls : Array Wiz.IR.Decl := #[{ name := "wiz.entry", params := #[], body := .unreachable }]
  let bytes ← match Wasm.program decls false with
    | .ok bytes => pure bytes
    | .error e => throw (IO.userError e)
  match WasmValidate.validate bytes with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"the trap module does not validate: {e}")
  let dir ← IO.FS.createTempDir
  let file := dir / "trap.wasm"
  IO.FS.writeBinFile file bytes
  let out ← IO.Process.output
    { cmd := "node", args := #[host.toString, file.toString], env := #[("LD_LIBRARY_PATH", none)] }
  if out.exitCode == 0 then throw (IO.userError s!"the trap module did not trap: {out.stdout}")
  unless (out.stderr.splitOn fragment).length > 1 do
    throw (IO.userError s!"the trap does not mention '{fragment}': {out.stderr.take 1500}")

/-- The validator must reject damaged bytes, not just accept the encoder's output. -/
def wasmValidatorCatchesDamage : IO Unit := do
  let (_, _, bytes) ← wasmCompile "import Prelude\ndef main : Nat := 1 + 2"
  match WasmValidate.validate bytes with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"a valid module was rejected: {e}")
  let badMagic := bytes.set! 0 0x01
  match WasmValidate.validate badMagic with
  | .ok () => throw (IO.userError "the validator accepted a module with bad magic")
  | .error _ => pure ()
  let truncated := bytes.extract 0 (bytes.size - 1)
  match WasmValidate.validate truncated with
  | .ok () => throw (IO.userError "the validator accepted a truncated module")
  | .error _ => pure ()
  let badSection := bytes.set! 8 0x63
  match WasmValidate.validate badSection with
  | .ok () => throw (IO.userError "the validator accepted an unknown section id")
  | .error _ => pure ()

/-- The Wasm backend's error for a program, if it rejects it. -/
def wasmError (src : String) : IO String := do
  let s := runFrontend (R := ZeroOneMany) src { loader := ← libLoader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let (decls, ty) ← match Build.irProgram s "main" with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  match Wasm.program decls (Build.isIO ty) with
  | .ok _ => throw (IO.userError "the Wasm backend accepted the program")
  | .error e => pure e

def wasmGroup : Group where
  name := "wasm"
  exercise := "Stage 8f"
  cases := [
    { name := "arithmetic (the interpreter is the oracle)", run := fun _ =>
        wasmGolden "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\ndef main : Nat := fact 12 + 7 * 9 - (Nat.pred 0)" },
    { name := "arithmetic at every size (small and BigInt)", run := fun _ =>
        wasmGolden ("import Prelude\ndef big : Nat := Nat.pow 3 50\n" ++
          "def main : List Nat := .cons (Nat.div big 1000007) (.cons (Nat.mod big 1000007) " ++
          "(.cons (Nat.div 100 7) (.cons (Nat.mod 100 0) (.cons (Nat.land big (Nat.pow 2 70 - 1)) " ++
          "(.cons (Nat.lor 12 10) (.cons (Nat.xor big big) (.cons (Nat.shiftLeft 3 70) " ++
          "(.cons (Nat.shiftRight big 40) (.cons (Nat.log2 big) (.cons (Nat.log2 0) " ++
          "(.cons (Nat.pow 0 0) .nil)))))))))))") },
    { name := "control flow: nested cases and a join point", run := fun _ =>
        wasmGolden ("import Prelude\ndef classify (n : Nat) : Nat := match n with\n" ++
          "  | .zero => 10\n  | .succ m => match m with\n" ++
          "    | .zero => 20\n    | .succ k => match k with\n      | .zero => 30\n      | .succ j => j + 40\n" ++
          "def main : Nat := classify 7 + classify 0 + classify 1") },
    { name := "mutual recursion through direct calls", run := fun _ =>
        wasmGolden ("import Prelude\nmutual\ndef even : Nat → Bool\n  | .zero => .true\n  | .succ n => odd n\n" ++
          "def odd : Nat → Bool\n  | .zero => .false\n  | .succ n => even n\nend\n" ++
          "def main : Nat := match even 1000 with | .true => 1 | .false => 0") },
    { name := "closures, partial and over-application", run := fun _ =>
        wasmGolden ("import Prelude\ndef add3 (a b c : Nat) : Nat := a + b + c\n" ++
          "def apply2 (f : Nat → Nat) (x : Nat) : Nat := f (f x)\n" ++
          "def digits (x : Nat) : Nat → Nat := fun y => x * 10 + y\n" ++
          "def main : Nat := apply2 (add3 1 2) 10 + digits 4 5") },
    { name := "codata: lazy observations (lazyTag/lazySet)", run := fun _ =>
        wasmGolden ("import Prelude\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n" ++
          "def nats (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => nats (n + 1)\n" ++
          "def main : Nat := (nats 1).tail.tail.head") },
    { name := "generic data: a recursive constructor built from variables (pack/mkObj)", run := fun _ =>
        wasmGolden ("import Prelude\ninductive Tree where\n  | leaf\n  | node (l : Tree) (r : Tree)\n" ++
          "def mk (x : Tree) : Tree := Tree.node x x\n" ++
          "def size : Tree → Nat\n  | .leaf => 1\n  | .node l r => size l + size r + 1\n" ++
          "def main : Nat := size (mk (mk Tree.leaf))") },
    { name := "strings are algebraic values", run := fun _ =>
        wasmRun "import Prelude\ndef main : String := String.append \"hello, \" (String.append \"world\" \"!\")"
          "\"hello, world!\"" },
    { name := "numbers and big integers (the JS host's BigInt bridge)", run := fun _ =>
        wasmRun "import Prelude\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (.succ n) * fact n\ndef main : Nat := fact 25"
          "15511210043330985984000000" },
    { name := "small numbers, division, powers and bits", run := fun _ =>
        wasmRun ("import Prelude\ndef big : Nat := Nat.pow 3 50\n" ++
          "def main : List Nat := .cons (Nat.div big 1000007) (.cons (Nat.mod big 1000007) (.cons (Nat.div 100 7) " ++
          "(.cons (Nat.mod 100 0) (.cons (Nat.land big (Nat.pow 2 70 - 1)) (.cons (Nat.lor 12 10) " ++
          "(.cons (Nat.xor big big) (.cons (Nat.shiftLeft 3 70) (.cons (Nat.shiftRight big 40) " ++
          "(.cons (Nat.log2 big) (.cons (Nat.log2 0) (.cons (Nat.pow 0 0) (.cons (Nat.shiftLeft 1 61) " ++
          "(.cons (Nat.shiftLeft 1 62) .nil)))))))))))))")
          ".cons 717892962441115500 (.cons 961749 (.cons 14 (.cons 100 (.cons 98282295666516288457 (.cons 14 (.cons 0 (.cons 3541774862152233910272 (.cons 652924416219 (.cons 79 (.cons 0 (.cons 1 (.cons 2305843009213693952 (.cons 4611686018427387904 .nil)))))))))))))" },
    { name := "closures and partial application", run := fun _ =>
        wasmRun "import Prelude\ndef adder (n : Nat) : Nat → Nat := fun x => x + n\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\ndef main : Nat := twice (adder 10) 1"
          "21" },
    { name := "join points (a non-tail case's continuation)", run := fun _ =>
        wasmRun "import Prelude\ndef g (n : Nat) : Nat := (match n with | .zero => 1 | .succ m => m) + 5\ndef main : Nat := g 10"
          "14" },
    { name := "memoised suspensions", run := fun _ =>
        wasmRun ("import Prelude\ndef twice (t : Unit → Nat) : Nat := t () + t ()\n" ++
          "def lazyAdd (m n : Nat) : Unit → Nat := memo (fun _ => m + n)\n" ++
          "def main : Nat := twice (lazyAdd 20 1) + twice (memo (fun _ => 0))") "42" },
    { name := "over-application of a memo thunk (arguments survive forcing)", run := fun _ =>
        wasmGolden ("import Prelude\ndef f : Unit → Nat → Nat := memo (fun _ => fun x => x + 1)\n" ++
          "def main : Nat := f () 41") },
    { name := "closed definitions (recomputed, not cached)", run := fun _ =>
        wasmRun "import Prelude\ndef c : Nat := 7 * 2\ndef main : Nat := c + c" "28" },
    { name := "arrays (Std's Array externs)", run := fun _ =>
        wasmRun ("import Std\ndef arr : Array Nat := Array.push (Array.push (Array.empty) 1) 40\n" ++
          "def main : Nat := Array.getD arr 1 0 * 100 + Array.getD (Array.set arr 0 2) 0 0") "4002" },
    { name := "Int (constructors over Nat)", run := fun _ =>
        wasmRun "import Int\ndef main : Int := (3 : Int) * (4 : Int) - 5" "7" },
    { name := "trap: an `unreachable` entry fails under the host", run := fun _ =>
        wasmTrapIr "unreachable" },
    { name := "trap: deep non-tail recursion exhausts the engine's stack", run := fun _ =>
        wasmTrap ("import Prelude\npartial def deep (n : Nat) : Nat := n + deep (n + 1)\ndef main : Nat := deep 0")
          "stack" },
    { name := "the validator rejects damaged bytes", run := fun _ => wasmValidatorCatchesDamage },
    { name := "IO main is rejected", run := fun _ => do
        let e ← wasmError "import IO\ndef main : IO Unit := IO.println \"hi\""
        unless (e.splitOn "IO-less").length > 1 do throw (IO.userError e) },
    { name := "Bytes (a native foreign type) is rejected", run := fun _ => do
        let e ← wasmError "import IO\ndef main : Nat := Bytes.size Bytes.empty"
        unless (e.splitOn "not supported by the Wasm backend").length > 1 do throw (IO.userError e) },
    { name := "the build path validates, writes and runs the module", run := fun _ => do
        unless ← nodeAvailable do skip "no node"; return
        let host : System.FilePath := "web" / "wasm-host.mjs"
        unless ← host.pathExists do skip "no web/wasm-host.mjs"; return
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef main : Nat := 6 * 7"
          { loader := ← libLoader, trustedModule := Tests.libModule }
        let dir ← IO.FS.createTempDir
        let file := dir / "wiz_main.wasm"
        match ← Build.build ({} : Toolchain) s "main" file false false false 0 true with
        | .error e => throw (IO.userError e)
        | .ok _ =>
          let bytes ← IO.FS.readBinFile file
          match WasmValidate.validate bytes with
          | .error e => throw (IO.userError s!"Build.build wrote an invalid module: {e}")
          | .ok () => pure ()
          match ← Build.runWasmGlobal s "main" dir with
          | .error e => throw (IO.userError e)
          | .ok v => checkEq "42" v },
    { name := "--lib and --no-main are refused for the Wasm target", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) "import Prelude\ndef main : Nat := 1"
          { loader := ← libLoader, trustedModule := Tests.libModule }
        let dir ← IO.FS.createTempDir
        match ← Build.build ({} : Toolchain) s "main" (dir / "m.wasm") false true false 0 true with
        | .ok _ => throw (IO.userError "the Wasm target accepted --lib")
        | .error e =>
          unless (e.splitOn "not supported").length > 1 do throw (IO.userError e) },
    { name := "an unknown foreign function is reported, not called", run := fun _ => do
        let e ← wasmError ("import Std\ndef main : Nat := Str.size (Str.ofString \"abc\")")
        unless (e.splitOn "not supported by the Wasm backend").length > 1 do throw (IO.userError e) }
  ]

builtin_initialize registerGroup wasmGroup

end Tests.Elab
