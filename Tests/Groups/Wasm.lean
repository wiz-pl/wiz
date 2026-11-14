import Tests.Elab

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

/-- Compile `main` with the Wasm backend, run it under Node with `web/wasm-host.mjs`,
and read its printed result back with `main`'s type (as `wiz run` does for C). -/
def wasmRun (src expected : String) : IO Unit := do
  unless ← nodeAvailable do skip "no node"; return
  let host : System.FilePath := "web" / "wasm-host.mjs"
  unless ← host.pathExists do skip "no web/wasm-host.mjs"; return
  let s := runFrontend (R := ZeroOneMany) src { loader := ← libLoader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let (decls, ty) ← match Build.irProgram s "main" with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let bytes ← match Wasm.program decls (Build.isIO ty) with
    | .ok bytes => pure bytes
    | .error e => throw (IO.userError e)
  -- (the module starts with the WebAssembly magic)
  unless bytes.size > 8 && bytes.toList.take 4 == [0x00, 0x61, 0x73, 0x6D] do
    throw (IO.userError "not a WebAssembly module")
  let dir ← IO.FS.createTempDir
  let file := dir / "wiz_main.wasm"
  IO.FS.writeBinFile file bytes
  let out ← IO.Process.output
    { cmd := "node", args := #[host.toString, file.toString], env := #[("LD_LIBRARY_PATH", none)] }
  if out.exitCode != 0 then
    throw (IO.userError s!"the Wasm program failed ({out.exitCode}): {out.stderr.take 1500}")
  match Build.parseValue out.stdout with
  | none => throw (IO.userError s!"could not read the result: {out.stdout}")
  | some v => checkEq expected (readback s.globals s.builtins (eval s.globals [] ty) v).pretty

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
    { name := "closed definitions (recomputed, not cached)", run := fun _ =>
        wasmRun "import Prelude\ndef c : Nat := 7 * 2\ndef main : Nat := c + c" "28" },
    { name := "arrays (Std's Array externs)", run := fun _ =>
        wasmRun ("import Std\ndef arr : Array Nat := Array.push (Array.push (Array.empty) 1) 40\n" ++
          "def main : Nat := Array.getD arr 1 0 * 100 + Array.getD (Array.set arr 0 2) 0 0") "4002" },
    { name := "Int (constructors over Nat)", run := fun _ =>
        wasmRun "import Int\ndef main : Int := (3 : Int) * (4 : Int) - 5" "7" },
    { name := "strings are algebraic values", run := fun _ =>
        wasmRun "import Prelude\ndef main : String := String.append \"hello, \" \"world\"" "\"hello, world\"" },
    { name := "IO main is rejected", run := fun _ => do
        let e ← wasmError "import IO\ndef main : IO Unit := IO.println \"hi\""
        unless (e.splitOn "IO-less").length > 1 do throw (IO.userError e) },
    { name := "an unknown foreign function is reported, not called", run := fun _ => do
        let e ← wasmError ("import Std\ndef main : Nat := Str.size (Str.ofString \"abc\")")
        unless (e.splitOn "not supported by the Wasm backend").length > 1 do throw (IO.userError e) }
  ]

builtin_initialize registerGroup wasmGroup

end Tests.Elab
