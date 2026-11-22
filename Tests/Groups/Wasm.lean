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

/-- Run a compiled module under Node with `web/wasm-host.mjs` and return the printed result
together with the module's peak linear memory in 64 KiB pages. The module's memory only
grows, so its size after `wiz_main` is its peak: the collector's footprint, read from the
host. -/
def wasmPeakBytes (bytes : ByteArray) : IO (String × Nat) := do
  let host ← IO.FS.realPath ("web" / "wasm-host.mjs")
  let dir ← IO.FS.createTempDir
  let file := dir / "wiz_main.wasm"
  IO.FS.writeBinFile file bytes
  let script := dir / "peak.mjs"
  IO.FS.writeFile script <|
    "import { instantiate, show } from \"" ++ host.toString ++ "\";\n" ++
    "const ex = await instantiate(\"" ++ file.toString ++ "\");\n" ++
    "const v = ex.wiz_main();\n" ++
    "console.log(show(ex, v) + \" \" + String(ex.memory.buffer.byteLength / 65536));\n"
  let out ← IO.Process.output
    { cmd := "node", args := #[script.toString], env := #[("LD_LIBRARY_PATH", none)] }
  if out.exitCode != 0 then
    throw (IO.userError s!"the Wasm program failed ({out.exitCode}): {out.stderr.take 1500}")
  match out.stdout.trimAscii.toString.splitOn " " |>.reverse with
  | pages :: rest =>
    match pages.toNat? with
    | some n => pure (String.intercalate " " rest.reverse, n)
    | none => throw (IO.userError s!"could not read the peak memory: {out.stdout}")
  | [] => throw (IO.userError s!"could not read the peak memory: {out.stdout}")

/-- Like `wasmRun`, and the module's peak linear memory must stay at most `maxPages` 64 KiB
pages. A bump allocator's peak is everything the program allocated; the reference
counting allocator's is its peak live set. -/
def wasmRunPeak (src expected : String) (maxPages : Nat) : IO Unit := do
  unless ← nodeAvailable do skip "no node"; return
  let host : System.FilePath := "web" / "wasm-host.mjs"
  unless ← host.pathExists do skip "no web/wasm-host.mjs"; return
  let (s, ty, bytes) ← wasmCompile src
  let (out, pages) ← wasmPeakBytes bytes
  match Build.parseValue out with
  | none => throw (IO.userError s!"could not read the result: {out}")
  | some v => checkEq expected (readback s.globals s.builtins (eval s.globals [] ty) v).pretty
  if pages > maxPages then
    throw (IO.userError s!"peak linear memory was {pages} pages, over the {maxPages} bound")

/-- Run a module twice under Node and return the printed result of the first run, the
CAF build counter after each run. A cached closed definition is built exactly once, so
the second run must not move the counter; a counter that is still 0 means the program
under test had no CAF at all (not a useful test). -/
def wasmCafRunTwice (bytes : ByteArray) : IO (String × Nat × Nat) := do
  let host ← IO.FS.realPath ("web" / "wasm-host.mjs")
  let dir ← IO.FS.createTempDir
  let file := dir / "wiz_main.wasm"
  IO.FS.writeBinFile file bytes
  let script := dir / "caf.mjs"
  IO.FS.writeFile script <|
    "import { instantiate, show } from \"" ++ host.toString ++ "\";\n" ++
    "const ex = await instantiate(\"" ++ file.toString ++ "\");\n" ++
    "const v1 = ex.wiz_main();\n" ++
    "const b1 = Number(ex.wiz_caf_builds.value);\n" ++
    "const v2 = ex.wiz_main();\n" ++
    "const b2 = Number(ex.wiz_caf_builds.value);\n" ++
    "console.log(show(ex, v1) + \"\\n\" + b1 + \"\\n\" + b2);\n"
  let out ← IO.Process.output
    { cmd := "node", args := #[script.toString], env := #[("LD_LIBRARY_PATH", none)] }
  if out.exitCode != 0 then
    throw (IO.userError s!"the Wasm program failed ({out.exitCode}): {out.stderr.take 1500}")
  match out.stdout.trimAscii.toString.splitOn "\n" with
  | [v, b1, b2] =>
    match b1.toNat?, b2.toNat? with
    | some n1, some n2 => pure (v, n1, n2)
    | _, _ => throw (IO.userError s!"could not read the CAF counter: {out.stdout}")
  | _ => throw (IO.userError s!"could not read the CAF run: {out.stdout}")

/-- A closed definition is evaluated once and shared: the module's CAF-build counter
is non-zero after `main`, and running `main` a second time does not build it again. -/
def wasmCafCached (src expected : String) : IO Unit := do
  unless ← nodeAvailable do skip "no node"; return
  let host : System.FilePath := "web" / "wasm-host.mjs"
  unless ← host.pathExists do skip "no web/wasm-host.mjs"; return
  let (s, ty, bytes) ← wasmCompile src
  let (out, b1, b2) ← wasmCafRunTwice bytes
  match Build.parseValue out with
  | none => throw (IO.userError s!"could not read the result: {out}")
  | some v => checkEq expected (readback s.globals s.builtins (eval s.globals [] ty) v).pretty
  if b1 == 0 then throw (IO.userError "the program built no CAF, so the test proves nothing")
  if b2 != b1 then
    throw (IO.userError s!"a CAF was rebuilt on the second run ({b1} → {b2} builds)")

/-- The same source must emit byte-identical modules, including the CAF global cells and
the tail calls. -/
def wasmDeterministic (src : String) : IO Unit := do
  let (_, _, a) ← wasmCompile src
  let (_, _, b) ← wasmCompile src
  unless a == b do throw (IO.userError "two compilations of the same source differ")

def wasmGroup : Group where
  name := "wasm"
  exercise := "Stage 8f"
  parallel := true
  cases := [
    { name := "a function with no type entry is a compile error naming it", run := fun _ => do
        -- the emitter indexes the type table by signature and used to fall back to
        -- type 0, giving the function a different signature
        let b : Wasm.Built :=
          { types := Wasm.hostSigs.map (·.2),
            funcs := #[{ name := "f", params := #[.i64], results := #[.i64] }],
            tableSize := 0, heapStart := 16, data := #[], entry := 0 }
        match Wasm.moduleBytes b with
        | .ok _ => throw (IO.userError "a module with no type for its function was emitted")
        | .error e =>
          unless (e.splitOn "`f`").length > 1 do throw (IO.userError e) },
    { name := "an entry outside the function table is a compile error", run := fun _ => do
        let types := (Wasm.hostSigs.map (·.2)).push { params := #[], results := #[.i64] }
        let b : Wasm.Built :=
          { types := types, funcs := #[{ name := "f" }], tableSize := 0, heapStart := 16,
            data := #[], entry := 1 }
        match Wasm.moduleBytes b with
        | .ok _ => throw (IO.userError "a module whose entry index is past its functions was emitted")
        | .error e =>
          unless (e.splitOn "entry").length > 1 do throw (IO.userError e) },
    { name := "the type and runtime lookups are total", run := fun _ => do
        check (Wasm.runtimeSig? "wiz_nat_add").isSome "a runtime function has a signature"
        check (Wasm.runtimeSig? "wiz_no_such_function").isNone "an unknown runtime function has no signature"
        check (Wasm.typeIndex? #[{ params := #[.i64], results := #[.i64] }]
          { params := #[.i32], results := #[.i32] }).isNone "an unknown signature has no type index" },
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
    { name := "closed definitions (the value is shared when it does work)", run := fun _ =>
        wasmRun "import Prelude\ndef c : Nat := 7 * 2\ndef main : Nat := c + c" "28" },
    { name := "arrays (Std's Array externs)", run := fun _ =>
        wasmRun ("import Std\ndef arr : Array Nat := Array.push (Array.push (Array.empty) 1) 40\n" ++
          "def main : Nat := Array.getD arr 1 0 * 100 + Array.getD (Array.set arr 0 2) 0 0") "4002" },
    { name := "Int (constructors over Nat)", run := fun _ =>
        wasmRun "import Int\ndef main : Int := (3 : Int) * (4 : Int) - 5" "7" },
    { name := "an allocation loop completes in bounded memory", run := fun _ =>
        -- 800 trees of 4095 nodes: ~105 MB allocated, one tree live at a time. Under the
        -- bump allocator this peak was every allocation (1600+ pages).
        wasmRunPeak ("import Prelude\ninductive Tree where\n  | leaf\n  | node (l : Tree) (r : Tree)\n" ++
          "def full : Nat → Tree\n  | .zero => Tree.leaf\n  | .succ k => Tree.node (full k) (full k)\n" ++
          "def size : Tree → Nat\n  | .leaf => 1\n  | .node l r => size l + size r\n" ++
          "partial def spin (i acc : Nat) : Nat := match i with\n" ++
          "  | .zero => acc\n  | .succ j => spin j (acc + size (full 12))\n" ++
          "def main : Nat := spin 800 0") "3276800" 8 },
    { name := "alloc/free/realloc churn keeps the peak bounded", run := fun _ =>
        -- lists of constructors with 0..3 fields (four size classes), rebuilt 200 times
        wasmRunPeak ("import Prelude\ninductive Shape where\n  | dot\n  | lin (a : Nat)\n" ++
          "  | quad (a b : Nat)\n  | hexa (a b c : Nat)\n" ++
          "def mk : Nat → List Shape\n  | .zero => .nil\n  | .succ k => match Nat.mod k 4 with\n" ++
          "    | .zero => .cons Shape.dot (mk k)\n    | .succ a => match a with\n" ++
          "      | .zero => .cons (Shape.lin k) (mk k)\n      | .succ b => match b with\n" ++
          "        | .zero => .cons (Shape.quad k k) (mk k)\n" ++
          "        | .succ _ => .cons (Shape.hexa k k k) (mk k)\n" ++
          "def weight : Shape → Nat\n  | .dot => 0\n  | .lin _ => 1\n  | .quad _ _ => 2\n" ++
          "  | .hexa _ _ _ => 3\n" ++
          "def total : List Shape → Nat\n  | .nil => 0\n  | .cons x xs => weight x + total xs\n" ++
          "partial def loop (i acc : Nat) : Nat := match i with\n" ++
          "  | .zero => acc\n  | .succ j => loop j (acc + total (mk 1500))\n" ++
          "def main : Nat := loop 200 0") "450000" 8 },
    { name := "closures and memo thunks are reclaimed in a loop", run := fun _ =>
        wasmRunPeak ("import Prelude\ndef adder (k : Nat) : Nat → Nat := fun x => x + k\n" ++
          "def applyTo (f : Nat → Nat) (x : Nat) : Nat := f x\n" ++
          "partial def loop (i acc : Nat) : Nat := match i with\n" ++
          "  | .zero => acc\n  | .succ j =>\n" ++
          "    let f := adder i\n" ++
          "    let g := memo (fun _ => applyTo f 1)\n" ++
          "    loop j (acc + g ())\n" ++
          "def main : Nat := loop 2000 0") "2003000" 8 },
    { name := "functional updates reuse cells (reset/reuse)", run := fun _ =>
        -- each `incAll` rebuilds the list; `reset`/`reuse` keep the cells, so the peak is
        -- one list, and the result is the sum of (i + 1)
        wasmRunPeak ("import Prelude\ndef mkList : Nat → List Nat\n  | .zero => .nil\n" ++
          "  | .succ k => .cons k (mkList k)\n" ++
          "def sumList : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sumList xs\n" ++
          "def incAll : List Nat → List Nat\n  | .nil => .nil\n" ++
          "  | .cons x xs => .cons (x + 1) (incAll xs)\n" ++
          "partial def loop (i acc : Nat) : Nat := match i with\n" ++
          "  | .zero => acc\n  | .succ j => loop j (acc + sumList (incAll (mkList 2000)))\n" ++
          "def main : Nat := loop 300 0") "600300000" 8 },
    { name := "deep mutual tail recursion completes (return_call)", run := fun _ =>
        -- 200k frames: without tail calls this exhausts the engine's stack (as the
        -- non-tail trap case below still does)
        wasmRun ("import Prelude\nmutual\ndef even : Nat → Bool\n  | .zero => .true\n" ++
          "  | .succ n => odd n\ndef odd : Nat → Bool\n  | .zero => .false\n" ++
          "  | .succ n => even n\nend\n" ++
          "def main : Nat := match even 200000 with | .true => 1 | .false => 0") "1" },
    { name := "deep self tail recursion is a loop (jmp/return_call)", run := fun _ =>
        wasmRun ("import Prelude\npartial def countdown (n acc : Nat) : Nat := match n with\n" ++
          "  | .zero => acc\n  | .succ k => countdown k (acc + 1)\n" ++
          "def main : Nat := countdown 200000 0") "200000" },
    { name := "closed definitions are built once and shared (CAF cache)", run := fun _ =>
        wasmCafCached ("import Prelude\ndef c : List Nat := .cons 1 (.cons 2 (.cons 3 .nil))\n" ++
          "def sumList : List Nat → Nat\n  | .nil => 0\n  | .cons x xs => x + sumList xs\n" ++
          "def main : Nat := sumList c + sumList c") "12" },
    { name := "the emitted module bytes are deterministic", run := fun _ =>
        wasmDeterministic ("import Prelude\ndef c : List Nat := .cons 1 (.cons 2 .nil)\n" ++
          "partial def loop (n acc : Nat) : Nat := match n with\n" ++
          "  | .zero => acc\n  | .succ k => loop k (acc + 1)\n" ++
          "def main : Nat := loop 20 0 + (match c with | .nil => 0 | .cons x _ => x)") },
    { name := "the validator requires the tail-call proposal", run := fun _ => do
        let (_, _, bytes) ← wasmCompile ("import Prelude\npartial def loop (n : Nat) : Nat := match n with\n" ++
          "  | .zero => 0\n  | .succ k => loop k\ndef main : Nat := loop 10")
        match WasmValidate.validate bytes { tailCalls := false } with
        | .ok () => throw (IO.userError "the validator accepted return_call with the tail-call feature off")
        | .error e =>
          unless (e.splitOn "tail-call").length > 1 do throw (IO.userError e) },
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
