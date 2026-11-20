import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- At least one error, and every error mentions `fragment`, with every library
importable (a sized copattern that fails reports its mismatch once per elaboration
attempt, so `failsLibs`'s exactly-one does not fit). -/
def failsLibsEvery (input : String) (fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  if errs.isEmpty then throw (IO.userError "expected an error, got none")
  for e in errs do
    unless (e.splitOn fragment).length > 1 do
      throw (IO.userError s!"error does not mention '{fragment}':\n{e}")

/-- Stage 34a: Clash-style signals (`lib/Hdl/Signal.wiz`, lane L1 of the Clash HDL plan).
The positive file is `examples/hdl-signal.wiz`: counters as Mealy machines, registers
with reset and enable, `Hw` code and a derived `Bundle` on signals, an every-cycle
temporal property, and wiz-rv's baud generator as a signal (`Signal.ofCircuit`), equal to
`Circuit.trace` for every input and to `Circuit.run` on ten cycles by `rfl`. The
rejections are the typing that sized `scofix` (lane L2) will build on: a register that
keeps the size (a combinational loop), a size-preserving `map` (not expressible until
L2), and signals of two clock domains. 34b adds lane L3: `pureS` and numerals at a size
check (they never observe); `+` and `if` at a size, `Signal.fix` and a raw `scofix` are
rejected, so the Clash counter and baud generator are still written as Mealy machines. -/
def hdlSignalGroup : Group where
  name := "hdl-signal"
  exercise := "HDL 34a (Clash-style signals)"
  cases := [
    { name := "34a: signals, registers, Hw code and bundles on signals, the baud generator through Signal.ofCircuit (examples/hdl-signal.wiz)", run := fun _ => do
        okLibs (← IO.FS.readFile "examples/hdl-signal.wiz") [
          ".cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 (.cons 6 (.cons 7 (.cons 8 (.cons 9 .nil)))))))))",
          ".cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 (.cons 6 (.cons 7 (.cons 8 (.cons 9 .nil)))))))))",
          ".cons 7 (.cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 .nil)))))",
          ".cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 4 .nil)))))",
          ".cons 7 (.cons 7 (.cons 7 (.cons 2 (.cons 3 (.cons 4 .nil)))))",
          ".cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))",
          ".cons 0 (.cons 0 (.cons 0 (.cons 1 (.cons 0 .nil))))",
          ".cons 0 (.cons 0 (.cons 0 (.cons 1 (.cons 0 .nil))))",
          ".cons 0 (.cons 2 (.cons 4 .nil))",
          ".cons 0 (.cons 0 (.cons 0 (.cons 1 (.cons 0 (.cons 0 (.cons 0 (.cons 1 (.cons 0 (.cons 0 .nil)))))))))",
          "10"] },
    { name := "34a: a register that keeps the size is rejected (a combinational loop as a size error)", run := fun _ => do
        failsLibs "import Hdl.Signal\ndef badReg {d : ClockDomain} {A : Type} {i : Size} (init : A) (s : (Signal d A)^i) : (Signal d A)^i\n  | .head => init\n  | .tail => s\n" "builds a value of size ↑s or ∞, not i" },
    { name := "34a: a size-preserving map is rejected (needs sized scofix, lane L2)", run := fun _ => do
        failsLibsEvery "import Hdl.Signal\ndef mapS {d : ClockDomain} {A B : Type} {i : Size} (f : A → B) (s : (Signal d A)^i) : (Signal d B)^i\n  | .head => f s.head\n  | .tail => mapS f s.tail\n" "inferred: Signal^i d A" },
    { name := "34a: signals of two clock domains do not mix", run := fun _ => do
        failsLibs "import Hdl.Signal\ndef crossDomain (s : Signal ClockDomain.sys Nat) : Signal (ClockDomain.named \"fast\") Nat := s\n" "type mismatch" },
    { name := "34b: L3 partial: `pureS` (pure at any size) and a numeral at a sized signal check; at ∞ they are `pure`", run := fun _ => do
        okLibs "import Hdl.Signal\ndef p {d : ClockDomain} {A : Type} (a : A) : Signal d A := Signal.pureS (i := ∞) a\ndef numS {d : ClockDomain} {i : Size} : (Signal d (BitVec 8))^i := 3\ndef reg {d : ClockDomain} {i : Size} (a : Nat) (s : (Signal d Nat)^i) : (Signal d Nat)^(↑i) := Signal.registerS a s\ndef regPure {d : ClockDomain} {i : Size} : (Signal d Nat)^(↑i) := reg 0 (Signal.pureS (i := i) 5)\n#eval Signal.sample 3 (p 5 : Signal ClockDomain.sys Nat)\n#eval Signal.sample 3 (Signal.map BitVec.toNat (numS (d := ClockDomain.sys) (i := ∞) : Signal ClockDomain.sys (BitVec 8)))\n"
          [".cons 5 (.cons 5 (.cons 5 .nil))", ".cons 3 (.cons 3 (.cons 3 .nil))"] },
    { name := "34b: L3 blocked on L2: `+` and `if` at size i are rejected (they observe), and `Signal.fix`/`scofix` do not exist", run := fun _ => do
        -- `+` at a size: no `Add (Signal^i d A)`, because a pointwise add observes its
        -- arguments at the size it runs at (a size-preserving `zipWith`, lane L2)
        failsLibs "import Hdl.Signal\ndef addS {d : ClockDomain} {i : Size} (a b : (Signal d (BitVec 8))^i) : (Signal d (BitVec 8))^i := a + b\n" "needs an instance of Add"
        -- `if` at a size: branching on a sized signal needs its head, which is not observable
        failsLibs "import Hdl.Signal\ndef ifS {d : ClockDomain} {i : Size} (c : (Signal d (BitVec 1))^i) (a b : (Signal d (BitVec 8))^i) : (Signal d (BitVec 8))^i := if c then a else b\n" "cannot match on a value of type"
        -- the fixed point itself needs both the kernel change and a surface `scofix`
        failsLibs "import Hdl.Signal\ndef counter {d : ClockDomain} : Signal d (BitVec 8) := Signal.fix (fun (i : Size) (c : (Signal d (BitVec 8))^i) => Signal.registerS (BitVec.ofNat 8 0) c)\n" "unknown identifier 'Signal.fix'"
        failsLibs "import Hdl.Signal\ndef raw := scofix\n" "unknown identifier 'scofix'" } ]

builtin_initialize registerGroup hdlSignalGroup

end Tests.Elab
