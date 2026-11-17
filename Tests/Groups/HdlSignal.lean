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
L2), and signals of two clock domains. -/
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
        failsLibs "import Hdl.Signal\ndef crossDomain (s : Signal ClockDomain.sys Nat) : Signal (ClockDomain.named \"fast\") Nat := s\n" "type mismatch" } ]

builtin_initialize registerGroup hdlSignalGroup

end Tests.Elab
