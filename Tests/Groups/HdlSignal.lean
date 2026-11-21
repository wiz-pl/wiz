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
`Circuit.trace` for every input and to `Circuit.run` on ten cycles by `rfl`. 34b adds
lane L2/L3: a size-preserving `mapS` (a sized copattern compiled to `scofix`), `+`/`if`
at size `i`, `Signal.fix`, the Clash counter and the baud generator check; a register
that keeps the size, a sized copattern that recurses at the same size, and a
combinational loop through `Signal.fix` are size errors. Signals of two clock domains
still do not mix. -/
def hdlSignalGroup : Group where
  name := "hdl-signal"
  exercise := "HDL 34a (Clash-style signals)"
  cases := [
    { name := "34a: signals, registers, Hw code and bundles on signals, the baud generator through Signal.ofCircuit (examples/hdl-signal.wiz)", run := fun _ => do
        okLibs (← IO.FS.readFile "examples/hdl-signal.wiz") [
          "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]",
          "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]",
          "[7, 0, 1, 2, 3, 4]",
          "[0, 0, 0, 2, 0, 4]",
          "[7, 7, 7, 2, 3, 4]",
          "[1, 2, 3, 4, 5]",
          "[0, 0, 0, 1, 0]",
          "[0, 0, 0, 1, 0]",
          "[0, 2, 4]",
          "[0, 0, 0, 1, 0, 0, 0, 1, 0, 0]",
          "10"] },
    { name := "34a: a register that keeps the size is rejected (a combinational loop as a size error)", run := fun _ => do
        failsLibs "import Hdl.Signal\ndef badReg {d : ClockDomain} {A : Type} {i : Size} (init : A) (s : (Signal d A)^i) : (Signal d A)^i\n  | .head => init\n  | .tail => s\n" "builds a value of size ↑s or ∞, not i" },
    { name := "34a: a size-preserving map checks (sized copattern → scofix, lane L2)", run := fun _ => do
        okLibs "import Hdl.Signal\ndef mapS {d : ClockDomain} {A B : Type} {i : Size} (f : A → B) (s : (Signal d A)^i) : (Signal d B)^i\n  | .head => f s.head\n  | .tail => mapS f s.tail\n#eval Signal.sample 3 (Signal.map BitVec.toNat (mapS (fun (x : BitVec 8) => BitVec.add x (BitVec.ofNat 8 1)) (Signal.pureS (i := ∞) (BitVec.ofNat 8 250))))\n"
          [".cons 251 (.cons 251 (.cons 251 .nil))"] },
    { name := "34a: a sized copattern that recurses at the same size is a size error, not a loop", run := fun _ => do
        failsLibsEvery "import Hdl.Signal\ndef bad {d : ClockDomain} {i : Size} (s : (Signal d (BitVec 8))^i) : (Signal d (BitVec 8))^i\n  | .head => s.head\n  | .tail => bad s\n" "type mismatch" },
    { name := "34a: signals of two clock domains do not mix", run := fun _ => do
        failsLibs "import Hdl.Signal\ndef crossDomain (s : Signal ClockDomain.sys Nat) : Signal (ClockDomain.named \"fast\") Nat := s\n" "type mismatch" },
    { name := "34b: L3 partial: `pureS` (pure at any size) and a numeral at a sized signal check; at ∞ they are `pure`", run := fun _ => do
        okLibs "import Hdl.Signal\ndef p {d : ClockDomain} {A : Type} (a : A) : Signal d A := Signal.pureS (i := ∞) a\ndef numS {d : ClockDomain} {i : Size} : (Signal d (BitVec 8))^i := 3\ndef reg {d : ClockDomain} {i : Size} (a : Nat) (s : (Signal d Nat)^i) : (Signal d Nat)^(↑i) := Signal.registerS a s\ndef regPure {d : ClockDomain} {i : Size} : (Signal d Nat)^(↑i) := reg 0 (Signal.pureS (i := i) 5)\n#eval Signal.sample 3 (p 5 : Signal ClockDomain.sys Nat)\n#eval Signal.sample 3 (Signal.map BitVec.toNat (numS (d := ClockDomain.sys) (i := ∞) : Signal ClockDomain.sys (BitVec 8)))\n"
          ["[5, 5, 5]", "[3, 3, 3]"] },
    { name := "34b: L3: `+`/`if` at size i, `Signal.fix` counter, and the baud generator (lane L2)", run := fun _ => do
        okLibs "import Hdl.Signal\ndef addS {d : ClockDomain} {i : Size} (a b : (Signal d (BitVec 8))^i) : (Signal d (BitVec 8))^i := a + b\ndef ifS {d : ClockDomain} {i : Size} (c : (Signal d (BitVec 1))^i) (a b : (Signal d (BitVec 8))^i) : (Signal d (BitVec 8))^i := if c then a else b\ndef counter {d : ClockDomain} : Signal d (BitVec 8) := Signal.fix (fun (i : Size) (c : (Signal d (BitVec 8))^i) => Signal.registerS (BitVec.ofNat 8 0) (c + 1))\n#eval Signal.sample 10 (Signal.map BitVec.toNat (counter : Signal ClockDomain.sys (BitVec 8)))\n#eval Signal.sample 3 (Signal.map BitVec.toNat (addS (Signal.pureS (i := ∞) (BitVec.ofNat 8 7)) (Signal.pureS (i := ∞) (BitVec.ofNat 8 9))))\n"
          ["[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]",
           "[16, 16, 16]"] },
    { name := "34b: a combinational loop through Signal.fix is a size error (no register in the body)", run := fun _ => do
        -- `c + 1` keeps the size; the body of `fix` must produce `Signal^(↑i)`, and only
        -- `registerS` raises the size. This is the whole point of the lane.
        failsLibs "import Hdl.Signal\ndef bad {d : ClockDomain} : Signal d (BitVec 8) := Signal.fix (fun (i : Size) (c : (Signal d (BitVec 8))^i) => c + 1)\n" "type mismatch" },
    { name := "34b: raw `scofix` is a term former (the primitive behind the sized definitions)", run := fun _ => do
        okLibs "import Hdl.Signal\ndef raw {d : ClockDomain} {A : Type} (g : (i : Size) → (Signal d A)^i → (Signal d A)^(↑i)) : Signal d A := scofix (fun (j : Size) => fun _ => Unit) (fun j rec idx a => g j (rec idx a)) ∞ () ()\n"
          [] } ]

builtin_initialize registerGroup hdlSignalGroup

end Tests.Elab
