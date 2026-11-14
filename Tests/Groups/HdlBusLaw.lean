import Tests.Elab

open Wiz

-- The closed terms of the example are normally evaluated at start-up; that would
-- execute unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- The protocol laws of `Hdl.Bus`: valid/ready stability, arbiter mutual exclusion and
progress, decode/route correctness, RAM read-after-write/address stability, and the
`Bus.ReqW` byte strobes. The example checks a Boolean form of each law on generated
inputs and compares the value simulation, `Netlist.simulate` and `Circuit.simFast`.
"Tested, not proved" for everything except the lemmas `Hdl.BusLaw` proves. -/
def hdlBusLawGroup : Group where
  name := "bus-law"
  exercise := "HDL libraries: Hdl.BusLaw (valid/ready laws, arbiter, route, RAM, byte enables)"
  cases := [
    { name := "Hdl.Bus law: stability, arbiter exclusion/progress, route, RAM read-after-write and strobes", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-bus-law.wiz")
          ("route: all laws yes, value = simulate = simFast yes, 4608 inputs\n" ++
           "arb mutex yes, answers only requests yes, stable under stall yes, windows yes, generated matches yes, value = simulate = simFast yes\n" ++
           "arb fast grants 2 1 2 1 2 1 2 1 2 1 2 1 2 1 2 1 yes, hold grants 4 4 4 4 3 4 yes\n" ++
           "n-master pick n=1..4 yes\n" ++
           "n-master step law n=3 yes\n" ++
           "n-master fair n=3, 32 starts yes\n" ++
           "ram read-after-write yes, answered after 2 yes, value = simulate = simFast yes\n" ++
           "ramw strobes yes, value = simulate = simFast yes\n" ++
           "well formed yes\n") }
  ]

builtin_initialize registerGroup hdlBusLawGroup
