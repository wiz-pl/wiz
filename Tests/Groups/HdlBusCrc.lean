import Tests.Elab

open Wiz

-- The closed terms of the examples are normally evaluated at start-up; that would
-- execute unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- The two standard-library HDL cells extracted from the golem bus and the iCEstick CRC:
`Hdl.Bus` (a generic valid/ready bus with a round-robin arbiter, decode/route and a RAM
model) and `Hdl.Crc` (CRC-8/SMBUS, specification and hardware). Both examples check the
value simulation, `Netlist.simulate` and `Circuit.simFast` against each other. -/
def hdlBusCrcGroup : Group where
  name := "bus-crc"
  exercise := "HDL libraries: Hdl.Bus (valid/ready bus, arbiter, route, RAM) and Hdl.Crc"
  parallel := true
  cases := [
    { name := "Hdl.Bus: value = Netlist.simulate = simFast; round-robin arbiter, decode/route, RAM model", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-bus.wiz")
          ("ram: value = simulate = simFast yes, reads 42 0 99, well formed yes\n" ++
           "arb fast: value = simulate = simFast yes, grants 2 1 2 1 2 1 2 1\n" ++
           "arb hold: value = simulate = simFast yes, grants 4 4 4 4 3 4\n" ++
           "route: value = simulate = simFast yes, errs 0 0 1 1, forwarded 1 1 0 0\n") },
    { name := "Hdl.Crc: CRC-8/SMBUS hardware = specification on 65536 inputs; known answer; stream simulation", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-crc.wiz")
          ("crc-8 step = spec: 65536 of 65536 inputs\n" ++
           "hexDigit = Crc.hex: 16 of 16 inputs\n" ++
           "known answer: 244 (0xF4 = 244)\n" ++
           "stream: value = simulate = simFast yes, crc 244, well formed yes\n") }
  ]

builtin_initialize registerGroup hdlBusCrcGroup
