import Tests.Elab

open Wiz

-- The closed terms of the example are normally evaluated at start-up; that would
-- execute unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- The protocol bridges over `Hdl.Bus`: APB in both directions (the full two-phase
bus-to-APB bridge and the combinational APB-to-bus direction), classic Wishbone in both
directions, and the AXI4-Lite channel bundles. The example checks the
`Hdl.ProtocolLaw` obligations (source/transfer stability, response matching and no lost
strobes) on generated traces, and compares the value simulation, `Netlist.simulate` and
`Circuit.simFast` for every bridge. -/
def hdlProtocolGroup : Group where
  name := "bus-protocol"
  exercise := "HDL libraries: Hdl.Apb, Hdl.Wishbone, Hdl.AxiLite bridges and bundles"
  cases := [
    { name := "Hdl protocol bridges: APB/Wishbone stability, response order, strobes and the three simulations", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-protocols.wiz")
          ("apb bus->slave: generated matches yes, value = simulate = simFast yes, 96 cycles\n" ++
           "apb bus->slave: stable yes, source stable yes, responses match yes, one ack per transfer yes (32 acks, 32 setups), order yes\n" ++
           "apb master->bus: generated matches yes, value = simulate = simFast yes, apb stable yes, bus stable yes, responses match yes\n" ++
           "apb master->bus: reads 43690 43616 21930 21878 = 43690 43616 21930 21878 yes, 12 transfers\n" ++
           "wishbone bus->slave: generated matches yes, value = simulate = simFast yes, stable yes, responses match yes, order yes, err/rty/no-request yes yes yes\n" ++
           "wishbone master->bus: generated matches yes, value = simulate = simFast yes, stable yes, responses match yes, reads 43690 43616 21930 21878 yes, 12 transfers\n" ++
           "axi-lite bundles: slave-in yes, slave-out yes, write view yes, read view yes, resp yes\n" ++
           "well formed yes\n") }
  ]

builtin_initialize registerGroup hdlProtocolGroup
