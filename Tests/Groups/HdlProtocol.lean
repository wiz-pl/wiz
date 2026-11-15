import Tests.Elab

open Wiz

-- The closed terms of the example are normally evaluated at start-up; that would
-- execute unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- The AXI4 burst adapters' Verilog through yosys (`check -assert`, `synth_ice40`) when
yosys is on PATH: an unmapped cell or a combinational loop in the write or read adapter
fails here. -/
def hdlAxi4Synthesis : IO Unit := do
  let ys ← (do let o ← IO.Process.output { cmd := "yosys", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
  unless ys do return
  let src ← IO.FS.readFile "examples/hdl-axi4.wiz"
  let body := "import Hdl.Core\nimport Hdl.Axi4\nimport Hdl.Axi4Law\n" ++ src ++
    "\n#eval Verilog.emit (Circuit.netlist \"axi4_wr\" (Axi4.wrC 8 16 4))\n" ++
    "#eval Verilog.emit (Circuit.netlist \"axi4_rd\" (Axi4.rdC 8 16 4))\n"
  let s := runFrontend (R := ZeroOneMany) body { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render body
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {"\n".intercalate errs.toList}")
  let texts := s.messages.toList.map (·.text)
  let unq (t : String) : String := ((t.drop 1).dropEnd 1).replace "\\n" "\n" |>.replace "\\\"" "\""
  IO.FS.withTempDir fun dir => do
    for t in texts, top in ["axi4_wr", "axi4_rd"] do
      IO.FS.writeFile (dir / s!"{top}.v") (unq t)
      let o ← IO.Process.output { cmd := "yosys", args := #["-q", "-p",
        s!"read_verilog {top}.v; check -assert; synth_ice40 -top {top}; tee -q -o {top}.stat stat"], cwd := dir }
      unless o.exitCode == 0 do throw (IO.userError s!"yosys fails on {top}.v:\n{o.stderr}")

/-- The protocol bridges over `Hdl.Bus`: APB in both directions (the full two-phase
bus-to-APB bridge and the combinational APB-to-bus direction), classic Wishbone in both
directions, and the AXI4-Lite channel bundles. The example checks the
`Hdl.ProtocolLaw` obligations (source/transfer stability, response matching and no lost
strobes) on generated traces, and compares the value simulation, `Netlist.simulate` and
`Circuit.simFast` for every bridge. The second case is the AXI4 burst subset
(`Hdl.Axi4`, `Hdl.Axi4Law`): INCR/WRAP writes and reads through the `Bus.ReqW` adapters,
with a stalling bus slave, checked for address progression, beat count, WLAST/RLAST,
write strobes, response IDs/order and the error mapping. -/
def hdlProtocolGroup : Group where
  name := "bus-protocol"
  exercise := "HDL libraries: Hdl.Apb, Hdl.Wishbone, Hdl.AxiLite and Hdl.Axi4 bridges and bundles"
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
           "well formed yes\n") },
    { name := "Hdl AXI4 bursts: INCR/WRAP writes and reads, address progression, beat count, WLAST/RLAST, strobes and response IDs/order", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-axi4.wiz")
          ("axi4 addr model: incr/wrap yes, legal wrap yes, bad yes\n" ++
           "axi4 write incr: beats/strobes/b yes, value = simulate = simFast yes, 4 beats, stalled 3\n" ++
           "axi4 write wrap: beats/strobes/b yes, value = simulate = simFast yes, 4 beats, stalled 2\n" ++
           "axi4 write err: bresp yes\n" ++
           "axi4 read incr: beats/r/rlast yes, value = simulate = simFast yes, 4 beats, backpressure\n" ++
           "axi4 read wrap: beats/r/rlast yes, value = simulate = simFast yes, 4 beats, backpressure\n" ++
           "axi4 read err: rresp yes\n" ++
           "axi4 outstanding id order yes\n" ++
           "axi4 bundles yes\n" ++
           "axi4 well formed yes\n")
        hdlAxi4Synthesis }
  ]

builtin_initialize registerGroup hdlProtocolGroup
