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
  unless ys do skip "no yosys"; return
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

/-- The AXI4-Stream circuits' Verilog through yosys (`check -assert`, `synth_ice40`) when
yosys is on PATH: the register slice, both width converters and the source/sink pair. -/
def hdlStreamSynthesis : IO Unit := do
  let ys ← (do let o ← IO.Process.output { cmd := "yosys", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
  unless ys do return
  let src ← IO.FS.readFile "examples/hdl-stream.wiz"
  let body := "import Hdl.Core\nimport Hdl.AxiStream\nimport Hdl.AxiStreamLaw\n" ++ src ++
    "\n#eval Verilog.emit (Circuit.netlist \"stream_slice\" (AxiStream.sliceC 8))\n" ++
    "#eval Verilog.emit (Circuit.netlist \"stream_up\" (AxiStream.upC 8 2))\n" ++
    "#eval Verilog.emit (Circuit.netlist \"stream_down\" (AxiStream.downC 8 2))\n"
  let s := runFrontend (R := ZeroOneMany) body { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render body
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {"\n".intercalate errs.toList}")
  let texts := s.messages.toList.map (·.text)
  let unq (t : String) : String := ((t.drop 1).dropEnd 1).replace "\\n" "\n" |>.replace "\\\"" "\""
  IO.FS.withTempDir fun dir => do
    for t in texts, top in ["stream_slice", "stream_up", "stream_down"] do
      IO.FS.writeFile (dir / s!"{top}.v") (unq t)
      let o ← IO.Process.output { cmd := "yosys", args := #["-q", "-p",
        s!"read_verilog {top}.v; check -assert; synth_ice40 -top {top}; tee -q -o {top}.stat stat"], cwd := dir }
      unless o.exitCode == 0 do throw (IO.userError s!"yosys fails on {top}.v:\n{o.stderr}")

/-- The SPI mode master, mock slave and link's Verilog through yosys (`check -assert`,
`synth_ice40`) when yosys is on PATH. -/
def hdlSpiSynthesis : IO Unit := do
  let ys ← (do let o ← IO.Process.output { cmd := "yosys", args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
  unless ys do return
  let src ← IO.FS.readFile "examples/hdl-spi.wiz"
  let body := "import Hdl.Core\nimport Hdl.Spi\nimport Hdl.SpiLaw\n" ++ src ++
    "\n#eval Verilog.emit (Circuit.netlist \"spi_mode0\" (Spi.masterModeCW 8 Spi.cntW 1 0 2))\n" ++
    "#eval Verilog.emit (Circuit.netlist \"spi_mode3\" (Spi.masterModeCW 8 Spi.cntW 1 3 2))\n" ++
    "#eval Verilog.emit (Circuit.netlist \"spi_slave\" (Spi.slaveC 2))\n" ++
    "#eval Verilog.emit (Circuit.netlist \"spi_link\" (Spi.linkC 2 2))\n"
  let s := runFrontend (R := ZeroOneMany) body { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render body
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {"\n".intercalate errs.toList}")
  let texts := s.messages.toList.map (·.text)
  let unq (t : String) : String := ((t.drop 1).dropEnd 1).replace "\\n" "\n" |>.replace "\\\"" "\""
  IO.FS.withTempDir fun dir => do
    for t in texts, top in ["spi_mode0", "spi_mode3", "spi_slave", "spi_link"] do
      IO.FS.writeFile (dir / s!"{top}.v") (unq t)
      let o ← IO.Process.output { cmd := "yosys", args := #["-q", "-p",
        s!"read_verilog {top}.v; check -assert; synth_ice40 -top {top}; tee -q -o {top}.stat stat"], cwd := dir }
      unless o.exitCode == 0 do throw (IO.userError s!"yosys fails on {top}.v:\n{o.stderr}")

/-- The protocol bridges over `Hdl.Bus`, the AXI4 burst adapters, the AXI4-Stream
parts and the SPI master: APB and Wishbone in both directions, AXI4-Lite bundles, INCR/
WRAP AXI4 bursts, source/sink/slice/width converters with a stalling sink, and SPI in
all four CPOL/CPHA modes. Every case checks its laws on generated traces and compares the
value simulation, `Netlist.simulate` and `Circuit.simFast`. -/
def hdlProtocolGroup : Group where
  name := "bus-protocol"
  exercise := "HDL libraries: Hdl.Apb, Hdl.Wishbone, Hdl.AxiLite, Hdl.Axi4, Hdl.AxiStream and Hdl.Spi"
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
        hdlAxi4Synthesis },
    { name := "Hdl AxiStream: source/sink backpressure, tlast, register slice and 8<->16 width conversion", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-stream.wiz")
          ("stream pair: 8 beats period 1 yes, period 3 yes, period 2 yes, stable yes, value = simulate = simFast yes\n" ++
           "stream slice: order/no loss period 3 yes, period 2 yes, value = simulate = simFast yes\n" ++
           "stream upsize 8->16: grouping/keep/last yes, period 1 yes, value = simulate = simFast yes\n" ++
           "stream downsize 16->8: grouping/keep/last yes, period 1 yes, value = simulate = simFast yes\n" ++
           "stream bundles yes, well formed yes\n")
        hdlStreamSynthesis },
    { name := "Hdl SPI: all four CPOL/CPHA modes, divider sweep, sclk/mosi timing, mock slave and loopback", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-spi.wiz")
          ("spi modes: names 0 (CPOL=0, CPHA=0) | 1 (CPOL=0, CPHA=1) | 2 (CPOL=1, CPHA=0) | 3 (CPOL=1, CPHA=1)\n" ++
           "spi round-trip: mode 0 yes, mode 1 yes, mode 2 yes, mode 3 yes\n" ++
           "spi divider sweep div 1..8, all modes yes\n" ++
           "spi loopback sweep div 1..8, all modes yes, byte model yes\n" ++
           "spi mode 0 = original master yes, value = simulate = simFast yes\n" ++
           "spi well formed yes\n")
        hdlSpiSynthesis }
  ]

builtin_initialize registerGroup hdlProtocolGroup
