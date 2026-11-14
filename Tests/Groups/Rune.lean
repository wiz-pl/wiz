import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- The artifacts the `rune-synth` harness prints between `//@@file NAME` and
`//@@end NAME` lines. -/
def runeBlocks (raw : String) : List (String × String) :=
  let rec go (ls : List String) (cur : Option String) (buf : List String) (acc : List (String × String)) :
      List (String × String) :=
    match ls with
    | [] => acc.reverse
    | l :: rest =>
      match cur with
      | none =>
        if l.startsWith "//@@file " then
          go rest (some (l.drop 9).trimAscii.toString) [] acc
        else go rest none buf acc
      | some n =>
        if l == "//@@end " ++ n then
          go rest none [] ((n, "\n".intercalate buf.reverse) :: acc)
        else go rest (some n) (l :: buf) acc
  go (raw.splitOn "\n") none [] []

/-- The Rune designs through Icarus Verilog and yosys: every module compiles, the
self-checking benches replay the value simulation, and the logic maps to iCE40 cells
(the DDR model before its memory map, as a `$mem_v2` cell). The DDR model's 64K-word
store is a `$readmemh` side file (`ddr_model_mem.hex`), so it no longer needs an
in-line initial block stripped before synthesis. Skipped without the tools, like the
`hdl` group's tool cases. -/
def runeSynthTools : IO Unit := do
  let has (c : String) : IO Bool :=
    (do let o ← IO.Process.output { cmd := c, args := #["-V"] }; pure (o.exitCode == 0)) <|> pure false
  let ys ← has "yosys"
  let iv ← has "iverilog"
  unless ys && iv do skip "no iverilog, no yosys"; return
  let src ← IO.FS.readFile "examples/rune-synth.wiz"
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors: {errs}")
  IO.FS.withTempDir fun dir => do
    let raw ← match ← Build.runGlobal (← toolchain) s "main" dir false (timeout := some 180) with
      | .ok v => pure v
      | .error e =>
        if ["gmp.h", "llc:", "No such file", "could not execute external process"].any
            fun m => (e.splitOn m).length > 1 then skip "no toolchain"; return
        else throw (IO.userError e)
    let blocks := runeBlocks raw
    unless blocks.length == 22 do
      throw (IO.userError s!"expected 22 artifacts, got {blocks.length}")
    for (name, text) in blocks do IO.FS.writeFile (dir / name) text
    let mods := ["uart_baud", "uart_tx", "uart_rx", "uart_loopback", "spi_master", "spi_loop", "ddr_model"]
    for m in mods do
      let v := dir / (m ++ ".v")
      -- the same lint gate as scripts/rune-synth.sh: `-Wall`, and no warning text
      let ivc ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-Wall", "-o", "/dev/null", v.toString] }
      unless ivc.exitCode == 0 && (ivc.stderr.splitOn "warning").length == 1 do
        throw (IO.userError s!"iverilog -Wall rejects {m}.v:\n{ivc.stderr}")
      let tb := dir / (m ++ ".tb.v")
      if ← tb.pathExists then
        let vvp := dir / (m ++ ".vvp")
        let c ← IO.Process.output { cmd := "iverilog", args := #["-g2005", "-o", vvp.toString, tb.toString, v.toString] }
        unless c.exitCode == 0 do
          throw (IO.userError s!"iverilog rejects {m}'s bench:\n{c.stderr}")
        let r ← IO.Process.output { cmd := "vvp", args := #["-n", vvp.toString], cwd := dir }
        unless r.exitCode == 0 && (r.stdout.splitOn s!"PASS {m}:").length > 1 do
          throw (IO.userError s!"{m}'s bench fails:\n{r.stdout}{r.stderr}")
      let script := if m == "ddr_model" then
          s!"read_verilog {m}.v; hierarchy -top {m}; proc; check -assert; memory -nomap; opt; tee -o {m}.stat stat"
        else
          s!"read_verilog {m}.v; hierarchy -top {m}; proc; check -assert; synth_ice40 -top {m}; tee -o {m}.stat stat"
      let y ← IO.Process.output { cmd := "yosys", args := #["-q", "-p", script], cwd := dir }
      unless y.exitCode == 0 do
        throw (IO.userError s!"yosys fails on {m}:\n{y.stderr}")
      let st ← IO.FS.readFile (dir / (m ++ ".stat"))
      if m == "ddr_model" then
        unless (st.splitOn "$mem_v2").length > 1 do
          throw (IO.userError s!"ddr_model: no memory cell in the synthesis report:\n{st}")
      else
        unless (st.splitOn "SB_LUT4").length > 1 do
          throw (IO.userError s!"{m}: no logic cells in the synthesis report:\n{st}")

/-- The rune group: the HDL standard library of reusable, simulated primitives
(`lib/Hdl/Uart.wiz`, `lib/Hdl/Spi.wiz`, `lib/Hdl/Ddr.wiz`). Each case runs the example
through the front end, compiles it, and compares its report: the value simulation and
the fast netlist simulation (`Hdl.Sim`) agree and the protocol behaves (a byte through
the UART loopback, the SPI edges and byte, the DDR handshake and masked writes). -/
def runeGroup : Group where
  name := "rune"
  exercise := "rune: the HDL standard library (UART, SPI, DDR)"
  cases := [
    { name := "UART: baud generator, TX/RX loopback with 8 and 16 clocks per bit; simFast = values, every byte back, well formed", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/rune-uart.wiz")
          "baud n=8: sim yes, ticks 4\n\
           baud n=16: sim yes, ticks 4\n\
           uart n=8: sim yes, sent 85 165 0 255 , got 85 165 0 255 , ok yes, well formed yes\n\
           uart n=16: sim yes, sent 85 165 0 255 , got 85 165 0 255 , ok yes, well formed yes\n" },
    { name := "SPI: mode 0 master loopback, divider 1 and 3; eight rising edges per byte, most significant first; simFast = values", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/rune-spi.wiz")
          "spi div=1: sim yes, edges 16, shift yes, bytes 165 60 , ok yes, well formed yes\n\
           spi div=3: sim yes, edges 16, shift yes, bytes 165 60 , ok yes, well formed yes\n" },
    { name := "DDR: native-port valid/ready handshake, read responses and byte-masked writes against the model; simFast = values", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/rune-ddr.wiz")
          "ddr: sim yes, accepted 11, ready-low 5, rvalid 5, values yes, well formed yes\n" },
    { name := "Verilog: yosys synthesises the UART, SPI and DDR logic to iCE40 cells; Icarus Verilog compiles the modules and replays the benches (skipped without the tools)", run := fun _ => runeSynthTools }
  ]

builtin_initialize registerGroup runeGroup

end Tests.Elab
