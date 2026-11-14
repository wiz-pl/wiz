import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

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
          "ddr: sim yes, accepted 11, ready-low 5, rvalid 5, values yes, well formed yes\n" }
  ]

builtin_initialize registerGroup runeGroup

end Tests.Elab
