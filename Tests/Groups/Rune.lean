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
the UART loopback at each counter width, the SPI edges and byte, the DDR handshake and
masked writes). -/
def runeGroup : Group where
  name := "rune"
  exercise := "rune: the HDL standard library (UART, SPI, DDR)"
  cases := [
    { name := "UART: baud generator and TX/RX loopback at the 16-bit default, 7-bit (iCEstick) and 10-bit (Arty/OLED) widths, n=1 and max n, reset/CDC receiver; simFast = values, every byte back, well formed", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/rune-uart.wiz")
          "baud n=8: sim yes, ticks 4\n\
           baud n=16: sim yes, ticks 4\n\
           uart n=8: sim yes, sent 85 165 0 255 , got 85 165 0 255 , ok yes, well formed yes\n\
           uart n=16: sim yes, sent 85 165 0 255 , got 85 165 0 255 , ok yes, well formed yes\n\
           baud 7-bit n=1: sim yes, ticks 4\n\
           baud 7-bit n=128: sim yes, ticks 4\n\
           baud 10-bit n=1: sim yes, ticks 4\n\
           baud 10-bit n=1024: sim yes, ticks 4\n\
           baud 16-bit n=1: sim yes, ticks 4\n\
           baud 16-bit n=65536: tick at n-1 yes, wraps to 0 yes\n\
           uart 7-bit n=104: sim yes, sent 85 165 0 255 , got 85 165 0 255 , ok yes, well formed yes\n\
           uart 10-bit n=866: sim yes, sent 85 165 0 255 , got 85 165 0 255 , ok yes, well formed yes\n\
           uart 16-bit n=5: sim yes, sent 85 165 0 255 , got 85 165 0 255 , ok yes, well formed yes\n\
           reset/CDC rx 7-bit n=5: sim yes, bytes 85 165 , ok yes, well formed yes\n" },
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
