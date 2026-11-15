import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- The display group: the reusable SSD1306/SSD1331 OLED command, data and window layer
(`lib/Hdl/Display.wiz`). The case compiles and runs the example, which decodes the pins
of the two writers back into command/data bytes, and compares the report: the datasheet
command bytes and init/window sequences, the pixel and colour helpers, the value
simulation = `Netlist.simulate` = `Hdl.Sim`'s `simFast`, and a well-formed netlist. -/
def displayGroup : Group where
  name := "display"
  exercise := "display: the OLED command, data and window layer (SSD1306/SSD1331)"
  cases := [
    { name := "Display: SSD1306/SSD1331 command bytes, init, windows, pixel/colour helpers; seqC/serC decoded byte streams; values = Netlist.simulate = simFast", run := fun _ => do
        cRunLibs (← IO.FS.readFile "examples/hdl-display.wiz")
          "ssd columns: 33 0 127 pages 32: 34 0 3 pages 64: 34 0 7 \n\
           ssd window 32: 33 0 127 34 0 3 window 64: 33 0 127 34 0 7 \n\
           ssd init 32: len 24, comPins 218 2 pump 141 20 start len 31\n\
           s1331 columns: 21 0 95 rows: 117 0 63 init len 39, start len 46\n\
           rgb565: 65535 2115, fields 2 17 20\n\
           ssd pack: 1 128, unpack 129: 1 0 0 0 0 0 0 1 \n\
           ssd pixels: set 1 0, byte 4, rect 1 1 1 0\n\
           seq_ssd32: sim yes netlist yes, done 1, bytes 31/31, ok yes, well formed yes\n\
           seq_window_data: sim yes netlist yes, done 1, bytes 8/8, ok yes, well formed yes\n\
           dc flags: 0 0 0 0 0 0 1 1 \n\
           seq_s1331: sim yes netlist yes, done 1, bytes 47/47, ok yes, well formed yes\n\
           serC: sim yes netlist yes, done 3, bytes 33 384 256 , ok yes, well formed yes\n" }
  ]

builtin_initialize registerGroup displayGroup

end Tests.Elab
