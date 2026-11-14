import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- H14 T2: the temporal properties of the iCEstick UART, for every input trace and byte
(`examples/hdl-uart-temporal.wiz`). One `wiz check` of the whole file: the transmitter is
idle-high, frames a byte for 40 cycles, takes the next one; the receiver reports a
well-formed frame (and nothing on a bad stop bit or a glitch), for ever; the loopback
delivers each byte 41 cycles after it is accepted. About three minutes cold, so a group
of its own in a heavy shard (like `hdl-verified`), not a case in `hdl`. -/
def hdlUartTemporalGroup : Group where
  name := "hdl-uart-temporal"
  exercise := "HDL H14 T2 (iCEstick UART, temporal properties)"
  shard := "hdl-uart-temporal"
  cases := [
    { name := "H14 T2: the iCEstick UART's temporal properties for every trace and byte (examples/hdl-uart-temporal.wiz)", run := fun _ => do
        okLibs (← IO.FS.readFile "examples/hdl-uart-temporal.wiz") } ]

builtin_initialize registerGroup hdlUartTemporalGroup

end Tests.Elab
