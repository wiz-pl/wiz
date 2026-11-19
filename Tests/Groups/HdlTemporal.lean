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
of its own in a heavy shard (like `hdl-verified`), not a case in `hdl`.

The seven property names are checked in the elaborated state as well: `okLibs` alone only
requires the file to check, so a case that deleted a theorem (the tests-27 hole) would
still pass.  Each name must exist, have a proof and have a Π-type; five of them are also
`#print axioms`ed.  `Tx.idleHigh` and `Tx.frame` are not axiom-free: their proofs unfold
the native `UIntN` operations registered by `lib/Word.wiz`, so `#print axioms` lists those
natives (the "nothing trusted" claim is `hdl-verified`'s, and it checks it separately). -/
def hdlUartTemporalGroup : Group where
  name := "hdl-uart-temporal"
  exercise := "HDL H14 T2 (iCEstick UART, temporal properties)"
  shard := "hdl-uart-temporal"
  cases := [
    { name := "H14 T2: the iCEstick UART's temporal properties for every trace and byte (examples/hdl-uart-temporal.wiz)", run := fun _ => do
        let props := ["Tx.idleHigh", "Tx.frame", "Tx.returns",
                      "Rx.receives", "Rx.badStop", "Rx.glitch", "Loop.delivers"]
        -- these five are axiom-free; the other two unfold native UIntN operations
        let axiomFree := ["Tx.returns", "Rx.receives", "Rx.badStop", "Rx.glitch", "Loop.delivers"]
        let src := (← IO.FS.readFile "examples/hdl-uart-temporal.wiz") ++ "\n" ++
          "\n".intercalate (axiomFree.map fun n => s!"#print axioms {n}")
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
        checkEq (repr (axiomFree.map fun n => s!"'{n}' does not depend on any axioms")).pretty
                (repr (s.messages.toList.map (·.text))).pretty
        for n in props do
          let some d := s.globals.find? n | throw (IO.userError s!"{n} is missing")
          check d.value.isSome s!"{n} has no proof"
          check (match d.type with | .pi _ _ _ _ _ _ => true | _ => false)
            s!"{n} is not a theorem (its type is not a Π)" } ]

builtin_initialize registerGroup hdlUartTemporalGroup

end Tests.Elab
