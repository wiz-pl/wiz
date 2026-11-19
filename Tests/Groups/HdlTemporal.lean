import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- The theorems the file's header names, in the order the documentation lists them. A
`#check` pins each name *and* its statement: deleting a theorem, renaming it or weakening
its type is an error, not a silent pass (`okLibs` with no `infos` only asserted "no
errors", which is why deleting any proof still passed — coverage audit §4, tests-27). -/
def uartTheorems : List String :=
  ["Tx.idleHigh", "Tx.frame", "Tx.returns", "Rx.receives", "Rx.badStop", "Rx.glitch",
   "Loop.delivers"]

/-- What `#check` prints for each name above (the file's own statements). -/
def uartTheoremTypes : List String :=
  ["Tx.idleHigh : (xs : Trace (Bool × Bits8)) → (□ TL.imp (TxS × Bool × Bits8) Tx.idleA (fun σ u => Tx.lineAt xs u = Tx.embOut .true)) (Tx.obs xs) 0",
   "Tx.frame : (xs : Trace (Bool × Bits8)) → (t : Nat) → (e : Bits8) → TxS.l (Tx.run xs t) = 0 → xs t = (.true, e) → (m : Nat) → Nat.lt m 40 = .true → Tx.lineAt xs (Nat.add m (.succ t)) = Tx.embOut (Uart.frameBit e (Nat.div m 4))",
   "Tx.returns : (xs : Trace (Bool × Bits8)) → (t : Nat) → (e : Bits8) → TxS.l (Tx.run xs t) = 0 → xs t = (.true, e) → Tx.run xs (Nat.add 40 (.succ t)) = .mk 0 0 e",
   "Rx.receives : (rs : Trace Bool) → (v : Nat) → (c0 : Nat) → (cs : Bits8) → (e : Bits8) → Rx.run rs v = .mk 0 c0 cs → Rx.WellFormed rs v e → rs (Nat.add 38 v) = .true → (if Nat.beq (RxS.ph (Mealy.stateAt RxS Bool (Bool × Bits8) Rx.spec Rx.s0 rs (Nat.add 38 v))) 1 then Bool.and (Nat.beq (RxS.c (Mealy.stateAt RxS Bool (Bool × Bits8) Rx.spec Rx.s0 rs (Nat.add 38 v))) 3) (rs (Nat.add 38 v)) else .false, RxS.cs (Mealy.stateAt RxS Bool (Bool × Bits8) Rx.spec Rx.s0 rs (Nat.add 38 v))) = (.true, e)",
   "Rx.badStop : (rs : Trace Bool) → (v : Nat) → (c0 : Nat) → (cs : Bits8) → (e : Bits8) → Rx.run rs v = .mk 0 c0 cs → Rx.WellFormed rs v e → rs (Nat.add 38 v) = .false → (Rx.outs rs (Nat.add 38 v)).1 = .false ∧ Rx.run rs (Nat.add 39 v) = .mk 0 0 e",
   "Rx.glitch : (rs : Trace Bool) → (v : Nat) → (c0 : Nat) → (cs : Bits8) → Rx.run rs v = .mk 0 c0 cs → rs v = .false → rs (Nat.add 2 v) = .true → Rx.run rs (Nat.add 3 v) = .mk 0 0 cs",
   "Loop.delivers : (xs : Trace (Bool × Bits8)) → (t : Nat) → (e : Bits8) → Loop.Quiet xs t → xs t = (.true, e) → (if Nat.beq (RxS.ph (Mealy.stateAt RxS Bool (Bool × Bits8) Rx.spec Rx.s0 (Loop.rs xs) (Nat.add 38 (.succ (.succ (.succ t)))))) 1 then Bool.and (Nat.beq (RxS.c (Mealy.stateAt RxS Bool (Bool × Bits8) Rx.spec Rx.s0 (Loop.rs xs) (Nat.add 38 (.succ (.succ (.succ t)))))) 3) (Loop.rs xs (Nat.add 38 (.succ (.succ (.succ t))))) else .false, RxS.cs (Mealy.stateAt RxS Bool (Bool × Bits8) Rx.spec Rx.s0 (Loop.rs xs) (Nat.add 38 (.succ (.succ (.succ t)))))) = (.true, e)"]

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
