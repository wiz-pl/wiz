# Hardware in Wiz

Wiz describes synchronous circuits as ordinary programs, simulates them, emits Verilog
for an FPGA, and proves things about every run of them, all with one semantics. This
page follows one example from circuit to proved property:
[`examples/hardware-tour.wiz`](../examples/hardware-tour.wiz), a traffic light
controller. The libraries are described in [libraries.md](libraries.md) (sections H14).

| piece | where | what it is |
|---|---|---|
| circuits | `lib/Hdl/Core.wiz` | `Circuit i o`: a Mealy machine whose step is code over any representation `r : HwTy → Type` (values, or wires for synthesis) |
| bundles | `lib/Hdl/Core.wiz`, `lib/Hdl/Optic.wiz` | structures of signals (`deriving Bundle`), with a lens per field (`deriving Lens`) |
| memories | `lib/Hdl/Core.wiz` | `HwTy.mem aw dw`, `Hw.memRead`/`memWrite`; block RAM on iCE40 |
| traces | `lib/Trace.wiz` | `Trace A := Nat → A`, `Mealy`, invariants, refinement |
| temporal logic | `lib/Hdl/Temporal.wiz` (PR #146) | `□`, `◇`, `○`, SVA-style implications, fairness, over traces |
| bit reasoning | `lib/Hdl/Bits.wiz` (PR, needs 22l) | laws of one-bit logic by case split; the bridge to `sat_decide` |
| solvers | `sat_decide` (stage 28b), `native_refl` (stage 27a) | certified SAT for Boolean goals; compiled evaluation for long closed runs |

## 1. A circuit

The state and the inputs are *bundles*: structures parameterised by the representation,
so one definition is a simulation model (at `HwTy.El`, values) and a netlist (at `Wire`).

```
structure Light (r : HwTy → Type) where
  phase : r B2
  waiting : r Bit
  deriving Bundle, Lens

def nextPhase {r : HwTy → Type} [Hw r] (p : r B2) (waiting tick : r Bit) : r B2 :=
  let advance := tick &&& (waiting ||| ~~~(p === 0));
  if advance then (if p === 2 then 0 else p + 1) else p

def lightStep {r : HwTy → Type} [Hw r] (s : Light r) (x : Sensors r) : r (HwTy.prod Light.code B2) :=
  let p := nextPhase s.phase s.waiting x.tick;
  let w := (s.waiting ||| x.car) &&& (p === 0);
  Hw.pair (Light.pack (Lens.set Light.waitingL (Lens.set Light.phaseL s p) w)) s.phase
```

Signals have operators (section H14 S2): numerals take their width from the type,
`+ - *`, bitwise `&&& ||| ^^^ ~~~`, shifts `<<< >>>`, comparisons `=== =/= <ᵤ …` (one
bit), and `if c then a else b` on a one-bit signal is a multiplexer. They are the `Hw`
operations, so the netlist is the same as with `Hw.and`, `Hw.mux` and friends.

`Light.phaseL : Lens (Light r) (r B2)` is a lens at every representation; `Hdl.zoom` runs
a sub-step on one field, and `Hdl.zoom_frame` says the other fields are untouched (the
frame rule, from `Lens.Indep`, the same notion the separation-logic and Feral threads use
for disjoint places). `Circuit.bundled` turns the step into a `Circuit`. Combinators
(`seq`, `par`, `loop`, `withReset`, `withEnable`) compose circuits, each with its
semantics as a lemma.

## 2. Its semantics: a trace

A circuit is a Mealy machine (`Circuit.mealy c`), and its run along an input trace is a
trace: `Circuit.trace c xs : Trace (El o)`, with the states `Circuit.stateAt c xs`.
Simulation (`Circuit.run`, on a list of inputs) is the prefix of it:
`Circuit.run_take : run c (take n xs) = take n (trace c xs)`. So the waveform a
simulation prints and the trace a theorem talks about are the same object.

## 3. A specification

The specification is a machine too, over the types one would choose for an explanation:
an enumeration of colours and Booleans for the inputs (`specStep : Abs → Bool × Bool →
Abs × Color`). It is not hardware; it never needs to be synthesised.

## 4. Refinement: one step, then every cycle

`Mealy.simulates` turns a one-step fact into a fact about every cycle of every run:

```
step_ok : (s : Abs) → (x : Bool × Bool) →
  Circuit.stepEl lightC (embS s) (embI x) = (embS (specStep s x).1, Color.code (specStep s x).2)
refines xs t : Circuit.stateAt lightC (Trace.map embI xs) t = embS (Mealy.stateAt specStep Abs.start xs t)
```

`embS` maps an abstract state to the circuit's state (the colour's code, the flag as a
bit), `embI` an abstract input to the sensors. `step_ok` has one case per abstract state
and input, each closed, so each is `rfl`: the kernel evaluates the circuit's step on
known bits, gates and all.

When a step obligation has *symbolic* bits (a register left as a variable, a control
input not embedded from Booleans), `rfl` gets stuck on gates such as `Hw.and 0 x` (finding
C2 of the toy CPU). Three tools cover that, in increasing strength:

* `lib/Hdl/Bits.wiz`: `Bit.ind` (a property of every bit is a property of 0 and of 1,
  from the words' range, stage 22l) and the laws it proves (`Bit.and_zero`, `Bit.or_mux`,
  `HwTy.El.mux_same`, …): case split, then `rfl`.
* `Bit.toBool` is a homomorphism (`Bit.toBool_and`, …), and `Bit.eq_of_toBool` turns an
  equation of bits into one of Booleans, which `sat_decide` decides with a certificate
  the kernel checks (stage 28b).
* Long closed runs (all 256 bytes through a UART at the board's baud rate) are bounded
  checks: `Mealy.checkFrom` evaluated by `refl`, or by `native_refl` (stage 27a) when the
  kernel's evaluation is too slow, and `Mealy.checkFrom_spec` turns the `true` into a
  statement about the trace.

## 5. A temporal property

"The light never goes from green straight to red", for every input trace and at every
cycle:

```
light_safe xs t : isGreen (stateAt specStep start xs t).color = .true →
                  isRed (stateAt specStep start xs (t + 1)).color = .false
light_phase xs t : (stateAt lightC (map embI xs) t).phase = Color.code (stateAt specStep start xs t).color
```

The property is proved once, on the specification (a case analysis); refinement carries
it to the circuit's phase register. With the temporal library (`lib/Hdl/Temporal.wiz`) the
statement is the formula `□ (green → ○ ¬red)`, i.e.
`TL.always (TL.imp (TL.now isGreen) (TL.next (TL.not (TL.now isRed))))` over the trace,
and its proof rules (invariance, `TL.splitAt` for a transient phase followed by an
invariant, fairness and ranking for liveness) apply to the same traces.

## 6. Netlist, Verilog, board

`Circuit.netlist`, `Verilog.emit`, `Testbench.verilog` (a self-checking bench replaying
a value simulation), `Vcd.ofRun` (a waveform) and `Pcf.emit` (pin constraints) take the
same circuit to an iCE40 board; the hdl test group checks that the value simulation, the
netlist simulation and Icarus Verilog agree. For long simulations in compiled programs,
`Design.simFast` (`lib/Hdl/Sim.wiz`, PR #199) runs the netlist about 25 times faster than
the value simulation; the value simulation stays the reference that proofs are about.
Memories (`HwTy.mem`) become Verilog arrays,
which yosys maps to the iCE40's block RAM; at values a memory is a function, so a proof
about it is pointwise (`HwTy.El.memRead_write_miss`).

## Running examples

* `examples/hardware-tour.wiz`: this page.
* `examples/hdl-compose.wiz`: composition, reset and enable, emitters.
* `examples/hdl-optic.wiz`: lenses on bundles, the frame rule.
* `examples/hdl-mem.wiz`: a RAM with a registered read, a ROM, block RAM inference.
* `examples/hdl-temporal.wiz` (PR #146): a UART's line is idle-high for ever, the
  loopback delivers every byte, a valid/ready buffer is stable and live.
* The iCEstick project (UART, toy CPU) uses all of the above; its findings drove them.

Design notes: `wiz-notes/cohesion-hardware.md`.
