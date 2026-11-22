# Stage 34: Clash-style signals

Wiz's HDL (`hdl/src/Hdl/Core.wiz`, docs/libraries.md "H14") describes a design as a
`Circuit`: a Mealy machine whose step is tagless-final code over a representation
`r : HwTy → Type`, run at values for simulation and proofs and at `Wire` for a netlist.
Clash describes the same hardware as functions on *signals*, infinite streams of values
in a clock domain, with registers inline. This stage adds that view as a layer over
`Circuit`, not a replacement: netlists, Verilog, fast simulation and every proof about
circuits stay where they are, and a signal is connected to them by a theorem. The plan
and its later lanes are in `wiz-notes/clash-hdl-plan.md`; this is lane L1.

## 34a: signals as ν-streams (`hdl/src/Hdl/Signal.wiz`)

```wiz no-check
-- (from hdl/src/Hdl/Signal.wiz; the whole module is checked by the hdl-signal group)
coinductive Signal (d : ClockDomain) (A : Type) where
  head : A
  tail : Signal d A
```

`Signal d A` is the value of a wire in every cycle of clock domain `d`. The domain is the
HDL's `ClockDomain` (the clock net's name and its period) and is a phantom parameter:
phantom parameters are checked (stage 22e), so a `Signal ClockDomain.sys Nat` is not a
`Signal (ClockDomain.named "fast") Nat`.

**Productivity is typing.** There is no separate guardedness checker for signals. A
copattern definition elaborates to `coit` when every recursive observation is a direct
corecursive call, and to `cocon` when there is none; both are total in the kernel. So
`Signal.at s t` is defined for every signal and every `t`, and
`Signal.sample_length : List.length (Signal.sample n s) = n` says so for every `s`.

**The operations.**

* Observation: `Signal.at`, `Signal.sample n`, `Signal.toTrace` (a `Trace A`, the
  semantics `Circuit.trace` and hdl/src/Hdl/Temporal.wiz use), `Signal.fromList`.
* Combinational: `pure`, `map`, `zipWith`/`zipWith3`/`zipWith4`, each a `coit`, with
  `map_at`, `zipWith_at`, `pure_at`.
* State: `register init s` (`init, s₀, s₁, …`; one `cocon` cell, no corecursion),
  `registerR` (synchronous reset), `registerEn` (clock enable), `mealy` (the state is an
  argument of the `coit`, so a cycle costs O(1)) and `moore`.
  `Signal.mealy_at` says a `mealy` signal is `Mealy.outAt` of its step at every cycle.
* `Signal.registerS : (Signal d A)^i → (Signal d A)^(↑i)`, the sized register: the only
  operation that raises a size. A register that keeps the size is rejected ("a
  copattern definition builds a value of size ↑s or ∞, not i"): this is how a
  combinational loop will be a type error once sized feedback exists (below).

**Hardware code runs on signals.** `Signal.Sig d : HwTy → Type` (signals of the values
of a hardware type) has a pointwise `Hw` instance, so any combinational code written
against `[Hw r]` applies to signals unchanged (`incr (r := Signal.Sig d) counter8`), and
a structure derived with `deriving Bundle` at `r := Signal.Sig d` is Clash's unbundled
record. `Signal.bundle b` and `Signal.unbundle b` convert between it and one signal of
the bundle's code; `bundle2`/`unbundle2` do the same for plain pairs.

**Equivalence and temporal properties.** Equality at ν is stuck (stage 4, "a design
decision"), so two signals are equivalent when they agree at every cycle
(`Signal.Eqv`, with `refl`/`symm`/`trans`). `Signal.bisim` is the bisimulation
principle: a relation that relates heads and is closed under `tail` relates only
equivalent signals. Temporal properties are the `TL` formulas of hdl/src/Hdl/Temporal.wiz
over `toTrace` (`Signal.sat`), so every proof rule there applies, and `Signal.sat_eqv`
moves a property between equivalent signals.

**The bridge to `Circuit`.**

```wiz no-check
-- (from hdl/src/Hdl/Signal.wiz)
def Signal.ofCircuit {d : ClockDomain} {i o : HwTy} (c : Circuit i o) (xs : Signal d (HwTy.El i)) : Signal d (HwTy.El o) :=
  Signal.mealy (Circuit.stepEl c) c.init xs

def Signal.ofCircuit_at {d : ClockDomain} {i o : HwTy} (c : Circuit i o) (xs : Signal d (HwTy.El i)) (t : Nat) :
    Signal.at (Signal.ofCircuit c xs) t = Circuit.trace c (Signal.toTrace xs) t
```

`ofCircuit_at` is proved from `mealy_at`; `toTrace_ofCircuit` states it as an equation of
traces and `sat_ofCircuit` transfers a temporal property between a circuit's signal and
its trace (and from there through `Circuit.Simulates` to the netlist).
`Signal.ofCircuit_delay` proves that `register` is `Circuit.delay`.

**Example** (`hdl/examples/hdl-signal.wiz`, the `hdl-signal` test group): counters as Mealy
machines (`natCounter` is `t` at every cycle `t`, and always steps by one as a `TL`
property), the three registers on ten cycles, `Hw` code and a derived bundle on signals,
and wiz-rv's baud generator (`Uart.baudCw 10 4`, a 10-bit counter with period 4) driven
as a signal:

```wiz no-check
-- (from hdl/examples/hdl-signal.wiz)
def baud4 {d : ClockDomain} (ce : Signal d (BitVec 1)) : Signal d (BitVec 1) :=
  Signal.ofCircuit (Uart.baudCw 10 4) ce

def baud4_run :
    Signal.sample 10 (baud4 (ones : Signal Sys (BitVec 1))) = Circuit.run (Uart.baudCw 10 4) (Signal.sample 10 (ones : Signal Sys (BitVec 1))) :=
  rfl
-- Signal.sample 10 …  =  0 0 0 1 0 0 0 1 0 0; the netlist has 10 nodes
```

The group also checks three rejections: the size-keeping register, a size-preserving
`map`, and a signal of one domain used as a signal of another.

**What is not here: feedback.** Clash writes a counter as
`cnt = register 0 (cnt + 1)`. In Wiz that is `Signal.fix`, a sized fixed point
`((i : Size) → (Signal d A)^i → (Signal d A)^(↑i)) → Signal d A` in which the loop must
pass through `registerS`. It needs the kernel's sized `scofix` to let its state depend on
the size: today a size-preserving `map : (Signal d A)^i → (Signal d B)^i` is rejected
(the second rejection above), so `registerS 0 (map succ c)` cannot be typed, and
`scofix` has no surface syntax. That kernel change is lane L2 of the plan, after the
μ/ν size checks it shares code with. Until then, state is written with `register`,
`mealy`, `moore`, or as a `Circuit` driven through `ofCircuit`. Blocked behind it:
`Signal.fix` and the observing size-polymorphic operators on sized signals (`+`, `if`;
numerals already type, see 34b), the ν denotation of a feedback loop in the deep
embedding with verified extraction to `Circuit` (L4) and the Clash-style surface built on
it (L5).

**Cost.** Signals are for specifications and short simulations. A `mealy` signal costs
O(1) per cycle, but a long or feedback-heavy simulation belongs on the circuit
(`Circuit.run`, `Hdl.Sim`).

## 34b: L2/L3 status — feedback and the sized operator surface

Lane L3 of the plan is `Signal.fix`, the `Hw`-style operators at a *size* (`+`,
numerals and `if` on `(Signal d A)^i`), and Clash's counter and baud generator written
with them. Lane L2 (the kernel change) landed on `hdl-l2`: `scofix` has a
size-dependent state, sized copatterns compile to it, and the library has the sized
operators. The design is `wiz-notes/hdl-l2.md`.

* The kernel's `scofix` state is `A : (j : Size) → I → Type`
  (`scofixStateTy`, `scofixFunTy` in `Wiz/Core/Conv.lean`, mirror
  `selfhost/Kernel.wiz`). The body runs at `A (↑j)` and produces `ν^{↑j}`; the recursive
  argument is the value at the predecessor, `A j → ν^j`. The fixpoint's size is still
  the *result* size (`scofix A f s i a : ν^s D i`, `a : A s i`). `↑` therefore appears
  in the body state and result, not in the seed.
* `scofix` also has surface syntax (like `coit`/`cocon`): `scofix A f s i a`.
* Sized copatterns: `def mapS {i : Size} (s : (Signal d A)^i) : (Signal d B)^i` with
  `.head`/`.tail` clauses is `elabCopatternsScofix` (`Wiz/Elab/Command.lean`). It views
  `i` as `↑j`, checks the body at `↑j`, binds the explicit arguments from the state, and
  turns a recursive call into the `rec` argument at `j`. A clause that recurses at the
  same size is a size error. `elabSizedDef`'s `sfix` path is unchanged.
* `Signal.mapS`/`zipWithS`/`zipWith3S` (`hdl/src/Hdl/Signal.wiz`) preserve the size; only
  `registerS` raises it. `Add`/`Sub` and `Mux` at `(Signal d A)^i` are the pointwise
  operations, so `c + 1` and `if c then a else b` work at size `i`.
* `Signal.fix g` is `scofix` with unit state: `g j (rec idx ())` is the body at `j`, so
  the loop value is the recursive argument. `Signal.fix (fun i c => registerS 0 (c + 1))`
  is the counter; `Signal.fix (fun i c => c + 1)` is a size error at the lambda (the
  body is not a `Signal^i → Signal^{↑i}`), which is the causality check.

The `hdl` group checks `hdl/examples/hdl-l3.wiz` (the counter, the baud generator, the sized
`map`, `+` and `if`); the `hdl-signal` group pins the sized `map` positive, the
same-size-recursion rejection and the combinational-loop rejection. The workaround
(`register`/`mealy`/`moore`/`ofCircuit`) stays for designs that do not need the sized
surface; the Mealy baud generator is still in `hdl/examples/hdl-signal.wiz`.

A `partial def` knot is not a substitute: it has neither the delay discipline (a
combinational loop diverges) nor a totality story, and it is opaque to the kernel, so a
property of a feedback design would not compute.
