# Libraries

## H0c: vectors and bit vectors

`lib/Vec.wiz` (`import Vec`): `Fin n` (a `Nat` with an erased proof `Nat.lt val n = .true`;
`Fin.of 5 3 rfl`) and `Vec A n`, whose length is an **erased** index: at runtime a
vector is a list, and `Vec.length` counts it, with `Vec.length_eq : Vec.length v = n`.
Functions: `head`/`tail`/`last`/`init` on non-empty vectors, `get`/`set` by `Fin`,
`map`, `zipWith`, `zip`, `foldl`/`foldr`, `replicate`, `ofFn`, `append`, `reverse`
(linear, with a `cast` along `m + (k+1) = (m+k)+1`), `snoc`, `splitAt`, `shiftIn`,
`toList`/`fromList` (`fromList l : Vec A (List.length l)`). Theorems: `length_eq`,
`length_toList`, `toList_fromList`, `map_map`, `get_set` (`get (set v i x) i = x`),
`get_map`, and the `Nat` lemmas they need (`add_zero`, `add_succ`, `add_comm`), all by
structural recursion. `map_map`, `get_set` and `get_map` go through equations such as
`Vec.map_cons : map f (cons x xs) = cons (f x) (map f xs)`, which hold only up to casts at
the element type and are proved with the Prelude's axiom `castRefl` (below).

`lib/BitVec.wiz` (`import BitVec`): `BitVec n` (since [22h](stages/22-numbers.md), `UIntN n` under another name), a `Nat` below `2^n` by construction
(every operation reduces mod `2^n`). Wrapping `add`/`sub`/`neg`/`mul`, `udiv`/`umod`,
`and`/`or`/`xor`/`not`, `shl`/`lshr`/`ashr`, `getBit`, `msb`, `beq`/`ult`/`ule`/`slt`/`sle`,
`concat`, `extract hi lo`, `zeroExtend`, `signExtend`, and `toVec`/`ofVec` (to and
from `Vec Bool n`, least significant bit first). Operations that need `2^n` take the
width at runtime (`{ω n : Nat}`). The arithmetic is the Prelude's native `Nat`
operations ([22a](stages/22-numbers.md)), so the kernel computes on literal bit vectors:
`(BitVec.add (BitVec.ofNat 8 200) (BitVec.ofNat 8 100)).toNat = 44 := rfl`. Compiled code
runs `lib/Word.wiz`'s native words ([22h](stages/22-numbers.md)).

Along the way the elaborator learned to:
* keep erased constructor fields and arguments erased when a `match` reverts them, and
  name a field directly instead of through a `let` at ω (`| .mk i h => … h …` with
  `0 h`);
* prove an equation that has already computed with `rfl` (`Nat.succ a = Nat.succ a`
  is a Σ of `True`s and `a = a`), and recompute an equation stuck on a metavariable
  once it is solved (`congrArg Nat.succ ih` against such a goal). The proof follows the
  elaborator's computed form; where the kernel computes the equation to another shape
  (a numeral on one side, a constructor on the other), the kernel rejects it;
* erase a `cast` against its source type (the solution rule casts a function, so
  `head`, `tail` and `zipWith` on vectors failed at runtime).

Not yet: facts like `Vec.get v (Fin.of 3 1 rfl) = 20 := rfl` (the `rfl` shape
problem above; `drafts/vec-lib/VecProofs.wiz`), arithmetic facts about `BitVec` in general, numerals and operators
(`a + b`) for `BitVec` (decision HD9).

`lib/BitVecShift.wiz` (`import BitVecShift`): the first of those arithmetic facts, for
shifts. `BitVec.toNat_concat_zero`, `BitVec.shl_toNat` and `BitVec.shlStage_toNat` put
the barrel's left `concat`/`slice` stages and `BitVec.shl` in one normal form (the low
bits of a product); `Bits.low_shift` and `Bits.low_low` compose stages. The right-shift
side has `BitVec.lshr_toNat`/`lshr_low_toNat` (`Bits.high`, the barrel's other normal
form), the stage `BitVec.shrStage`/`shrStage_toNat`, and the stage-composition facts
`Bits.low_of_lt`, `Bits.low_low_rev`, `Bits.high_high`, `Bits.high_lt`,
`Bits.div_add_pow`/`high_add_pow`, `Bits.high_add_pow_l`, `Bits.high_low`, plus the fill
lemmas `BitVec.and_zero_left`/`and_one_left`/`and_zero_toNat` and the fill-by-value
stage `BitVec.fillWord`/`shrStageK` (a symbolic fill value, so a probe's `Nat` steps are
genuine equations). For arithmetic shifts `Bits.sub_one_high` and `Bits.sub_pow_ones` are
the ones-fill identities, `Bits.pow_add`/`pow_sub`/`dec_mul`/`add_sub_one` are its `Nat`
lemmas, and `IntN.shiftRight_pos_toNat`/`neg_toNat`/`neg_ones_toNat` read
`IntN.shiftRight` (the `BitVec.ashr` of `lib/BitVec.wiz`) in `toNat` form; they use the
now-public `IntN.shiftRightBody`/`IntN.below_toNat` of `lib/Word.wiz`. This is the lemma set the RV core's barrel shifter proofs need (SLLI is closed;
the right-shift instruction probes are blocked on a conversion limitation, see
`wiz-notes/rv-shift-lemmas.md`). It imports `BitBlast` for `Bits.low`, so it is a proof
module, not part of `BitVec` itself.

## H14 S0: hardware as tagless-final code, with sharing

`lib/Hdl/Core.wiz` (`import Hdl.Core`) is the L2 layer of the HDL plan: combinational
logic is code polymorphic in its representation, `{r : HwTy → Type} → [Hw r] → r a → r b`,
over hardware type codes `HwTy` (`bits n`, `prod a b`). `Hw` has the operations (`lit`,
`add`, `sub`, `mul`, `and`, `or`, `xor`, `not`, `eq`, `ult`, `mux`, `cat`, `slice`, `pair`,
`fst`, `snd`, `share`); such code can only combine wires with them, so it is synthesisable
by construction. Two instances: `HwTy.El` (values: simulation) and `Wire` (a netlist
builder). A `Circuit i o` is a Mealy machine whose step is such code: `Circuit.run`
simulates it on values, `Circuit.netlist` builds its netlist, `Netlist.simulate` runs the
netlist, and `Verilog.emit` prints Verilog-2005. The module declares its registers (with sized initial
values), then one wire per node, then the register updates, so every name is declared
before its use (Icarus Verilog insists; the `hdl` test group runs it when it is installed). `examples/hdl.wiz` has a counter, a
saturating counter, a popcount, a 4-tap sum and a doubling chain.

Sharing has two parts:
* the netlist builder **hash-conses**: emitting a node whose operation, width and
  arguments (sorted, for commutative operations) are already present returns the existing
  node, so identical subterms are one node however they were reached;
* **auto-share**: in check mode, a `let x := v; body` with no explicit quantity becomes
  `ShareLet.share v (fun x => body)` when the class `ShareLet` is declared and an instance
  `ShareLet A B` exists for the value's type `A` and the body's type `B`. `Hdl.Core`'s one
  instance is `[Hw r] → ShareLet (r a) (r b)` (through `Hw.share`), so a meta-level `let`
  of an object value names one wire: the doubling chain `let y := x + x` at depth 20
  emits 20 adders in 25 builder steps. Write `let ω x := …` to opt out.

## H14 S1: a usable HDL: names, bundles, composition, reset, emitters

Driven by a real design (a UART on a Lattice iCEstick, written in this library and run on
the board; its findings G1–G10 are the requirements). Design notes:
`wiz-notes/hdl-usability.md`. Everything is in `lib/Hdl/Core.wiz`; examples and
tests in `examples/hdl-compose.wiz` (group `hdl`) and in the `scaling` group.

```
structure Tx (r : HwTy → Type) where      -- a bundle: a structure of signals
  line : r Bit
  left : r B4
  deriving Bundle                         -- Tx.code, Tx.pack, Tx.unpack, Tx.bundle
def txStep {r : HwTy → Type} [Hw r] (s : Tx r) (go : r Bit) : r Tx.code :=
  let idle := Hw.eq s.left (Hw.lit 4 0);  -- field access by name
  Tx.pack (Tx.mk (Hw.mux go (Hw.lit 1 0) s.line) (Hw.label "left" …))
def top : Circuit In.code Out.code := Circuit.bundled Tx.bundle In.bundle Out.bundle init topStep
-- module top(input clk, input [0:0] rx, output [0:0] tx, output [4:0] leds); reg … line; reg … left;
```

* **Structured wires.** `Wire t` is a product of node ids, one per leaf of `t`: pairs and
  projections emit nothing, `mux` at a product is one multiplexer per leaf. A code may
  carry names, `HwTy.named s t` (ignored by `El`, `width` and the bus encoding). Ports
  and registers are one per leaf, named by the path of `named` segments joined with `_`
  (`HwTy.portNames`; an unnamed leaf is `x`/`y`/`r`, with `_k` where names would clash);
  wires are named by `Hw.label "name" x`, others are `nK`. Verilog names are sanitised
  and unique. `Hw` gained `const`, `tag`/`untag`, `label`, `resetTo`, `hold`.
* **Bundles.** A structure parameterised by `r : HwTy → Type` with fields `r T` or nested
  bundles; `deriving Bundle` defines its code (a product of `named` fields) and the
  conversions. The code's tails are definitions too (`S.code := HwTy.prod (named "f₀" T₀)
  S.code.tail1`, …), `pack` ascribes each rest its tail's name and `unpack` walks the
  product with one `let` per field, so the code of both is linear in the number of fields
  (it was quadratic and cubic). (Reading field k of a structure is still k projections in
  the IR, so `pack` of a wide bundle has a quadratic number of projections.) A bundle is a *value* (`S.bundle`), not an instance: structures are
  structural types, so two structures with the same field types are one type and
  instance resolution could not tell their bundles apart (instances once declared types get
  kernel-level brands).
* **Composition** (Lava/Clash-style arrows): `Circuit.comb`, `delay`, `seq`, `par`,
  `loop` (feedback through a register), `named` (names the state), `mapIn`/`mapOut`,
  `inputName`/`outputName`, and `Circuit.inst c s x` for an instance with its own state
  inside a hand-written step. Each has its semantics as a lemma: `Circuit.runFrom_seq`,
  `run_seq` (`run (seq a b) xs = run b (run a xs)`), `run_par`, `run_delay`,
  `runFrom_loop`, `run_named`, `runFrom_comb`, `inst_el`, `stepEl_withReset`/`Enable`.
  Combinational code passed to a combinator is a function at every representation,
  `Comb i o := {r : HwTy → Type} → [Hw r] → r i → r o` (`Circuit.comb (fun x => Hw.xor x k)`),
  and a bundled step is such a function on structures (`Circuit.bundled … cntStep`).
  The netlist is flat.
* **Reset and enable**, by construction: `Circuit.withReset c` adds an input `rst` (while
  high, the next state is `c.init`: synchronous) and `withEnable` an input `en` (while low,
  the state holds), built from `Hw.resetTo`/`Hw.hold`, whose meaning at values is a
  multiplexer and which the netlist turns into a reset or enable of the register they
  feed: `always @(posedge clk) if (rst) r <= 4'd0; else if (en) r <= next;`. Where the
  pattern does not apply (a `resetTo` not feeding a register), the node stays a
  multiplexer with the same meaning. `initial` values are always printed.
* **Emitters.** `Testbench.verilog n vec cycles` (a bench that replays a vector file and
  compares every output in every cycle), `Circuit.vectors n c xs` (the vector file of a
  value simulation), `Vcd.ofRun name c xs` (a waveform of every input, output and state
  leaf), `Pcf.emit n clkPin pins` and `Pcf.check` (pin constraints from named ports:
  `Pin.one "uart_tx" 8`, `Pin.bus "leds" [99, 98, …]`).
* **Designs in a list.** `Circuit i o` quantifies over representations and lives in
  `Type 1`; `Circuit.design name c : Design` packs a top at the first order (the step at
  values and the netlist), so `List Design` works.
* **Simulation scales.** `Circuit.run` is tail recursive (`Circuit.run_eq` relates it to
  the structural `Circuit.runFrom`, the one to reason with); `Netlist.simulate` keeps node
  values in a skew-binary random-access list: O(n log n) per cycle instead of O(n²).
* **Names.** The generic helpers are `Hdl.map`, `Hdl.nthD`, `Hdl.rev`, `Hdl.show`, …
  (importers keep `List.map` and the like); the netlist types are `NetOp`, `NetNode`,
  `NetReg`, `NetPort`. (`<+>` stays.)

Not done: module hierarchy in the Verilog, enumerations at `HwTy`, wire names from `let`
binders (an elaborator hook, wishful `hdl-let-names`), asynchronous reset, several clocks.
(Numerals and operators: H14 S2.)

## H14 S2: operator notation for signals

Signals are written with operators: `c + 1`, `x &&& ~~~y`, `s.left === 0`,
`if go then 10 else if tick then s.left - 1 else s.left`, instead of
`Hw.add c (Hw.lit 7 1)` …, `Hw.mux go (Hw.lit 4 10) (Hw.mux tick …)`.
`examples/hdl-operators.wiz` shows each design both ways.

| notation (at `r (HwTy.bits n)`, `[Hw r]`) | meaning | precedence |
|---|---|---|
| numeral `k` | `Hw.lit n k`: the width from the type | |
| `a + b`, `a - b`, `a * b`, `-a` | `Hw.add`, `Hw.sub`, `Hw.mul`, `0 - a` | 65, 65, 70, 75 |
| `a &&& b`, `a ^^^ b`, `a \|\|\| b`, `~~~a` | `Hw.and`, `Hw.xor`, `Hw.or`, `Hw.not` | 60, 58, 55, max |
| `a <<< k`, `a >>> k` (`k : Nat`) | logical shifts by a fixed number of places: wiring (`Hw.shl`, `Hw.lshr`) | 75 |
| `a <ᵤ b`, `a ≤ᵤ b`, `a >ᵤ b`, `a ≥ᵤ b` | unsigned comparisons, one bit (`Hw.ult`, `Hw.ule`, `Hw.ugt`, `Hw.uge`) | 62 |
| `a === b`, `a =/= b` | equality, inequality, one bit (`Hw.eq`, `Hw.neq`) | 61 |
| `if c then a else b` (`c : r HwTy.bit`) | `Hw.mux c a b`, at any `r t` | |

* **Classes.** `+ - * -x` and numerals are the numeric classes (`Add` … `OfNat`, HD9).
  The bitwise operators are new classes in the prelude, as in Lean: `AndOp`, `OrOp`,
  `XorOp`, `Complement`, `ShiftLeft`, `ShiftRight`, with instances for `Nat`, `UIntN w`
  (and so `BitVec n`) and signals. The shifts take the amount as a `Nat`: a fixed amount
  is what hardware shifts by wiring (a concatenation with `k` zeros and a slice; no
  shifter; by `n` or more places, `0`).
* **Comparisons are the HDL's own.** They return a 1-bit signal, not a `Bool`, so they are
  not `==`/`<` (Chisel makes the same choice: `===`, `=/=`), and they are unsigned (`ᵤ`,
  leaving room for signed ones). As in Verilog they bind tighter than the bitwise
  operators: `idle &&& s.cnt === 9` needs no parentheses.
* **`if` on a signal.** `if c then a else b` is a `match` on a `Bool` (13c). When the
  condition's type is not a data type and has an instance `Mux C C` (the prelude's class
  `Mux C A`, whose HDL instance is `Mux (r HwTy.bit) (r t)`), the elaborator makes it
  `Mux.mux c a b` instead (`ifMux?` in `Wiz/Elab/Term.lean`), at an instance `Mux C A`
  for the branches' type `A`. Every other condition (a `Bool`, an unsolved type, `Nat`, a
  type without a `Mux` instance) takes the ordinary path, with its messages, and
  `if b then rfl else rfl` still refines the goal. A branch that is a numeral (or an `if`
  of numerals) is elaborated after the other, so `if t then 0 else c + 1` gets its width
  from `c`.
* **Constants of the expected width.** A numeral is a literal; a meta-level `Nat`
  expression is `Hw.ofNat e` (`c === Hw.ofNat (n - 1)`), whose width comes from the type.
* **Same circuits.** The instances are the `Hw` operations, so a circuit written with the
  operators has the netlist and the Verilog of the one written with `Hw.add` …, byte for
  byte (`examples/hdl-operators.wiz`; also the iCEstick UART's `txStep` and `rxStep`
  rewritten). Associativity matters for that: `a &&& b &&& c` is `(a &&& b) &&& c`, a
  different (equivalent) netlist from `Hw.and a (Hw.and b c)`.
* **Printing.** The operators print back as written (11r): `fun x y => if x === y then
  x + 1 else x <<< 2 &&& ~~~y`. `Mux.mux` and `Hw.mux` print as `if`; and a numeral at any
  type other than `Nat` (`OfNat.ofNat A n _`) now prints as the numeral, for `Int` and
  words too (`fun x => x + 1 : Int → Int`).

Not done: ASCII spellings of `≤ᵤ` …. (Shifts by a signal, signed comparisons, arithmetic
shift and `&&`/`||` on signals: H14 S4.)

## H14 T: temporal properties of circuits (prototype)

Stating and proving properties of circuits over unbounded time, after TLA+, LTL and
SVA. `lib/Hdl/Temporal.wiz`, on the traces and Mealy machines of H14 C1 (`lib/Trace.wiz`);
examples and tests in `examples/hdl-temporal.wiz` (group `hdl`). Survey and design:
`wiz-notes/hdl-temporal.md`.

```
def Uart.onlyThat_a5 :     -- the loopback reports byte 0xa5 and nothing else, for ever
    TL.always (TL.nowB (fun o => onlyByte 165 o.1 o.2)) (Mealy.obs loopM loopback.init (sendOnce 165)) 0 :=
  Mealy.always_settled_const loopM (onlyByte 165) loopback.init (sendOnce 165) quiet F (loopIdle 165)
    (sendOnce_from 165) (refl Bool.true) (refl (loopIdle 165)) (loopIdle_fixed 165) (loopIdle_ok 165)
```

* **Formulas** `TL A := Trace A → Nat → Prop`: a proposition about a trace at a cycle.
  `TL.always φ σ t := ∀ k, φ σ (k + t)`, `TL.eventually` its `∃` (traces are functions, so
  □ is a Π and ◇ an impredicative `∃`, not ν and μ).
* **Operators**: `now`/`nowB` (atoms), `and`/`or`/`imp`/`not`, `next` (○), `nexts n`
  (`##n`), `within n` and `during n` (bounded ◇ and □), `delayRange m n` (`##[m:n]`),
  `until`, `implies`/`impliesNext` (`|->`/`|=>` for a Boolean antecedent), `past n`
  (`$past`), and TLA's `leadsTo`, `infOften`, `WF`, `SF`, `act` and `stut` (`[R]_v`).
* **Laws**: `always_now`, `always_next`, `always_cons`, `always_ind` (induction on time),
  `always_of`, `always_mono`, `always_and`, `always_during`, `eventually_now`,
  `eventually_next`, `eventually_mono`, `within_eventually`, `splitTime`/`splitAt` (a
  transient phase, then the rest).
* **Proof rules** (with `Mealy.invariant` and `Mealy.simulates` from H14 C1):
  `Mealy.refinesStut` (TLA refinement up to stuttering), `TL.fairStep` (liveness from a
  fair Boolean event: WF1), `TL.rank` (liveness with a bound from a ranking function),
  `Mealy.settles`, `always_settled` and `always_settled_const` (the run reaches a state
  that is fixed under the remaining inputs; the facts are named, `Mealy.Reaches`,
  `Mealy.Fixed`, `Trace.From`, so that concrete instances are matched by name).
* **Bounded checks by evaluation**: `Mealy.checkFrom`/`findFrom` (one pass over a run)
  with `_spec`, `checkFrom_during`, `findFrom_within`: `refl Bool.true` (the kernel
  evaluates) becomes a temporal statement. For long checks, `native_refl` (stage 27a).

The examples: the UART transmitter's line is high whenever it is idle, at every cycle;
the loopback delivers the byte sent within 45 cycles and reports no other, for ever
(per byte: 48 evaluated cycles and a fixed point); a valid/ready buffer refines a
Bool-level specification for every input trace (eight cases of the control bits, data
variables), keeps an offered item stable (AXI), and hands on every accepted item if the
consumer is ready infinitely often.

Not done: sequences with repetition (SEREs; planned as monitor circuits), stuttering
invariance as a theorem, a deep embedding printable as SVA, notation (□, ◇, `|->`:
dsl-ergo, stacked on this), case splits on neutral bits (they need the range of `UIntN` in
the sealed type; wishful `uintn-range-proof`), a tactic for the Bool case splits.

## H14 C1: traces, the common semantics (`lib/Trace.wiz`)

One semantics for everything that runs step by step (design:
`wiz-notes/cohesion-hardware.md`, 2.1). A trace is a function, `Trace A :=
Nat → A` (equality is pointwise and computes; a ν-stream's is stuck), and a Mealy machine
is a step `Mealy S I O := S → I → S × O`, run along an input trace by
`Mealy.stateAt m s0 xs t` and `Mealy.outAt`. `Mealy.run` is the finite run on a list and
`Mealy.run_take` says it is a prefix of the infinite one. Proof rules on the trace:
`Mealy.invariant` (an inductive invariant under an environment assumption) and
`Mealy.simulates`/`simulatesOut` (refinement by a representation map, one step as the
premise). `Trace.tail`, `map`, `zip`, `cons`, `const`, `once`, `ofList`, `take`.

A circuit is such a machine: `Circuit.mealy c` (its step at values),
`Circuit.trace c xs : Trace (El o)`, `Circuit.stateAt`, `Circuit.obs` (state and input
per cycle, what temporal formulas are about), and `Circuit.run_take`:
`Circuit.run c (Trace.take n xs) = Trace.take n (Circuit.trace c xs)`, so what a
simulation prints is what a theorem about the trace says. The temporal logic (H14 T)
builds on these.

## H14 C3: memories (`HwTy.mem`)

The toy CPU's finding C1 (no memories: a ROM as a chain of multiplexers, RAM as
flip-flops). A memory is a code, `HwTy.mem aw dw` (2^aw words of dw bits), and at values
a function `BitVec aw → BitVec dw`, so reasoning about it is pointwise. `Hw.memRead m a`
reads a word (combinationally); `Hw.memWrite m we a d` is the memory with word `a`
replaced by `d` when `we` is high (a disabled write is the memory itself, so a value
simulation's read costs the number of enabled writes so far, not the number of cycles).
A memory that is part of a circuit's state takes the
writes of its next value at the clock edge; a read of the written value in the same
cycle sees the write (the netlist adds the bypass). `Hw.const (HwTy.mem aw dw) f` is a
ROM. Lemmas: `HwTy.El.memRead_write_miss` (another address: the old word),
`memRead_write_hit`, `memRead_write_off`. A reset leaves the contents alone
(`HwTy.El.resetToAt`, as block RAM does; `Circuit.stepEl_withReset` states it), a clock
enable gates the writes.

In the netlist a memory is a `NetMem` (name, widths, initial contents, its writes in
order) read by `memRead k` nodes; the simulator keeps its contents in a trie. Verilog: an
array with an `initial` block, reads `m[addr]`, the writes in one `always` block (a later
write wins). yosys maps a memory whose read data (or address) goes through a register to
iCE40 block RAM (`SB_RAM40_4K`): `examples/hdl-mem.wiz` (a 16×8 RAM with a registered read,
a ROM; checked by Icarus and yosys in group `hdl` when they are on PATH). Small ROMs
become LUTs, a 256-word one block RAM. For Xilinx 7-series (`synth_xilinx`) the same RAMs
become RAMB18E1 or RAMB36E1 and `Hw.mul` a DSP48E1; a ROM of 4 Kbit or more is declared
`(* rom_style = "block" *)`, without which synth_xilinx builds it of LUTs
(`examples/hdl-arty.wiz`, below). What the netlist cannot express is listed in
`Netlist.errors` and printed as `// error:` lines: a choice between two different
memories, a memory in a port, a state memory replaced instead of written.
## H14 C2: lenses for structures and bundles (`lib/OpticDerive.wiz`, `lib/Hdl/Optic.wiz`)

`deriving Lens` gives every field of a structure a lens (lib/Optic.wiz's `Lens S A`), its
laws and the independence of every two distinct fields, all by `rfl`:
`S.fL : Lens (S Δ) T`, `S.fL_lawful : Lens.Lawful S.fL`, `S.f_g_indep : Lens.Indep S.fL
S.gL` (f declared before g; `Hdl.indep_symm` turns it round). The names and statements
are the ones Feral's lowering of `struct` writes, so lowered code can switch to the
deriver. On an HDL bundle (`deriving Bundle, Lens`) a lens is polymorphic in the
representation, `Tx.leftL : Lens (Tx r) (r B4)`: the same lens updates values in a proof
and wires in synthesis. `Hdl.zoom l g` runs a sub-step `g` on the place `l` of a state
(`Hdl.zoom_get`), and `Hdl.zoom_frame` is the frame rule: a place independent of `l` is
unchanged, for every state (no evaluation needed). `Bundle.lens b` (with
`Bundle.Lawful b`, `rfl` for derived bundles) and `HwTy.fstL`/`sndL` are the packed
views at values. Example: `examples/hdl-optic.wiz` (group `hdl`).

## H14 S3: fast simulation for compiled programs (`import Hdl.Sim`)

Compiled, the value simulation (`Circuit.run`, `Design.runLeaves`) runs the step function
at `HwTy.El` every cycle, and with it every meta-level computation the step contains:
table trees and top-level constants (compiled code does not cache a closed top-level
definition: each use computes it again), widths and constants computed from the
configuration, bundle codes, `pack`/`unpack`, and a dictionary call and a closure per
operation. Profiled on the iCEstick OLED demo (`oled_fast`, 1068 netlist nodes, about
1400 cycles/s): about 60% of the time is allocation and reference counting, and the
table trees (`RomT.go`, `List.take`) are rebuilt in every cycle. `Netlist.simulate` is no
faster (an allocation per node in its random-access list).

`lib/Hdl/Sim.wiz` runs the netlist instead: synthesis is the partial evaluation (all the
meta-level work is done once, and the netlist is hash-consed), and the netlist is turned
once into a flat program (a constructor per node with exactly its operands, constants
written once, input ports and register outputs as slots) that runs over native arrays
updated in place (`Array`, lib/Std.wiz). Memories (`NetMem`, H14 C3) are one flat native array (each
memory's words from its base) plus a trie for addresses beyond a memory's range (as raw
port values can give); `memRead` nodes read it during the cycle and the writes are applied
at the clock edge in order (a later write wins), exactly as `Netlist.simulate` does (a read
in the same cycle sees the old contents; the netlist's bypass nodes give the new word).

* `Netlist.simFast n xs` computes exactly what `Netlist.simulate n xs` computes (the same
  formulas on the same numbers, node by node) for every well-formed netlist
  (`Netlist.wellFormed`: arguments refer to earlier nodes, register reads to registers,
  register inputs and outputs to nodes; every netlist `Circuit.netlist` builds), and is
  `Netlist.simulate` on any other.
* `Circuit.simFast c xs` = `Circuit.runLeaves c xs`, `Design.simFast d xs` =
  `Design.runLeaves d xs`, by the netlist's agreement with the values (which the `hdl`
  group and a design's own check, such as `oled gen`'s, establish).
* Compiled code only: `Array` has no definition the kernel or `#eval` could run.
* About 25× the value simulation on `oled_fast` (about 35000 cycles/s) and 13× on
  `examples/hdl-sim-bench.wiz` (informal numbers; `bench/hdl-sim` in wiz-tools times it).
  `examples/hdl-sim.wiz` (the `hdl` group) checks `simFast` against `Netlist.simulate`
  (hash-consed and naive netlists) and `Circuit.run` on every operation, 70-bit widths,
  reset and enable, a table tree and composition, and the fallback.

Not done: skipping nodes whose arguments did not change (event-driven simulation),
generated C for a netlist, a value simulation that keeps its meta-level work (caching
closed top-level definitions in compiled code would remove the table rebuilding).

## H14 S4: the iCEstick gaps: shifts by a signal, signed operations, `&&`/`||`, BitPack, reset and enable

What the iCEstick projects (`wiz-icestick-uart`, FINDINGS.md) still had to
work around after S1 and S2. Everything is in `lib/Hdl/Core.wiz`; the examples and tests
are `examples/hdl-gaps.wiz` (group `hdl`, with Icarus Verilog test benches when
`iverilog` is installed) and a shifter in `examples/hdl-sim.wiz` (S3's fast simulation).

| notation (at `r (HwTy.bits n)`) | meaning | Verilog |
|---|---|---|
| `a <<< s`, `a >>> s` (`s : r (HwTy.bits m)`) | logical shifts by a signal (`Hw.shlBy`, `Hw.lshrBy`) | `a << s`, `a >> s` |
| `a >>>ₛ s` | arithmetic shift right by a signal (`Hw.ashrBy`) | `$signed(a) >>> s` |
| `a >>>ₛ k` (`k : Nat`) | arithmetic shift right by a fixed amount: wiring (`Hw.ashr`) | |
| `a <ₛ b`, `a ≤ₛ b`, `a >ₛ b`, `a ≥ₛ b` | signed (two's complement) comparisons, one bit (`Hw.slt`, `sle`, `sgt`, `sge`) | `$signed(a) < $signed(b)` |
| `a && b`, `a \|\| b` (`a b : r HwTy.bit`) | `a &&& b`, `a \|\|\| b` | `&`, `\|` |

* **Shifts by a signal** are four new `Hw` operations (`shlBy`, `lshrBy`, `ashrBy`, `slt`)
  and four new `NetOp`s (`shl`, `lshr`, `ashr`, `slt`; codes 20–23, leaving 17–19 to
  memories, H14 C3). The values (`HwTy.El`), the netlist simulation and `Hdl.Sim` all
  compute them with one set of functions on numbers (`Hdl.shlN`, `lshrN`, `ashrN`,
  `sltN`), and an amount of `n` or more gives 0 (or all sign bits) without computing
  `2^s`. `examples/hdl-gaps.wiz` checks the values against lib/BitVec.wiz's own
  `BitVec.shl`/`lshr`/`ashr`/`slt`/`sle` (every 8-bit value and amount), and the
  Verilog with a test bench that replays the value simulation in Icarus Verilog.
* **The shift notation takes any amount type.** `<<<` and `>>>` are now the prelude's
  `HShiftLeft A B`/`HShiftRight A B` (Lean's `HShiftLeft` without its result type), with
  `HShiftLeft A Nat` from every `ShiftLeft A`, so `Nat`, words and the fixed shifts of S2
  are unchanged, and the HDL adds `HShiftLeft (r (bits n)) (r (bits m))`. A numeral amount
  is a `Nat` (the default type of a numeral), so `x <<< 2` is still wiring.
  `>>>ₛ` is the HDL's class `AShiftRight A B` (signals only).
* **`&&` and `||` on one-bit signals.** The prelude's `a && b` is
  `if a then b else Bool.false` and `a || b` is `if a then Bool.true else b`. When `a` is a
  signal (S2's `if`-as-a-mux test), the elaborator (`ifMux?`) makes them the gates
  `AndOp.and a b` / `OrOp.or a b` at the condition's type, so they print as `&&&`/`|||`
  and have the Verilog of those. On `Bool` they are unchanged (`!` is still `Bool.not`
  only: use `~~~` on a signal).
* **`deriving BitPack`.** `structure BitPack A` is a type's values as bit vectors of one
  width (a value, not an instance, as `Bundle`). For an **enumeration** (no parameters,
  constructors without fields) constructor `i` is the number `i` in
  `⌈log₂ #constructors⌉` bits (Clash's encoding):
  ```
  inductive Phase where | idle | start | data | stop  deriving BitPack
  -- Phase.width = 2, Phase.code = HwTy.bits 2, Phase.toNat, Phase.ofNat (out of range:
  -- the first constructor), Phase.pack : Phase → HwTy.El Phase.code, Phase.unpack,
  -- Phase.unpack_pack : Phase.unpack (Phase.pack p) = p (by cases), Phase.bitPack,
  -- Phase.lit p : r Phase.code (the constant in a circuit: `s.ph === Phase.lit .stop`)
  ```
  A bundle's field can be `r Phase.code`. For a **bundle** `S Δ r` it adds `S.width`,
  `S.toBits : S Δ r → r (HwTy.bits (S.width Δ))` and `S.ofBits` (the bundle as one bus:
  `Hw.packBits`/`Hw.unpackBits`, first field in the high bits as `HwTy.pack`; wiring
  only), `S.unpack_pack : S.unpack (S.pack s) = s` at values and `S.bitPack`; it derives
  the `Bundle` too when `S.code` does not exist yet (`deriving Bundle, BitPack` or just
  `deriving BitPack`). The bit-level round trip `S.ofBits (S.toBits s) = s` holds by `rfl`
  for closed values (the example checks one, and all 32 values of a 5-bit bundle); a
  general lemma needs words' range proofs (stage 22l) and lemmas on `concat`/`slice`.
* **Reset and enable: the convention.** A design with a reset or a clock enable takes
  them as its first inputs, named `rst` and `en`, reset first: both synchronous and
  active high, and the reset wins over the enable, as
  `always @(posedge clk) if (rst) r <= init; else if (en) r <= next;`. Three ways to get
  it, all of which the netlist turns into the register's reset and enable (not
  multiplexers):
  * a whole circuit: `Circuit.withResetEnable c` (= `withReset (withEnable c)`; S1's
    `withReset`, `withEnable` alone);
  * one register: `Circuit.registerR t init`, `registerE`, `registerRE` (a `delay` with
    them; `Circuit.stepEl_registerRE` … say what they do in a cycle);
  * a field of a state, inside a step function: `Hw.regNext rst en init cur next`
    (`init` under `rst`, else `next` under `en`, else `cur`). The netlist sees the reset
    when `init` is the register's initial value, and the enable when `cur` is the
    register itself; otherwise it is the same multiplexers, with the same meaning.

  Every register keeps its `initial` value, which is all an iCE40 needs (yosys turns a
  non-zero initial value into inverters around a flip-flop); a reset is for targets
  without initial values and for restarting a design.

Not done: a general bit-level round-trip lemma for bundles (above), `BitPack` for
inductive types with fields (a tag and the widest constructor's fields), `!` on signals,
`match` on an enumeration signal (staged `match`, hdl-staging-research S3), asynchronous
reset.

## Xilinx 7-series pin constraints and the Arty A7 (`Hdl.Xdc`, `Hdl.Arty`)

`lib/Hdl/Xdc.wiz` (`import Hdl.Xdc`) is `Pcf` for Xilinx: an `XBoard` is the clock's
package pin and period (picoseconds), an I/O standard and a table of resources (`XPin.one
port pin`, `XPin.bus port pins`, bit 0 first; `XPin.rename`, `XPin.take k`).
`Xdc.emit n board` writes the XDC (`set_property -dict { PACKAGE_PIN … IOSTANDARD … }`
per port bit, `create_clock` for `clk`) that Vivado and nextpnr-xilinx read; ports are
looked up by name, so the table can list the whole board. `Xdc.check n board` lists the
ports without a resource and those of another width.

`lib/Hdl/Arty.wiz` (`import Hdl.Arty`) is the Digilent Arty A7 (Artix-7, CSG324): its pins
from Digilent's master XDC (`clk` E3 at 100 MHz, `led` 4, `rgb` 12, `btn` 4, `sw` 4,
`uart_rx` A9 and `uart_tx` D10 (FT2232 channel B), `ck_rst`, the Pmod headers `ja` … `jd`
8 each; all LVCMOS33) as `Arty.board`, and its two devices, `Arty.Device.a35t`
(xc7a35ticsg324-1L, the default) and `.a100t` (xc7a100tcsg324-1), with the part names
Project X-Ray and nextpnr use. `examples/hdl-arty.wiz` (group `hdl`) checks the XDC and
that synth_xilinx maps its RAMs, ROM and multiply to RAMB18E1, RAMB36E1 and DSP48E1. The
flow from there to a bitstream (yosys, nextpnr-xilinx, fasm2frames, xc7frames2bit; the
openXC7 toolchain from Nix) is a separate package, wiz-arty, as wiz-icestick-uart is for
the iCEstick. Its four designs (blinky, UART hello and echo, and `squares` with a RAMB18E1
and a DSP48E1) ran on an Arty A7-35T on 2026-11-12.

**UART clock rates.** An FT2232 (the USB-UART of both boards) makes its baud rate from
3 MHz with an integer divisor, so "115200" is 3 MHz / 26 = 115384.6 baud, 0.16 % fast. A
design that relays at line rate with bounded buffering (an echo with one byte of
buffer) must send at least as fast as the host sends. A divider rounded to the nominal
rate makes the board slow, and it then drops a byte every few thousand in a long burst.
That happened on the Arty with 100 MHz / 868 = 115207 baud: one byte in about 2200. The
iCEstick's 12 MHz / 104 = 115384.6 baud equals the FT2232's rate exactly, which is why
it never showed there. Compute the divider from the host's real rate and round it down
(wiz-arty's `Ftdi.divisor` and `clocksPerBit`: 866 at 100 MHz).

## H14 P1: vendor primitives (black boxes): `Hdl.Prim`, `Hdl.Xilinx7`

A `Prim i o` (in `Hdl.Core`) declares a vendor cell: its Verilog module name, parameters
(Verilog text; `PrimParam` and `Prim.decl` write them), one port name per leaf of `i` and
of `o`, and optionally a behavioural model `HwTy.El i → HwTy.El o`. `Hw` has two more
operations: `Hw.prim p x`, an instance, and `Hw.clock`, the implicit clock as a clock
net. At the wire instance an instance is one netlist node (`NetOp.inst`, never
hash-consed) with an `instOut` node per output leaf; `Verilog.emit` prints it as a module
instance after the wires (`OSERDESE2 #(.DATA_WIDTH(8), …) u22 (.CLK(sys4x), .CLKDIV(clk),
…)`). An instance none of whose outputs is used is dropped, like any unused node.

Three kinds of leaf connect primitives only, marked by a `named` segment starting with
`@` that port names skip: `HwTy.clock` (a clock net), `HwTy.pad n` (a package pin a
buffer drives or reads) and `HwTy.inout n` (a bidirectional one, an `inout` port). A
clock goes from a circuit's clock input, `Hw.clock` or a primitive's clock output to a
primitive's clock port; a pad from a circuit's input to a buffer, or from a buffer to the
circuit's output, which is then the buffer's port with no `assign`. The netlist checks
this (`Netlist.kindErrors`, appended to `Netlist.errors`): a clock or pad used as data,
data fed to a clock port, a pad on a data output.

Registers stay on the one implicit clock. For more clocks a `Clocking` (`Hdl.Prim`)
describes a top-level wrapper: `Verilog.emitTop n ck` prints the circuit as `NAME_core`
and a module `NAME` whose clock primitive (a PLL, `X7.pll`) takes the board's `clk`, and
drives the core's first clock through a BUFG and each other domain from a PLL output
(through a BUFG) or an input pin (`Clocking.domains`).

Clock domains (`ClockDomain`: the Verilog net and its period; `ClockDomain.sys` is `clk`)
name a design's clocks without giving a circuit a second one: a circuit's registers and
memories are all on the domain `Circuit.netlistIn d` builds it for, and
`Circuit.netlist` is the `sys` case. A design with two clocks is a composition of such
circuits wired at the top; data crossing from one domain into another must pass a
synchroniser (`Hdl.Cdc`'s `Cdc.sync2 dst d`: two flops in the destination domain,
declared with `Prim.declSync`). `Netlist.domainErrors` (appended to `Netlist.errors` next
to `Netlist.kindErrors`) infers each node's domain (`Net.domOf`: an input from its
port's, a register or memory read from its own, a synchroniser's output from its clock's,
anything else the union of its arguments') and rejects a combinational path that mixes
domains, a register or memory write sampling another domain, a synchroniser clocked by
the domain it samples, and a domain the netlist does not declare. `Cdc.verilog` is the
Verilog module `wiz_sync2` that the emitted instances refer to, with `async_reg`. A
clock used as data, and data fed to a clock port, stay kind errors. A primitive clock
output can name its domain (`Prim.withOutDom`; `X7.bufgIn d` is a BUFG on `d`'s output),
so a synchroniser clocked by a BUFG output is in that domain.

Simulation: a primitive without a model is 0 at values and in `Netlist.simulate`.
`Netlist.unmodelled`/`Circuit.unmodelled` name such instances, and
`Circuit.runModelled`/`Netlist.simulateModelled` refuse to run a circuit with one. They
also refuse a netlist with more than one clock domain (`Netlist.domainRefusals`): its
registers tick at different rates, which the one-tick-per-input simulation cannot
express (a merged event schedule is not implemented).

`Hdl.Xilinx7` (`X7.*`) declares the 7-series cells of a DDR3 PHY: OBUF, IBUF, IOBUF,
OBUFDS, IOBUFDS, BUFG (with models), ODDR, OSERDESE2 (8:1 DDR with tristate),
ISERDESE2 (NETWORKING 8:1 DDR, from an IDELAYE2), IDELAYE2 (VAR_LOAD, 200 MHz reference),
IDELAYCTRL, and PLLE2_BASE as a `Clocking`. Tests (group `hdl`, examples/hdl-prim.wiz):
the Verilog, refusal, buffer models and kind errors, and yosys synth_xilinx keeping every
cell.

## H14 P2: several clock domains at the top: `Multi`, `Clocking.domains`, constraints

`Multi` (`Hdl.Core`) composes single-clock `Circuit`s into one design. A `MultiPart` is a
circuit, its `ClockDomain` and the top-level name of each input and output leaf
(`MultiPart.circuit`); a `MultiWire` is either `link src dst`, which renames the
destination input to the source node (no hardware, and the domain checker sees the
crossing), or `through cell ins outs`, one primitive instance between named nets
(`Cdc.wire dst src dstName` is `Cdc.sync2` as a top-level wire). `Multi.netlist` replays
the parts into one netlist, prefixing registers and memories with the part's name,
creates one top-level input/output for every unconnected port, shares one clock net per
domain, and runs `Netlist.kindErrors`/`Netlist.domainErrors` on the result;
`Multi.verilog` emits it. Wires must read names built earlier (parts are flattened in
order), so a wire's source is a previous part's output or a clock domain.

`Clocking.domains` maps each clock port/domain of the core to a `ClockSource`: `.pll out`
(a PLL output, through a BUFG) or `.pin port` (an input pin, connected directly).
`Verilog.emitTop` connects every clock port of the core (the first through `sys`'s BUFG)
and declares the pin ports; `Clocking.problems` reports a domain with no source.

`Xdc.emit` writes a `create_clock` for every clock domain (`ClockDomain.periodPs`; the
first falls back to the board's period) and a package pin for a second clock the board's
table names; `Xdc.check` also compares the first domain's period with the board's and
asks every later domain for a period (`Netlist.clockProblems`). `Pcf.emit` writes a
`set_frequency` for each domain with a known period, and `Pcf.check` reports a missing
one. The example/tests (group `hdl`, examples/hdl-cdc.wiz) are a `link` crossing
(rejected) and a `Cdc.wire` crossing (accepted) between two parts, their core and wrapper
Verilog, the XDC/PCF text, a BUFG output as a synchroniser's clock (`Prim.withOutDom`),
and the multi-clock simulation refusal.

## H14 V1: verified circuit optimisation (`lib/Hdl/Verified.wiz`)

The OLED demo's arithmetic units (wiz-icestick-uart, branch oled-demo: `Sphere.wiz`,
`Blobs.wiz`) are hand-optimised: no multiplier, no divider, one result bit a cycle.
`lib/Hdl/Verified.wiz` copies them (the same `Hw` code, with the control multiplexers
resolved for the phase each unit is in) and states each against its plain `Nat`
definition, one input at a time (`Hv.sqOk`, `Hv.rtOk`, …); `allBelow p n = .true` decides
it for every input of the domain, and `allBelow_sound` turns that into a `∀`.

| unit | claim | inputs | checked by |
|---|---|---|---|
| shift-add squarers (Sphere, 5 cycles) | `acc = ax² + ay²` | all 2¹⁰ | kernel |
| bit-serial root (Sphere, 5 cycles) | `h = ⌊√n⌋` | n ≤ 400 (its inputs) | kernel |
| | | n < 1024 | native |
| bit-serial root (Blobs, 7 cycles, 14 bits) | `h = ⌊√m⌋` | all 2¹³ | native |
| Blobs stage A (squares, × 4, root) | `ρ = 2⌊√(4(ax² + ay²))⌋` | all 2¹⁰ | native |
| smooth-min table | entry i = (4i)²/256 (i ≤ 16), else 0 | all 32 | kernel |
| smooth-min correction by e = abs(d₂ − d₁) | g = max(64 − e, 0), c ≤ g²/256 < c + 2 | e < 64 | kernel |
| | | all 2¹² | native |
| smooth minimum (`sminK`) | `min(d₁, d₂) − c − 1`, c as above | d₁, d₂ ∈ [−64, 192) | native |
| | | d₁, d₂ ∈ [−64, 960) (the march's) | native, on demand |
| octagonal length (`norm2`), its 11/16 | 16t ≤ 11s < 16t + 38 | s < 2048 (a, c < 1024) | kernel |
| | | all 2¹² | native |
| octagonal length | n² ≤ a² + c² ≤ 1.21 (n + 2)² | a, c < 256 | native |
| | | a, c < 1024 | native, on demand |

Two structure lemmas tie the 24-bit units to the kernel-checked pieces by definition
(`rfl`): `sminK_eq` (the smooth minimum is `smin12 − c(abs(d₂ − d₁)) − 1`) and `norm2_eq`
(`max(max(a, c), t(a + c))`). The lower bound n² ≤ a² + c² is what makes the march safe
(a step never passes through a surface).

**Trust.** `examples/hdl-verified.wiz` is kernel-checked, nothing trusted.
`examples/hdl-verified-native.wiz` uses `native_refl` (27a): with `--trust-native` only,
one axiom per check (`#print axioms` lists it), trusting erasure and the interpreter.
Both run in the test group *hdl-verified* (a heavy shard: minutes). The two 2²⁰-input
checks (about ten minutes) are `examples/hdl-verified-full.wiz`, run on demand:
`wiz check --trust-native examples/hdl-verified-full.wiz`.

**What was hard (findings).** `sat_decide` (28b/28c, PRs #197/#208) was meant to do the word-level
units, but: (F1) it is Boolean only, and nothing bit-blasts `UIntN`/`BitVec` (the bit
library, #167, is one-bit; the Nat div/mod lemmas a bridge needs don't exist); (F2) `unfold`
left a definition by cases on a numeral as a raw eliminator (PR #224); (F5) its
certificate check costs about 0.3 s per LRAT step, so a 6-bit adder's commutativity
takes about 40 s, and these units would need 10⁴ and more; (F3) exhaustive `rfl` is
about 14 ms per case for eight word operations, so the kernel stops near 2¹² inputs.
A computing reflection (`bit_decide`) is in drafts/hdl-verified/, for when the check is
fast (compiled, or a faster kernel evaluator).

## H14 C4: bit-level reasoning (`lib/Hdl/Bits.wiz`)

The toy CPU's finding C2: `rfl` reduces a multiplexer on a known select but not a gate on
a symbolic bit (`Hw.and 0 x`), so a circuit had to be written with multiplexers for its
proof to go through. `Bit.ind P h0 h1 x` (from the words' range, 22l: a one-bit word is 0
or 1) splits a property of a bit into its two closed cases, `Bit.ind2`/`ind3` two or
three bits; each case is then evaluation. Closed equations of bits are best closed with
`Bit.eqv _ _ rfl` (by their numbers), since two equal words may carry different range
proofs. The library proves the laws once: constants (`Bit.and_zero`, `or_one`, …),
`not_not`, idempotence, complements, commutativity, associativity, De Morgan,
distributivity; the multiplexer normal form (`Bit.and_mux`: `a & b = a ? b : 0`,
`or_mux`, `not_mux`, `xor_mux`; `HwTy.El.mux_same`, `mux_not` at any type); and the
Boolean bridge `Bit.toBool` (a homomorphism: `toBool_and/or/xor/not/mux`;
`Bit.eq_of_toBool`), which turns an equation of bits into a Boolean goal for
`sat_decide` (28b). Example: `examples/hdl-bits.wiz` (the CPU's stall signal written
with gates, proved equal to its multiplexer form and, once the opcode is known, to
`!txReady`, for every value of the status bits).

## Logic, heap predicates and Hoare triples

`lib/Logic.wiz` (`∧`, `∨`, `∃` with binder notation `∃ x : A, P`, `↔`, `¬`, ASCII
`/\`, `\/`, `exists`, `<->`, equality lemmas, `funext`, `propext`; [13e](stages/13-language.md)),
`lib/HProp.wiz` (model heaps, `emp`, `↦`, `⋆`, `−∗`, entailment and the separation-logic
laws), `lib/Hoare.wiz` (`wp`, triples, the frame rule, adequacy for an interpreter),
`lib/HoareTactics.wiz` (SLF-style automation: `xsimpl`, `xpull`, `xstep`, `xapp`, …) and
`lib/HoareExamples.wiz` (verified swap, list reversal, counter, list length, in-place map,
freeing a list). See [stage 24](stages/24-separation-logic.md).

`lib/EffHeap.wiz` connects the effects library ([stage 10](stages/10-effects.md)) to
these heap programs. `Cell V l` is a state effect on the cell at location `l`, and
`Eff.toProg` interprets a program over cells as a `Prog V` (with `interpret` and a
`Handler` into `Prog`). Its specification is then `Triple P (Eff.toProg c) Q`, proved
with the `x`-tactics. Separate cells commute without a `Commute` instance:
`Commute (Cell V p) (Cell V q) (Prog V)` is false, because the two orders are different
trees. `Cell.commute` proves instead that both orders meet the same specification from
`(p ↦ x) ⋆ (q ↦ y)`, so a proof of whatever follows serves either order.
The interpretation is a monad morphism: `Eff.toProg_bind` (running `c >>= f` is running
`c`, then `f` of its answer; `Prog.bind_assoc` on the way), and `Triple.effBind` states
it for specifications, so a verified `Eff` program is called with `xapp` by its
specification instead of being stepped through again.
`lib/HeapBorrow.wiz` is the bridge to Feral's functional model: a `&mut`/`&` borrow of a
heap cell (`Prog.borrowMut`, `Prog.borrowMut2`, `Prog.borrowShr`: read the cell, run the
value-level function, write the final value back), whose triples follow from the
function's `Result.Holds` specification (`Prog.borrowMut_spec`, …) or from its computed
result (`Prog.handBack_ok`, `Prog.handBack2_ok`, for `xapp`). How it fits with regions,
optics and quantities: [Resources in Wiz](resources.md); the example is
`examples/resources.wiz`.

`lib/Ref.wiz` puts mutable cells in `IO` under linear points-to tokens (plan CS7b). A
location `l : Loc V` is an ordinary value. Owning the cell is a separate token `Pts l v`
at quantity 1, so one owner per cell, no leak, no double free and no use after free are
all type errors. The token's ghost index is the cell's value, so a function's type is its
Hoare triple: `swap : (1 tp : Pts p a) → (1 tq : Pts q b) → (1 k : (1 tp : Pts p b) →
(1 tq : Pts q a) → IO B) → IO B`. `Ref.get` hands back the value with an erased proof
that it is the index. The trusted part is the four natives `wiz_ref_*` (runtime/,
over MVar cells) and their types, kept true by an invariant the API maintains; the header
of lib/Ref.wiz has the argument. Compiled code only.

## Owned handles (`lib/Handle.wiz`)

`Owned h` is the obligation to release the handle `h`: a token at quantity 1 indexed by
the handle, as `MVar.Hole m` and `Lock.Guard l` are ([25d](stages/25-concurrency.md)).
The owned constructors `File.withOwned`, `Fd.withOwned` and `Process.spawnOwned` open a
fresh handle and mint its one token; nothing else can mint one. `Handle.use` passes the
token in and hands it back, and `File.releaseOwned`, `Fd.releaseOwned` and
`Child.releaseOwned` (close, close, wait) use it up. **For handles obtained through the
owned constructors**, the release happens exactly once on every path, and there is no use
after release through this API. Handles from lib/Sys.wiz's ω API (`File.open`, …) have no
token and are not covered; the handles stay ω values, so direct calls to lib/Sys.wiz on an
owned handle are not checked either. Making the handles themselves linear (direct style,
with lib/Sys.wiz and lib/Serial.wiz moved onto this module) waits for linear Σ fields
(linear-case stage 2). Trusted: two natives (`wiz_handle_own`/`wiz_handle_disown`).

**Direct style (`IO1`, cohesion M6 part 2).** `IO1 A` (lib/IO.wiz) is an action whose result
is used once. In `do1`, `x ⇐ e;` binds an `IO1` result at quantity 1, and `(x, y) ⇐ e;` takes a
pair apart, so an owned handle's token is threaded through straight-line code. The
operations: `File.writeOwned`, `readLineOwned`, `readAllOwned` and `flushOwned`;
`Fd.writeOwned` and `Fd.readOwned`; the generic `Handle.use1`. Each returns
`(result, token)`. The releases are `File.closeOwned`, `Fd.closeOwned` and
`Child.waitOwned`.

```
File.withOwned p "w" (fun f o => do1
  (r1, o) ⇐ File.writeOwned f o "one\n";
  (r2, o) ⇐ File.writeOwned f o "two\n";
  File.closeOwned f o)
```

`IO` is unchanged and so is lib/Sys.wiz's ω API; only the owned variants are `IO1`.
Acquisition stays in continuation style until linear `match` lands (linear-case stage 2).

## Functors and Booleans

`lib/Functor.wiz` (`import Functor`): `Functor`, `Applicative`, `<$>`, `<*>`; every `Monad`
is an `Applicative` and every `Applicative` a `Functor`; `Monad`/`Functor` instances for
`Option`, `Except E` and `List`, and `Option.map`/`bind`, `Except.map`/`bind`,
`List.flatMap` (`List.map` is `lib/Text.wiz`'s, which Functor imports). See [13d](stages/13-language.md). The Prelude itself has `if … then …
else`, short-circuiting `&&` and `||`, and `!` ([13c](stages/13-language.md)).

## 9j: text and lists (`lib/Text.wiz`)

`import Text` (only `Prelude` underneath): the string and list functions a program needs,
pure (so `#eval` runs them) and linear in their input.

* **Lists**: `List.reverse`, `revApp`, `map`, `filter`, `foldl`, `foldr`, `any`, `all`,
  `find`, `isEmpty`, `head`, `take`, `drop`, `concat`.
* **Characters**: `Char.eq`, `isSpace` (ASCII), `isDigit`.
* **Strings**: `chars`, `ofChars`, `singleton`, `length`, `isEmpty`, `eq` (also `beq`),
  `lt` (by code point), `startsWith`, `endsWith`, `stripPrefix`, `stripSuffix`
  (`Option`), `contains`, `containsChar`, `take`, `drop`, `dropEnd`, `splitOn`, `join`,
  `intercalate`, `trim`, `trimLeft`, `trimRight`, `replace`, `parseNat` (`Option Nat`),
  `lookup` (in a list of pairs keyed by strings), `elem`; `Nat.repr` (decimal, pure).
  The same functions on `List Char` are `Chars.*`.

**Cost model.** A `String` is `String.mk` around a `List Char` in the kernel *and* at
runtime (`builtin string` only changes how values print). Walking a string from the
front, prefix tests, `take`/`drop` are proportional to what they walk; `String.append a b`
copies `a`, so appending in a loop from the left is quadratic (`join` and `intercalate`
build from the right); the end of a string is far (`endsWith`, `dropEnd`, `trimRight`
reverse once); and each call into C converts the list to a C string and back. Splitting
200000 characters, joining and trimming them takes 0.1 s compiled (the `text` tests).
`Std.Str` is the native alternative for indexing.

`lib/Json.wiz`, `lib/Deriving.wiz` and `lib/Hoare.wiz` import `Text` and use its
`String.eq`, `String.chars`, `String.beq`, `Nat.repr`, `List.revApp` and `List.reverse`
instead of copies of their own (two modules declaring one name are an error at import).

## Numbers: classes, integers, words

(Stage doc: docs/stages/07-type-classes.md, 7e and 7f.) The Prelude's `Add`, `Sub`, `Mul`,
`Div`, `Mod`, `Neg` and `OfNat` give `+ - * / %`, prefix `-` and numerals at every
numeric type. The operators themselves are the heterogeneous classes `HAdd A B C` … (7f,
as in Lean), which default to the homogeneous ones (`instHAdd [Add A] : HAdd A A A`), so a
library gives an `Add` instance and gets `+`; it may also give a mixed one (`HMul Nat V V`).
`x ^ k` is `HPow`, with `Pow Nat Nat`. A numeral that meets no type is a `Nat`.

| type | where | numerals | operators |
|------|-------|----------|-----------|
| `Nat` | Prelude | native literals | `+ - * / %` (natural subtraction: `2 - 3 = 0`) |
| `Int` | `lib/Int.wiz` | `5`, `-5` | `+ - * / %`, prefix `-` |
| `UIntN w` (`U8` … `U64`, `USize`, `BitVec n`) | `lib/Word.wiz` | wrap around, with a warning: `(300 : U8) = 44` | `+ - * / %`, `-` (wrapping) |
| `IntN w` (`I8` … `I64`) | `lib/Word.wiz` | `-7 : I32` | `+ - * -`, signed `/ %` (truncating, as Rust) |
| `UInt64`, `Float64` | `lib/IO.wiz` | through `ofNat` | `+ - * /` (and `%` for `UInt64`) |

* **`Int`** is `ofNat n | negSucc n`, as in Lean. Arithmetic is defined by cases on the
  natively computed Nat operations, so the kernel computes on numerals
  (`rfl : (-3 : Int) * 4 + 2 = -10`) and compiled code runs Nat's natives on the
  magnitudes (an `Int` is a small object holding a number; no native signed numbers
  yet). `builtin int := Int` makes `#eval`, `#run` and compiled `main` print `-10`
  instead of `.negSucc 9` (a printing hint, not an axiom: `#print axioms` lists nothing
  for it). Division truncates (`-7 / 2 = -3`, `-7 % 2 = -1`), like `IntN` and C. Also
  `Int.natAbs`, `Int.toNat` (negatives to 0), `Int.lt`/`le`/`beq`, and lemmas
  `Int.neg_neg`, `Int.add_zero`, `Int.zero_add`, `Int.natAbs_neg`, `Int.lt_irrefl`, `Int.abs` with `Int.abs_mul`, `Int.abs_neg`. The ring laws, `int_ring!` and the order
  are in lib/IntRing.wiz and lib/IntOrder.wiz ("Arithmetic", below).
* **Words.** One set of instances at `UIntN w` serves `U8 … U64` and `BitVec n` (aliases
  are seen through). `UIntN w` and `IntN w` have the same shape but are sealed, different
  types (22k), so `-7 / 2 : I32` is signed division and `x / 2 : U32` unsigned. Their
  constructors are private to `lib/Word.wiz` and carry the proof that the bits are below
  `2^w` (22l, erased): build a word with `ofNat`, read it with `toNat`, and use
  `UIntN.toNat_lt` for the range (`UIntN.ext`: same bits, same word; `UIntN.cases1`, in
  `lib/BitVec.wiz`: a one-bit word is 0 or 1). Compiled, `a + b : U32` is the native `wiz_word_add` (the dictionary is
  inlined away), as `UIntN.add a b` was.

## Arithmetic: laws, orders and ring normalisers

Moved from the dogfooding package wiz-reals (its finding G2: lib/ had no arithmetic
library, so it proved everything from `0` and `succ`). Each module has a module doc
and doc comments; std's tests check one example of each.

| module | contents |
|--------|----------|
| `lib/Order.wiz` | the classes `LE`, `LT`, `Equiv`: notation `a ≤ b`, `a < b`, `a ≈ b` (propositions) |
| `lib/Nat.wiz` | `congrArg`, `congrArg2`, `Eq.mp'`, `Eq.via`; the commutative semiring laws of `Nat`, cancellation, truncated subtraction; `Nat.Le`/`Nat.Lt` (`Nat.le m n = .true`, so many facts are `rfl`) with `≤`/`<` instances; `Ordering`, `Nat.cmp` |
| `lib/Ring.wiz` | `nat_ring! lhs = rhs`: identities of commutative semirings at `Nat`, by reflection |
| `lib/IntRing.wiz` | `int_ring! lhs = rhs` at `Int`; the ring laws `Int.add_comm` … `Int.neg_mul`; the pair representation `Int.ofPair a b = a - b` |
| `lib/IntOrder.wiz` | `Int.Le`/`Int.Lt` (`b - a` not negative) with `≤`/`<`; monotonicity, cancellation, `Int.abs` and the triangle inequality |
| `lib/Rat.wiz` | `Q`: unreduced fractions with `≈`, an ordered field up to `≈` (`Q.inv`, `Q.mul_inv`, `Q.abs_add`, `Q.lt_ceil`); `q_ring! lhs ≈ rhs` |
| `lib/RingTactic.wiz` | `by ring`: the three normalisers as a tactic that reads the goal |

```
import Rat

def t (a b c : Nat) : (a + b) * c = c * b + a * c := nat_ring! (a + b) * c = c * b + a * c
def u (a b : Int) : (a - b) * (a + b) = a * a - b * b := int_ring! (a - b) * (a + b) = a * a - b * b
def v (p q : Q) : (p + q) * (p + q) ≈ p * p + 2 * p * q + q * q :=
  q_ring! (p + q) * (p + q) ≈ p * p + 2 * p * q + q * q
```

* **The normalisers** read the syntax of the equation (`+`, `*`, `-`, parentheses,
  ascriptions, numerals, and `Nat.succ` at `Nat`); every other subterm is an atom,
  compared by its syntax. Each side is reified as an expression over atoms
  (`NatExpr`, `IntExpr`, `QExpr`), normalised to a sorted list of monomials, and the
  macro expands to `X.proveAt lhs rhs ρ e₁ e₂ rfl rfl rfl`: the kernel checks that the
  expressions evaluate to the sides and that their normal forms agree (with a Boolean
  comparison: an `rfl` at a list type computes through OTT's Σ of equations and is much
  slower). Soundness is proved once (`NatExpr.eval_norm`, …), so no axiom is involved.
* **`by ring`** (`lib/RingTactic.wiz`) reads the goal instead of repeating it: after
  introducing its `∀`s, a goal `lhs = rhs` at `Nat` or `Int` (seen through
  `TacticM.eqView`, stage 28b) or `lhs ≈ rhs` at `Q`. It reifies the *elaborated* sides
  (`Add.add`/`HAdd.hAdd`, `Mul.mul`, `Sub.sub`, `Neg.neg`, `Nat.add` …, `OfNat.ofNat`,
  literals, `Nat.succ`; atoms compared with `Expr.beq`, so `f x` and `f (x)` are one
  atom), compares the normal forms itself (a false identity is an error naming both
  sides) and closes the goal with `NatExpr.prove ρ e₁ e₂ Ring.trivial` (or `IntExpr`,
  `QExpr`), which the kernel checks by computing. `def t (a b : Int) : (a - b) * (a + b)
  = a * a - b * b := by ring`.
* **The `!` forms are term macros**, so the equation is written twice (statement and
  proof): a term macro sees only its own syntax. They remain for terms (`Eq.trans (…)
  (int_ring! …)`), where no goal is at hand.
* **`int_ring!` is bootstrapped.** Its soundness needs the ring laws of `Int`, proved by
  `int_pair_ring!`, which maps an integer identity through `Int.ofPair` to a `nat_ring!`
  identity (slower; use `int_ring!`).
* **`Q` is not reduced**: `p ≈ q` is `p.num · q.den = q.num · p.den`, so every law is an
  integer identity and `q_ring!` is `int_ring!` on numerators and denominators. Use the
  congruences (`Q.add_congr`, `Q.le_congr`, …) to rewrite under `≈`.
* `Vec.wiz` and `Hoare.wiz` import `Nat` for the lemmas they used to define themselves.
## Native structures: word arrays, word maps, interned strings

`lib/WordArray.wiz` (`U8Array`, `U32Array`, `U64Array`), `lib/WordMap.wiz` (`U64Map V`)
and `lib/Intern.wiz` (`InternTable`, ids as `U32`): list models with laws, run natively
in compiled code, updated in place when unique. See `docs/stages/29-natives.md`.
