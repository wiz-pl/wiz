# rv-add: the 34-bit adder bridge and the first arithmetic instructions

Agent `rv-adder`, 2026-11-14. Worktree `/workspace/wt/rv-adder`, branch
`agent/rv-adder`, based on `origin/master` 2ebcfd13 (the rv-shift lemmas merged).
Nothing outside the worktree is changed: `/workspace/wiz-rv` is read-only and the probes
import it with `-I`. Local commit only (no push, no PR).

**TL;DR.** FINDINGS H2's word-level lemma is `lib/BitVecAdd.wiz`: the core's
`slice 1 32 (zext1 {a,1} + zext1 {b', sub})` is `BitVec.add a b` (sub = 0) or
`BitVec.sub a b` (sub = 1). `AddSub.wiz` then proves `Pf.Claim` for **ADD**, **ADDI**
and **SUB** against the canonical multi-cycle core with one `Eq.congrArg` each, no
`native_refl`, kernel-checked: `wiz --no-cache check -I /workspace/wiz-rv/src` is
**77 s** (the eight existing claims re-check in the same run), under the 2 GB `light`
cap. `SLT`/`SLTU` are the next instructions; the remaining lemma is the adder's
*carry-out* bit (bit 33) and its comparison reading (below).

## 1. The library lemma (`lib/BitVecAdd.wiz`, `import BitVecAdd`)

The circuit (`Rv.Core`'s `s34`/`sum`), for `a b : BitVec 32` and the instruction's
`sub` control bit `s : BitVec 1`:

```
adcForm s a b = add (zext1 (cat a 1)) (zext1 (cat (mux s (not b) b) s))   : BitVec 34
adc      s a b = ofNat 32 (shiftRight (adcForm s a b).toNat 1)             : BitVec 32
```

`zext1 x = cat 0 x`, `muxBit` is `Hw.mux`'s term at values (`Bool.not (Nat.beq c.toNat 0)`
then `match`), so `BitVec.adc s a b` *is* the core's `slice 1 32 s34` by unfolding.

| lemma | statement |
|---|---|
| `BitVec.adc_eq` | `adc s a b = muxBit s (sub a b) (add a b)` (**the bridge**) |
| `BitVec.adc_zero`, `adc_one` | `adc 0 a b = add a b`, `adc 1 a b = sub a b` |
| `BitVec.catToNat` | `(concat hi lo).toNat = low (m+n) (hi.toNat · 2^n + lo.toNat)` |
| `BitVec.zext1ToNat` | `(zext1 x).toNat = low (1+n) x.toNat` |
| `Bits.cat_lt` | `A < 2^32 → A·2+1 < 2^33`; `Bits.dec32_lt` is the closed instance |
| `Bits.low33_cat`, `low33_cat0` | `low 33 (A·2+1) = A·2+1`, `low 33 (A·2+0) = A·2` |
| `Bits.div_low_succ` | `low (w+1) n / 2 = low w (n / 2)` (the carry falls off) |
| `Bits.div_two_add`, `div_two` | `(2q+1)/2 = q`, `(2q)/2 = q` |
| `BitVec.adcW1`, `adcW2_zero`, `adcW2_one` | the three operand values (`2a+1`, `2b`, `2~b+1`) |
| `BitVec.adc_zero_toNat`, `adc_one_toNat` | `(adc 0 a b).toNat = low 32 (a+b)`, `(adc 1 a b).toNat = low 32 (a + (2^32 - b))` |

Proof shape (same normal form as `lib/BitVecShift.wiz`): everything is a `Bits.low` of a
`Nat` expression. The `low 33` of each 32-bit `cat` operand is the operand
(`Bits.low_of_lt`), the 34-bit sum's `low 34` divided by 2 is `low 33` of the half
(`Bits.div_low_succ`), and the last step is `(2q+1)/2 = q` or `(2q)/2 = q`. For the
borrow form, `~b + 1 = 2^32 - b` (`Bits.sub_pow` + `Bits.wnot_val`), which is
`BitVec.sub`'s `toNat`. No step relies on a `Nat` identity that the kernel's normalizer
closes (those are `True` and cannot be `Eq.trans` links: `wiz-notes/rv-shift-lemmas.md`
§4/§7); the polynomial reshapes are `nat_ring!` equations and the `+ 0` of a `cat` is
removed by an explicit `Nat.add_zero` (a stuck `q + 0` and `q` are **not** convertible,
so it cannot be left to the conversion check under a `low`).

## 2. The claims (`drafts/rv-add/AddSub.wiz`)

`Rv.Proofs`'s `Pf` framework, unchanged: from the decode phase, for a symbolic
architectural state and instruction word `w`, two cycles give `Rv.exec`'s PC and `rd`.

```wiz
def RvAdd.add_ok  : Pf.Claim (Pf.w (A.add 9 2 3)) 9
def RvAdd.addi_ok : Pf.Claim (Pf.w (A.addi 7 7 1365)) 7
def RvAdd.sub_ok  : Pf.Claim (Pf.w (A.sub 5 5 1)) 5
```

Each is one `Eq.congrArg` on the register half of `Pf.G` (`adc_zero`/`adc_one`) and
`Pf.ok` for the two cycles, exactly as `drafts/rv-shift/SLLI.wiz`. The `sub` control
signal is concrete for a fixed word (ADD/ADDI: 0; SUB: 1), so the two specialised
lemmas suffice; `adc_eq` states the general form.

## 3. What was run

```
heavy lake build wiz tests                                        # 415 jobs, OK
wiz --no-cache check lib/BitVecAdd.wiz                            # EXIT 0, 20 s (5 s cached)
wiz check --no-cache -I /workspace/wiz-rv/src drafts/rv-add/AddSub.wiz
    # EXIT 0, 77 s (Rv.Proofs' eight existing claims re-check too), light 2 GB
heavy lake test -- '=vec'          # 24 passed, 0 failed (new BitVecAdd case)
```

Logs: `/tmp/rv-adder-final-lib.log`, `/tmp/rv-adder-final-addsub.log` (uncached),
`/tmp/rv-adder-vec.log`, plus the earlier probes `/tmp/rv-adder-*.log`. The `vec` test
group has a `BitVecAdd` case (`Tests/Groups/Vec.lean`).

## 4. The carry-out (for SLT/SLTU), and what remains

`SLTU` writes `zext32 (not (bitOf 33 s34))` (the carry out of the 34-bit sum), the spec
writes `one32 (BitVec.ult a b)`. With `s34 = 2·(a + (2^32 - b))` the carry-out is
`a ≥ b`, so `not carry = a < b`. The *Nat* half is now in the library:

| lemma | statement |
|---|---|
| `Bits.div_div` | `(n / 2^k) / 2^j = n / 2^(k+j)` |
| `Bits.div_low_pow` | `div (low (w+1) n) 2^w = low 1 (div n 2^w)` (the carry bit) |
| `Bits.mul2_add` | `2·P = P + P` |
| `Bits.div_one_of` | `P ≤ Z < 2P → Z / P = 1` |
| `Bits.borrow_le` | `b ≤ a → (a + (2^32 - b)) / 2^32 = 1` |
| `Bits.borrow_gt` | `a < b → (a + (2^32 - b)) / 2^32 = 0` |

What is still needed for the SLTU claim is the 1-bit *assembly*, in this order:

1. `BitVec.adcTop s a b = ofNat 1 (div (adcForm s a b).toNat 2^33)` (the core's
   `bitOf 33 s34`), and for `s = 1`
   `(adcTop 1 a b).toNat = div (a + (2^32 - b)) 2^32`: `adcFormToNat`, then
   `Bits.div_low_pow 33`, then `s34 = 2·Z` (`nat_ring!`) with `Bits.div_div 1 32` +
   `Bits.div_two`, then the `~b + 1 = 2^32 - b` step from `adc_one_toNat`;
2. `Nat.lt_not_le a b : Nat.lt a b = Bool.not (Nat.le b a)` (4 lines: `Nat.lt a b` and
   `Nat.le b a = Nat.lt b (succ a)` are complementary, by induction on `a`, `b`), to turn
   `BitVec.ult` into the `Nat.le` of `borrow_le`/`borrow_gt`;
3. the word equality `zext32 (not (adcTop 1 a b)) = one32 (BitVec.ult a b)` by
   `UIntN.ext`: `(zext32 u).toNat = low 32 u.toNat` (`BitVec.catToNat`), `u.toNat =
   1 - T` (`Bits.wnot_val` at width 1), then `Bool.cases` on `Nat.le b a`:
   `Nat.le b a = true` gives `T = 1`, so `1 - T = 0` while `ult = Bool.not true = false`
   (both sides `low 32 0`); `= false` gives `T = 0`, so `1 - T = 1` while
   `ult = Bool.not false = true` (both sides `low 32 1`), each branch by `transp` along
   the branch equation (the `Bool.not`/`if`/`low` of numerals compute).

`SLT`/`SLTI` then use the same top-bit lemma at bit 31 with the sign selection
(`bit 31 sum` when the signs agree), i.e. `adcTop` at bit 31 plus `IntN.isNeg`.

**JAL/JALR/branches** need the adder only for `pc + imm`, which the core already does
with `BitVec.add`, so it is free; their remaining obstacle is the target's alignment
trap: the core checks `bitOf 1 target`, the ISA checks `Nat.mod target 4 = 0`. With a
symbolic PC those differ when `PC` is odd (the core ignores bit 0), so the local claim
needs a PC-alignment invariant (`Nat.mod pc 4 = 0`) — a statement decision, not a lemma.
