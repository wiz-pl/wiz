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
cap. `SLTU`/`SLTIU` (the carry-out bit, bit 33) are in `Compare.wiz`; **`SLT`/`SLTI`**
(the sign-XOR mux, §6) are in `Signed.wiz`, and §7 is the branch/JAL alignment decision
(the `Nat.mod`/addition lemma and a `Pf.ClaimAligned` variant).

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

## 2. The claims (`drafts/rv-add/AddSub.wiz`, `Compare.wiz`)

`Rv.Proofs`'s `Pf` framework, unchanged: from the decode phase, for a symbolic
architectural state and instruction word `w`, two cycles give `Rv.exec`'s PC and `rd`.

```wiz
def RvAdd.add_ok   : Pf.Claim (Pf.w (A.add 9 2 3)) 9
def RvAdd.addi_ok  : Pf.Claim (Pf.w (A.addi 7 7 1365)) 7
def RvAdd.sub_ok   : Pf.Claim (Pf.w (A.sub 5 5 1)) 5
def RvAdd.sltu_ok  : Pf.Claim (Pf.w (A.sltu 9 2 3)) 9
def RvAdd.sltiu_ok : Pf.Claim (Pf.w (A.sltiu 7 7 1365)) 7
```

Each is one `Eq.congrArg` on the register half of `Pf.G` (`adc_zero`/`adc_one`/
`sltu_val`) and `Pf.ok` for the two cycles, exactly as `drafts/rv-shift/SLLI.wiz`. The
`sub` control signal is concrete for a fixed word (ADD/ADDI/SLTU/SLTIU: 0, 0, 1, 1), so
the specialised lemmas suffice; `adc_eq` states the general form. The comparison word is
`zext32 (not carry)`, so `Compare.wiz` also needs the branch on `Nat.le b a` (below).

## 3. What was run

```
heavy lake build wiz tests                                        # 415 jobs, OK
wiz --no-cache check lib/BitVecAdd.wiz                            # EXIT 0, 21 s (5 s cached)
wiz check --no-cache -I /workspace/wiz-rv/src drafts/rv-add/AddSub.wiz
    # EXIT 0, 92 s (Rv.Proofs' eight existing claims re-check too), light 2 GB
wiz check --no-cache -I /workspace/wiz-rv/src drafts/rv-add/Compare.wiz
    # EXIT 0, 94 s (SLTU + SLTIU, same import), light 2 GB
heavy lake test -- '=vec'          # 24 passed, 0 failed (BitVecAdd case covers the new lemmas)
```

Logs: `/tmp/rv-adder-final-lib.log`, `/tmp/rv-adder-final-addsub.log`,
`/tmp/rv-adder-cmp3.log`, `/tmp/rv-adder-vec2.log`, plus the earlier probes
`/tmp/rv-adder-*.log`. The `vec` test group has a `BitVecAdd` case
(`Tests/Groups/Vec.lean`) that applies the adder, carry, borrow and div lemmas.

## 4. The carry-out and SLTU/SLTIU

`SLTU` writes `zext32 (not (bitOf 33 s34))` (the carry out of the 34-bit sum), the spec
writes `one32 (BitVec.ult a b)`. With `s34 = 2·(a + (2^32 - b))` the carry-out is
`a ≥ b`, so `not carry = a < b`. The pieces are now all in the library:

| lemma | statement |
|---|---|
| `BitVec.adcTop` | the core's carry bit: `ofNat 1 (shiftRight (adcForm s a b).toNat 33)` |
| `BitVec.adcTop_one` | `(adcTop 1 a b).toNat = (a + (2^32 - b)) / 2^32` |
| `Bits.div_div` | `(n / 2^k) / 2^j = n / 2^(k+j)` |
| `Bits.div_low_pow` | `div (low (w+1) n) 2^w = low 1 (div n 2^w)` (the carry bit) |
| `Bits.div_one_of` | `P ≤ Z < 2P → Z / P = 1` |
| `Bits.borrow_le`, `borrow_gt` | `(a + (2^32 - b))/2^32` is 1 iff `b ≤ a`, 0 iff `a < b` |
| `Nat.lt_not_le` (`lib/Nat.wiz`) | `Nat.lt a b = Bool.not (Nat.le b a)` |

and `Compare.wiz` has the 1-bit assembly: `RvAdd.sltu_le`/`sltu_gt` (the two branches of
`Nat.le b a`, each with `transp` along the branch equation and the `1 - carry` step) and
`RvAdd.sltu_val : zext32 (not (adcTop 1 a b)) = one32 (BitVec.ult a b)`, then
`RvAdd.sltu_ok` (`A.sltu 9 2 3`) and `RvAdd.sltiu_ok` (`A.sltiu 7 7 1365`, the immediate
as the `b` operand).

**A conversion trap worth knowing** (it cost hours): `BitVec.adcTop` first used
`Nat.div (adcForm s a b).toNat (Nat.pow 2 33)`, which is *definitionally* the core's
`Nat.shiftRight s34.toNat 33` (`Hw.slice`'s own definition) — but the claim's
`Pf.G ... = Pf.spec ...` check then did not finish (> 13 min, and `--inert ground` did
not help), while the `rfl` from `Pf.G` to the `shiftRight`-shaped form took 84 s. Writing
`adcTop` with `Nat.shiftRight` (the same reduction the core takes) makes it 109 s for
both claims. If a word-level lemma "should" be convertible but the check hangs, match
the *syntactic* shape of the core's expression, not just its value.

## 5. The signed forms, and the branch alignment decision

(This section is the plan as it stood after SLTU/SLTIU; §6 and §7 are what was done.)

`SLT`/`SLTI` (funct3 = 2) write `zext32 slt` with
`slt = mux (xor (bitOf 31 a) (bitOf 31 b)) (bitOf 31 a) (bitOf 31 sum)`, the spec writes
`one32 (BitVec.slt a b)`. The pieces still needed:

1. `Bits.testBit : Nat.testBit n i = Bits.bit n i` (10 lines: `Nat.testBit n i =
   Nat.isOdd (Nat.shiftRight n i)` and `Bits.bit n i = Nat.isOdd (div n 2^i)`, by
   induction on `i`);
2. the top-bit lemma `Bits.bit n w = Nat.le (2^w) n` for `n < 2^(w+1)` (induction on `w`
   with `Bits.decomp`, `Bits.bit_cons0`/`bit_consS`), so that `bit 31 (low 32 Z)`
   reads `Z ≥ 2^31`;
3. the same-sign order identity: for `A B < 2^32` with `bit 31 A = bit 31 B`,
   `Nat.lt A B` iff `bit 31 (A + (2^32 - B)) = 1` (the difference is `2^32 + (A - B)`,
   which lies in `(2^31, 2^32 + 2^31)`, so its bit 31 is 1 exactly when it is below
   `2^32`, i.e. when `A < B`);
4. the 1-bit assembly with `UIntN.cases1` on the two sign bits (`IntN.isNeg` is
   `Nat.testBit A 31`, and `IntN.lt`'s definition splits on them: signs differ gives
   `bit 31 a` directly, signs agree gives item 3).

**Branches/JAL/JALR: a statement decision, not a lemma.** Done in §7: the alignment
hypothesis, the `Nat.mod`/addition lemma, and a `Pf.ClaimAligned` variant; the general
claim is blocked by the core's *state* (see §7, "what is left").

## 6. SLT/SLTI: the sign-XOR mux (`lib/BitVecSigned.wiz`, `Signed.wiz`)

`SLT` writes `zext32 slt` with
`slt = mux (xor (bitOf 31 a) (bitOf 31 b)) (bitOf 31 a) (bitOf 31 sum)` and
`sum = adc 1 a b = sub a b`; the spec writes `one32 (BitVec.slt a b)`. The pieces, all
in `lib/BitVecSigned.wiz` (`import BitVecSigned`):

| lemma | statement |
|---|---|
| `Bits.testBit` | `Nat.testBit n i = Bits.bit n i` |
| `Bits.bit_top` | `n < 2^(w+1) → Bits.bit n w = Nat.le (2^w) n` (the top bit) |
| `Bits.bit_mod` | `Bits.bit n i = Nat.le (2^i) (Nat.mod n (2^(i+1)))` |
| `Bits.bit_add_pow` | `l < 2^w → bit (2^w + l) w` is set (induction via `Bits.cons_add`) |
| `Bits.bit31_diff` | same sign bits: `bit 31 (A + (2^32 - B)) = Nat.lt A B` |
| `Bits.bit31Word`, `bit31Word_val` | the core's `bitOf 31 x = ofNat 1 (shiftRight x.toNat 31)` and its value |
| `Bits.adc_bit31` | the difference word's bit 31 is `a < b` under equal signs |
| `Bits.slt_char` | `BitVec.slt a b` as the sign pattern of the two top bits |
| `Bits.sltMux` | **the bridge**: the core's mux (as a `BitVec 1`) is `Bits.bv (BitVec.slt a b)` |

The order identity: both words are in the same half (`|A - B| < 2^31`), the difference
of the adder is `2^32 - (B - A)` when `A < B` and `2^32 + (A - B)` otherwise
(`Bits.sub_borrow`/`Bits.sub_noBorrow`, by cancelling `B` resp. `B - A` with
`Nat.add_right_cancel`), so bit 31 of `low 32` of it is 1 exactly when `A < B`
(`Bits.mod_of_lt`, `Bits.mod_add_self`). `Signed.wiz` then has `RvAdd.slt_val` (the
core's `zext32` mux is `one32 (BitVec.slt a b)`, via `zext32_val`, `sltMux`,
`one32_val`) and the `Pf.Claim`s `RvAdd.slt_ok` (`A.slt 9 2 3`) and `RvAdd.slti_ok`
(`A.slti 7 7 1365`).

Two `Nat` induction lessons (they cost most of the time):

* `Nat.mul 2 (Nat.succ q)` is **stuck** (`2` is a numeral; `Nat.mul` recurses on its
  first argument), so `2 (h+1)` and `2h+2` are not convertible and `Nat.le (2P)
  (cons c h)` is not `Nat.le P h` by computation. The fix is to prove the comparison
  from *both implications* (`Bool.cases` + `Nat.le_or_lt`) using `Bits.le2`/
  `Bits.le_mul2_cons`, `Bits.mul2_succ`, and to keep every intermediate type as the
  literal RHS of the previous lemma (`Eq.via b h1 h2`, `Eq.mp'`, `Eq.mpr'`).
* `Eq.mp'`/`Eq.mpr'` take the motive first and are *not* interchangeable: `mp'` rewrites
  a proof at the equation's left side to the right one, `mpr'` the reverse. `transp`'s
  argument order is the surface form of `.transp` (`motive, proof, equation`) and is
  easy to get backwards.

## 7. Branch/JAL alignment (`drafts/rv-add/Align.wiz`)

`Align.wiz` has the word `jal x1, l; l:` (target `pc + 4`) and:

| lemma | statement |
|---|---|
| `Bits.mod_add_four` | `(a + 4) mod 4 = a mod 4` (the `Nat.mod`/addition lemma, via `Bits.split 2`, `Nat.mod_mq`, `nat_ring!`) |
| `Bits.mod_low_32_4` | `(low 32 n) mod 4 = n mod 4` |
| `Bits.bit1_of_mod4` | `n mod 4 = 0 → bit n 1 = .false` (the core's `bitOf 1` check) |
| `RvBr.add4_val`, `mod4_target`, `bit1_target` | the target's value and both checks under `pc mod 4 = 0` |
| `RvBr.aligned_target` | the ISA's `Nat.beq (mod t 4) 0` |
| `Pf.ClaimAligned` | `Pf.Claim` + `Nat.beq (Nat.mod a.pc.toNat 4) 0 = .true` |

`RvBr.jal_ok0` is a JAL claim for a **concrete** (all-zero) aligned state, kernel-checked
by computation (`Pf.ok ... rfl`): the core writes `pc + 4` to `x1`, jumps to `pc + 4`,
and does not trap, matching `Rv.spec`.

**What is left, and why it is a core-state problem.** With a *symbolic* PC the core's
trap check `bitOf 1 target` (a `BitVec 1` built by `ofNat 1 (shiftRight …)`) is stuck,
so `code`, `trapE`, `goE`, `npc` and the write-enable are all stuck: the kernel cannot
reduce `Pf.G` (`(Pf.step (Pf.setQ (Pf.step (Pf.at …)) q)).2.1`), and no `Eq.congrArg`
can rewrite the stuck bit because it is not a subterm of the (opaque) `Pf.G` applied to
the state. The spec's side is stuck on `Nat.beq (Nat.mod t 4) 0` for the same reason.
So the general JAL/branch claim needs a transport of the *whole core state* along the
two equations (equivalently: an unfolded `coreStep` pc/we lemma given `bit 1 target =
0`), which is `coreStep`-sized work, not a lemma. `Pf.ClaimAligned` and the alignment
lemmas above are the statement and the word-level half of it.

## 8. What was run (signed comparison and alignment)

```
wiz --no-cache check lib/BitVecSigned.wiz                        # EXIT 0, 28 s
wiz --no-cache check -I /workspace/wiz-rv/src drafts/rv-add/AddSub.wiz   # EXIT 0, 87 s
wiz --no-cache check -I /workspace/wiz-rv/src drafts/rv-add/Compare.wiz  # EXIT 0, 89 s
wiz --no-cache check -I /workspace/wiz-rv/src drafts/rv-add/Signed.wiz   # EXIT 0, 87 s
wiz --no-cache check -I /workspace/wiz-rv/src drafts/rv-add/Align.wiz    # EXIT 0, 85 s
heavy lake build wiz tests                                       # 415 jobs, OK
heavy lake test -- '=vec'                                        # 25 passed, 0 failed
```

Logs: `/tmp/rv-slt/lib.log`, `/tmp/rv-slt/addsub-final.log`,
`/tmp/rv-slt/compare-final.log`, `/tmp/rv-slt/signed-final.log`,
`/tmp/rv-slt/align-final.log`, `/tmp/rv-slt/build2.log`, `/tmp/rv-slt/vec2.log`. All
probes are under `light`'s 2 GB cap. The `vec` group has a `BitVecSigned` case
(`Tests/Groups/Vec.lean`) applying the signed/alignment lemmas.

**Next target.** The general JAL (and then BEQ/BNE) claim: unfold the E cycle's pc and
write-enable given `bit 1 target = 0` (a `coreStep` state lemma), then the claim is
`Eq.congrArg`-plus-`rfl` as in §2. After that: the remaining branch conditions
(`RLT`/`RGE` need `Bits.slt_char` for their `taken`), and `JALR` (whose core target has
bit 0 forced to 0, so its two alignment checks agree without a hypothesis).
