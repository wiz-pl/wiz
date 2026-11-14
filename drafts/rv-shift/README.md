# RV shift proofs

Three single-instruction proofs in the `Pf` framework of `Rv.Proofs`: from the decode
phase, two cycles of the multi-cycle core compute the specification's PC and `rd`.

| file | instruction | state |
|---|---|---|
| `SLLI.wiz` | `SLLI x9, x2, 5` | checks (fill is unused on a left shift) |
| `SRLI.wiz` | `SRLI x9, x2, 9` | checks (zero fill; stages 1 and 8) |
| `SRAI.wiz` | `SRAI x9, x2, 1` | checks (complement form; see below) |

The instruction word is fixed, the architectural state (PC, registers, memory, all the
core's leftover registers) is symbolic; no `native_refl`. The barrel stage lemmas are in
`lib/BitVecShift.wiz`.

## The RTL these proofs check

`SRAI.wiz` checks against the **wiz-rv worktree** `agent/rtl-proof-hooks`
(`/workspace/wt/wiz-rv-rtl`, `src/Rv/Core.wiz`): it computes an arithmetic right shift in
the complement form `~(~x >> k)` for a negative `x`, the form `IntN.shiftRight` already
uses, so the proof needs only the definitional branches and the zero-fill stage chain.
The canonical `wiz-rv` ones-fill core is still supported by `SLLI`/`SRLI` but not by
`SRAI`: proving the ones fill at w = 32 needs `Bits.sub_one_high`, whose
`Nat.add_sub_of_le` recursion over `2^31` overflows the checker (see
`wiz-notes/rv-shift-lemmas.md` §9).

Checks (from a wiz-lang worktree with a built `wiz`, under `light`):

```
wiz check -I /workspace/wt/wiz-rv-rtl/src drafts/rv-shift/SLLI.wiz
wiz check --no-cache -I /workspace/wt/wiz-rv-rtl/src drafts/rv-shift/SRLI.wiz
wiz check --no-cache -I /workspace/wt/wiz-rv-rtl/src drafts/rv-shift/SRAI.wiz
```

Each imports `Rv.Proofs`, so the eight existing XOR/OR/AND/XORI/ORI/ANDI/LUI/AUIPC
claims are checked too (against the same RTL). The lockstep
(`wiz-rv/src/Rv/Lockstep.wiz`, `tests/lockstep.wiz`) checks the RTL change behaviourally;
its shift program covers SLL/SRL/SRA/SLLI/SRLI/SRAI at shamt 0, 1, 4, 5, 6, 9, 24, 31 on
negative and positive operands.

## Names

All three files use the `Rs.` prefix; importing two of them in one module clashes on the
shared helper names, so they are checked separately.
