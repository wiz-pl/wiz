# HD5/H14 staging: decision record (2026-11-15)

Based on `origin/master` `627b48f6`. Question: **is two-level type theory staging still
wanted?** The wish-list entry for HDL staging had said "designing" since 2026-11-10;
decisions SD1–SD11 were taken; implementation S2 never started. A triage of the wish
list (2026-11-15) flagged the same question.

**Decision: dropped (superseded).** The ten-week L3 type theory is not wanted. The one
remaining item, `match` on a signal, is a small case-tree elaboration and is now
its own wish-list item, deliberately *not* a staging feature.

## 1. Premise check: is the pain still real?

Checked against `627b48f6` (file:line below are that tree).

| the entry's claim | today |
|---|---|
| "static synthesisability" needs a stage check | **Already by construction.** `Comb i o := {r : HwTy → Type} → [Hw r] → r i → r o` (`lib/Hdl/Core.wiz:1772`) and `Circuit.step` (`:1697`) are polymorphic in `r`; `Hw` (`:396`) has no eliminator, so no `Nat`, `Bool` or constructor can come out of a wire. docs/libraries.md H14 S0 states the consequence ("synthesisable by construction"). The dynamic path H14 was to replace (`Sym`, hdl-plan §3.2) does not exist in the tree: `grep -rn "Sym\." lib →` nothing, no `lib/Sym.wiz`, no `Sym.lean`. H14's exit criterion ("E1–E4 with no dynamic errors possible") is vacuous when there is no dynamic synthesizer. |
| "meta computation at staging time" (widths, ROMs, unrolling) | **Works.** Widths are meta `Nat`s in `HwTy.bits n`; `Crc.hwIter` (`lib/Hdl/Crc.wiz:45`) is `Nat` recursion that unrolls eight CRC bits into hardware; `Display.seqC` (`lib/Hdl/Display.wiz:574`) turns a meta `List Byte` into a ROM, an index width and a circuit. `deriving BitPack` (`docs/libraries.md:611`) computes enum/bundle widths at meta time. |
| "`match` on a wire should be a mux tree" | **Still missing** — the only real gap. Probe: `match p with …` on `r Phase.code` errors `cannot match on a value of type r Phase.code`. The workaround is an `if` chain on `Phase.lit` (`docs/libraries.md:620`), verified below. |
| "L2 is implicit; quote/splice sugar" | **Delivered by S2 without staging.** `if c then a else b` on a signal is `Hw.mux` via `ifMux?` (`Wiz/Elab/Term.lean:3096`); `+ - * &&& \|\|\| ~~~ === <ᵤ` are instance methods (`docs/libraries.md` H14 S2). Probe 1 below is the entry's own `clampedInc`/`addK`, written quote-free. |
| "sized signals" (`Signal d A` at the object level) | **Not the blocker.** SD2 chose `Circuit`/Mealy + combinators, and those landed (`Circuit.seq/par/loop/delay`, `lib/Hdl/Pipe.wiz`). Sized `Signal.fix` is a separate kernel item (`wishful/sized-signal-fix.md`), not something L3 would supply. |
| "`#netlist`/`#verilog` generation" | Independent of staging. `wishful/hdl-commands.md` is still wanted and covers it: today `Verilog.emit (Circuit.netlist "c" c)`. `hdl-let-names` is also separate (a `ShareLet.shareNamed` hook). |

The entry's own "workaround today" (explicit `Hw.mux`/`Hw.share`, no `match` on wires) is
now only half true: `Hw.mux` chains are gone where S2 notation is used (98 `Hw.mux`
remaining, mostly in older modules), `Hw.share` is automatic for `let` (S0 `ShareLet`),
and hash-consing keeps netlists linear. Only `match` remains.

Probe transcript (canonical build `bea4396e`; `lib/Hdl/Core.wiz` is byte-identical to
`627b48f6`, `git diff` empty, so the results apply to this tree). The three files are in
`drafts/hdl/2ltt-probe/`:

```
$ wiz check drafts/hdl/2ltt-probe/01-l2-surface.wiz   # clampedInc / addK / meta incN
info: .cons 4 (.cons 1 (.cons 2 (.cons 2 .nil)))     # 0,253,254,255 + 3 (clamped)
info: 9                                              # netlist nodes
$ wiz check drafts/hdl/2ltt-probe/02-match-on-wire.wiz     # match on a wire
error: cannot match on a value of type r Phase.code
$ wiz check drafts/hdl/2ltt-probe/03-if-chain-workaround.wiz  # the if-chain workaround
info: .cons 0 (.cons 1 (.cons 2 (.cons 3 .nil)))     # 4-way Phase decode
info: 15                                             # netlist nodes
```

So: safety is there, ergonomics are 90% there, one feature is missing and it is not
type theory.

## 2. Options

| | what | cost | risk | verdict |
|---|---|---|---|---|
| **(a)** 2LTT staging (SD1–SD11, S2–S5) | ASCII `Code A` / `[| t |]` / splice, `hw` blocks, object `match`, `Gen`, auto-share, PHOAS | 6–9 expert-weeks remaining of the 9–14 total (S2 2–3, S3 2–3, S4 1–2), plus optional S6/S8 | medium: elaborator mode/ postponement, path explosion in `splitHw`, BitPack layout agreement, and a second surface for code that already type-checks; `HwTy` codes + `r`-polymorphism already provide the guarantee SD1 was going to prove | reject: pays 6–9 weeks for sugar over an existing guarantee |
| **(b)** small stage marker in the elaborator (`Hdl.Stage`, no new type theory) | label meta vs hardware values and reject mixing | 1–2 weeks for the marker + `match` case tree | low | reject the *marker*: mixing is already rejected by ordinary typing (probe 2), so the marker would improve messages only. Its one useful part is the `match` case tree, which needs no marker. |
| **(c)** status quo + `hdl-commands` (+ `hdl-let-names`) | keep L2; add `#netlist`/`#verilog`/`attribute [hdl]` and named `let` wires | `hdl-commands` days; `hdl-let-names` days | low | **accept.** It covers the remaining *emission* asks and does not touch the object language. |
| **(d)** the residual `match`, as its own elaboration | `matchMux?` next to `ifMux?`: scrutinee `r T` with `T` an enum code (or `bits n` literals) → `Hw.eq` per constructor + right-nested `Hw.mux`; auto-share the scrutinee; size lint above a case threshold (SD10) | 0.5–1.5 weeks | low–medium (constructor enumeration from `BitPack`; expected-type discipline; nesting) | **accept as its own wish-list item**, not as staging |

A one-week vertical slice of (a) would have proved: `[| … |]`/splice round-trips and one
negative stage error. It would not have proved anything about synthesisability, because
that already holds. That is why (a) is dropped rather than "started small".

## 3. What is dropped, what survives

* Dropped: the L3 object universe as a *new* surface, quote/splice, `hw` sections,
  stage inference, `Gen`/`splitHw`, the L3-vs-L1 differential (there is no L1), and the
  kernel 2LTT (S8).
* Survives, as ordinary elaborator work: `match` on a signal (new wishful entry),
  `hdl-commands`, `hdl-let-names`.
* Survives as research, no dependency on this entry: the PHOAS `HwExp` instance and the
  netlist-vs-values theorem (S6) — `lib/Hdl/Netlist.wiz` already proves it for the Mealy
  core without a staging layer; a third `Hw` instance can be added whenever it pays.
* `drafts/hdl/Staged.wiz` stays as a historical sketch; `STATUS.md` now says so.

Outcome: the staging item is dropped, and `match` on a signal is done (2026-11-15: the
case-tree elaboration `matchMux?` in `Wiz/Elab/Term.lean`; probe `02-match-on-wire.wiz` now checks). `docs/libraries.md`
H14 S4 describes the `match` bullet instead of "staged match".
