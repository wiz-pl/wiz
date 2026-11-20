# HDL lane L3: `Signal.fix` and the sized operator surface (draft)

Lane L3 of `wiz-notes/clash-hdl-plan.md`: the feedback primitive `Signal.fix`, the
`Hw`-style operators at a size (`+`, numerals, `if` on `(Signal d A)^i`), and the two
Clash examples (a counter and the baud generator).

**Status on `integration/train8` (2026-11-20): blocked by lane L2, except numerals.** The
code here is the *target*, not checked code: `drafts/` is outside the build by design
(AGENTS.md, "Writing Wiz ahead of features"). Every definition that needs a missing
feature is marked `-- wishful: sized-signal-fix`; the gap is written up in
`docs/stages/34-hdl-signals.md` §34b and `wiz-notes/wishful/sized-signal-fix.md`.

What has landed (in `lib/Hdl/Signal.wiz`, checked):

* `Signal.pureS : A → (Signal d A)^i` — pure at any size; it never observes, so the
  current kernel types it (`coit` at `∞` used at `i`). `Signal.pureS_at` says it is
  `pure` at `∞`.
* a numeral at a sized signal: `OfNat ((Signal d (BitVec n))^i) k`.

What is missing, precisely:

1. **Surface `scofix`.** `Signal.fix` is `scofix` with no separate state
   (`Neg.wiz` N4: the identifier is unknown). With the current kernel this is enough
   to *define* `fix`, because the recursive argument of `scofix` is already the loop
   value at the recursive size:
   `scofix (fun _ => Unit) (fun s rec i () => g s (rec i ())) ∞ () ()`.
2. **Size-dependent `scofix` state** (L2 proper). `scofixFunTy` is
   `A : I → Type` (`Wiz/Core/Conv.lean:189`, mirror `selfhost/Kernel.wiz:3018`); the
   plan changes it to `A : Size → I → Type` so that the state can be the loop value at
   the recursive size. Without it there is no size-preserving map, so the *body* of
   `fix` — Clash's `c + 1`, a numeral or an `if` on `c` — cannot be typed.
3. **Sized copatterns → `scofix`.** `elabSizedDef` (`Wiz/Elab/Command.lean:498`)
   compiles sized recursion on an inductive argument to `sfix`; copatterns go to
   `coit`/`cocon` (`elabCopatterns`, `:1083`). So the surface form below (a sized
   copattern with result `(Signal d A)^i`) does not reach `scofix` either.

The examples are written in the plan's spelling. `Signal.registerS` is the only size
bump, so the feedback path *must* go through it; a `Signal.fix` whose body uses `c`
combinationally is a size error, not a runtime loop.
