# HDL lane L3: `Signal.fix` and the sized operator surface (draft)

Lane L3 of `wiz-notes/clash-hdl-plan.md`: the feedback primitive `Signal.fix`, the
`Hw`-style operators at a size (`+`, numerals, `if` on `(Signal d A)^i`), and the two
Clash examples (a counter and the baud generator).

**Status on `hdl-l2` (2026-11-20): landed.** Lane L2 supplied the size-dependent
`scofix`, the sized-copattern elaboration, surface `scofix`, and the size-preserving
`mapS`/`zipWithS`; the target below is now checked in `hdl/src/Hdl/Signal.wiz` and
`hdl/examples/hdl-l3.wiz` (the `hdl` and `hdl-signal` groups). This file is kept as the
target spelling and design record; the design is `wiz-notes/hdl-l2.md`.

What landed (in `hdl/src/Hdl/Signal.wiz`, checked):

* `Signal.mapS`/`zipWithS`/`zipWith3S` — size-preserving pointwise operations,
  compiled from sized copatterns to `scofix`.
* `Signal.fix : ((i : Size) → (Signal d A)^i → (Signal d A)^(↑i)) → Signal d A` —
  `scofix` with unit state; the recursive argument is the loop value at the
  predecessor.
* `Add`/`Sub`/`Mux` at `(Signal d A)^i`, and the `OfNat`/`pureS` numeral surface.
* `Signal.registerS` is the only size bump, so a `Signal.fix` body that uses `c`
  combinationally (`fun i c => c + 1`) is a size error, not a runtime loop; the counter
  and baud generator are in `hdl/examples/hdl-l3.wiz`.
