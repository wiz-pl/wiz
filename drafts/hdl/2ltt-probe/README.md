# 2LTT decision probes

Three files behind `../DECISION-2ltt.md` (2026-11-15). Run from the worktree root with
the canonical `wiz`:

```
/workspace/wiz-lang/.lake/build/bin/wiz check drafts/hdl/2ltt-probe/01-l2-surface.wiz
```

| file | expected |
|---|---|
| `01-l2-surface.wiz` | checks; `#eval`s print `4 1 2 2` and `9` (nodes) |
| `02-match-on-wire.wiz` | `error: cannot match on a value of type r Phase.code` |
| `03-if-chain-workaround.wiz` | checks; `#eval`s print `0 1 2 3`, `15` (nodes), and the Verilog (3 comparators + 3 multiplexers + constants) |

`01` is the staged entry's `clampedInc`/`addK` on the L2 surface (H14 S2 operators) plus
a meta-level `Nat` recursion that emits hardware. `02` is the one gap: a `match` on a
signal. `03` is the workaround (an `if` chain on `Phase.lit`). `Hdl.Core` is unchanged
between the probe build (`bea4396e`) and `627b48f6`, so the outputs are this tree's.
