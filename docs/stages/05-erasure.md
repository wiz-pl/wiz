# Stage 5: erasure and the interpreter

<!-- no-check: `#eval` and `#erase` demonstrations that use the `fib` and `Vec.cons` defined on the page -->
```wiz no-check
#eval fib (.succ (.succ (.succ (.succ (.succ .zero)))))   -- .succ (… 8 …)
#erase Vec.cons                                          -- the erased code
```

* **Erasure** (`Compiler/Erase.lean`) is type-directed and bidirectional, like the
  kernel. Types, proofs, sizes, quantities, and everything of quantity `0` become `◾`.
  QTT guarantees the erased parts are never needed. Binders are kept, and an erased
  argument is passed as `◾`.
* **Data at runtime**: a value of `μ D i` is its payload (nested pairs with a tag), and
  descriptions are runtime values. `ind`, `Desc.elim` and the `map` behind
  coiteration are runtime primitives that walk the description.
* **The interpreter** (`Compiler/Run.lean`) is strict, with lazy codata (`coit`,
  `scofix`) that unfolds under `out`. `#eval` reads results back with their type, so
  they print with constructor names.

| #   | Where                   | What                                              |
|-----|-------------------------|---------------------------------------------------|
| 5.1 | `Compiler/Erase.lean`   | `eraseCheck`, `eraseInfer`                         |
| 5.2 | `Compiler/Run.lean`     | `run`                                             |
| 5.3 | `Compiler/Run.lean`     | `ind` (hypotheses) and `out` (coiteration's `map`) |

Next: an ANF intermediate representation with join points and explicit closures,
specialising the primitives for known descriptions (flat constructor objects), and
then macros (stage 6), which run in this interpreter.
