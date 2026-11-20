# The four things that do not move

Each file is expected to be *rejected*. Run with a worktree binary (the library is the
toolchain's own):

```sh
wiz check -I drafts/optics drafts/optics/limits/pair.wiz
```

| file | what it tries | error (captured 2026-11-20) |
|---|---|---|
| `pair.wiz` | `Lens.pair` from two `LensP`s | `expected: P B B / inferred: P (A × B) (A × B)` |
| `getter.wiz` | a `Getter`/`Fold` as a `∀P` transformer | `expected: P S S / inferred: P S A` |
| `traversemut.wiz` | `TraverseMut.traverseM` from a `TraversalP` | `expected: A / inferred: S` |
| — | `ALens`'s `Result` error | not a failing term: `ALens` is `S → Result (Affine A S)`, and `PrismP` has no error field. No caller uses `ALens`; `MutOpt.ofAffine` takes `S → Affine`, which `MutOpt.ofPrism` covers. |

The reason each is a *cannot* rather than a missing lemma:

* `pair`: `Strong` adds a context to a `P` (`first'`/`second'`); it has no eliminator
  that decomposes one `S` into two independent places. The store form can, because the
  representation carries `S`.
* `getter`: an optic is `P A B → P S T` for every `P`. Reading needs the *return* leg
  `A → S`; a getter has only `S → A`.
* `traversemut`: `traverseM` threads one `σ`, stops at the first `.err`, and returns the
  partially updated `S`; `Wandering` is an `Applicative` copy with no error branch and no
  loop state.
