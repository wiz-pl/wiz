# A third checker for the self-hosted kernel's proof terms (TT-11)

`selfhost/Kernel.wiz` is the kernel of the self-hosted toolchain.  The existing
differential tests compare its *verdicts* with the Lean kernel's on hand-written programs.
A shared bug in both kernels makes both say "accepted" and the differential test stays
green.  This directory adds the third check recommended in
`prior-art/type-theory-proof-assistants.md` §2.16 and `DECISIONS.md` TT-11: a small,
independent checker (in Lean4Lean/MetaRocq spirit, not a second production kernel) that
reads proof terms the self-hosted kernel accepted and type-checks them again.

**This is a bounded experiment, not a replacement kernel.**  It checks one corpus and
implements the rules that corpus, plus the `split` rule of `docs/CoreSpec.md`, need;
everything else is rejected, not guessed.

## Layout

| file | what it is |
|---|---|
| `driver.py` | the corpus, written in the self-hosted kernel's term language (`Tm`), and an emitter for a Wiz program that checks it |
| `serializer.wiz` | a `Tm -> String` serializer appended to `selfhost/Kernel.wiz`; it is *not* trusted |
| `corpus.dump` | the committed output: one line per declaration, `OK`/`ERR`, name, type, value |
| `checker.py` | the independent checker: parser, bidirectional type checker, conversion, quantities, levels |
| `harness.py` | runs the checker over the dump and compares with the kernel's verdicts |
| `test_checker.py` | corpus verdicts, rule tests (`split`, levels, projections, quantities), format and mismatch tests |
| `regen.sh` | regenerates `corpus.dump` (needs `wiz run`, therefore a C compiler) |
| `repro/` | minimal reproducers for the interpreter issue found while building the corpus |

## What is checked

The checker re-implements these rules from `docs/CoreSpec.md` and the rule code in
`selfhost/Kernel.wiz` (read, not imported):

* sorts and **levels** (`Prop`, `U n`, `sortL`, `lsucc`, `lmax`, `imax`), including
  **level parameters** with the kernel's normal form and `Level.equiv`'s split on an
  `imax` parameter (`p = 0` and `p = p+1`), non-cumulativity, and instantiation of a
  constant's `ps`/`ls`;
* Π, λ, application, `let`/`letq` (transparent, with the bound variable's usage
  checked before substitution), ascription, β-conversion and δ-unfolding of a
  constant's embedded value/type;
* Σ, pairs and the projections (with the dependent second projection, the `ω` scaling
  of a projected pair, and the erased-field check), the `⟦D⟧` payload template for
  descriptions;
* `Unit`/`True`, `Empty`/`False`, `exfalso`, finite enumerations, `tag`, `ecase`;
  `True` and `False` are propositions (`Sort 0`), not `Unit 0`/`Empty 0`;
* observational equality: `eq`, `eqTy`, `refl`, `reflTy`, `cast`, `transp`, with the
  equations at a proposition/`Unit`/`Empty`/`Enum`/`ULift` computing as the kernel's
  `vEq` does; a `cast` between propositions stays stuck (it is a proof);
* `ULift`, `up`, `down`;
* descriptions (`Desc`, `ret`, `arg`, `rec`, `hrec`), `μ` and `con` (including `con` at
  `darg`/`drec` payloads), the descriptions' eliminator **`delim`** (with all four
  method types), **`ind`** (with the `All` template), and **`split`**;
* more inductive types: `Nat` (zero/succ) and `List Unit` (nil/cons), built from
  descriptions, with constructors and an `ind`-defined function;
* **quantities**: usage vectors over `{0,1,ω}`, subusaging at a binder, the
  application/let/pair/projection scaling, the `ecase` join, the `split` component
  bounds, and the `let () := u; b` unit eliminator;
* the proof marker `prf`, recursively checking a `const`'s embedded value and type
  (a stronger check than the self-hosted kernel, which trusts the pair).

### `split`

`Kernel.wiz` has no `split` (no `let (x, y)` in its term language), so no declaration
in `corpus.dump` uses it.  The checker nevertheless implements the CoreSpec rule, with
the term `(split q scrut motive body)`:

```
Γ ⊢ t ⇒ (p x : A) × B    Γ, z :0 T ⊢ M type    Γ, x :ρ·p A, y :ρ B ⊢ b ⇐ M[(x,y)/z]
u_y ≤ ρ    u_x ≤ ρ·p
────────────────────────────────────────────────────────────────────────────────
Γ ⊢ let ρ (x, y) := t as z. M; b ⇒ M[t/z]
```

and its η computation on a pair.  `test_checker.py` exercises the ω and linear forms,
dropping/repeating a linear component, and the computation.  Because the kernel cannot
emit a `split`, these are checker-only tests, not dump agreement.

## Trusted base

This list is explicit; each item is a place where the checker trusts something other
than its own rules.

* **Python 3 and its standard library.**  The checker is ordinary Python; there is no
  generated code and no shared module with `selfhost/`.
* **The dump is data.**  `harness.py` trusts the `OK`/`ERR` column only as the *thing
  being compared*.  A forged dump can make the comparison vacuous; `regen.sh`
  reproduces it from the kernel, and CI's `third-checker` group re-runs the comparison
  on the committed dump.  `test_checker.py` also round-trips the Wiz serializer against
  the Python one, so a dump that does not serialize the corpus is caught.  The
  mismatch tests forge an `OK`/`ERR` and check that the harness reports it.
* **The serializer.**  `serializer.wiz` is appended to the kernel at regeneration time
  and is not trusted: the checker parses its text and re-checks the term from scratch.
* **Axioms.**  The corpus contains no `axiomC`; the checker accepts one whose type is a
  type, exactly as the kernel does.  Axioms are outside the proof.
* **The rules themselves.**  The checker is a transcription of `docs/CoreSpec.md`; a
  shared misreading of a rule by both implementations would not be caught.  This is why
  it is a *third* check, not a proof.
* **Internal lazy terms.**  `interp` and `all` are checker-internal terms used to keep
  the dependent payload and `All` templates lazy; they are never serialized and have no
  counterpart in the dump.  `split` is likewise an extra rule from CoreSpec, not a
  kernel term.

## Out of scope (rejected, not approximated)

* sizes and `ν`: `Size`, `Size<`, `szSuc`, `mus`, `nu`, `out`, `cocon`, `sfix`,
  `scase`, `scofix`, `coit` (typing rules are not implemented);
* numerals, `natOp`, native `builtin` registrations;
* `μ`/`ν` display hints (`Kernel.wiz` has none);
* function/pair η, general proof irrelevance in conversion (the checker computes `vEq`
  at propositions and keeps a proposition cast stuck, but does not compare arbitrary
  proofs), and the `cast` rules for Π/Σ/`μ`/`Desc` (a stuck cast is kept stuck);
* structural equality of descriptions (`vEqDesc`) and the general `A ≡ B` comparison
  for neutral types/propositions (only the constructor cases used by the corpus are
  implemented);
* a `split` through `Kernel.wiz` (the kernel has no such term, so the corpus cannot
  contain one).

Consequence: the checker may **reject** a term the kernel accepts (it is stricter).
The corpus is chosen so this does not happen; a mismatch is reported, not hidden.

`wiz-check` versus the compiled kernel: the self-hosted kernel's proof budget calls the
native `wiz_proof_tick`.  Under the host *interpreter* (`wiz check`) a term that reaches
`suspend` panics ("foreign functions only run in compiled code"); `wiz run` compiles the
driver and works.  The committed dump is from `wiz run`.  See `repro/`.

## The corpus and its verdicts

50 declarations: 45 accepted by the kernel and the checker, 5 rejected by both:

```
positive: id const K-type prop-impred apply2 beta let swap fst pair-eta trivial absurd
          not ecase-unit refl-unit refl-enum cast-unit cast-enum transp-unit ulift-star
          ulift-down desc-ret mu-ret con-ret desc-arg desc-rec mu-rec desc-hrec
          level-sort level-imax pi-prop nat-type nat-zero nat-succ nat-ind list-type
          list-nil list-cons desc-elim cast-prop level-param-sort level-param-max
          level-param-id level-param-const
negative: bad-proof (a proof of the wrong equation), bad-level (Type 0 : Type 0),
          bad-eq-prop (equality at a proposition), bad-linear-dup (a linear variable
          used twice), bad-linear-drop (a linear variable dropped)
```

`corpus.dump`'s header comment is followed by the exact kernel verdicts (`#err` lines
repeat the kernel's message for a rejected declaration).  The result of the committed
dump is:

```
50 declarations: kernel 45 accepted, 5 rejected, 0 crashed;
                checker 45 accepted, 5 rejected; 0 mismatches
```

`pi-prop`, `cast-prop` and `level-param-id` are proof-valued (their types are
propositions or may be one), so their values carry the explicit `prf` marker the kernel
requires; the marking pass would otherwise supply it (the corpus is the term the kernel
accepted, markers included).  `level-param-id`'s marker is at
`imax (u+1) u`, the symbolic sort of its type.

The new positives cover: induction (`nat-ind`), `Desc.elim` (`desc-elim`), constructor
payloads at `darg`/`drec` (`nat-*`, `list-*`), a proposition cast (`cast-prop`), and
level parameters in a sort (`level-param-sort`, `level-param-max`), a Π (`level-param-id`)
and a constant (`level-param-const`).

## Running it

```
python3 tools/third-checker/harness.py -v        # check the committed dump
python3 tools/third-checker/harness.py --regen   # re-run the selfhost kernel
python3 -m unittest discover -s tools/third-checker -p 'test_checker.py' -v
```

`--regen` uses `$WIZ_BIN` (default `.lake/build/bin/wiz`) and `wiz run`, so it needs
`cc` and the GMP/GC flags; `regen.sh` uses `nix develop` when `cc` is absent.  Normal
runs need only Python.

## Known issues found while building this

1. **Interpreter panic on proofs** (`repro/proof-tick.sh`): `wiz check` of a term that
   reaches the proof suspender panics with
   `extern:wiz_proof_tick ... foreign functions only run in compiled code`.  It affects
   `transp` and a proof-returning Π (`pi-prop`), not the kernel's rules; the compiled
   driver accepts them.  This is a host-tool limitation, not a soundness bug, but it
   means "`wiz check` the self-hosted kernel on proof-heavy terms" does not work today.
2. **`con` at a dependent `arg` description** is now exercised (`nat-zero`, `nat-succ`,
   `list-nil`, `list-cons`) under `wiz run`; the earlier interpreter stack overflow was
   not reproduced there.  The checker keeps the payload lazy in the field value so that
   the tag selects the rest of the description before it is interpreted.
3. **The "hang" was not a kernel hang.**  Batching 35 checks into one `wiz check` under
   load looked like a hang: the interpreter buffers `#eval` output until the process
   ends, and a warm single check takes ~10 s (some took >40 s under contention).  The
   corpus is therefore driven by a compiled `wiz run` with progress on stderr.  The two
   reproducers above are the real failures that were isolated.
