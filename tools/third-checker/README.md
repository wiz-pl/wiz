# A third checker for the self-hosted kernel's proof terms (TT-11)

`selfhost/Kernel.wiz` is the kernel of the self-hosted toolchain.  The existing
differential tests compare its *verdicts* with the Lean kernel's on hand-written programs.
A shared bug in both kernels makes both say "accepted" and the differential test stays
green.  This directory adds the third check recommended in
`prior-art/type-theory-proof-assistants.md` §2.16 and `DECISIONS.md` TT-11: a small,
independent checker (in Lean4Lean/MetaRocq spirit, not a second production kernel) that
reads proof terms the self-hosted kernel accepted and type-checks them again.

**This is a bounded experiment, not a replacement kernel.**  It checks one 37-declaration
corpus and implements the rules that corpus needs; everything else is rejected, not
guessed.

## Layout

| file | what it is |
|---|---|
| `driver.py` | the corpus, written in the self-hosted kernel's term language (`Tm`), and an emitter for a Wiz program that checks it |
| `serializer.wiz` | a `Tm -> String` serializer appended to `selfhost/Kernel.wiz`; it is *not* trusted |
| `corpus.dump` | the committed output: one line per declaration, `OK`/`ERR`, name, type, value |
| `checker.py` | the independent checker: parser, bidirectional type checker, conversion, quantities, levels |
| `harness.py` | runs the checker over the dump and compares with the kernel's verdicts |
| `test_checker.py` | the required tests (positive corpus, ill-typed proof, wrong level, quantity violation), plus tampering and format tests |
| `regen.sh` | regenerates `corpus.dump` (needs `wiz run`, therefore a C compiler) |
| `repro/` | minimal reproducers for the interpreter issue found while building the corpus |

## What is checked

The checker re-implements these rules from `docs/CoreSpec.md` and the rule code in
`selfhost/Kernel.wiz` (read, not imported):

* sorts and **levels** (`Prop`, `U n`, `sortL`, `lsucc`, `lmax`, `imax`), `imax`/`max`
  on closed levels, non-cumulativity;
* Π, λ, application, `let` (transparent), ascription, β-conversion and δ-unfolding of a
  constant's embedded value/type;
* Σ, pairs and the projections (with the dependent second projection and the quantity
  scaling), the `⟦D⟧` payload template for descriptions;
* `Unit`/`True`, `Empty`/`False`, `exfalso`, finite enumerations, `tag`, `ecase`;
* observational equality: `eq`, `eqTy`, `refl`, `reflTy`, `cast`, `transp`, with the
  equations at `Unit`/`Empty`/`Enum` computing to `True`/`False` as the kernel's `vEq`
  does;
* `ULift`, `up`, `down`;
* descriptions (`Desc`, `ret`, `arg`, `rec`, `hrec`), `μ`, and `con` (the corpus's
  payloads);
* **quantities**: usage vectors over `{0,1,ω}`, subusaging at a binder, the
  application/let/pair scaling, and the `ecase` join;
* the proof marker `prf`, and recursively checking a `const`'s embedded value and type
  (a stronger check than the self-hosted kernel, which trusts the pair).

## Trusted base

* **Python 3 and its standard library.**  The checker is ~1,000 lines of ordinary Python;
  there is no generated code and no shared module with `selfhost/`.
* **The dump is data.**  `harness.py` trusts the `OK`/`ERR` column only as the *thing
  being compared*.  A forged dump can make the comparison vacuous; `regen.sh` reproduces
  it from the kernel, and CI's `third-checker` group re-runs the comparison on the
  committed dump.  `test_checker.py` also round-trips the Wiz serializer against the
  Python one, so a dump that does not serialize the corpus is caught.
* **Axioms.**  The corpus contains no `axiomC`; the checker accepts one whose type is a
  type, exactly as the kernel does (`checker.infer`).  Axioms are outside the proof.
* **The rules themselves.**  The checker is a transcription of `docs/CoreSpec.md`; a
  shared misreading of a rule by both implementations would not be caught.  This is why
  it is a *third* check, not a proof.

## Out of scope (rejected, not approximated)

* sizes and `ν`: `Size`, `Size<`, `szSuc`, `mus`, `nu`, `out`, `cocon`, `sfix`, `scase`,
  `scofix`, `coit` (typing rules are not implemented);
* the eliminators `ind` and `delim` (the corpus uses `con`/descriptions only);
* `split` (the self-hosted kernel has no `split` either);
* numerals, `natOp`, native `builtin` registrations;
* level *parameters* and `imax` with parameters (closed levels only; a parameter is
  compared syntactically);
* subtyping for sizes (the checker uses conversion), function/pair η, proof irrelevance
  in conversion, and the `cast` rules for Π/Σ/`μ`/`Desc` (a stuck cast is kept stuck);
  consequence: the checker may **reject** a term the kernel accepts (it is stricter).
  The corpus is chosen so this does not happen; a mismatch is reported, not hidden.

`wiz-check` versus the compiled kernel: the self-hosted kernel's proof budget calls the
native `wiz_proof_tick`.  Under the host *interpreter* (`wiz check`) a term that reaches
`suspend` panics ("foreign functions only run in compiled code"); `wiz run` compiles the
driver and works.  The committed dump is from `wiz run`.  See `repro/`.

## The corpus and its verdicts

37 declarations: 32 accepted by the kernel and the checker, 5 rejected by both:

```
positive: id const K-type prop-impred apply2 beta let swap fst pair-eta trivial absurd
          not ecase-unit refl-unit refl-enum cast-unit cast-enum transp-unit ulift-star
          ulift-down desc-ret mu-ret con-ret desc-arg desc-rec mu-rec desc-hrec
          level-sort level-imax pi-prop linear-ok
negative: bad-proof (a proof of the wrong equation), bad-level (Type 0 : Type 0),
          bad-eq-prop (equality at a proposition), bad-linear-dup (a linear variable
          used twice), bad-linear-drop (a linear variable dropped)
```

`corpus.dump`'s header comment is followed by the exact kernel verdicts (`#err` lines
repeat the kernel's message for a rejected declaration).  The result of the committed
dump is:

```
37 declarations: kernel 32 accepted, 5 rejected, 0 crashed;
                checker 32 accepted, 5 rejected; 0 mismatches
```

`pi-prop` is a proof-valued Π, so its value carries the explicit `prf 0` marker the
kernel requires; the marking pass would otherwise supply it (the corpus is the term the
kernel accepted, markers included).

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
2. **`con` at a `darg` description** crashed the host interpreter (stack overflow) while
   this corpus was being built; it was excluded and replaced by `desc-arg`/`desc-rec`/
   `desc-hrec` (description formation) and `con-ret` (payload checking).  Not reproduced
   under `wiz run`.
3. **The "hang" was not a kernel hang.**  Batching 35 checks into one `wiz check` under
   load looked like a hang: the interpreter buffers `#eval` output until the process
   ends, and a warm single check takes ~10 s (some took >40 s under contention).  The
   corpus is therefore driven by a compiled `wiz run` with progress on stderr.  The two
   reproducers above are the real failures that were isolated.
