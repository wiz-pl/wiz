# Numerics and solver trust: the host-side recommendations

Status: implemented on `agent/recs-numerics-host`, 2026-11-22. This is the host-side
half of `wiz-notes/sota-numerics.md` §5 (tracker rows R2–R7 of
`wiz-notes/roadmap/sota-recommendations.md`). R1 (the self-hosted `Nat`) is another
lane's file and is not touched here.

The trust question is not "fast or slow" but **which equations the kernel decides by
computation and which facts enter as axioms**. This page records, for each host-side
recommendation, what changed, what is trusted, and the test that fails if the property
is reverted.

## R2 — pin and attest GMP

Host `Nat` is a 62-bit scalar plus GMP (`runtime/wiz_rt.h`, `runtime/rt_num.inc`). Lean
admits GMP into the kernel TCB and requires GMP ≥ 6.3.0 because older GMP can make it
unsound; Wiz's `rfl` on a large numeral trusts the same bignum. The release bundles a
statically linked GMP built from `scripts/bundle-cc.sources`; the Nix toolchain uses
`pkgs.gmp`. Both must be the same source, and that identity is now recorded in three
places:

The two build paths carry the same upstream release in different archives: nixpkgs
builds GMP from `gmp-6.3.0.tar.bz2`, the release bundles `gmp-6.3.0.tar.xz`. Both are
pinned; neither hash can stand for the other.

| Where | What it records | Checked by |
|---|---|---|
| `flake.nix`, `gmpPin` | GMP `6.3.0`, nix source `sha256-rCghGnz7YJuuLiyNYFjWbI/pZDT3QM9v4uR7AA0cIMs=` (tar.bz2), release source `sha256-a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898` (tar.xz) | `nix eval` assert in `unwrapped`: a different version or nix source hash fails and **names the actual and pinned hashes** (and the release archive) |
| `scripts/bundle-cc.sources` | `gmp-6.3.0.tar.xz` and its SHA-256 (the archive the release builds) | `release.yml` already downloads and `sha256sum -c`s it; `scripts/sbom.py` records `wiz:resolved-gmp` |
| `docs/release/gmp-pin.json` | the machine-readable attestation (version, both archive hashes and URLs, why, owner, review) | the `numerics` test group; a release gate can read the JSON directly |

The `numerics` group's first two cases read all three and fail with every version/hash
in the message when they disagree, and check that the flake assert still names the
hashes. Changing GMP is therefore a deliberate attestation update (edit all three, with
a reason), never a side effect of `nix flake update`.

`flake.nix` is also being edited by `ci-fast-build`; this lane's diff is the `gmpPin`
block plus the one assert in `unwrapped` and the `gmpSrcHash` helper, nothing else.

## R3 — make the SMT range assumption explicit

`UIntN w` is proof-carrying since 22l: a sealed inductive whose private constructor
takes an erased proof `toNat < 2^w` (`lib/Word.wiz`). `Wiz/Smt/Translate.lean` maps it
to `(_ BitVec w)`, where the range is a *sort* invariant. That invariant was assumed;
it is now **checked**:

* `Smt.sealedPrivate g "UIntN"` requires both halves of the seal: the `seal:UIntN`
  registration and `UIntN.mk` in `Globals.privates`.
* `sortOfChecked` wraps every `sortOf` use in the translator: a `UIntN`-sorted type
  that is not the library's sealed, privately-constructed type is refused with
  "`UIntN` is not sealed with a private constructor; its range invariant … would be
  assumed, not checked". Without the check, a look-alike `Word` module with a public
  constructor would be read as an in-range bit vector: a hypothesis that cannot hold
  becomes satisfiable, and its negation is an **unsound `unsat`** that closes a false
  goal.
* A `Nat` literal met at a bit-vector sort is emitted exactly (`(_ bv n w)`) when
  `n < 2^w` and is an **error** otherwise, rather than abstracted to a fresh variable.
  This is unreachable while `UIntN` is sealed; it is the second, local belt.

Tests (`Tests/Smt.lean`, group `smt`):

* "R3: a word type that is not sealed with a private constructor is refused…": a fake
  `Word` whose `UIntN.not` is constant 0. With the range assumed, Z3 proves
  `not (not x) = x` unsat and `smt` accepts it; with the check, the translation refuses
  the type. This is the negative control (revert the check and the test fails).
* "R3: the seal/private-constructor predicate holds for lib/Word's `UIntN`…": the real
  library passes and an unsealed type does not.
* The existing words case still proves `not (not x) = x` for the real `UIntN 8`, so the
  check is not simply refusing everything.

There is no non-vacuous SMT assertion to add for a `(_ BitVec w)` value (`x ≤ 2^w − 1`
is the sort); the meaningful constraint is the type invariant, hence the checked side
condition.

## R4 — audit the trust boundaries

| Path | Checked by | Trusted | Cached | In `lib/`? |
|---|---|---|---|---|
| `sat_decide` | reflection, CNF, LRAT; the kernel checks `Sat.lratCheck` | the blaster and LRAT parser are untrusted (bad output only fails) | proof (R5) | no use; `SatTactic.wiz` implements it, adds no axiom |
| `bv_decide` | the same SAT path, bit-blasting words | `UIntN`'s seal and its native rows in the ledger; the blaster | proof (R5) | no use; `BvDecide.wiz`/`BitBlast.wiz` implement it |
| `sat_decide_native` | the LRAT check compiled (native evaluation) | the compiler, erasure, the interpreter | proof; the native acceptance is an axiom per use | declaration only (`SatTactic.wiz`), no use |
| `smt` | nothing | solver + translation + this cache | **no verdict is cached** (R5) | declaration only (`Prelude.wiz`), no use |
| `native_refl` | nothing | compiler, erasure, interpreter, Lean `Nat`/GMP, every reached `implemented_by` | key includes the binary and flag; the acceptance is an axiom | no use |

**Findings.** There is no `lib/` declaration whose `#print axioms` contains `.smt✝` or
`.native✝`. The authoritative check is the trust ledger (`Tests/Native.lean`, group
`native`, case "every library source of trust is a reviewed ledger row"): every source
must be a row in `.github/trust-baseline.tsv`, and that file has **no**
`smt …`/`native_refl …` rows. The rows that `bv_decide`'s proofs do use are the
`UIntN` representation's: `Word UIntN.seal✝ axiom UIntN.seal✝` and
`Word UIntN.seal✝ builtin seal:UIntN := UIntN.seal✝` (plus the `UIntN.*Native`
registrations for the operations the bit-blaster reflects). Those are reviewed,
representation-level rows, not solver trust.

Two `lib/` declarations name the trusted forms because they *implement* the surface
syntax, not because they use it: `lib/Prelude.wiz` declares `syntax "smt"` and
`TacticM.smt`, and `lib/SatTactic.wiz` declares `syntax "sat_decide_native"`. They
introduce no axiom (no ledger row), and every library check runs without
`--trust-smt`/`--trust-native`, so a use is an error. Per the task, this is reported,
not changed.

The mechanical second net is the `numerics` group's "R4: lib/ contains no use of the
trusted forms" case: a comment-aware scan for `by smt`, `native_refl`, `native_decide`
and `by sat_decide_native` over every `lib/**.wiz` (syntax-declaration lines are
excluded; `sat_decide`/`bv_decide` are proof-carrying and allowed).

## R5 — cache proofs, not verdicts

The answer cache (`Wiz/Smt/Process.lean`, `<cache>/smt/<key>.ans`) was keyed by the
solver's `path --version`, the arguments and the whole input, and stored the answer —
including a trusted `smt` verdict. A cached verdict is an axiom in the TCB: a poisoned
`unsat` proves `False`.

Now:

* **Only certificates are written.** An entry is written only when the caller asked for
  the solver's output file (`wantOut`) and that file is non-empty. For `sat_decide`
  that is CaDiCaL's LRAT; a SAT model (exit 10, no proof file) is not cached either —
  a cached counterexample would be a verdict. The trusted `smt` calls with
  `wantOut = false`, so **it never caches** and always runs Z3.
* **The entry names its certificate.** Format `wiz-smt-cache-v2`: `kind proof`,
  `exit`, `out-sha256`, then the proof, the query and the solver's stdout. On read the
  proof's SHA-256 is recomputed and must match; the proof is then re-parsed by
  `Smt.parseLrat` and checked by the kernel at every use (`Sat.lratCheck`), so a bad,
  stale or forged proof can only make the tactic fail.
* **A verdict is refused, not marked.** An old-format entry, an entry with no proof, or
  an entry whose digest does not match is a miss; the solver runs. There is no
  "trusted verdict" mode to opt into.
* **The solver's identity is its binary, not its version line.** The key now includes
  the SHA-256 of the solver executable, so a rebuilt or repackaged binary that keeps
  `--version` is a different key. The translation is covered by the key because the
  whole script is hashed.
* The cache stays user-local (`<cache>` comes from `--cache`; `--no-cache` runs in a
  temporary directory), and `Cache.smtKey` keeps the solver settings in every command
  and module cache key.

Tests (`Tests/Smt.lean`): a certificate entry is written for `sat_decide` and contains
`wiz-smt-cache-v2`/`kind proof`; tampering with the proof while keeping the digest is
detected (the tactic fails on the re-parsed LRAT); tampering without updating the digest
is a miss (the solver re-runs); `smt` with `--cache` writes no entry at all; a legacy
verdict entry planted for the exact query key is refused (the solver runs, and a false
goal still reports a counterexample).

## R6 — Ryu, not `%.17g`; no fast-math

`Float64.toString` is `wiz_f64_show` in `runtime/rt_data.inc`. It printed with
`snprintf("%.17g")`: not shortest, and the last digit is the libc's. It now uses a port
of **Ryu** (`d2s`, the 64-bit algorithm with the small lookup tables; Copyright 2018
Ulf Adams, Apache-2.0 OR Boost-1.0; prefixed `wiz_ryu_`): the shortest decimal that
parses back to the same double.

The exact strings (scientific form) are pinned in `Tests/Groups/Numerics.lean`:

| Value | `Float64.toString` |
|---|---|
| `0` | `0E0` |
| `-0.0` | `-0E0` |
| `1` | `1E0` |
| `0.1` (nearest double) | `1E-1` |
| `1/3` | `3.333333333333333E-1` |
| `0.1 + 0.2` | `3.0000000000000004E-1` |
| `2^53` and `2^53 + 1` | `9.007199254740992E15` |
| `2^64 − 1` (as a double) | `1.8446744073709552E19` |
| least positive subnormal `2^-1074` | `5E-324` |
| `2^1023` | `8.98846567431158E307` |
| `10^308` (nearest double) | `1E308` |
| `1/0`, `-1/0` | `Infinity`, `-Infinity` |
| `0/0`, `inf − inf` | `NaN` (the sign bit and payload are not part of the value) |

The same case runs a C probe built from the runtime's Ryu block: it prints 200,000
pseudo-random non-NaN bit patterns plus the boundaries, parses each string back with
`strtod`, and requires the same bits. `Tests/Semantics/cells.tsv` and
`docs/semantics-matrix.md` were regenerated with the same strings (the generator's
`ryu_show` derives them from Python's shortest `repr`).

**Scope.** The self-hosted runtime has its own `wiz_f64_show` (`selfhost/rt.c`,
`%.17g`); it is not this lane's file (the selfhost lanes own `selfhost/*`), so its
`Float64.toString` still prints `%.17g` and the `=selfhost` FFI test keeps its `0.25`
expectation. Until that copy is ported, host-run and selfhost-run programs print
different (both deterministic) float text; the host contract above is what `lib/IO.wiz`
documents.

Fast-math: the C backend invocations in `Wiz/Compiler/Build.lean` pass
`-ffp-contract=off` (FMA contraction is the one fast-math-like transformation that C
allows by default), and the `numerics` group scans every build path — `Build.lean`,
`Toolchain.lean`, `flake.nix`, the runtime headers/includes, `bundle-cc.sh`,
`test-runtime.sh`, `release-tarball.sh`, `web/build.sh` — refusing
`-ffast-math`, `-Ofast`, `-funsafe-math-optimizations`, `-ffinite-math-only`,
`-freciprocal-math`, `-fassociative-math`, `-fno-signed-zeros` and
`-ffp-contract=fast`. Adding any of them fails the case.

## R7 — a certificate-producing `omega` (deferred plan)

R7 needs `Wiz/Elab/Tactic.lean`, held by another lane, so only the plan is recorded
here, in the note's terms: **grow `omega` into a certificate-producing Cooper/Omega
procedure over the linear fragment, with no external solver.** Wiz's current `omega`
(`lib/Prelude.wiz`, a sound 10,000-node BFS over order lemmas) already sits on the
right side of the line — it builds a proof term and `#print axioms` shows no solver
axiom — but its search is not a decision procedure. The replacement should keep the
fragment explicitly linear (Presburger is triply exponential in general; Oppen 1978),
**fail loudly** outside it (no silent fallback to an oracle), and emit a *proof term*
whose every step is a kernel-checked order/divisibility lemma: Cooper elimination for
the existential case, the Omega test's dark-shadow/splice steps for the universal one,
and an arithmetic certificate for each coefficient comparison, so that the only trust
is the kernel and the library lemmas the certificate cites. That is strictly stronger
than calling an SMT solver (which would add `smt✝`) or enlarging the BFS: an oracle with
a bigger search buys completeness at the price of a new axiom, while a certificate buys
it with no new trust.
