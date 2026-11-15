# The trust ledger

`.github/trust-baseline.tsv` is the reviewed list of everything in `lib/` (and the
axiom-free examples) that the kernel does not check. `scripts/trust-ledger.sh` regenerates
it, and the `trust-ledger` CI job plus the `native` test group compare it with the source.

## What is a source of trust

The ledger is produced by elaborating every module and running `#print axioms`, so it
records sources rather than dependency edges. One row per:

| Wiz | ledger `item` | what it trusts |
| --- | --- | --- |
| `axiom` | `axiom X` | the proposition `X` |
| `extern "f" X …` (FFI) | `axiom X` and `builtin extern:… := X` | the C function, and how it is marshalled |
| `partial def` | `partial` | the compiled body (its witness is kernel-checked) |
| `attribute [implemented_by g] f` | `native f := g` | compiled code runs `g` for `f` |
| a type's `repr:` | `native T := mk/get` | the native representation |
| `native_refl` | `native_refl X.native✝` | compiled evaluation, the analogue of Lean's `native_decide`/`ofReduceBool` |
| `smt`/`sat_decide_native` | `smt X.smt✝…` | the solver's answer |
| `builtin k := n` | `builtin k := n` | a registration that decides how a definition computes |

`builtin inline` (a compiler hint) and `builtin int` (only how values print) are not
trust and are not listed. Wiz has no `unsafe` keyword: an `unsafe` declaration is a parse
error, and `sorry` is rejected by the ledger walker before it elaborates.

## Format

Rows are tab-separated:

```
module	declaration	item	reason	owner	review
```

`review` is a `YYYY-MM-DD` date: the next review due date. A row is **expired** when
that date is before today, and `--check` fails.

A row from before the gate still has all six columns, but its reason is `legacy:
pre-gate baseline; not individually reviewed` and its owner is `unassigned`. It is
accepted, counted in the check's summary, and still expires on its review date.
`--strict-legacy` fails on those rows too. Such a row gains a real review when its
reason and owner are replaced (use `--strict-legacy` to list them). New rows may not use
the migration marker: a bare three-column row is an error.

A row with any of reason/owner/review must have all three, non-empty; otherwise the
check fails with "missing a reason", "missing an owner" or "missing a review date".

## The gates

`scripts/trust-ledger.sh --check` fails when:

* a source of trust in `lib/` (or `examples/hdl-verified.wiz`) has no matching row —
  the **new-entry gate**;
* a row names a declaration that is no longer there (a stale row; a renamed declaration
  is called out explicitly when the item kind matches);
* a row is incomplete (including a bare three-column row), has an invalid date, or is
  expired.

A successful check prints the source count and the number of legacy rows.

## Updating

```
scripts/trust-ledger.sh --update --reason "why this is trusted" \
  --owner "who reviewed it" [--review YYYY-MM-DD]
```

`--update` regenerates the ledger from the source and preserves the metadata of rows
that stay. It **refuses to add a new row without `--reason`** (exit 2) and lists the new
sources. New rows get `--owner` (default: `git config user.name`, then `$USER`) and
`--review` (default: today + 180 days). A review date in the past is refused. An
explicit `--review` also renews rows that still carry the migration marker, so a bulk
deferral is `--update --review YYYY-MM-DD` (no `--reason` needed if there are no new
sources). Review the diff before committing: a new `axiom` is a proof obligation, not a
formality.

The migration gave the 753 pre-gate rows the reason `legacy: pre-gate baseline; not
individually reviewed`, owner `unassigned`, and review date `2027-05-14`: they are
accepted now, but will fail on 2027-05-14 unless individually reviewed or renewed.

## Reducing the legacy rows

The migration's 753 rows are not a renewal list: the reviewed base is now 682 rows
(639 still carrying the migration marker), 71 fewer. The reduction is no longer over 10%:
the signed shift/compare exception below is a correctness fix for the native IR. The
removals are all structural, not a loosening of the gate:

| what was removed | rows | why it was not trust |
| --- | --- | --- |
| signed-word natives (`IntN.*Native`, `IntN.toNat`) | 52 | every other `IntN` operation has a Wiz body that delegates to a retained `UIntN` native or reads the representation (`IntN.toNat`); signed `shiftRight` and `lt` are kept native below |
| `toList`/`ofList` projections on arrays, maps and intern tables | 8 | the constructor's `repr:` registration already gives the native representation; the separate projection registration proved nothing new |
| `InternTable.empty`/`size` and `U64Map.contains` natives | 9 | their Wiz bodies are `.mk .nil`, a length and a match on the (still native) `find`/`toList`; all are cheaper to review than to trust twice |
| `partial` definitions that the kernel accepts as total | 2 | `Json.digits` recurses on the list tail, `Ring.synEq` on the syntax tree (`Json.sub` stays partial as an elaboration fence and is now reasoned) |

The rule the BitVec IR test encodes: **a native is removed only if the Wiz body emits
the same primitive**. `IntN.shiftRight` and `IntN.lt` fail that test: their Wiz
bodies allocate (`IntN.not`/`IntN.below`, `IntN.isNeg`/`IntN.toNat`), so their
`wiz_word_ashr`/`wiz_word_slt` registrations and externs are back, with reasons.
`IntN.isNeg`, `IntN.shiftLeft` and `IntN.toNat` stay removed: their bodies read the
representation or delegate to a retained `UIntN` native and the IR has no word
constructor or projection.

The remaining rows fall into five groups, with the plan for each:

* **FFI, 210 declarations (420 rows).** Each `extern` contributes an axiom (the C
  function) and a `builtin extern:` row (the marshalling). These are the mechanical
  bulk and the next review unit: audit by C symbol against `runtime/` and `c/`, then
  replace the two `legacy:` rows with one reason naming the symbol and its contract.
  Do not bulk-renew them.
* **Mutual recursion, 109 `partial` rows.** `Feral` (70), `Json` (9), `SatTactic` (7),
  `BvDecide` (6), `Tagged` (6), `Ring` (2) and the rest are compiled engines. Wiz's
  structural checker does not accept nested/mutual induction here, so they cannot be
  made total mechanically; the plan is to de-mutualise or size-index the few that are
  worth it, and otherwise review them as intentionally compiled-only engines.
* **Explicit `partial`, 25 rows (27 before this pass; two are now total).** The rest are fuel loops
  (`Scry.*`, `Text`, `IO`, `Prelude`) or recurse through a helper (`stripPrefix`,
  `Nat.div`); they need a structurally recursive variant or an individual review, not
  a blind renewal.
* **`implemented_by`, 56 rows.** The remaining ones are the performance-critical
  `UIntN`, array, map, intern and channel fast paths. They are covered by the
  differential `=word`/`=natives` tests; review each against the C function it names.
* **`builtin`, 30 rows and `repr:`, 7 rows.** Ten seals (opaque native
  representations) and the twenty `Prelude` numerals/operations/`memo` registrations
  are load-bearing: numerals and compiled arithmetic do not work without them. They
  should be reviewed as a group, not removed.

The 35 pure axioms (the foreign types, the seals, `Region`'s `Outlives` evidence and
`Prelude.castRefl`) now carry a specific reason and the owner `Reuben Steenekamp`; so
do the kept `UIntN.toNat` native (the word tests pin it in the compiled IR) and the six
signed shift/compare rows. The FFI
and engine rows still say `legacy:`; `--strict-legacy` lists them, and the 2027-05-14
expiry is the deadline for the per-symbol and per-engine review above. `Json.sub` is
partial by intent (it is an elaboration fence, not recursion) and now has a reason.

## Tests

`Tests/trust-ledger/run.sh` checks the gate's exit codes and messages against small
trees: a new axiom with no row, a row with no reason, an expired row, a renamed
declaration, a legacy row, a clean tree, and `--update` with and without a reason. The
`native` group runs it, so `lake test -- '=native'` covers it.

CI runs `scripts/trust-ledger.sh --check` (see the `trust-ledger` job in
`.github/workflows/ci.yml`); the gate is inside `--check`, so no new flag is needed.
