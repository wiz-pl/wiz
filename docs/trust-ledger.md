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

## Tests

`Tests/trust-ledger/run.sh` checks the gate's exit codes and messages against small
trees: a new axiom with no row, a row with no reason, an expired row, a renamed
declaration, a legacy row, a clean tree, and `--update` with and without a reason. The
`native` group runs it, so `lake test -- '=native'` covers it.

CI runs `scripts/trust-ledger.sh --check` (see the `trust-ledger` job in
`.github/workflows/ci.yml`); the gate is inside `--check`, so no new flag is needed.
