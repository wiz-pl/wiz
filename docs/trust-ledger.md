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
accepted by a plain `--check`, counted in the summary, and still expires on its review
date; `--strict-legacy` fails on it too, and that is what CI runs. Such a row gains a
real review when its reason and owner are replaced. New rows may not use the migration
marker: a bare three-column row is an error. No row in this ledger carries the marker.

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
individually reviewed`, owner `unassigned`, and review date `2027-05-14`. That
migration is **complete**: every row now has a declaration-specific reason and a named
owner, so no row carries the marker and `--strict-legacy` passes.

## Merging the ledger

A key is `(module, declaration, item)`, and that is also the merge key: two branches
that review different declarations are a union, even when their rows are adjacent. A
git merge driver does that mechanically. `.gitattributes` names it, but a driver is
local config (not cloned, and CI cannot set it), so each clone installs it once; the
stored path is relative to the worktree root, so it serves every worktree:

```sh
scripts/setup-trust-merge.sh
```

The command stored is `merge.trust-ledger.driver`; `--show` prints it and `--unset`
removes it. Without it git falls back to a line merge and is likely to conflict.

The driver's rule (`scripts/trust-ledger-merge.sh`, inputs `%O %A %B`) is:

* merge three-way by key against the base: a row added on either side is kept; a
  row changed on one side only takes that side's version; a row deleted on one side
  and unchanged on the other is deleted (so a branch cannot resurrect a row master
  removed when the source stopped being trust);
* keep header/comment lines once: the base's comments in order, then comments new
  on either side;
* sort the rows by key in byte order, the order `--update` writes;
* when both sides changed one key to different contents, take the row whose reason
  is not the migration marker (`legacy:`);
* if both rows are reasoned and differ, both are still legacy and differ, or one side
  deleted a row the other modified, the merge is ambiguous: the driver exits 1, prints the keys, and does not write `%A`.
  Choose one row by hand.

The failure mode is deliberate: a reasoned row names who trusts what, so silently
picking one of two reviewed rows would lose a review. Git reports the file as
unmerged; edit `.github/trust-baseline.tsv` to keep one row per key, then run the gate.

CI runs `scripts/trust-ledger.sh --check`, not a merge driver; a merge made without
the local driver can leave a ledger that is textually merged but stale, duplicated or
missing a source. After any merge of this file, run `scripts/trust-ledger.sh --check`.

## Reducing the legacy rows

The ledger now has 730 rows: the migration's 753, minus the 73 removals below, plus 50
`partial` rows added by later modules (the `partial` group is 182 rows). The removals are
all structural, not a loosening of the gate:

| what was removed | rows | why it was not trust |
| --- | --- | --- |
| signed-word natives (`IntN.*Native`, `IntN.toNat`) | 52 | every other `IntN` operation has a Wiz body that delegates to a retained `UIntN` native or reads the representation (`IntN.toNat`); signed `shiftRight` and `lt` are kept native below |
| `toList`/`ofList` projections on arrays, maps and intern tables | 8 | the constructor's `repr:` registration already gives the native representation; the separate projection registration proved nothing new |
| `InternTable.empty`/`size` and `U64Map.contains` natives | 9 | their Wiz bodies are `.mk .nil`, a length and a match on the (still native) `find`/`toList`; all are cheaper to review than to trust twice |
| `partial` definitions that the kernel accepts as total | 2 | `Json.digits` recurses on the list tail, `Ring.synEq` on the syntax tree (`Json.sub` stays partial as an elaboration fence and is now reasoned) |
| `Scry.rdLoop` and `Scry.domLoop` fuel loops | 2 | their only recursive argument is `fuel`, a `Nat` predecessor, so removing `partial` is checked structural recursion (see the group below) |

The rule the BitVec IR test encodes: **a native is removed only if the Wiz body emits
the same primitive**. `IntN.shiftRight` and `IntN.lt` fail that test: their Wiz
bodies allocate (`IntN.not`/`IntN.below`, `IntN.isNeg`/`IntN.toNat`), so their
`wiz_word_ashr`/`wiz_word_slt` registrations and externs are back, with reasons.
`IntN.isNeg`, `IntN.shiftLeft` and `IntN.toNat` stay removed: their bodies read the
representation or delegate to a retained `UIntN` native and the IR has no word
constructor or projection.

The reviewed base falls into these groups:

* **FFI, 210 declarations (420 rows).** Each `extern` contributes an axiom (the C
  function) and a `builtin extern:` row (the marshalling). Both FFI audits are done:
  the OS/runtime modules (142 declarations, 208 rows) and the word/array/map modules
  (68 declarations, 212 rows: `Word`, `WordArray`, `WordMap` and `Intern`) carry
  symbol-specific reasons, naming the C function,
  the property that makes it the definition, and the marshalling's kind string. Do not
  bulk-renew them. `UInt64.ofNat` reduces mod 2^64 (the marshalling used to panic above
  2^64 while the doc promised modulo), and `scripts/trust-ffi-audit.sh --check`
  compiles each `builtin extern:` declaration against `runtime/wiz_rt.h`.
* **Mutual recursion and `partial`, 182 rows.** The rows come from `Feral` (70: 67
  mutual plus `Fe.core`/`Fe.tyStr`/`Fe.zonk`), `Web.React` (14), the `Scry` modules
  (49), `Json` (10: 9 mutual plus the deliberately opaque `Json.sub`), `SatTactic` (7),
  `Infoview` (7), `Tagged` (6), `BvDecide` (6), `Plot` (4), `Text` (3), `Prelude` (3),
  `Ring` (2) and `IO` (1). Wiz's kernel treats a `partial`
  definition as opaque: the definition is justified by an inhabited witness of its
  type (22f), never by a termination proof, so a row is not a claim that the recursion
  terminates. The 182 rows are accepted as one reviewed group, deliberately not
  de-mutualised: each reason names its block and what would remove the row —
  de-mutualising into structural recursion over the syntax or data tree, or a checked
  measure (fuel, a decreasing counter, or a worklist/visited-set measure). A
  `mutual`/`partial` row is therefore a documented design choice, not an unreviewed
  gap: a new one still needs a reason, and `--strict-legacy` still lists any that has
  not been through this review.
* **`implemented_by`, 56 rows.** The remaining ones are the performance-critical
  `UIntN`, array, map, intern and channel fast paths. They are covered by the
  differential `=word`/`=natives`/`=conc` tests; each reason names the Wiz model it
  replaces and the group that compares the two.
* **`builtin`, 30 rows and `repr:`, 7 rows.** The seals (opaque native
  representations) and the twenty `Prelude` numeral/operation/`memo` registrations are
  load-bearing: numerals, string literals and compiled arithmetic do not work without
  them. They are reviewed individually: each reason says what the registration makes
  native, why the Wiz definition is the specification, and what would remove it
  (unsealing the type, or deleting the registration and falling back to the definition
  that `=audit` already checks).

The 35 pure axioms (the foreign types, the seals, `Region`'s `Outlives` evidence and
`Prelude.castRefl`) carry a specific reason and the owner `Reuben Steenekamp`; so do
the kept `UIntN.toNat` native (the word tests pin it in the compiled IR) and the six
signed shift/compare rows. The last migration rows are gone: `Float64.ofNat` was
renamed `Float64.ofNatU64` when the rounding moved into Wiz and is reasoned under the
new name; the twenty `Prelude` numeral/`memo` registrations, the `PMap`/`Scry` seals
and `Proc.runLinked` now have their own reasons. `Json.sub` is partial by intent (it
is an elaboration fence, not recursion) and has a reason.

## Review cadence

Every row has a review date; a row is expired when that date is before today, so a
review is due at least every 180 days and `--check` fails until it is renewed with
`--update --review YYYY-MM-DD`. A new row defaults to today + 180 days. The migration
marker cannot come back: `--strict-legacy` is now enforced in CI (the ledger step of
the `build` job runs `scripts/trust-ledger.sh --check --strict-legacy`), and the `native` group
checks the same ledger.

### `partial` and `mutual`: a reviewed design choice

A `mutual … end` block of definitions and an explicit `partial def` are the same
source of trust: the kernel records the declaration with no value, checks an inhabited
witness of its type (22f), and treats the compiled body as opaque. The ledger row says
so; it does not say the recursion terminates, and the kernel makes no such claim. The
reason on every such row names the block, calls it compiled-only general recursion, and
states the removal path. De-mutualising is not a blanket goal: for the parser core,
`Feral`, `Json`, `SatTactic`, `BvDecide`, `Tagged` and the `Scry` engines the mutual
shape is the readable form of the algorithm, and a checked measure or a structural
rewrite is worthwhile only for a block that is small and hot.

### The numeric/container FFI audit

`Word`, `WordArray`, `WordMap` and `Intern` declare 68 externs (212 rows: each extern's
`axiom` and `builtin extern:` pair, plus the `native` registration and the seal
`builtin`s). All are reviewed with a reason naming the C function, the property that
makes it the definition, and the marshalling's kind string; the `native` rows name the
extern and point at the group that runs the model and the native against each other
(`=word` for the words, `=natives` for arrays, maps and intern tables, in C and LLVM).

The declaration is checked against the C prototype by
`scripts/trust-ffi-audit.sh --check` (the OS audit's script, shared): for every ledger
`builtin extern:SYM:kinds:result:…` it writes
`static <result> (*chk)(<params>) = SYM;` with the C types the marshalling uses and
compiles it against `runtime/wiz_rt.h`. `-Werror=incompatible-pointer-types` makes a
width or signedness mismatch a failure on compilers that would otherwise only warn:
without it a `uint64_t` declaration against an `int` definition is a silent
truncation, which the `native`/`natives` tests need not reach.

That check and the review found one real mismatch, in the `IO` module's machine types:
`UInt64.ofNat` said "modulo 2⁶⁴" and had type `Nat → UInt64`, so its `Nat` was
marshalled as a `uint64_t` (`wiz_in_nat`), which **panics** for a `Nat` of 2⁶⁴ or more.
The reduction now happens in Wiz before the call
(`UInt64.ofNat n := UInt64.ofNatRaw (Nat.mod n (2^64))`, with a private
`wiz_u64_id` extern), and the `ffi` group pins 2⁶⁴−1, 2⁶⁴ and 2⁶⁴+1 in C and LLVM.
`UInt64.toNat` needs no change (a `UInt64` is a raw 64-bit box, so the C side takes the
bits). `Float64.ofNat`'s rounding is another change; the `UInt64` fix does not overlap
it.

Not established by this pass: whether a *word* scalar in [2⁶², 2⁶³) can ever reach a
runtime path that assumes every scalar is a `Nat` (a word's representation is its bits,
so `wiz_word_out` boxes up to 2⁶³−1, while `wiz_out_nat` boxes only to 2⁶²−1); the
answer turns on the type discipline between `UIntN w` and `Nat` at every C entry point,
not on any one function. `UInt64`/`Float64`/`Array`/`Str`/`StrMap` externs are in
`IO`/`Std` (the OS audit's modules), so their reasons are not in this pass.

## Tests

`Tests/trust-ledger/run.sh` checks the gate's exit codes and messages against small
trees: a new axiom with no row, a row with no reason, an expired row, a renamed
declaration, a legacy row, a clean tree, and `--update` with and without a reason. The
`native` group runs it, so `lake test -- '=native'` covers it.

`scripts/trust-ledger-merge_test.sh` checks the merge driver without a build: disjoint
rows, the same row, a reasoned row against a legacy one, two reasoned rows (must
refuse), a row deleted on one side and unchanged on the other (both directions; must
be deleted), a row deleted on one side and modified on the other (both directions;
must refuse), comments, CRLF, and 100 pseudo-random rows. Its last cases install the
driver with `scripts/setup-trust-merge.sh` in a throwaway repository and run real
`git merge`s (a union, a deletion, a refused conflict), so they also check the
`.gitattributes` registration. CI runs it in the ledger step of the `build` job.

CI runs `scripts/trust-ledger.sh --check --strict-legacy` (a step in the `build` job of
`.github/workflows/ci.yml`), so both the new-entry gate and the end of the migration
are enforced before any test shard starts.
