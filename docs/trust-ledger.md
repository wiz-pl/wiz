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

The migration's 753 rows are not a renewal list: the reviewed base is now 680 rows
(24 still carrying the migration marker), 73 fewer (9.7%). The reduction is no longer
over 10%: the signed shift/compare exception below is a correctness fix for the native
IR. The removals are all structural, not a loosening of the gate:

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

The remaining rows fall into five groups, with the plan for each:

* **FFI, 210 declarations (420 rows).** Each `extern` contributes an axiom (the C
  function) and a `builtin extern:` row (the marshalling). These are the mechanical
  bulk and the next review unit: audit by C symbol against `runtime/` and `c/`, then
  replace the two `legacy:` rows with one reason naming the symbol and its contract.
  Do not bulk-renew them. Both FFI audits are done: the OS/runtime modules (147
  declarations, 290 rows) and the word/array/map modules (66 declarations, 198
  rows) now carry symbol-specific reasons. `UInt64.ofNat` reduces mod 2^64 in Wiz
  (the marshalling used to panic above 2^64 while the doc promised modulo), and
  `Float64.ofNat` rounds for every `Nat` on top of the `Float64.ofNatU64` extern.
  The remaining legacy rows are outside the `partial` group (below).
* **Mutual recursion and `partial`, 132 rows (109 in `mutual` blocks, 23 standalone
  `partial`).** The blocks are `Feral` (70: 67 mutual plus `Fe.core`/`Fe.tyStr`/
  `Fe.zonk`), `Json` (9 mutual plus the deliberately opaque `Json.sub`), the `Scry`
  engines (18), `SatTactic` (7), `BvDecide` (6), `Tagged` (6), `Infoview` (7), `Ring`
  (2), `Prelude` (2), `Text` (3) and `IO` (1). Wiz's kernel treats a `partial`
  definition as opaque: the definition is justified by an inhabited witness of its
  type (22f), never by a termination proof, so a row is not a claim that the recursion
  terminates. The 134 rows are accepted as one reviewed group, deliberately not
  de-mutualised: each reason names its block and what would remove the row —
  de-mutualising into structural recursion over the syntax or data tree, or a checked
  measure (fuel, a decreasing counter, or a worklist/visited-set measure). Two small
  fuel loops are structural and are now total (`Scry.rdLoop`, `Scry.domLoop`: the only
  recursive argument is the `Nat` predecessor of `fuel`), so 2 rows are gone and 132
  remain. A `mutual`/`partial` row is therefore a documented design choice, not an
  unreviewed gap: a new one still needs a reason, and `--strict-legacy` still lists any
  that has not been through this review.
* **`implemented_by`, 56 rows.** The remaining ones are the performance-critical
  `UIntN`, array, map, intern and channel fast paths. They are covered by the
  differential `=word`/`=natives` tests; review each against the C function it names.
* **`builtin`, 30 rows and `repr:`, 7 rows.** Ten seals (opaque native
  representations) and the twenty `Prelude` numerals/operations/`memo` registrations
  are load-bearing: numerals and compiled arithmetic do not work without them. They
  should be reviewed as a group, not removed.

The 35 pure axioms (the foreign types, the seals, `Region`'s `Outlives` evidence and
`Prelude.castRefl`) now carry a specific reason and the owner `Reuben Steenekamp`; so
do the kept `UInt64.toNat` native (the word tests pin it in the compiled IR) and the six
signed shift/compare rows. The 24 rows that still say `legacy:` are outside the group:
the twenty `Prelude` numeral/`memo` registrations, the `PMap`/`Scry` seals, and
`Proc.runLinked`. `--strict-legacy` lists them, and the 2027-05-14 expiry is their
deadline. `Json.sub` is partial by intent (it is an elaboration fence, not recursion)
and has a reason.

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

`Word`, `WordArray`, `WordMap` and `Intern` declare 66 externs (198 rows: each extern's
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

CI runs `scripts/trust-ledger.sh --check` (see the `trust-ledger` job in
`.github/workflows/ci.yml`); the gate is inside `--check`, so no new flag is needed.
