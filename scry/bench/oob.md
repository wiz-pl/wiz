# Out-of-bounds writes and reads (CWE-787 / CWE-125)

Status: new opt-in rule family. `lib/Scry/rules/oob.scry` is not in `default.scry`, so no
default finding, benchmark baseline or safe-corpus count changes. The analysis is
`lib/Scry/Bounds.wiz`; the C fixtures are `scry/tests/fixtures/oob-*.c` and the package
test is `scry/tests/oob.wiz`.

```sh
cd scry
../.lake/build/bin/grail build scry
../.lake/build/bin/grail test oob
.grail/bin/scry taint tests/fixtures/oob-write-heap.c --rules ../lib/Scry/rules/oob.scry
```

## What the rule claims

A finding is reported only when all three are known:

1. the points-to layer resolves the access pointer to an allocation (`Loc.heap` or
   `Loc.stack`);
2. the lowering recorded a **statically known** cell count for that allocation;
3. the subscript index or copy length is tainted by the pack's sources, and no
   dominating `index < capacity` (or `count <= capacity`) branch proves it in range.

If the allocation size is a runtime expression, the lowering records `0` and the result
is `scry/memory/unknown-memory`, not a finding. This is the deliberate boundary: the
rule does not turn "I do not know the extent" into an out-of-bounds claim.

The analysis does **not** reason about loops, induction variables, pointer walks
(`*dst++`), negative indices, symbolic capacities, or interprocedural object extents.

## Fixtures

| fixture | family | expected |
|---|---|---|
| `oob-write-heap.c` | CWE-787 | one `out-of-bounds-write`; `int *a = malloc(32)` is 4 cells and `i = getenv(...)[0]` is tainted |
| `oob-write-heap-safe.c` | CWE-787 control | none; `if (i >= 4) return;` dominates the store |
| `oob-write-read.c` | CWE-787 | one `out-of-bounds-write`; `read(0, buf, n)` into `char buf[16]` with tainted `n` |
| `oob-write-read-safe.c` | CWE-787 control | none; `n = clamp_len(n, 16)` is the trusted cap |
| `oob-read-heap.c` | CWE-125 | one `out-of-bounds-read`; the same heap object on the load side |
| `oob-read-heap-safe.c` | CWE-125 control | none; `if (i >= 4) return;` dominates the load |
| `oob-read-memcpy.c` | CWE-125 | one `out-of-bounds-read`; `memcpy(dst, src, n)` with `char src[16]` and tainted `n` |
| `oob-read-memcpy-safe.c` | CWE-125 control | none; `if (n > 16) return;` dominates the copy |
| `oob-unknown.c` | size trap | no finding; `malloc(n)` has unknown size and yields `unknown-memory` |

The `read` fixture also triggers the pre-existing model rule `buffer-overflow` (the
`read` length sink). That is a different rule family and is not counted as this rule's
finding; the control uses the trusted `clamp_len` sanitiser, which kills both.

## Measurement on the out-of-scope CVE cases

These are the CVE corpus entries that `scry/bench/cve-v2.md` lists as out of scope
because no CWE-787/125 family existed. Measured with the branch's build and the opt-in
pack:

```sh
for c in cve-2021-23017 cve-2018-1000001 cve-2014-0160; do
  scry taint bench/cases/$c/case.c --rules ../lib/Scry/rules/oob.scry
done
```

| case | CWE | shape | result |
|---|---|---|---|
| CVE-2021-23017 | 787 | nginx resolver one-byte write, `malloc(len)` with runtime `len`, writes at `*dst++` | no fire; 5 `unknown-memory` boundaries |
| CVE-2018-1000001 | 787 | glibc realpath underflow, `char resolved[128]`, writes at `*dest++` | no fire; 3 `unknown-memory` boundaries |
| CVE-2014-0160 | 125 | Heartbleed, `memcpy(bp, pl, payload)` where `payload` is a length field and `record[64]` is the source | no fire; 6 `unknown-memory` boundaries (the copy source is an unknown pointer) |

A fire on a fixed control would be a false positive. The CVE v2 corpus has no fixed
control for these out-of-scope entries; the fixtures above supply the fixed controls for
the two families.

**Result: 0/3, honestly.** The two CWE-787 reductions are pointer walks (`*dst++`,
`*dest++`), not indexed accesses, and one of them allocates with a runtime size; the
CWE-125 copy's source is an unresolved pointer, so the points-to layer cannot name an
object with a size. The rule reports the latter two facts as `unknown-memory` boundaries
and stays silent; it does not turn them into findings. Per family the reduction recall
is CWE-787 **0/2**, CWE-125 **0/1**. This is a measurement of the existing reductions,
not a claim about the CVE population.

## False-positive cost

The rule is opt-in, so the checked-in benchmark corpus and its baseline are unchanged:
`scry bench --no-timing` still reports **52 cases, TP 32, FP 1, TN 17, FN 0, unknown 2**
and matches `bench/baseline.json`. That FP is the pre-existing `infeasible-safe` case,
not this family.

On the OOB fixtures, the four fixed controls fire **0** times (0/4 FP) and the unknown
size probe yields a boundary, not a finding. The two `read`/`memcpy` controls also stay
clean from the pre-existing `buffer-overflow` model rule; the read control uses the
trusted `clamp_len` cap, the memcpy control an explicit `n <= 16` branch. Recall on the
hand-authored fixtures is **4/4** (two writes, two reads). These are eight hand-authored
cases, so the numbers are a smoke test, not a population estimate.
