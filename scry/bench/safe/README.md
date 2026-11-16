# The safe-code corpus (precision half)

Scry's measured false-positive story on real code is one synthetic `infeasible-safe`
case. This directory is the other half: **25 realistic C files that use the same
constructs as the vulnerable corpus but with the correct guard**. Every file must
produce **zero findings**; a finding here is a measured false positive.

The corpus is deliberately **opt-in**. It is not listed in `bench/corpus/manifest.json`
and `bench/baseline.json` does not mention it, so a precision experiment cannot change
the recall baseline, and a recall regression in the vulnerable corpus is still visible.

## Run

```sh
cd scry
../.lake/build/bin/grail build scry
# the group-level pass/fail (exit 1 if any case has a finding)
../.lake/build/bin/grail test safe
# the same group through the bench harness: 25 safe cases, 0 expected findings
.grail/bin/scry bench --corpus bench/safe --no-baseline --no-timing
# a per-case TSV with findings / use-after-free warnings / boundaries
SCRY_BIN=$PWD/.grail/bin/scry scripts/safe-measure.sh
```

`expect: safe` cases with a *blocking* lowering boundary are reported as `unknown`, not
`tn`, exactly as in `bench/corpus/README.md`. The gate here is `findings == 0`, not the
outcome string: an `unknown` case is still allowed to be a boundary, but a finding in it
is not.

## What each case mirrors

| directory | vulnerable sibling | safe guard |
|---|---|---|
| `cmd/` | `cwe78/direct-unsafe.c`, the CVE-2016-3714 / CVE-2024-23749 shape | `escape_shell`, an in-place `sanitize`, `quote_arg`, or an allow-list |
| `fmt/` | `cwe134/printf-unsafe.c`, the CVE-2000-0573 / CVE-2012-0809 shape | a literal format, a `sanitize_format` result, or a size-limited `snprintf` |
| `copy/` | `cwe120/strcpy-unsafe.c`, `cwe242/gets-unsafe.c`, `memcpy`/`read` lengths | `strncpy`/`strlcpy`/`strncat`, a literal length, a size-limited `snprintf`, a checked `read`, or a `clamp_len` helper |
| `alloc/` | the CWE-190 size sink | a checked wire length before `malloc` |
| `uaf/` | `mem-free.c`, CVE-2020-1752 / CVE-2019-7317 | free-then-null, reallocation, an error-path free, a checked `realloc` |
| `path/` | CVE-2021-41773 | `realpath` before the open, a `sanitize_path` result |
| `alias/` | pointer/alias memory flow | two distinct slots, a pointer re-bound after its copy |

## Results

The table is generated from `scripts/safe-measure.sh`; "before" is the base commit
`54f6ded5` (the `agent/scry-models` tip), "after" is this branch.

| case | findings before | findings after | class |
|---|---:|---:|---|
| `alias/distinct-slots.c` | 0 | 0 | — |
| `alias/rebind-write.c` | 1 | 1 | alias imprecision (flow-insensitive points-to) — pinned |
| `alloc/size-checked.c` | 0 | 0 | — (allocation size sinks do not reach the C pipeline) |
| `cmd/allowlist.c` | 0 | 0 | — |
| `cmd/escape-shell.c` | 0 | 0 | — |
| `cmd/inplace-sanitise.c` | 0 | 0 | — |
| `cmd/quote-arg.c` | 1 | 0 | missing sanitiser trust (policy model) — fixed |
| `copy/memcpy-literal.c` | 0 | 0 | — |
| `copy/read-checked.c` | 1 | 1 | missing path correlation (bounds check) — pinned |
| `copy/read-clamped.c` | 1 | 0 | missing sanitiser semantics (`clamp_len` was trusted but `retsrc` bypassed the kill) — fixed |
| `copy/snprintf-clamped.c` | 1 | 1 | missing path correlation (bounds check) — pinned |
| `copy/strcpy-literal.c` | 1 | 1 | blanket rule (`strcpy` is forbidden whenever it appears) — pinned |
| `copy/strlcpy-sized.c` | 0 | 0 | — |
| `copy/strncat-bounded.c` | 0 | 0 | — |
| `copy/strncpy-bounded.c` | 0 | 0 | — |
| `fmt/chained-literal.c` | 0 | 0 | — |
| `fmt/literal-format.c` | 0 | 0 | — |
| `fmt/sanitised-format.c` | 1 | 0 | missing sanitiser trust (policy model) — fixed |
| `fmt/snprintf-bounded.c` | 0 | 0 | — |
| `path/realpath.c` | 0 | 0 | — (two `unmodelled-external` warnings, a coverage boundary) |
| `path/sanitised-path.c` | 0 | 0 | — (one `unmodelled-external` warning, a coverage boundary) |
| `uaf/early-return.c` | 0 | 0 | — |
| `uaf/free-then-null.c` | 0 findings, 1 UAF warning | 0, 0 | flow-insensitivity — fixed |
| `uaf/realloc-checked.c` | 0 | 0 | — |
| `uaf/reassign.c` | 0 findings, 1 UAF warning | 0, 0 | flow-insensitivity — fixed |

**Before: 7 findings in 7 of 25 cases, plus 2 false `use-after-free` warnings.**
**After: 4 findings in 4 of 25 cases (all pinned), 0 in the other 21, and 0 UAF
warnings.** The pack fix removes 3 findings and the lifetime fix removes 2 warnings;
the 4 remaining findings are the S6/alias/blanket backlog, each with its reason.

The "after" column is a composite of three measurements, because a fresh C CLI build
is blocked by the `Models.wiz` checker timeout in this environment (see
`scry/bench/cve.md`):

* `quote-arg` and `sanitised-format` are measured end to end with the base model binary
  and this branch's `lib/Scry/rules/default.scry` (the pack is runtime data);
* `read-clamped` also needs the `rtRuleRetSrc`/`!san` engine fix, verified by the
  `scry-taint` case **return-value summary: a pack sanitiser kills a unit-defined
  callee's return** (0 findings with the sanitiser pack, 1 without);
* the lifetime rows' "0 warnings" are verified by the `scry-taint` case
  **lifetime: a null-after-free is not a use-after-free** and by a standalone probe over
  the same `freedHit`/`stillDangling` code that prints `direct: 1`, `null-after: 0`.

The full group is **38 passed, 0 failed**. The C gate `grail test safe` is ready to run
as soon as a binary built from this branch exists; `scry/scripts/safe-measure.sh` and
`scry bench --corpus bench/safe` produce the same table from any binary.

## False-positive causes and fixes

* **Missing sanitiser trust and a seed bypass (fixed).** `quote_arg`,
  `sanitize_format` and `clamp_len` were already policy models
  (`Scry.Models.policyModels`), but the default pack did not name them, and a model
  sanitiser only applies when the pack trusts it. The pack now names them: `quote_arg`
  on the command rule, `sanitize_format` on the format rule, and
  `clamp_len`/`checked_size` on a `buffer-overflow` rule. The last block is placed after
  `strcpy-overflow` so `withModels` appends `integer-overflow` in the same order as
  before (the SARIF rule indices are stable). `clamp_len` is a **unit-defined** helper
  whose body returns its input, so the callee-return summary seeded the call result
  through `retsrc` and the propagation rule's `!san` never saw it; `rtRuleRetSrc` now
  carries `!san` too. A result sanitiser therefore kills a tainted return from a
  unit-defined callee as well as an external one.
* **Flow-insensitivity of the freed set (fixed).** `Scry.freedWarning` asked only
  whether a free reaches the access and the (flow-insensitive) location set overlaps.
  `free(p); p = 0; *p` and `free(p); p = malloc(...); *p` therefore warned. The use test
  now checks the *reaching definitions of the access register*: a literal, a havoc, or a
  fresh allocation/address taken after the free kills the dangling value; a copy from an
  `unknown` or overlapping pointer does not; a load or a derived pointer is never a kill.
  The points-to table stays flow-insensitive, so the true `free(p); *p`, the alias case
  and the loop back edge are unchanged. The points-to fix is in `Scry.RuleTaint`
  (`defKillsAlias`, `stillDangling`, `freedHit`).
* **Blanket rule (reported, not fixed).** `copy/strcpy-literal.c` copies a literal into a
  buffer that is large enough, and the `strcpy-overflow` rule reports the call anyway.
  `strcpy` is a *forbidden call*: the rule's evidence is "this unbounded call appears",
  not "this data reaches it". Making it taint-conditional would stop the synthetic
  `cwe120/strcpy-unsafe.c` (whose source argument is a constant) from firing, which is a
  recall regression. A useful rule needs the destination bound and the source length
  (S9/S12's bounds work), not a weaker taint condition.
* **Missing path correlation (reported, needs S6).** `copy/read-checked.c` and
  `copy/snprintf-clamped.c` check the wire length against the buffer (or clamp it with a
  branch) before the copy; the `buffer-overflow` rule is a reachability rule for a
  tainted length and does not see the path condition. `alloc/size-checked.c` is the same
  shape; it currently has no finding because `malloc` is lowered to `Wil.alloc` and the
  size sink cannot reach the C pipeline, which is a separate documented gap. Pruning
  these needs S6's path conditions/SMT (the exclusive-branch prototype in
  `lib/Scry/Smt.wiz`), not a rule change: a bounds check is a branch, and a sanitiser
  would have to be a call.
* **Alias imprecision (reported, needs flow-sensitive points-to).** In
  `alias/rebind-write.c` the copy runs while `p` points at `a`; `b` is initialised
  separately and `p` is re-bound only afterwards. One location set per register merges
  `a` and `b`, so the copy's store taints `b` and `system(b[0])` fires. A strong update
  on the pointer assignment (or S6 path correlation) is the fix; the 1-call-site context
  already removed the interprocedural half of this class.
* **Not a finding (coverage boundary).** `path/realpath.c` and
  `path/sanitised-path.c` have zero findings but emit `unmodelled-external` warnings for
  `realpath` and `fopen`. `realpath` has no points-to model (its result is `unknown`),
  so an `unknown-memory` warning accompanies a later open; this is the explicit external
  boundary, not a false alarm. A path model is future work (`realpath` as a fresh/arg-0
  result and a sanitiser).
