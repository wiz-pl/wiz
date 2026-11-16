# scry on a real C corpus (2026-11-14)

Status: measurement report, no analysis changes. Branch `agent/scry-real-corpus`
(based on `agent/scry-points-to` `bb1a6294`, with `agent/scry-bench` `08d292e4`
merged for the `scry bench` harness). The raw machine-readable record is
[`real-corpus.json`](real-corpus.json); the runner is
[`../scripts/real-corpus.sh`](../scripts/real-corpus.sh).

Command (run once, under `heavy`, with the worktree's own `grail`/`scry`):

```sh
cd scry && cp ../grail.local.wiz .
../.lake/build/bin/grail build
scry/scripts/real-corpus.sh                  # 24 files, 300 s per-file limit
SCRY_STRESS=1 scry/scripts/real-corpus.sh    # also the 3.8 MB tree-sitter parser
```

The harness runs `scry taint FILE --json --allow-errors --sarif OUT` (the same
parse → lower → points-to → rule-pack taint → certify pipeline as `scry taint`) and
records the JSON counts, one SARIF file per source, exit status, parse-error count and
wall time. Points-to is not a separate CLI: its diagnostics are the `scry/memory/*`
entries in the same JSON/SARIF. `--allow-errors` is deliberate: the question here is what the analysis does
on real code, including recovery trees; the CLI's default refusal is recorded
separately below. Wall time is informational on this shared machine and is **not** a
`perf-run` measurement.

## Corpus actually present on disk

The brief named `wiz/runtime`, `wiz-rv/golem`, `wiz-ddr3`, `wiz-crucible`,
`wiz-reals` and `projects`. On this machine (2026-11-14) the tracked C is:

| requested project | what exists | used |
|---|---|---|
| `wiz/runtime` | the runtime is split into `runtime/rt_*.inc` on this branch; no `runtime/wiz.c` | `selfhost/rt.c` (the self-hosted runtime), `c/*.c`, `lib/serial.c`, `infoview/term.c`, `web/js.c` |
| `wiz-rv/golem` | no `golem` directory or file under `/workspace`; the C sources are `sw/*.c` | all 8 `wiz-rv/sw` files |
| `wiz-ddr3` | no tracked `.c`; only `.wiz` sources and generated `.grail/build/*/main.c` | no tracked C; generated trees excluded (they are not reproducible inputs) |
| `wiz-crucible` | Python only | no C |
| `wiz-reals` | Wiz only | no C |
| `projects` | `/workspace/wizard-test/build/old-wizard.c`, `/workspace/soyjack/droste.c` | both, as `generated` |
| — | vendored `scry/native/tree-sitter/lib/src/*.c` | 8 files, as `tree-sitter` |

The two generated projects are listed only if present; on a bare checkout the script
records them as `missing` and still succeeds.

## Exact counts

`scry/scripts/real-corpus.sh`, `SCRY_LIMIT=300`, total runtime **366 431 ms**
(24 files; all present; 0 timeouts; 0 errors).

| project | files | findings | checked | boundary | unknown-memory | unknown-indirect | parse errors | ms |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| wiz-lang | 6 | 1 | 1 | 1 331 | 0 | 1 | 161 | 53 654 |
| wiz-rv | 8 | 1 | 1 | 783 | 14 | 0 | 0 | 54 993 |
| tree-sitter | 8 | 0 | 0 | 4 363 | 25 | 5 | 23 | 256 887 |
| generated | 2 | 0 | 0 | 0 | 0 | 0 | 1 984 | 897 |
| **total** | **24** | **2** | **2** | **6 477** | **39** | **6** | **2 168** | **366 431** |

"unknown-memory" and "unknown-indirect" are the two `scry/memory/*` warning kinds;
there were no `use-after-free` warnings. The 45 memory warnings are 39 + 6.

Per file (files with findings or non-trivial diagnostics):

| project | file | findings | boundary | memory | parse errors | ms |
|---|---|---:|---:|---:|---:|---:|
| wiz-lang | `c/proc.c` | 0 | 25 | 0 | 0 | 53 |
| wiz-lang | `c/sockets.c` | 0 | 202 | 0 | 0 | 1 857 |
| wiz-lang | `lib/serial.c` | 0 | 226 | 0 | 11 | 22 756 |
| wiz-lang | `infoview/term.c` | 1 | 292 | 0 | 0 | 10 126 |
| wiz-lang | `selfhost/rt.c` | 0 | 586 | 1 | 146 | 18 858 |
| wiz-lang | `web/js.c` | 0 | 0 | 0 | 4 | 4 |
| wiz-rv | `sw/ctest/ctest.c` | 1 | 35 | 2 | 0 | 1 288 |
| wiz-rv | `sw/doomgeneric_wizrv.c` | 0 | 89 | 4 | 0 | 4 664 |
| wiz-rv | `sw/iss/iss.c` | 0 | 159 | 4 | 0 | 36 417 |
| wiz-rv | `sw/iss/mustest.c` | 0 | 51 | 2 | 0 | 5 370 |
| wiz-rv | `sw/mus_synth.c` | 0 | 90 | 0 | 0 | 586 |
| wiz-rv | `sw/sound_wizrv.c` | 0 | 268 | 0 | 0 | 6 272 |
| wiz-rv | `sw/syscalls.c` | 0 | 88 | 2 | 0 | 388 |
| wiz-rv | `sw/tone/tone.c` | 0 | 3 | 0 | 0 | 8 |
| tree-sitter | `alloc.c` | 0 | 32 | 0 | 4 | 51 |
| tree-sitter | `language.c` | 0 | 211 | 0 | 2 | 1 160 |
| tree-sitter | `lexer.c` | 0 | 417 | 5 | 2 | 3 441 |
| tree-sitter | `node.c` | 0 | 326 | 2 | 0 | 13 532 |
| tree-sitter | `parser.c` | 0 | 1 271 | 8 | 1 | 79 146 |
| tree-sitter | `query.c` | 0 | 1 473 | 9 | 14 | 149 221 |
| tree-sitter | `tree.c` | 0 | 142 | 0 | 0 | 414 |
| tree-sitter | `tree_cursor.c` | 0 | 491 | 6 | 0 | 9 922 |
| generated | `old-wizard.c` | 0 | 0 | 0 | 1 004 | 312 |
| generated | `droste.c` | 0 | 0 | 0 | 980 | 585 |

### Refusal path (without `--allow-errors`)

`scry taint` exits 1 and prints no JSON for a file with parse errors:

| file | parse errors | default result |
|---|---:|---|
| `lib/serial.c` | 11 | refused |
| `old-wizard.c` | 1 004 | refused |
| `droste.c` | 980 | refused |

### Stress case

`scry/native/tree-sitter-c/src/parser.c` (3 872 012 bytes) was also run directly with
`timeout 300 scry taint … --json --allow-errors`: **exit 124 (timeout) at 300 034 ms,
no JSON**. `SCRY_STRESS=1` includes it in the harness for a repeat.

## Precision spot-check (5 diagnostics per project)

There are only **two findings in 24 files**, both `strcpy-overflow`, both
certificate-checked, and **both judged false positives** on manual review. The
synthetic `scry bench` corpus is much better (20 TP, 1 FP); that is the gap this
report is about. Where a project has fewer than five findings, the spot-check covers
its memory and boundary diagnostics instead (and says so).

### wiz-lang (1 finding, 1 memory warning, 1 331 boundary warnings)

| # | diagnostic | verdict |
|---|---|---|
| 1 | `infoview/term.c:100` `strcpy-overflow` in `static:iv_addr` | **FP**: the preceding `if (strlen(path) >= sizeof a->sun_path) return -1;` proves the copy bounded; the forbidden-call rule is unconditional. |
| 2 | `selfhost/rt.c:301` `unknown-indirect` in `*p ` | correct unknown: dispatch through a variant field `p->f[0]`; the target set genuinely is not known. |
| 3 | `lib/serial.c:123` `integer literal \n not modelled` | **FP/noise**: a valid character literal, mis-tokenized during recovery (11 parse errors in this file). |
| 4 | `c/sockets.c:208` `identifier w not modelled: havoc i32` (34× in the project) | **FP/noise**: `w` is `lean_object *`; the unknown typedef makes every use havoc with the wrong type. |
| 5 | `infoview/term.c:273` `implicit return (undefined in C)` in `iv_exit` | **FP/noise**: `iv_exit` is a `void` function; reaching `}` is defined behaviour. |

Missed sink (not a diagnostic): `infoview/term.c:260`
`execl("/bin/sh", "sh", "-c", cmd, …)` → no finding; `execl`/`execv` are not sinks in
`default.scry`, and `iv_spawn`'s `cmd` parameter is an exported FFI entry
(`infoview/Tui.wiz:28`) with no source model.

### wiz-rv (1 finding, 14 memory warnings, 783 boundary warnings)

| # | diagnostic | verdict |
|---|---|---|
| 1 | `sw/ctest/ctest.c:20` `strcpy-overflow` in `main` | **FP**: `strcpy(buf + 1, "wiz-rv")` writes 7 bytes into `static char buf[64]`. |
| 2 | `sw/ctest/ctest.c:10` `unknown-memory` in `static:puts_` (first load) | **FP**: the only call is `puts_(buf + 9)` and `buf` is a known 64-byte global; the parameter set should be `field (glob buf) 9`. |
| 3 | `sw/ctest/ctest.c:10` `unknown-memory` (second load) | **FP**: same root cause as #2 (`*s` in the loop). |
| 4 | `sw/doomgeneric_wizrv.c:89` `unknown-memory` in `DG_GetKey` | correct boundary: `int *pressed`/`unsigned char *key` are output parameters of an exported entry with external callers. |
| 5 | `sw/syscalls.c:40` `unknown-memory` (external `memcpy`) in `_read` | correct boundary: `_read(fd, char *buf, n)` is called by the C runtime, not the unit; the buffer is genuinely unknown. |

`sw/iss/iss.c:43–47` (`key_at`) and `mustest.c:13/19` are the same API-boundary
unknown, not new bugs.

### tree-sitter (0 findings, 30 memory warnings, 4 363 boundary warnings)

| # | diagnostic | verdict |
|---|---|---|
| 1 | `lexer.c:91` `unknown-indirect` in `ts_lexer__get_chunk` | correct: `self->input.read(...)` is an external callback stored in the public `Lexer` struct. |
| 2 | `lexer.c:378` `unknown-memory` in `ts_lexer_init` | correct boundary: `Lexer *self` is an exported API pointer. |
| 3 | `node.c:862` `unknown-memory` in `ts_node_edit` | correct boundary: exported API parameter. |
| 4 | `parser.c:240` `unknown-memory` in `ts_parser__breakdown_lookahead` | **FP candidate**: all three callers pass `&lookahead` (a local), so `*lookahead` is a known stack cell; the parameter summary loses it. |
| 5 | `query.c:1078` `unknown-memory` in `analysis_state__compare` | correct: a `qsort` callback receives `AnalysisState **` from outside the unit. |

There are zero findings in 4 363 boundary warnings; the tree-sitter code has no
`system`/`popen`/`gets` sink, so recall cannot be measured positively here, but the
absence of any `strcpy` finding is notable (it does not call `strcpy`).

### generated (0 findings, 0 memory warnings, 0 boundary warnings)

Both files are a **total recall failure**, not a spot-checkable diagnostic set: the
lowering returns an empty unit after parse recovery. The missed real calls are:

| # | missed site | why it matters |
|---|---|---|
| 1 | `old-wizard.c:272` `strcpy(b->str+b->used, s)` | never reached: 1 004 parse errors, 0 findings. |
| 2 | `old-wizard.c:328` `strcpy(src + n, *p)` | same. |
| 3 | `droste.c:248` `strcpy(b->str+b->used, s)` | never reached: 980 parse errors, 0 findings. |
| 4 | `droste.c:304` `strcpy(src + n, *p)` | same. |
| 5 | whole file | 0 boundary and 0 memory warnings too, so a caller cannot tell "nothing found" from "not analysed". |

## Top five real-code false positives / false negatives

1. **FN (P0): parse recovery silently yields an empty analysis.** `old-wizard.c`
   (1 004 errors) and `droste.c` (980) produce **0 findings, 0 boundary, 0 memory**
   even with `--allow-errors`; they contain four `strcpy` calls. `lib/serial.c` (11
   errors) is refused by default; `selfhost/rt.c` (146 errors) does analyse. A recovery
   tree must either lower what it can or emit one whole-file "not analysed" boundary.
2. **FN (P0): command-execution sinks and FFI entry parameters are missing.**
   `infoview/term.c:260` `execl("/bin/sh","sh","-c",cmd)` has no rule;
   `execv`/`execvp`/`posix_spawn` are likewise unmodelled. `cmd` is an exported
   C-ABI entry (`Tui.wiz:28`), but public parameters are not sources.
3. **FP (P1): forbidden `strcpy`/`strcat` ignores dominating bounds.** Both real
   findings are safe: `term.c:100` is guarded by a `strlen`/`sizeof` check;
   `ctest.c:20` copies a 6-byte literal into a 64-byte array. Observed real-code
   precision is **0/2**; `scry bench` precision on the crafted corpus is 95.24%.
4. **FP (P1): `unknown-memory` on known stack/global cells.** `ctest.c:10`
   `puts_(buf + 9)` reports unknown even though `buf` is a known global; `parser.c:240`
   `*lookahead` reports unknown even though every caller passes `&lookahead` (a local).
   The same warning kind also covers genuine API boundaries, so users cannot separate
   "analysis bug" from "external caller".
5. **FP/noise (P1): boundary warnings swamp the report.** 6 477 warnings for 24 files:
   1 108 `field access on unknown` + 801 `struct field access not modelled` (no
   preprocessor/include model), 34 `identifier w not modelled` (unknown typedef), 39
   `integer literal … not modelled` (valid literals), 173 `implicit return (undefined
   in C)` (mostly `void` functions). SARIF for `query.c` alone has 1 473 warning
   results against 0 findings.

## Prioritized follow-up list

**P0 — silent recall loss**

- [ ] **`scry/C-recovery`**: when parse errors are present, either lower the recovery
  tree or emit a single `scry/lowering/not-analysed` result and make
  `--allow-errors` exit nonzero with `--fail-on-finding`. Regression gate:
  `old-wizard.c`/`droste.c` must not report an empty success.
- [ ] **`scry/rules-exec`**: add `execl`, `execlp`, `execv`, `execvp`, `execve`,
  `posix_spawn`, `posix_spawnp` with the command/argument selector, and a source
  policy for exported C-ABI entry parameters (or an explicit `entry` annotation).
  Fixture: `iv_spawn(const char *cmd)` from `infoview/term.c`.

**P1 — precision and signal quality**

- [ ] **`scry/strcpy-bounds`**: use constant destination size and a dominating
  `strlen`/`sizeof` guard to suppress the two observed FPs; keep the unconditional
  finding when the size is unknown. Fixtures: `term.c:100`, `ctest.c:20`.
- [ ] **`scry/pt-arg-summary`**: fix parameter summaries for `field (glob buf) k` and
  address-of locals (`&lookahead`), with `mem-global-arg.c` and `mem-param-local.c`
  regressions; the two `ctest.c:10` warnings and `parser.c:240` are the evidence.
- [ ] **`scry/includes`**: model `#include`/typedefs enough to resolve common headers,
  or classify "unknown type" as a distinct advisory (not per-use havoc); 1 909
  field-access warnings and 34 `identifier w` warnings come from this.
- [ ] **`scry/warning-taxonomy`**: stop warning on valid integer/character literals
  and `void` implicit returns; ensure the literal text is carried, not empty.
  (39 + 173 observed instances.)

**P2 — scale and reporting**

- [ ] **`scry/scaling`**: 3.8 MB `tree-sitter-c/src/parser.c` times out at 300 s;
  171 KB `query.c` takes 126 s, 80 KB `parser.c` 75 s. Add a size/step guard and a
  reproducible benchmark; investigate the apparent super-linear points-to/interproc
  work before claiming whole-translation-unit scale.
- [ ] **`scry/sarif-advisory`**: emit boundary/memory advisories in a separate SARIF
  run or behind a flag; 6 477 warnings for 2 findings is not a usable CI gate.
- [ ] **`scry/corpus`**: add `wiz-ddr3`/`wiz-crucible`/`wiz-reals` only when they grow
  tracked C; do not commit generated `.grail` trees. Add the stable 24-file list above
  to CI when the branch has a dedicated shard.

## `scry bench` (synthetic S0/S2 corpus, not real code)

Same run, `scry bench --no-timing --json -`, 34 cases / 34 files / 8 197 bytes:

| metric | value |
|---|---:|
| TP / FN / TN / FP / unknown | 20 / 0 / 11 / 1 / 2 |
| TPR / FPR / Youden | 100.00% / 8.33% / 91.67% |
| precision / F1 | 95.24% / 97.56% |
| path valid / certificates checked | 22/22 / 22/22 |
| boundary warnings | 30 (4 blocking, 3 cases) |

The 1 FP is the documented path-insensitive `cwe78/infeasible-safe.c`; the 2 unknown
cases are the struct-field and `else` boundary probes. This is the reference the real
corpus should be compared against, not a substitute for it.

## Validation

- `grail build` in `scry/` after the `agent/scry-bench` merge: **succeeds** (102 jobs
  up to date, 11 run).
- `grail test` in `scry/`: **9 passed, 0 failed** (8 recorded passes), including
  `tests/bench.wiz` after rebaselining.
- Merging `agent/scry-bench` brought its 34-case baseline, which still recorded the
  pre-points-to outcomes (18 TP / 2 FN). The points-to branch resolves the two
  documented FNs (`read-unsafe`, `alias-unsafe`, both boundary-clean now), so
  `scry/bench/baseline.json` is updated to **20 TP / 0 FN / 1 FP / 2 unknown**.
  That is a baseline refresh, not an analysis change.
- The real-corpus harness itself: 24/24 files, 0 timeouts, 0 crashes, 2 findings; the
  checked-in JSON above is its output for `SCRY_LIMIT=300`.

## Limits of this report

- 24 files, 2 findings; the precision number (0/2) has no statistical power. It is a
  qualitative spot-check, not an alert-level benchmark.
- Wall time is shared-machine time, not `perf-run`; reruns vary by tens of percent.
- `--allow-errors` is used for the counts; the default refusal is reported separately.
- The two generated files are external, not checked in; a bare checkout records them
  as missing.
- No semantic analysis code was changed. The only dependency merged is
  `agent/scry-bench` (`08d292e4`) for the `bench` command; `agent/stack-lang`
  `92710af5` was not merged because `bb1a6294` already contains the scry-relevant
  stack and this work does not depend on the later master merge.
