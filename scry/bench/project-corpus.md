# scry multi-file project corpus (2026-11-15)

Status: measurement report for the multi-file driver. Branch `agent/scry-multifile`,
worktree `/workspace/wt/scry-multifile`; raw machine record:
[`project-corpus.json`](project-corpus.json); ground truth for the synthetic project:
[`project-corpus.truth.json`](project-corpus.truth.json). No analysis code was changed by
the harness itself.

Command (run with the worktree's own `grail`/`scry`; `cc` is the gcc wrapper):

```sh
cd scry
../.lake/build/bin/grail build
scripts/project-corpus.sh
SCRY_LIMIT=900 scripts/project-corpus.sh   # override the global limit
```

The harness generates a `compile_commands.json` for each group (absolute `directory`,
file-relative `file`, group include flags), then runs:

```sh
scry project DIR --compdb FILE --allow-errors --skip-broken --taint \
  --json --sarif OUT.sarif --cache=OUT/cache --cache-stats
```

`--allow-errors` keeps recovery trees; `--skip-broken` records a TU whose `cc -E`/parse
fails instead of aborting the project. Wall time is informational on this shared
machine and is **not** a `perf-run` measurement.

## Counts

| group | status | units | functions | findings | checked | boundary | memory | cache hit/miss/write | ms |
|---|---|---:|---:|---:|---:|---:|---:|---|---:|
| synthetic | ok | 3 | 7 | 2 | 2 | 5 | 0 | 0/3/3 | 73 |
| wiz-lang | ok | 5 | 215 | 1 | 1 | 1 407 | 111 | 0/5/5 | 171 803 |
| wiz-rv | ok | 5 | 46 | 1 | 1 | 486 | 7 | 0/5/5 | 484 113 |
| tree-sitter (8 TUs) | timeout | — | — | — | — | — | — | — | 900 139 |
| tree-sitter (3 TUs, below) | ok | 3 | 187 | 0 | 0 | 1 697 | 50 | 0/3/3 | 172 197 |
| generated `old-wizard.c` | timeout | — | — | — | — | — | — | — | 120 048 |
| generated `droste.c` | timeout | — | — | — | — | — | — | — | 120 146 |
| synthetic (warm cache) | ok | 3 | 7 | 2 | 2 | 5 | 0 | 3/0/0 | 54–59 |

Skipped TUs (`--skip-broken`): `wiz-lang` skipped `web/js.c` (missing `emscripten.h`).
`wiz-rv` skipped `sw/doomgeneric_wizrv.c` (missing `doomgeneric.h`),
`sw/sound_wizrv.c` and `sw/tone/tone.c`; the remaining 5 units include a duplicate
`main` (3 definitions; the first is analysed and the rest are reported).

The full tree-sitter group (8 `lib/src` files, including `parser.c` and `query.c`) does
not finish in 900 s in project mode. The 3-file subset (`alloc.c`, `tree.c`,
`tree_cursor.c`) is the successful tree-sitter data point above.

## Precision / recall

Synthetic `corpus/project/taint` (ground truth in `project-corpus.truth.json`):

| TP | FN | FP | FP on a safe file | precision | recall | expected | actual |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 0 | 0 | 0 | 100.00% | 100.00% | 2 | 2 |

The two findings are both `command-injection`, both certificate-checked: one in `io.c`
(`run_cmd`'s `system`, with the path starting in `app.c`'s `main`) and one in `util.c`.
The sanitised `app.c` call is a true negative, and the two same-named `static` helpers
(`app.c`/`io.c`) stay distinct. This is a small regression fixture, not a statistical
estimate.

Real groups have no independent labels, so precision/recall are not measured. The two
reported findings are the same two manual false positives as the single-file real-corpus
report:

* `infoview/term.c:100` `strcpy-overflow` in `static:3:iv_addr` — guarded by the preceding
  `strlen`/`sizeof` check (FP).
* `sw/ctest/ctest.c:20` `strcpy-overflow` in `main` — a 7-byte literal into a 64-byte
  static array (FP).

Observed precision is therefore 0/2 on real code; recall is unknown (no ground truth, and
the tree-sitter sources have no `system`/`gets`/`strcpy` sink). The boundary/memory
warning volume is the same class of noise as `bench/real-corpus.md`: 1 407 + 486 boundary
warnings and 118 memory warnings for 4 findings.

## Cache and performance

The cache is per TU and stores the `scry-cst 1` store. Cold synthetic: `miss=3,
write=3`; the immediate warm run: `hit=3, miss=0, write=0`, 54–59 ms versus 73 ms cold.
Validation is against the actual preprocessed text, so a changed header/macro is a miss
(and a corrupt entry is recomputed and rewritten); `tests/project.wiz` covers cold, warm,
corrupt and header-edit cases.

The cache avoids parsing, not the whole-project points-to/summary/taint pass. On these
groups analysis dominates: the 3-file tree-sitter subset is ~172 s for 0 findings, and
`wiz-rv` is ~484 s for 5 units. That is the honest cost of running the current
flow-insensitive/context-insensitive engine over a combined program; it is not a
PR-speed result.

## Limits

- The real groups have no independent ground truth; their findings are a manual
  spot-check, not a precision/recall claim.
- The synthetic project is tiny; its 2/0/0 result is a regression check, not a
  statistical estimate.
- Timings are wall clock on a shared machine and are not a `perf-run` measurement.
- `tree-sitter` full and both generated files time out; they are recorded as `timeout`,
  not as `0 findings`.
