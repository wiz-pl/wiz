# The findings-store benchmark

`run.sh` runs the incumbent (JSON through `lib/Json` + whole-file `FS.writeFile`/
`FS.readFile`) and Quire (the page-backed store in `../Quire.wiz`) through the same
operations, for the same N, on one machine, in one `heavy` job:

```
heavy sh drafts/storage-engine/bench/run.sh
```

Each measurement is one process invocation, so peak RSS is that process's.

| operation | JSON | Quire |
|---|---|---|
| `build` | build N `Json` objects, `Json.render`, one `FS.writeFile` | N commits (one record each) |
| `batch` | (the same file) | one commit with N records |
| `reopen` | `FS.readFile` + `Json.parse` + count | `openQ` + `getQ` + one node read |
| `reopen-fast` | — | the same, without the two root-page checksums |
| `query` | parse + `List.filter` on `state` | `indexCursor` + `filterKey` (index-only) |
| `update` | parse, map one record's state, render, rewrite | `getQ`, lens `set`, `putQ` |
| `compact` | — | rewrite the live image and rename (Quire only) |

A finding is a 32-byte record: rule id in `kind`, state id in `label`, and line, path id,
function id and severity packed into `count`. The strings are interned (the design's
`Intern` precedent), so both sides do the same *numeric* query; JSON carries the strings
through the parse and render.

## What is measured, and how

* **wall time** — the harness brackets the process with `date +%s%N` (including start-up).
  The program also prints `Clock.monotonic` around the operation (`inner_ns` in the raw
  TSV). No `/usr/bin/time` on the nodes.
* **peak RSS** — `VmHWM` from `/proc/self/status`, read by the program at the end.
* **file size** — `stat -c %s` after the operation.

The output is `results.tsv` (one row per side/op/N) and two tables (fixed-width and
markdown). The N list defaults to `1000 10000 100000` (`BENCH_NS` overrides).

The programs are built once, before the measurements (`wiz build`), so the timings are
the compiled path, not `#eval`.
