# Scry parse/lower fuzz findings

This is a bounded bug search over the **Wiz side** of Scry: the native column store, `Scry.CstStore`, `Scry.lowerTU` (C -> Wil) and the taint pipeline reached by `scry taint`. It complements `scry/fuzz/run.py`, which fuzzes the vendored tree-sitter shim with libFuzzer. A run that finds nothing is not evidence of safety. The campaign below was measured on 2026-11-17 at commit `c249a8ad` with `scry 0.1.0-dev (S1)`; the regression replay is dated separately.

## Reproduce

```sh
python3 scry/scripts/fuzz-lower.py --iterations 400 --seed 20261117 --timeout 5 --memory-mb 256
python3 scry/scripts/fuzz-lower.py --regressions-only
```

* scry: `scry 0.1.0-dev (S1)`
* seed corpus: 122 C files at the time, from `bench/corpus`, `tests/fixtures`, `corpus` and `fuzz/lower/seeds` (`find scry/bench/corpus scry/tests/fixtures scry/corpus scry/fuzz/lower/seeds -name '*.c' | wc -l` reports 147 on 2026-11-18; the corpus grew after the run)
* executions: 400; wall time: 1245.9 s
* per-run limits: 5 s, 256 MiB **resident** memory (the kernel-killed process is reported as `oom`), core dumps off, process group killed on timeout

* categories: crash 0, hang 38, oom 19, wrong 0, refused 5, error 0, stalled 0, clean 338 (at the recorded run; see the replay status below)

## Findings

| id | category | mode | input | cpu/wall | peak RSS | signal | class | minimised | repro |
|---|---|---|---|---|---|---|---|---|---|
| F001 | oom | taint-open | 1.0 MiB | 299/304 ms | 258 MiB | SIGKILL | pathological:comment:1048576 | 1.0 MiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-pathological-comment-1048576.c` |
| F002 | hang | taint-open | 24.0 KiB | 4948/5011 ms | 23 MiB | SIGKILL | deep:calls:8192 | 327 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-external-deep-calls-8192.c` |
| F003 | hang | taint | 1.0 KiB | 3967/4010 ms | 7 MiB | builtin:--timeout | deep:binary:512 | 116 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-deep-binary-512.c` |
| F004 | hang | taint | 204.0 KiB | 3957/4018 ms | 79 MiB | builtin:--timeout | pathological:params:262144 | 63.3 KiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-pathological-params-262144.c` |
| F005 | oom | taint | 1.0 MiB | 344/365 ms | 259 MiB | SIGKILL | pathological:newlines:1048576 | 1.0 MiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-pathological-newlines-1048576.c` |
| F006 | hang | taint | 2.5 KiB | 3962/4009 ms | 8 MiB | builtin:--timeout | deep:field:512 | 516 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-deep-field-512.c` |
| F007 | hang | taint | 4.0 KiB | 3971/4005 ms | 9 MiB | builtin:--timeout | deep:comma:2048 | 212 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-deep-comma-2048.c` |
| F008 | hang | taint | 1.5 KiB | 3970/4008 ms | 7 MiB | builtin:--timeout | deep:subscript:512 | 172 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-deep-subscript-512.c` |
| F009 | oom | taint | 896.0 KiB | 831/842 ms | 258 MiB | SIGKILL | deep:switch:131072 | 896.0 KiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-deep-switch-131072.c` |
| F010 | hang | taint | 4.0 KiB | 3973/4011 ms | 10 MiB | builtin:--timeout | pathological:statements:1024 | 393 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-pathological-statements-1024.c` |
| F011 | hang | taint | 14.0 KiB | 3964/4013 ms | 16 MiB | builtin:--timeout | deep:switch:2048 | 234 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-deep-switch-2048.c` |
| F012 | oom | facts | 1.9 MiB | 507/530 ms | 258 MiB | SIGKILL | json:huge-array:2048 | 1.7 MiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-json-huge-array-2048.c` |
| F013 | oom | taint | 3.8 MiB | 181/199 ms | 258 MiB | SIGKILL | memory:initlist:8388608 | 3.8 MiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-memory-initlist-8388608.c` |
| F014 | oom | taint | 781.3 KiB | 1042/1069 ms | 262 MiB | SIGKILL | pathological:statements:1048576 | 781.3 KiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-pathological-statements-1048576.c` |
| F015 | oom | taint | 2.0 MiB | 221/226 ms | 260 MiB | SIGKILL | memory:comment:2097152 | 2.0 MiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-memory-comment-2097152.c` |
| F016 | hang | taint | 10.0 KiB | 3951/4015 ms | 18 MiB | builtin:--timeout | deep:if:2048 | 112 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-deep-if-2048.c` |
| F017 | oom | taint | 1.0 MiB | 863/878 ms | 257 MiB | SIGKILL | deep:while:131072 | 1.0 MiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-deep-while-131072.c` |
| F018 | hang | taint-open | 204.0 KiB | 4949/5014 ms | 79 MiB | SIGKILL | pathological:params:65536 | 75.5 KiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-external-pathological-params-65536.c` |
| F019 | oom | taint | 2.0 MiB | 312/320 ms | 261 MiB | SIGKILL | memory:string:2097152 | 898.8 KiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-memory-string-2097152.c` |
| F020 | oom | taint | 2.0 MiB | 323/332 ms | 259 MiB | SIGKILL | memory:identifier:2097152 | 2.0 MiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-memory-identifier-2097152.c` |
| F021 | oom | taint | 1.0 MiB | 356/379 ms | 261 MiB | SIGKILL | pathological:string:1048576 | 898.8 KiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-pathological-string-1048576.c` |
| F022 | oom | taint | 1.0 MiB | 678/688 ms | 269 MiB | SIGKILL | pathological:decls:262144 | 1.0 MiB | `scry/tests/fixtures/fuzz-regression/fuzz-regression-oom-rss-pathological-decls-262144.c` |
| F023 | hang | taint | 417 B | 3973/4013 ms | 7 MiB | builtin:--timeout | deep:calls:128 | 318 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-deep-calls-128.c` |
| F024 | hang | taint | 1.0 KiB | 3961/4008 ms | 6 MiB | builtin:--timeout | deep:while:128 | 158 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-builtin-deep-while-128.c` |
| F025 | hang | taint-open | 160.0 KiB | 4938/5016 ms | 84 MiB | SIGKILL | deep:field:32768 | 551 B | `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-external-deep-field-32768.c` |

### Signatures and notes

* **F001** `oom:rss` (sha256 `db8baff55430d59e`, cpu 299 ms, wall 304 ms, peak RSS 258 MiB) — artifact `F001-oom-rss-pathological-comment-1048576.c`; minimised form did not reproduce; kept the original
  * minimise: 20 evaluation(s), 1.0 MiB -> 1.0 MiB (unchanged)
* **F002** `hang:external` (sha256 `7f07078f979b3df2`, cpu 4948 ms, wall 5011 ms, peak RSS 23 MiB) — artifact `F002-hang-external-deep-calls-8192.c`
  * minimise: 13 evaluation(s), 24.0 KiB -> 327 B (changed)
* **F003** `hang:builtin` (sha256 `ae5a12d9c002f663`, cpu 3967 ms, wall 4010 ms, peak RSS 7 MiB) — artifact `F003-hang-builtin-deep-binary-512.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 9 evaluation(s), 1.0 KiB -> 116 B (changed)
* **F004** `hang:builtin` (sha256 `b77d0e476421bc94`, cpu 3957 ms, wall 4018 ms, peak RSS 79 MiB) — artifact `F004-hang-builtin-pathological-params-262144.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 18 evaluation(s), 204.0 KiB -> 63.3 KiB (changed)
* **F005** `oom:rss` (sha256 `2827cdc2413c1e8d`, cpu 344 ms, wall 365 ms, peak RSS 259 MiB) — artifact `F005-oom-rss-pathological-newlines-1048576.c`; minimised form did not reproduce; kept the original
  * minimise: 20 evaluation(s), 1.0 MiB -> 1.0 MiB (unchanged)
* **F006** `hang:builtin` (sha256 `d11812e0731d48f1`, cpu 3962 ms, wall 4009 ms, peak RSS 8 MiB) — artifact `F006-hang-builtin-deep-field-512.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 9 evaluation(s), 2.5 KiB -> 516 B (changed)
* **F007** `hang:builtin` (sha256 `2c17e394f6c1ee9c`, cpu 3971 ms, wall 4005 ms, peak RSS 9 MiB) — artifact `F007-hang-builtin-deep-comma-2048.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 11 evaluation(s), 4.0 KiB -> 212 B (changed)
* **F008** `hang:builtin` (sha256 `131c13ce34ba0e7f`, cpu 3970 ms, wall 4008 ms, peak RSS 7 MiB) — artifact `F008-hang-builtin-deep-subscript-512.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 9 evaluation(s), 1.5 KiB -> 172 B (changed)
* **F009** `oom:rss` (sha256 `a479ba35669029b0`, cpu 831 ms, wall 842 ms, peak RSS 258 MiB) — artifact `F009-oom-rss-deep-switch-131072.c`; minimised form did not reproduce; kept the original
  * minimise: 17 evaluation(s), 896.0 KiB -> 896.0 KiB (unchanged)
* **F010** `hang:builtin` (sha256 `89bd29d81a3dd87d`, cpu 3973 ms, wall 4011 ms, peak RSS 10 MiB) — artifact `F010-hang-builtin-pathological-statements-1024.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 10 evaluation(s), 4.0 KiB -> 393 B (changed)
* **F011** `hang:builtin` (sha256 `92e85be37e4f395d`, cpu 3964 ms, wall 4013 ms, peak RSS 16 MiB) — artifact `F011-hang-builtin-deep-switch-2048.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 11 evaluation(s), 14.0 KiB -> 234 B (changed)
* **F012** `oom:rss` (sha256 `c70dcac3af270026`, cpu 507 ms, wall 530 ms, peak RSS 258 MiB) — artifact `F012-oom-rss-json-huge-array-2048.c`
  * minimise: 80 evaluation(s), 1.9 MiB -> 1.7 MiB (changed)
* **F013** `oom:rss` (sha256 `a2d04bdb9afa4d8e`, cpu 181 ms, wall 199 ms, peak RSS 258 MiB) — artifact `F013-oom-rss-memory-initlist-8388608.c`; minimised form did not reproduce; kept the original
  * minimise: 80 evaluation(s), 3.8 MiB -> 3.8 MiB (unchanged)
* **F014** `oom:rss` (sha256 `707ee4d06e13bd88`, cpu 1042 ms, wall 1069 ms, peak RSS 262 MiB) — artifact `F014-oom-rss-pathological-statements-1048576.c`; minimised form did not reproduce; kept the original
  * minimise: 20 evaluation(s), 781.3 KiB -> 781.3 KiB (unchanged)
* **F015** `oom:rss` (sha256 `05594bca524bf017`, cpu 221 ms, wall 226 ms, peak RSS 260 MiB) — artifact `F015-oom-rss-memory-comment-2097152.c`; minimised form did not reproduce; kept the original
  * minimise: 80 evaluation(s), 2.0 MiB -> 2.0 MiB (unchanged)
* **F016** `hang:builtin` (sha256 `913cdbefb9f8873e`, cpu 3951 ms, wall 4015 ms, peak RSS 18 MiB) — artifact `F016-hang-builtin-deep-if-2048.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 11 evaluation(s), 10.0 KiB -> 112 B (changed)
* **F017** `oom:rss` (sha256 `7d35372ee8083735`, cpu 863 ms, wall 878 ms, peak RSS 257 MiB) — artifact `F017-oom-rss-deep-while-131072.c`; minimised form did not reproduce; kept the original
  * minimise: 17 evaluation(s), 1.0 MiB -> 1.0 MiB (unchanged)
* **F018** `hang:external` (sha256 `b77d0e476421bc94`, cpu 4949 ms, wall 5014 ms, peak RSS 79 MiB) — artifact `F018-hang-external-pathological-params-65536.c`
  * minimise: 16 evaluation(s), 204.0 KiB -> 75.5 KiB (changed)
* **F019** `oom:rss` (sha256 `7e51e1ea960731f7`, cpu 312 ms, wall 320 ms, peak RSS 261 MiB) — artifact `F019-oom-rss-memory-string-2097152.c`
  * minimise: 80 evaluation(s), 2.0 MiB -> 898.8 KiB (changed)
* **F020** `oom:rss` (sha256 `13a67df23e74f786`, cpu 323 ms, wall 332 ms, peak RSS 259 MiB) — artifact `F020-oom-rss-memory-identifier-2097152.c`; minimised form did not reproduce; kept the original
  * minimise: 80 evaluation(s), 2.0 MiB -> 2.0 MiB (unchanged)
* **F021** `oom:rss` (sha256 `430af15ae5172e09`, cpu 356 ms, wall 379 ms, peak RSS 261 MiB) — artifact `F021-oom-rss-pathological-string-1048576.c`
  * minimise: 20 evaluation(s), 1.0 MiB -> 898.8 KiB (changed)
* **F022** `oom:rss` (sha256 `3fe5474968df1b40`, cpu 678 ms, wall 688 ms, peak RSS 269 MiB) — artifact `F022-oom-rss-pathological-decls-262144.c`; minimised form did not reproduce; kept the original
  * minimise: 18 evaluation(s), 1.0 MiB -> 1.0 MiB (unchanged)
* **F023** `hang:builtin` (sha256 `5929bce104e49d86`, cpu 3973 ms, wall 4013 ms, peak RSS 7 MiB) — artifact `F023-hang-builtin-deep-calls-128.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 7 evaluation(s), 417 B -> 318 B (changed)
* **F024** `hang:builtin` (sha256 `d307fb1a003e78f6`, cpu 3961 ms, wall 4008 ms, peak RSS 6 MiB) — artifact `F024-hang-builtin-deep-while-128.c`
  * stderr: `scry: timeout after 4 s (--timeout); no analysis result was produced | scry: raise --timeout, or bound the work with --max-nodes/--max-rounds`
  * minimise: 7 evaluation(s), 1.0 KiB -> 158 B (changed)
* **F025** `hang:external` (sha256 `3bb8dd4b9acf2e94`, cpu 4938 ms, wall 5016 ms, peak RSS 84 MiB) — artifact `F025-hang-external-deep-field-32768.c`
  * minimise: 15 evaluation(s), 160.0 KiB -> 551 B (changed)

## Regression fixtures

`scry/tests/fixtures/fuzz-regression/` holds one minimised fixture per row.
`manifest.json` records its mode, expected category, memory cap and timeout, and
`--regressions-only` replays them with those limits (no RNG is involved):

* the hang fixtures replay at a 3 s budget and a 256 MiB RSS cap;
* the OOM fixtures replay at the campaign's 256 MiB RSS cap and 5 s timeout.

Replayed on 2026-11-18 with `python3 scry/scripts/fuzz-lower.py --regressions-only`
and a `scry` built from the tree at master `4ad29792`: 25/25 `ok`. The 13 hang
fixtures now print `fixed` (they terminate under their 3 s budget), and the 12 OOM
fixtures still print `ok` at the 256 MiB cap. A fixture that starts
terminating prints `fixed` (still exit 0); if the non-terminating boundary moves under
load (`oom` vs `hang`) the replay prints `ok (hang)`/`ok (oom)`; any other change is
`MISMATCH` and exits 1.

## Method

The generator mixes (a) byte/token mutations of the checked-in C corpus, (b) random bytes over a C-ish alphabet, (c) deeply nested expressions, declarations, initialisers, blocks and control flow (128 to 131 072 levels), (d) unterminated strings, comments, preprocessor conditionals and brackets, (e) pathological sizes (million-digit literals, 200 000-statement functions, 20 000 parameters, megabyte identifiers and comments), (f) small random but syntactically valid programs and (g) 2-8 MiB single-node inputs (one string literal, comment or wide initialiser) for the memory ratio. A small share also feeds deeply nested JSON fact stores to `scry facts`/`parse --stats` (the same loader process). Each input is run through one of `scry taint --allow-errors --json`, `scry parse --stats`, `scry facts` or `scry fuzz-span --json`; every tenth lowering run omits `--timeout` so the external sandbox is the only bound. A sample of clean runs is cross-checked between `parse --stats` and `fuzz-span --json` (same shim, two store paths), and every exit-0 JSON output is checked for malformed or negative spans. Findings are delta-minimised under the same sandbox after the campaign and deduplicated by category, fault signal and generator variant.

Hang classification uses **CPU time**, not wall time: the host is shared and a 300 ms launch can take 30 s to be scheduled. A run killed by the external timeout with less than a quarter of its interval on the CPU is counted as `stalled` (not a finding). The memory cap is on **resident** memory (VmRSS, sampled every 10 ms). RLIMIT_AS is not used: the runtime reserves a much larger virtual arena than it touches (VmPeak 1.5 GiB for a 4 MiB parse, VmRSS 459 MiB), so an address-space cap aborts an ordinary input with a SIGSEGV that looks exactly like a parser crash. A fatal signal at or above 90% of the RSS cap is reported as OOM, and a crash with the cap still in force is re-run once with the cap disabled; only a crash that reproduces without the cap is reported as `crash`.

## Limits

* One machine, one binary, one RNG seed; a different build can behave differently. The counts are observations, not a coverage claim.
* The RSS cap is a policy limit, not a proof: an input that exceeds it is reported as OOM even if the analyser would eventually succeed with a larger heap. Sampling every 10 ms can miss a short-lived allocation; a process that dies just below the cap is still treated as an OOM.
* Minimisation is bounded (a shared evaluation budget); a minimised input can still contain irrelevant bytes and can exercise a different path from the original.
* `wrong-but-terminating` checks are invariants on the output (valid JSON, spans ordered, parse/fuzz-span counts agree), not a semantic correctness oracle for taint results.

