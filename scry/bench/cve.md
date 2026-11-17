# Scry on real historical CVEs (2026-11-15)

Status: measurement report, **no analysis or rule changes**. Branch
`agent/scry-cve`, based on `agent/scry-scale` `f9294ec4` with
`agent/scry-real-corpus` `acd4b34c` merged (the 51-case `scry bench` harness and
the real-C source runner are present; this corpus does not use them).

This is an **opt-in benchmark**, not part of `scry bench`, `grail test`, the
default fast gate, or CI. It runs each case in its own process because one case
takes about a minute:

```sh
cd scry
../.lake/build/bin/grail build scry
scripts/cve-bench.sh                       # all 12 cases
scripts/cve-bench.sh --case cve-2020-1752  # one case
scripts/cve-bench.sh --timeout 180         # scry --timeout per case
```

Every case is compiled first with the plain compiler (`cc -std=c99 -Wall -c`)
and then analysed with `scry taint FILE --json --allow-errors --timeout 120
--max-nodes 200000`. The driver records per-case wall time, peak RSS
(`wait4`/`ru_maxrss`), nodes, boundary/memory counts, the matched expected
findings, and the extras. Results land in `scry/build/cve/` (`summary.json`,
`summary.md`, `results.tsv`, one `*.scry.json`/`*.measure.json` per case); this
file is the checked-in summary.

## Corpus

Twelve CVEs, vulnerable versions only, one reduced reproducer each. The full
upstream revision is linked in `case.json` and `README.md` in each
`cases/cve-<id>/` directory. A case is **in scope** when the default pack (or
the points-to memory diagnostics) has a rule family for its CWE; otherwise it
is explicitly **out of scope** with the reason below.

| CVE | CWE | product | in scope | expected result |
|---|---|---|---|---|
| [CVE-2000-0573](cases/cve-2000-0573/) | CWE-134 | wu-ftpd 2.6.0 | yes | `format-string` at the `vsnprintf` format argument (line 26) |
| [CVE-2012-0809](cases/cve-2012-0809/) | CWE-134 | sudo 1.8.3 | yes | `format-string` at the `vfprintf` format argument (line 38) |
| [CVE-2016-3714](cases/cve-2016-3714/) | CWE-78 | ImageMagick 7.0.1-0 | yes | `command-injection` at `system(sanitize_command)` (line 45) |
| [CVE-2024-23749](cases/cve-2024-23749/) | CWE-78 | KiTTY 0.76.1.13 | yes | `command-injection` at `system(buffer)` (line 53) |
| [CVE-2020-1752](cases/cve-2020-1752/) | CWE-416 | glibc 2.30 | yes | `scry/memory/use-after-free` at the last `mempcpy(..., end_name, ...)` (line 49) |
| [CVE-2019-7317](cases/cve-2019-7317/) | CWE-416 | libpng 1.6.36 | yes | `scry/memory/use-after-free` at `image->opaque->error_buf` after the callback (line 53) |
| [CVE-2021-41773](cases/cve-2021-41773/) | CWE-22 | Apache httpd 2.4.49 | no | out of scope: no path-traversal rule or file-path model |
| [CVE-2021-3449](cases/cve-2021-3449/) | CWE-476 | OpenSSL 1.1.1j | no | out of scope: no null-pointer / stale-length analysis |
| [CVE-2017-7529](cases/cve-2017-7529/) | CWE-190 | nginx 1.13.2 | no | out of scope: no integer-overflow, value-range or bounds analysis |
| [CVE-2021-23017](cases/cve-2021-23017/) | CWE-787 | nginx 1.20.0 | no | out of scope: no buffer-extent / off-by-one analysis |
| [CVE-2014-0160](cases/cve-2014-0160/) | CWE-125 | OpenSSL 1.0.1f | no | out of scope: no buffer-extent / length-validation analysis |
| [CVE-2018-1000001](cases/cve-2018-1000001/) | CWE-787 | glibc 2.26 | no | out of scope: no pointer/buffer bounds analysis |

Files are small (262-1 147 CST nodes), self-contained, and produce a normal
`cc -c` object. The reductions replace network/file plumbing with `read(2)`
and keep the vulnerable function's data flow; they are not full upstream
programs. Each case records its upstream URL and licence in `case.json`; the
licences are wu-ftpd BSD-style, ISC-style, ImageMagick, MIT, LGPL-2.1+,
libpng, Apache-2.0, BSD-2-Clause, OpenSSL/SSLeay and BSD-2-Clause.

## Measured results

Run under `heavy --mem 3G`, `--timeout 120 --max-nodes 200000`, on the shared
machine (informational; **not** a `perf-run` measurement). All 12 cases
finished; no timeout, no truncation, no parse failure, no more than 7.9 MiB
peak RSS.

| CVE | CWE | scope | outcome | expected | matched | extra | ms | peak RSS MiB | nodes |
|---|---|---|---|---:|---:|---:|---:|---:|---:|
| CVE-2000-0573 | CWE-134 | in | **miss** | 1 | 0 | 0 | 21 | 6.9 | 298 |
| CVE-2012-0809 | CWE-134 | in | **miss** | 1 | 0 | 2 | 36 | 6.9 | 262 |
| CVE-2016-3714 | CWE-78 | in | **miss** | 1 | 0 | 0 | 16 | 6.9 | 341 |
| CVE-2024-23749 | CWE-78 | in | **miss** | 1 | 0 | 11 | 245 | 6.9 | 624 |
| CVE-2020-1752 | CWE-416 | in | **miss** | 1 | 0 | 3 | 418 | 6.9 | 378 |
| CVE-2019-7317 | CWE-416 | in | **miss** | 1 | 0 | 1 | 18 | 6.6 | 394 |
| CVE-2021-41773 | CWE-22 | out | out of scope | 0 | 0 | 0 | 54 281 | 7.9 | 1 147 |
| CVE-2021-3449 | CWE-476 | out | out of scope | 0 | 0 | 3 | 183 | 6.9 | 521 |
| CVE-2017-7529 | CWE-190 | out | out of scope | 0 | 0 | 0 | 47 | 6.9 | 1 047 |
| CVE-2021-23017 | CWE-787 | out | out of scope | 0 | 0 | 5 | 378 | 6.9 | 783 |
| CVE-2014-0160 | CWE-125 | out | out of scope | 0 | 0 | 4 | 211 | 6.9 | 674 |
| CVE-2018-1000001 | CWE-787 | out | out of scope | 0 | 0 | 4 | 336 | 6.9 | 557 |

Total analysis wall time **56 190 ms**; the Apache case is 54.3 s of it
(see the operational gap below). Peak RSS **7.9 MiB**. The timing is end-to-end `scry` process
start + parse + lower + points-to + rules + certify; the `scry --version`
floor is about 2 ms / 6 MiB.

## Precision and recall

| metric | value |
|---|---:|
| in-scope cases | 6 |
| detected (TP) | **0** |
| missed (FN) | **6** |
| in-scope recall | **0.0% (0/6)** |
| out-of-scope cases | 6 |
| overall CVE detection | **0.0% (0/12)** |
| expected findings | 6 |
| matched expected findings | 0 |
| extra alerts (rule findings + memory diagnostics) | 33 |
| finding-level precision (CVE finding / all alerts) | **0.0% (0/33)** |

The 33 "extras" are not 33 false alarms of the same kind:

* **12 are `strcpy-overflow` findings** (11 in KiTTY, 1 in glibc realpath) on
  real unbounded `strcpy`/`strcat` calls. They are true warnings for that
  rule, but none is the CVE's root cause.
* **21 are memory diagnostics**: 20 `scry/memory/unknown-memory` ("the pointer
  target is unknown") and 1 `scry/memory/unknown-indirect` (the libpng
  callback). They are explicit coverage boundaries, not claims of a bug.

If only rule findings are counted, precision is still **0/12 (0%)**; if
memory diagnostics are treated as "unknown" rather than alerts, they should
not be scored as false positives but they also cannot be scored as detections.
Either way, **no in-scope CVE was detected**. This is the honest result: the
51-case synthetic corpus in `wiz-notes/scry-bench.md` reports 100% in-scope
TPR, and that number does not transfer to these real vulnerable versions.

## Why each in-scope case missed

| CVE | actual | reason |
|---|---|---|
| CVE-2000-0573 | nothing | the sink is `vsnprintf`; the pack only has `printf`/`fprintf`. `va_list` and the conditional size expression also lower as boundaries. |
| CVE-2012-0809 | 2 unknown-memory | the source is `argv[0]` (not `getenv`/`recv`/`read`) and the sink is `vfprintf` (not `printf`/`fprintf`); `easprintf` is an unknown external. |
| CVE-2016-3714 | nothing | the command is built by `snprintf` (arity mismatch, string literal havoc) and then copied by `SanitizeDelegateCommand`; taint does not reach `system`. |
| CVE-2024-23749 | 11 `strcpy-overflow` | the pscp command is built with `strcat`/`sprintf`; the forbidden-call rule fires on every call, but taint is not propagated through the string building, so `system(buffer)` is not tainted. |
| CVE-2020-1752 | 3 unknown-memory | `end_name = strchr(dirname, '/')` is an unknown external result, so the alias into `dirname` is invisible; after `free(dirname)` the `mempcpy(..., end_name, ...)` use is not connected to the freed object. |
| CVE-2019-7317 | 1 unknown-indirect | the free happens inside a callback copied through a stack control block; there is no stack-lifetime or indirect-call summary, so the stale `image->opaque` is not recognised as a freed heap object. |

## Top three analysis gaps

1. **Taint is register/value-level, not string-content-level.** Every real
   command-injection and format-string case builds the sink argument with a
   string function: `strcat`/`sprintf` (KiTTY), `snprintf` + a sanitiser copy
   (ImageMagick), `vsnprintf` (wu-ftpd), `easprintf` + `vfprintf` (sudo).
   Scry treats string literals and unknown externals as havocs, and has no
   summary for `strcat`, `sprintf`/`snprintf`, `strdup`/`strcpy` return values
   or `vsnprintf`/`vfprintf`. Consequence: **0/4 detections in the two in-scope
   CWE families built this way**, and the only alerts on those files are the
   blanket `strcpy-overflow` warnings. A real fix needs a string/format model
   (destination-taint for copy/format calls, source-taint for the formatted
   result) or an interprocedural string summary; a rule-pack tweak is not
   enough.

2. **Source and sink coverage is a literal, tiny whitelist.** The pack knows
   `getenv`, `recv result` and `read arg 1` as sources and `system`,
   `popen`, `printf arg 0`, `fprintf arg 1`, `gets`, `strcpy`/`strcat` as
   sinks. Real CVEs use `argv[0]` (sudo), network buffers through
   `vsnprintf` (wu-ftpd), `vfprintf`, `execl`/`execv` (OpenSMTPD-style
   command injection), `snprintf`, path APIs, and size-checked copies. In this
   corpus that whitelist explains three misses directly, and the 6
   out-of-scope cases (CWE-22/476/190/787/125) have no rule family at all.
   `argv`/environment arrays and format-family aliases (`v*printf`, `snprintf`)
   are the cheapest gaps to close; traversal and bounds need new analyses.

3. **The memory model cannot follow aliasing through library calls, custom
   allocators, or lifetimes.** The two in-scope CWE-416 cases both fail for
   this reason: `strchr` does not return a pointer into its first argument,
   and libpng frees through a callback/stack copy (`png_safe_execute`) rather
   than a direct `free`. The model has no `realloc`, no stack-lifetime
   tracking, no interprocedural heap summary, and only a one-level `anyOff`;
   CVE-2020-1752 and CVE-2019-7317 therefore produce only
   `unknown-memory`/`unknown-indirect`. A useful next step is a small set of
   aliasing models (`strchr`, `strdup`, `memcpy`/`mempcpy` return value,
   `realloc`) plus a "callback may free through its argument" summary, before
   attempting general shape analysis.

### Operational gap (not one of the top three)

`ap_normalize_path` is 1 147 CST nodes and takes **54.3 s** for the whole
`scry taint` run; the next slowest case is 418 ms (glibc glob, 378 nodes)
and the other ten are 16-378 ms. The nested byte loop and pointer arithmetic
are bounded by `--timeout 120` here, but this is not usable in an interactive
or CI setting. The large-file fixes on `agent/scry-scale` bound the work but
do not make a small, loop-heavy function cheap. This deserves a profile of the
rule evaluation/fixpoint on `ap_normalize_path`; it was left alone because
this task measures, and does not tune, the analysis.

## Follow-up issues (do not tune the corpus)

1. Add destination-taint models for `strcat`/`strcpy`/`sprintf`/`snprintf`
   and source-taint for the formatted result; add `vsnprintf`/`vfprintf` to
   the format-string rule family (and a `va_list` lowering path).
2. Add `argv`/`environ` as sources, and `execl*`/`execv*` as command sinks,
   with an explicit opt-in so the default pack does not change silently.
3. Model `strchr`/`strrchr`/`memchr` as returning a pointer into their first
   argument, `strdup` as a fresh allocation, `mempcpy`/`memcpy` return as the
   destination, and `realloc` as free+alloc; add a conservative callback
   summary for "may free through its argument".
4. Consider a path-traversal rule and a bounds/overflow analysis only as new
   analyses, not as taint rules; the 6 out-of-scope cases are a separate
   roadmap, not a rule-pack tweak.

## Reproduce

```sh
cd scry
cp ../grail.local.wiz .                      # once, if absent
../.lake/build/bin/grail build scry
scripts/cve-bench.sh --timeout 120 --max-nodes 200000
cat build/cve/summary.md
```

`scripts/cve-bench.sh --case <id>` runs one case; `--no-run` only summarises
existing `build/cve` output. `CC=...` overrides the compiler; the driver
falls back to a host-compatible Nix gcc wrapper when `cc` is not on `PATH`.

## Limitations

* The reproducers are reduced, not the full upstream programs. They keep the
  vulnerable function and its data flow, and replace the network/file plumbing
  with `read(2)`. A full build of wu-ftpd, ImageMagick, Apache or nginx is out
  of scope for this corpus and would add thousands of nodes and unrelated
  rules.
* One case per CVE, vulnerable version only. There is no patched control and
  no safe case, so this measures recall on a vulnerable corpus, not a
  TPR/FPR pair in the sense of `scry bench`. Precision here is
  "CVE-relevant finding / all alerts", not a safe/unsafe case-level rate.
* `CVE-2019-7317` is a use-after-free of a stack-copied control block in the
  upstream code; the reduction keeps that shape. Calling it CWE-416 is the
  upstream classification, but the lifetime is a stack lifetime, not a heap
  lifetime, and that is one reason Scry misses it.
* Timings are informational on the shared machine (AGENTS.md); a `perf-run`
  measurement of this driver is not claimed here.
* The corpus is intentionally small and selected for small, buildable
  reproducers. It is not a random sample of CVEs and cannot estimate
  precision on all real code.
