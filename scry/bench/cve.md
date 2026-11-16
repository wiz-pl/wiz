# Scry on real historical CVEs (2026-11-15)

Status: measurement report. The original run is on the corpus branch
`agent/scry-cve`, based on `agent/scry-scale` `f9294ec4` with
`agent/scry-real-corpus` `acd4b34c` merged (the 51-case `scry bench` harness and
the real-C source runner are present; this corpus does not use them), and it made
**no analysis or rule changes**. The external-model re-run is on
`agent/scry-cve-models` (`agent/scry-models` `54f6ded5` merged with
`agent/scry-cve` `722e3fe9`); see
[External-model re-run](#external-model-re-run-agentscry-models-54f6ded5).
`agent/scry-coverage` then closes the named source/sink gaps and detects the two
format-string CVEs; see
[Coverage re-run](#coverage-re-run-agentscry-coverage).

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

## External-model re-run (`agent/scry-models` `54f6ded5`)

Branch `agent/scry-cve-models` (merge `acbf3b47`) keeps the corpus and driver
unchanged and adds `lib/Scry/Models.wiz`: `fgets`/`getline`/`fread` sources,
the `exec*`/`posix_spawn*` and `v*printf` sinks, and `copy`/`copyArgs` effects
so `strcpy`/`strcat`/`sprintf`/`snprintf` destinations become `mstore` rows.
The question for this run is narrow: **does taint now survive string
construction?**

Run: same 12 cases, same `--timeout 120 --max-nodes 200000`, under
`heavy --mem 3G`. The model commit binary was used because the merged build
does not complete in this environment: a clean `grail build scry` timed out
checking `Models.wiz` itself at grail's 3600 s per-job limit, and the
stale-cache attempts first failed on `Lower.wiz`/`RuleTaint.wiz` and then on
`Interproc.wiz` (unknown `Scry.pointsToBounded` from the copied build DB). The
pre-merge model worktree has a binary built from its own cache. The merge only
adds the scale budget flags and the text-slice optimisation, neither of which
changes taint. All cases are 262-1 147 nodes, far below the
200 000-node limit. Timing is therefore again informational, not a `perf-run`.

| CVE | CWE | before | after | expected rule | matched / expected | after ms | after RSS MiB |
|---|---|---|---|---|---:|---:|---:|
| CVE-2000-0573 | CWE-134 | miss | **miss** | `format-string` | 0 / 1 | 38 | 6.6 |
| CVE-2012-0809 | CWE-134 | miss | **miss** | `format-string` | 0 / 1 | 31 | 6.6 |
| CVE-2016-3714 | CWE-78 | miss | **miss** | `command-injection` | 0 / 1 | 37 | 6.6 |
| CVE-2024-23749 | CWE-78 | miss | **miss** | `command-injection` | 0 / 1 | 248 | 6.6 |
| CVE-2020-1752 | CWE-416 | miss | **miss** | `scry/memory/use-after-free` | 0 / 1 | 381 | 6.6 |
| CVE-2019-7317 | CWE-416 | miss | **miss** | `scry/memory/use-after-free` | 0 / 1 | 37 | 6.6 |
| CVE-2021-41773 | CWE-22 | out | out | -- | 0 / 0 | 51 895 | 8.6 |
| CVE-2021-3449 | CWE-476 | out | out | -- | 0 / 0 | 207 | 6.7 |
| CVE-2017-7529 | CWE-190 | out | out | -- | 0 / 0 | 128 | 6.6 |
| CVE-2021-23017 | CWE-787 | out | out | -- | 0 / 0 | 413 | 6.9 |
| CVE-2014-0160 | CWE-125 | out | out | -- | 0 / 0 | 181 | 6.6 |
| CVE-2018-1000001 | CWE-787 | out | out | -- | 0 / 0 | 332 | 6.6 |

**Verdict: no delta. In-scope recall stays 0/6; overall stays 0/12.** The
model machinery is active -- a direct probe `printf(getenv(...))` reports
`format-string`, `execl(..., getenv(...))` reports `command-injection`, and
`sprintf(buf, "%s", getenv(...))` followed by `system(buf[0])` reports
`command-injection`. But every real corpus case passes the **buffer pointer**
to the sink (`system(buffer)`, `system(command)`, `vfprintf(..., fmt2)`), not a
load from it. The copy effect writes `mstore` rows; the sink rule reads the
register value. A direct probe with `sprintf(buf, "%s", getenv(...))` then
`system(buf)` is still a miss, while the same probe with `system(buf[0])` is a
hit. That is the dominant reason the new models do not move the CVE corpus.

The new diagnostics are honest but not detections: after the change the 45
"extras" are 12 `strcpy-overflow` findings, 21 `unknown-memory`, 1
`unknown-indirect`, and **11 new `unmodelled-external` warnings** (previously
silent havocs) for `va_start`/`va_end`, `easprintf`, `strdup`, `strpbrk`,
`mempcpy`, `RAND_pseudo_bytes` and `dtls1_write_bytes`. No in-scope expected
finding matched.

### Remaining mechanism per miss

| CVE | after actual | remaining mechanism |
|---|---|---|
| CVE-2000-0573 | no finding; `vsnprintf` unknown-memory, `va_start`/`va_end` unmodelled | **copy effect not applied through a `va_list` parameter.** `read` -> `cmd`, `lreply` -> `vreply(..., va_list ap)` loses the format taint. A probe with `vsnprintf` inlined in `lreply` hits; the separate `vreply` misses. |
| CVE-2012-0809 | 2 unknown-memory, `easprintf`/`va_start`/`va_end` unmodelled | **source not modelled** (`argv[0]`) and **copy effect not applied** (`easprintf` is an unmodelled external). `vfprintf` is now a sink, but its format string never becomes tainted. |
| CVE-2016-3714 | 2 `unmodelled-external` (`strdup`, `strpbrk`) | **copy effect not applied at the sink.** `snprintf` does write the tainted filename into `command`, but `system(sanitize_command)` is a pointer argument; `SanitizeDelegateCommand`'s `strdup` return is unmodelled. |
| CVE-2024-23749 | 11 `strcpy-overflow` findings, no command-injection | **copy effect not applied at the sink.** `strcat` writes the tainted filename into `buffer`, but `system(buffer)` is a pointer argument. The rule findings are real unbounded-copy warnings, not the CVE. |
| CVE-2020-1752 | 3 unknown-memory, 2 `unmodelled-external` (`mempcpy`) | **alias/lifetime.** `strchr` is modelled pure, not as returning a pointer into its first argument; `mempcpy` is unmodelled; no heap-use path from `end_name` to the freed `dirname`. |
| CVE-2019-7317 | 1 `unknown-indirect` | **alias/lifetime.** The free is reached through an indirect callback and a stack-copied control block; the model has no callback or stack-lifetime summary. |
| six out-of-scope cases | unchanged | **no rule family** (CWE-22/476/190/787/125). |

The model's own fixtures pass because they load from the destination
(`system(buf[0])`) or pass a direct value to the sink. The real-CVE corpus
uses the C idiom `system(buffer)`, so the copy effects are not observable at
the sink. The next model/engine change, if this direction is continued, is a
memory-aware sink: for a pointer argument, check the `mtainted` locations the
pointer may point at, with the same budget/unknown discipline as `ptrAccess`.
That is a change to the sink rule, not to this corpus, and it should be
measured on both the model fixtures and these twelve cases.

## Coverage re-run (`agent/scry-coverage`)

Branch `agent/scry-coverage` (from `agent/scry-cve-models` `64df0ae4`) closes the
source/sink gaps named above. The corpus and driver are unchanged; the same twelve
cases ran with `--timeout 120 --max-nodes 200000`, and the checked-in rule pack,
`lib/Scry/Models.wiz` and the model tests changed. Two engine prerequisites were
needed: `Scry.memDep` dropped all but one data edge between the same two points
(a call reading `n, f, 0` lost the edge for `f`), and the staged CLI pipeline had
stopped collecting `unmodelled-external` warnings.

| CVE | CWE | before | after | expected rule | matched / expected | extra | hints | after ms | after RSS MiB |
|---|---|---|---|---:|---:|---:|---:|---:|---:|
| CVE-2000-0573 | CWE-134 | miss | **tp** | `format-string` | 1 / 1 | 3 | 0 | 33 | 6.8 |
| CVE-2012-0809 | CWE-134 | miss | **tp** | `format-string` | 1 / 1 | 4 | 0 | 45 | 6.8 |
| CVE-2016-3714 | CWE-78 | miss | miss | `command-injection` | 0 / 1 | 1 | 0 | 28 | 6.8 |
| CVE-2024-23749 | CWE-78 | miss | miss | `command-injection` | 0 / 1 | 0 | 11 | 430 | 6.8 |
| CVE-2020-1752 | CWE-416 | miss | miss | `scry/memory/use-after-free` | 0 / 1 | 5 | 0 | 460 | 6.8 |
| CVE-2019-7317 | CWE-416 | miss | miss | `scry/memory/use-after-free` | 0 / 1 | 1 | 0 | 21 | 6.8 |
| CVE-2021-41773 | CWE-22 | out | out | -- | 0 / 0 | 0 | 0 | 69 746 | 9.2 |
| CVE-2021-3449 | CWE-476 | out | out | -- | 0 / 0 | 3 | 0 | 212 | 6.8 |
| CVE-2017-7529 | CWE-190 | out | out | -- | 0 / 0 | 0 | 0 | 90 | 6.8 |
| CVE-2021-23017 | CWE-787 | out | out | -- | 0 / 0 | 5 | 0 | 669 | 7.2 |
| CVE-2014-0160 | CWE-125 | out | out | -- | 0 / 0 | 6 | 0 | 171 | 7.0 |
| CVE-2018-1000001 | CWE-787 | out | out | -- | 0 / 0 | 3 | 1 | 383 | 6.8 |

**In-scope recall: 2/6 (33.3%); overall: 2/12 (16.7%).** Finding-level precision is
**2/33 (6.1%)** counting non-hint alerts (2 matched + 31 extras); the 12
`strcpy-overflow` results are now `note` hints and are excluded (with them the
denominator is 45). Both new detections are the
vulnerable sink argument itself: `format-string` at `vsnprintf` argument 2
(CVE-2000-0573) and at `vfprintf` argument 1 (CVE-2012-0809), each with a checked
source path from `read`/`argv[0]`.

### What changed

| kind | added or changed |
|---|---|
| source | `main` argument 1 (`argv`) at the entry; `getopt` and `getopt_long` results; `fgets`/`getline`/`fread` buffers and `read`/`recv` buffer arguments in the default pack |
| format sink | `vsyslog` (argument 1), `vdprintf` (1), `asprintf`/`easprintf`/`vasprintf` (1); `vsnprintf`, `vfprintf`, `syslog`, `dprintf` already present |
| formatted destination | `asprintf`/`easprintf`/`vasprintf` copy their formatted arguments into the object argument 0 points at; `vsnprintf`/`vsprintf` copy the `va_list` argument into the destination |
| command sink | the existing `exec*`/`posix_spawn*` family; the default pack now repeats the concrete argument indices (`execv` 0 and 1, `execve` 0 and 1, …) so a pack reader sees them |
| policy | `realpath` (result and argument 1), `strlcpy`/`strlcat` (destination) as **opt-in** sanitiser models; a pack has to name them. The default pack does not trust them for command/format taint, and `snprintf` is explicitly not a sanitiser |
| hint | `strcpy-overflow` is `severity note`, message "hint, not a finding: unbounded strcpy/strcat; destination capacity unknown". The driver reports `hints` separately |
| va_list | a `va_list` passed through parameters keeps its taint after the data-edge fix; the format string reaches `vsnprintf` even when the `va_list` is built by `va_start` in another function |

The 11 KiTTY `strcat` alerts and the glibc `realpath` alert remain true statements
about unbounded writes, but they do not claim a fixed-size overflow. Distinguishing
"write into a fixed-size array" from "write into a buffer whose capacity is unknown"
needs a bounds analysis; the rule now says it is a hint rather than pretending to
know.

### Deliberately left unmodelled

* `optarg` (the `getopt` side channel) and `environ`; only `getenv` and `main`'s
  `argv` are sources. A non-`main` entry point (a library constructor, `wmain`) does
  not get the argv seed.
* `snprintf` truncation is not a sanitiser, and `realpath`/`strlcpy`/`strlcat` are not
  trusted by the default pack: they are bounds/path sanitisers, not content
  sanitisers.
* `strdup`, `strchr`/`strrchr` returning a pointer into their argument, and callback
  frees (`png_safe_execute`) remain unmodelled: they need alias/lifetime models, not
  taint rows.
* `execl*` models command positions 0–7; a call with more variadic arguments is
  handled by those positions only.
* A `va_list` is modelled as a value that can be copied to a destination; it is not
  expanded into its individual formatted fields, and `vfprintf` has no destination
  string to taint. `easprintf`'s non-standard `char *` return value is not modelled
  as the formatted string; its `char **` out argument is.


## Precision and recall (original run)

The table below is the first run's score, kept for comparison with the coverage
re-run above.

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
The external-model re-run above is the same 0/6 and 0/12; its extra count is
45 (12 rule findings and 33 memory diagnostics, including 11 new explicit
`unmodelled-external` warnings).

## Why each in-scope case missed

This is the original run's diagnosis, kept for the record. CVE-2000-0573 and
CVE-2012-0809 are detected on `agent/scry-coverage`; the remaining four reasons
below still hold.

| CVE | actual | reason |
|---|---|---|
| CVE-2000-0573 | nothing | the sink is `vsnprintf`; the pack only has `printf`/`fprintf`. `va_list` and the conditional size expression also lower as boundaries. |
| CVE-2012-0809 | 2 unknown-memory | the source is `argv[0]` (not `getenv`/`recv`/`read`) and the sink is `vfprintf` (not `printf`/`fprintf`); `easprintf` is an unknown external. |
| CVE-2016-3714 | nothing | the command is built by `snprintf` (arity mismatch, string literal havoc) and then copied by `SanitizeDelegateCommand`; taint does not reach `system`. |
| CVE-2024-23749 | 11 `strcpy-overflow` | the pscp command is built with `strcat`/`sprintf`; the forbidden-call rule fires on every call, but taint is not propagated through the string building, so `system(buffer)` is not tainted. |
| CVE-2020-1752 | 3 unknown-memory | `end_name = strchr(dirname, '/')` is an unknown external result, so the alias into `dirname` is invisible; after `free(dirname)` the `mempcpy(..., end_name, ...)` use is not connected to the freed object. |
| CVE-2019-7317 | 1 unknown-indirect | the free happens inside a callback copied through a stack control block; there is no stack-lifetime or indirect-call summary, so the stale `image->opaque` is not recognised as a freed heap object. |

## Top three analysis gaps

The format-string half of gap 1 is closed on `agent/scry-coverage` (`vsnprintf`,
`vfprintf` and the `va_list` path); command injection through a copied buffer
still needs the memory-aware sink the model re-run called for.

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

Items 1–2 are implemented on `agent/scry-coverage` (see the coverage re-run); items
3–4 remain.

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

## Precision branch re-run (`agent/scry-precision`)

Status: measurement on the precision branch (base `agent/scry-models` `54f6ded5`). The
branch changes the **false-positive** side only:

1. the default pack now trusts the shipped policy sanitisers `quote_arg`,
   `sanitize_format` and `clamp_len`/`checked_size`; and
2. the points-to freed diagnostic asks the **reaching definitions** of the access
   register, so a pointer cleared or re-allocated after `free` is not a use-after-free;
3. a pack sanitiser also kills a **unit-defined** callee's tainted return
   (`rtRuleRetSrc` carries `!san`), which is what makes a `clamp_len` helper work.

None of the three adds or removes a source, sink or forbidden call; the second only
**filters** `scry/memory/use-after-free` warnings (it never creates a finding), and no
CVE reproducer calls a sanitiser name. The CVE corpus is therefore a control: it must
not move. The run below used the base model
binary with the branch's `lib/Scry/rules/default.scry` (the pack is loaded from the
working tree), because a fresh `scry` build is blocked by the `Models.wiz` checker
timeout recorded below.

Run (pack change only, same 12 cases):

```sh
cd scry
SCRY_BIN=/workspace/wt/scry-models/scry/.grail/bin/scry \
  scripts/cve-bench.sh --timeout 120 --max-nodes 200000
```

| metric | base `54f6ded5` | precision branch |
|---|---:|---:|
| in-scope cases | 6 | 6 |
| detected (TP) | 0 | **0** |
| missed (FN) | 6 | **6** |
| overall CVE detection | 0/12 | **0/12** |
| extra alerts (rule + memory diagnostics) | 45 | **45** |

**No delta.** The per-case outcomes are `fn` for the six in-scope cases and
`out-of-scope` for the six others, exactly as in the table above; the 45 extras are 12
`strcpy-overflow`, 21 `unknown-memory`, 1 `unknown-indirect` and 11
`unmodelled-external`. The pack's three new sanitiser names do not occur in any CVE
reproducer, and no CVE reaches a `free`-then-use warning on the paths the analysis sees.

### Build note (environment, not analysis)

A clean `grail build scry` in this worktree does not finish: the checker times out on
`../lib/Scry/Models.wiz` at grail's 1800 s per-job limit (the same failure recorded in
the external-model re-run above). The unchanged modules' job cache was seeded from the
base worktree (the keys are content-addressed and 192/194 match), which gets the build
past `Models`; `RuleTaint.wiz` then re-elaborates `Models` as an import and hits the same
limit. Consequence: the **C CLI** was not rebuilt on this branch. The safe-corpus CLI
numbers below use the base model binary with the branch's pack; the lifetime change is
verified by the `scry-taint` group (a new Wil-level null-after-free case) and a
standalone probe over the same `freedHit` code, both described in
`scry/bench/safe/README.md`.
