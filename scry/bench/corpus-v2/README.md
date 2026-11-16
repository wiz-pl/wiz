# CVE corpus v2 (pairs and controls)

This directory is the v2 real-CVE corpus for the opt-in `scry taint` bench.
It does **not** modify the twelve v1 cases in `scry/bench/cases/`; it reuses
their in-scope vulnerable files and adds patched controls beside them.

* `manifest.json` — every case: pair, variant, CVE, CWE, product, source URL,
  licence, scope, expected findings (rule, callee, argument, sink line/span),
  the fix applied to a control, and the out-of-scope reason.
* `cases/cve-<id>-fixed/` — a patched control for a v1 in-scope case, or the
  fixed half of a new pair.
* `cases/cve-<id>-vuln/` — the vulnerable half of a new pair.

Like v1, a case directory holds `harness.c` and `upstream.json`, not third-party code:
`scry/scripts/cve-fetch.py assemble` builds each `case.c` under
`scry/build/cve-src/corpus-v2/` from pinned upstream source, and `cve-bench-v2` reads that
tree. A patched control's fix lives in its harness. `upstream.json` also corrects three
source URLs: CVE-2019-18408 is in the RAR (v4) reader (`archive_read_support_format_rar.c`,
not the rar5 one, which 3.3.3 does not have), CVE-2020-1971's vulnerable release is
OpenSSL 1.1.1h (1.1.1i fixed it) at `crypto/x509v3/v3_genn.c`, and wu-ftpd 2.6.0 comes
from Debian's snapshot archive (the original FTP host is gone).

A **pair** is the unit: one vulnerable case and, for every in-scope pair, one
patched control with the same shape and the fix applied. The four fix shapes
are bounded copy, sanitiser, `snprintf` with a size, and a reordered/removed
free. A fixed control must produce no **rule** finding; memory diagnostics
(`unknown-memory`, `unknown-indirect`) are coverage boundaries and are
recorded separately.

## Scope

A pair is **in scope** when the default pack (`lib/Scry/rules/default.scry`)
or the points-to memory diagnostics has a rule family for its CWE. A pair that
has no such family is an explicit **out-of-scope** entry with the reason in
`manifest.json`; it is not omitted. Out-of-scope pairs are excluded from the
2x2 and from precision/recall.

The CWE-476 (null dereference) probes are deliberately out of scope for this
tool version: the S5 nullness alarm exists in `lib/Scry/AiFixpoint.wiz`, but
`scry taint` has no null-deref sink, so there is nothing to match. They are
kept as explicit coverage probes rather than dropped.

## Pairs

| pair | CVE | CWE | product | scope | fix in the control |
|---|---|---|---|---|---|
| cve-2000-0573 | CVE-2000-0573 | CWE-134 | wu-ftpd 2.6.0 | in | `lreply(200, "%s", cmd)` |
| cve-2012-0809 | CVE-2012-0809 | CWE-134 | sudo 1.8.3 | in | `vfprintf(stderr, "%s", fmt2)` |
| cve-2016-3714 | CVE-2016-3714 | CWE-78 | ImageMagick 7.0.1-0 | in | shell-escape before `system` |
| cve-2024-23749 | CVE-2024-23749 | CWE-78 | KiTTY 0.76.1.13 | in | escape + bounded `snprintf` |
| cve-2020-1752 | CVE-2020-1752 | CWE-416 | glibc 2.30 | in | free after the last use |
| cve-2019-7317 | CVE-2019-7317 | CWE-416 | libpng 1.6.36 | in | no post-callback `opaque` read |
| cve-2020-7247 | CVE-2020-7247 | CWE-78 | OpenSMTPD 6.6.1 | in | validate local part first |
| cve-2019-10149 | CVE-2019-10149 | CWE-78 | Exim 4.91 | in | parse the recipient; no `expand_string` |
| cve-2006-6772 | CVE-2006-6772 | CWE-134 | w3m 0.5.1 | in | `printf("%s", prompt)` |
| cve-2014-9157 | CVE-2014-9157 | CWE-134 | Graphviz 2.38.0 | in | `agerr(AGERR, "%s", ...)` |
| cve-2015-8106 | CVE-2015-8106 | CWE-134 | latex2rtf 2.3.9 | in | `fprintRTF("%s", ...)` |
| cve-2019-18408 | CVE-2019-18408 | CWE-416 | libarchive 3.3.3 | in | reset the PPMd table after free |
| cve-2019-19344 | CVE-2019-19344 | CWE-416 | Samba 4.11.4 | in | copy the ldb message first |
| cve-2017-6074 | CVE-2017-6074 | CWE-416 | Linux 4.9 (DCCP) | in | `consume_skb` instead of discard |
| cve-2020-1971 | CVE-2020-1971 | CWE-476 | OpenSSL 1.1.1j | out | `edipartyname_cmp` rejects NULL |
| cve-2017-7659 | CVE-2017-7659 | CWE-476 | Apache httpd 2.4.25 | out | check the allocator status |
| cve-2021-41773 | CVE-2021-41773 | CWE-22 | Apache httpd 2.4.49 | out | (v1 case, no control) |
| cve-2021-3449 | CVE-2021-3449 | CWE-476 | OpenSSL 1.1.1j | out | (v1 case, no control) |
| cve-2017-7529 | CVE-2017-7529 | CWE-190 | nginx 1.13.2 | out | (v1 case, no control) |
| cve-2021-23017 | CVE-2021-23017 | CWE-787 | nginx 1.20.0 | out | (v1 case, no control) |
| cve-2014-0160 | CVE-2014-0160 | CWE-125 | OpenSSL 1.0.1f | out | (v1 case, no control) |
| cve-2018-1000001 | CVE-2018-1000001 | CWE-787 | glibc 2.26 | out | (v1 case, no control) |

Source URLs and licences are in `manifest.json`. The new reproducers are
reductions, not the full upstream programs; each header says which function
is kept and which plumbing was replaced.

## Run

```sh
cd scry
cp ../grail.local.wiz .                      # once, if absent
../.lake/build/bin/grail build scry
scripts/cve-bench-v2.sh --timeout 120 --max-nodes 200000
cat build/cve-v2/summary.md
```

`--case <id|pair|cve>` runs one case or pair; `--no-run` only summarises
existing `build/cve-v2/` output; `--write-report` writes the full 2x2 report to
`build/cve-v2/report.md`. The report is generated, so it is not checked in; the
measured recall when the corpus was added was 1/14 in-scope pairs (7.1%). The v1 driver and its twelve cases are unchanged.

This is measurement infrastructure. It does not tune rules or analysis.
