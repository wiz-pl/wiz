#!/usr/bin/env python3
"""Generate the published benchmark page, ``web/bench/index.html``.

The page is a rendering of the benchmark JSON checked into the repository:

    bench/stdlib-baseline.json   the A side of the standard-library comparison
    bench/stdlib-bench.json      the B side, with the interleaved A/B ratios
    scry/bench/baseline.json     the Scry taint corpus metrics

Nothing here measures anything: every number is read from those files.  The
output is committed, so a JSON change that is not regenerated shows up as a
stale page in a diff, and CI's site job refuses it:

    python3 web/build-bench.py            # rewrite web/bench/index.html
    python3 web/build-bench.py --check    # exit 1 if the checked-in page is stale

``--out`` and ``--root`` exist for the tests (``web/build-bench_test.py``).
The page contains no timestamp of its own: dates and hosts come from the JSON,
so regenerating an unchanged set of inputs is a byte-for-byte no-op.
"""
from __future__ import annotations

import argparse
import difflib
import html
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
OUT = os.path.join(HERE, "bench", "index.html")

STDLIB_A = os.path.join("bench", "stdlib-baseline.json")
STDLIB_B = os.path.join("bench", "stdlib-bench.json")
SCRY = os.path.join("scry", "bench", "baseline.json")

EMPTY = "—"


def load(root: str, rel: str) -> dict:
    """Read one JSON file; a missing or malformed file is an error, not a blank page."""
    path = os.path.join(root, rel)
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        raise SystemExit(f"build-bench: missing {rel} (expected at {path})")
    except json.JSONDecodeError as e:
        raise SystemExit(f"build-bench: {rel} is not valid JSON: {e}")
    if not isinstance(data, dict):
        raise SystemExit(f"build-bench: {rel}: expected a JSON object")
    return data


def num(value):
    """A finite number, or None.  Booleans are not numbers here."""
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        value = float(value)
        if value != value or value in (float("inf"), float("-inf")):  # NaN/inf
            return None
        return value
    return None


def text(value, default: str = EMPTY) -> str:
    if value is None or value == "":
        return default
    return html.escape(str(value))


def fmt_ms(ns) -> str:
    """Nanoseconds as a human-readable duration."""
    ns = num(ns)
    if ns is None:
        return EMPTY
    ms = ns / 1e6
    if ms >= 100:
        return f"{ms:,.0f} ms"
    if ms >= 10:
        return f"{ms:.1f} ms"
    if ms >= 1:
        return f"{ms:.2f} ms"
    us = ns / 1e3
    if us >= 1:
        return f"{us:.0f} µs"
    return f"{ns:.0f} ns"


def fmt_change(a, b) -> str:
    """Relative change from a to b, with a sign ('' when it cannot be computed)."""
    a, b = num(a), num(b)
    if a is None or b is None or a == 0:
        return EMPTY
    return f"{(b - a) / a * 100:+.1f}%"


def fmt_ratio(r) -> str:
    r = num(r)
    return EMPTY if r is None else f"{r:.3f}×"


def fmt_pct(x) -> str:
    x = num(x)
    return EMPTY if x is None else f"{100.0 * x:.1f}%"


def fmt_bp(bp, fallback) -> str:
    """A basis-point percentage from the JSON, or the float it was made from."""
    bp = num(bp)
    if bp is not None:
        return f"{bp / 100.0:.2f}%"
    x = num(fallback)
    return EMPTY if x is None else f"{100.0 * x:.2f}%"


def fmt_defined(flag, bp, fallback) -> str:
    """A ratio, or — when the JSON says its denominator is zero."""
    if flag is False:
        return EMPTY
    return fmt_bp(bp, fallback)


def fmt_count(value) -> str:
    v = num(value)
    if v is None:
        return EMPTY
    return f"{int(v):,}" if v == int(v) else f"{v:,}"


def rep_count(record) -> str:
    samples = record.get("samples_ns")
    if isinstance(samples, list):
        return str(len(samples))
    return EMPTY


def is_single_run(record) -> bool:
    samples = record.get("samples_ns")
    if isinstance(samples, list):
        return len(samples) <= 1
    reps = num(record.get("reps"))
    return reps is not None and reps <= 1


def table(headers, rows, caption=None, cls="") -> str:
    """rows is a list of (cells, row-class); cells are pre-escaped strings."""
    out = []
    if caption:
        out.append(f'<p class="caption">{caption}</p>')
    out.append(f'<div class="table-wrap"><table class="{cls}">')
    out.append("<thead><tr>" + "".join(f"<th>{h}</th>" for h in headers) + "</tr></thead>")
    out.append("<tbody>")
    if not rows:
        out.append(f'<tr><td class="empty" colspan="{len(headers)}">no results recorded</td></tr>')
    for cells, row_cls in rows:
        attr = f' class="{row_cls}"' if row_cls else ""
        out.append(f"<tr{attr}>" + "".join(f"<td>{c}</td>" for c in cells) + "</tr>")
    out.append("</tbody></table></div>")
    return "\n".join(out)


def provenance(items) -> str:
    rows = [(k, v) for k, v in items if v is not None]
    if not rows:
        return ""
    return '<dl class="meta">' + "".join(f"<dt>{k}</dt><dd>{v}</dd>" for k, v in rows) + "</dl>"


def stdlib_section(a: dict, b: dict) -> str:
    a_results = a.get("results") if isinstance(a.get("results"), dict) else {}
    b_results = b.get("results") if isinstance(b.get("results"), dict) else {}
    ab = b.get("ab") if isinstance(b.get("ab"), dict) else {}
    ab_results = ab.get("results") if isinstance(ab.get("results"), dict) else {}

    modes = sorted(set(a_results) | set(b_results) | set(ab_results))
    a_reps = num(a.get("reps"))
    b_reps = num(b.get("reps"))
    reps = b_reps if b_reps is not None else a_reps

    meta = provenance([
        ("run date", text(b.get("created", a.get("created")), "not recorded")),
        ("machine", text(b.get("host", a.get("host")), "not recorded")),
        ("commit", text(b.get("commit", a.get("commit")))),
        ("samples per mode", EMPTY if reps is None else fmt_count(reps)),
        ("harness", text(b.get("generator", a.get("generator")))),
    ])

    # The A/B table.  When the JSON has interleaved pairs, use only those: they are
    # measured under the same load, which is the whole point of the pairing.  Without
    # them, fall back to the two runs' medians and say so.
    interleaved = bool(ab_results)
    rows = []
    for mode in modes:
        rec = ab_results.get(mode) or {}
        if interleaved and rec:
            av = rec.get("baseline_median_ns")
            bv = rec.get("median_ns")
            ratio = fmt_ratio(rec.get("median_ratio"))
            lo = num(rec.get("min_ratio"))
            hi = num(rec.get("max_ratio"))
            if lo is not None and hi is not None:
                rng = f"{lo:.3f}–{hi:.3f}×"
            else:
                rng = EMPTY
            same = rec.get("checksums_equal")
        else:
            arec = a_results.get(mode) or {}
            brec = b_results.get(mode) or {}
            av = arec.get("median_ns")
            bv = brec.get("median_ns")
            ratio = rng = EMPTY
            ca, cb = arec.get("checksum"), brec.get("checksum")
            same = None if ca is None or cb is None else ca == cb

        change = fmt_change(av, bv)
        row_cls = "changed" if same is False else ""
        if same is True:
            checks = "same"
        elif same is False:
            checks = "changed"
        else:
            checks = EMPTY
        rows.append(([
            f'<span class="mode">{text(mode)}</span>',
            fmt_ms(av),
            fmt_ms(bv),
            change,
            ratio,
            rng,
            checks,
        ], row_cls))

    if interleaved:
        caption = ("A and B are the medians of the interleaved samples (one run of each "
                   "build per sample, alternately first); the ratio is the median of the "
                   "per-pair B/A ratios, so 1.000× means no change and a lower value is "
                   "faster. The range is the slowest and fastest pair. Machine load cancels "
                   "in a pair, but absolute times still depend on the machine.")
    else:
        caption = ("A and B are the medians recorded in the two JSON files; this pair of "
                   "runs was not interleaved, so machine drift between them is not "
                   "cancelled and the change column is the weaker comparison.")

    out = [f"<h2 id=\"stdlib\">Standard library</h2>",
           f'<p class="lede">The {len(modes)} hot paths recorded here, from <code>lib/</code>: '
           'maps, arrays, bytes, strings, sorting and hashing. Each mode does a fixed '
           'amount of work and prints a checksum, so a timing cannot be “fast” because '
           'the work disappeared.</p>',
           meta,
           "<h3>A/B</h3>",
           table(["mode", "A (paired)" if interleaved else "A",
                  "B (paired)" if interleaved else "B",
                  "change", "ratio", "pair range", "checksums"], rows,
                 caption=caption)]

    changed = [m for m in modes
               if (ab_results.get(m) or {}).get("checksums_equal") is False]
    if changed:
        out.append(
            '<p class="warn"><strong>Not like-for-like:</strong> '
            + ", ".join(f"<code>{text(m)}</code>" for m in changed)
            + " changed its checksum between the two builds, so the work itself "
              "changed; the ratio compares different work, not a speed-up of the same work."
            "</p>")

    # The distribution of each recorded run: the JSON keeps every sample, so show the
    # spread rather than pretending a single number is exact.
    spread = []
    for mode in modes:
        arec = a_results.get(mode) or {}
        brec = b_results.get(mode) or {}
        single = is_single_run(arec) or is_single_run(brec)
        spread.append(([
            f'<span class="mode">{text(mode)}</span>',
            fmt_count(brec.get("n", arec.get("n"))),
            rep_count(arec),
            fmt_ms(arec.get("median_ns")),
            fmt_pct(arec.get("cv")),
            rep_count(brec),
            fmt_ms(brec.get("median_ns")),
            fmt_pct(brec.get("cv")),
            "single run" if single else "repeated",
        ], "single" if single else ""))

    out.append("<h3>Spread of each run</h3>")
    out.append(table(
        ["mode", "N", "A samples", "A median", "A CV", "B samples", "B median", "B CV", "kind"],
        spread,
        caption=("CV is the coefficient of variation of the samples inside one run: a "
                  "property of the machine and its load, not of the change. “single run” "
                  "means the file has one sample (or one repetition), so it records no "
                  "variance at all; treat such a number as anecdotal.")))

    inputs = provenance([
        ("A", f"<code>{STDLIB_A}</code>"),
        ("B", f"<code>{STDLIB_B}</code>"),
    ])
    out.append(inputs)
    return "\n".join(out)


METRIC_ORDER = [
    ("tp", "true positives", "count"),
    ("fn", "false negatives", "count"),
    ("tn", "true negatives", "count"),
    ("fp", "false positives", "count"),
    ("unknown", "unknown", "count"),
    ("error", "errors", "count"),
    ("skipped", "skipped", "count"),
    ("tpr", "TPR", "pct"),
    ("fpr", "FPR", "pct"),
    ("youden", "Youden J", "pct"),
    ("precision", "precision", "pct"),
    ("f1", "F1", "pct"),
]


def scry_section(s: dict) -> str:
    cases = s.get("cases") if isinstance(s.get("cases"), list) else []
    overall = s.get("overall") if isinstance(s.get("overall"), dict) else {}
    per_cwe = s.get("per_cwe") if isinstance(s.get("per_cwe"), list) else []

    meta = provenance([
        ("corpus", text(s.get("corpus"))),
        ("format", text(s.get("format"))),
        ("version", text(s.get("version"))),
        ("cases recorded", fmt_count(len(cases))),
        ("run date", text(s.get("created"), "not recorded")),
        ("machine", text(s.get("host"), "not recorded")),
    ])

    out = [f"<h2 id=\"scry\">Scry taint benchmark</h2>",
           '<p class="lede">The C taint corpus: for each case, the expected outcome is '
           'compared with the findings, and the ratios are computed in integer basis '
           'points so the file is stable. These are counts and detection rates, not '
           'timings.'
           + ('' if any(k in s for k in ('runtime', 'runtime_ms', 'runtime_ns'))
              else ' The baseline records no runtime for this run.')
           + '</p>',
           meta]

    missing = [k for k in ("created", "host") if not s.get(k)]
    note = ("Paths in the file are relative to <code>scry/</code>. "
            "The case metrics are produced by the Scry checker’s <code>bench</code> "
            "command over the checked-in corpus manifest.")
    if missing:
        what = " and no ".join("date" if k == "created" else "machine" for k in missing)
        note += f" The baseline records no {what}."
        if "created" in missing:
            note += " Its git history is the only record of when it changed."
        if "host" in missing:
            note += " It says nothing about the machine it ran on."
    out.append(f'<p class="caption">{note}</p>')

    rows = []
    for key, label, kind in METRIC_ORDER:
        if key not in overall:
            continue
        value = overall.get(key)
        if kind == "pct":
            shown = fmt_defined(overall.get(key + "_defined"),
                                overall.get(key + "_bp"), value)
        else:
            shown = fmt_count(value)
        rows.append(([text(label), shown], ""))
    # Metrics the file may add later: show them rather than silently dropping them.
    known = {k for k, _, _ in METRIC_ORDER} | {k + "_bp" for k, _, _ in METRIC_ORDER}
    for key in sorted(overall):
        if key in known or key.endswith("_defined") or key.endswith("_negative"):
            continue
        value = overall[key]
        if isinstance(value, bool):
            continue
        shown = fmt_bp(None, value) if isinstance(value, float) and value <= 1 else fmt_count(value)
        rows.append(([text(key.replace("_", " ")), shown], ""))
    out.append("<h3>Overall</h3>")
    out.append(table(["metric", "value"], rows,
                     caption=("TP/FN/TN/FP are cases, not alerts; a case is a true "
                              "positive only when every expected finding is matched with "
                              "valid evidence. No variance is recorded: the analysis is "
                              "deterministic, and each case is one run.")))

    # Boundary warnings and the two evidence summaries are nested objects.
    boundary = [num(c.get("boundary")) for c in cases if isinstance(c, dict)]
    blocking = [num(c.get("blocking_boundary")) for c in cases if isinstance(c, dict)]
    boundary = [x for x in boundary if x is not None]
    blocking = [x for x in blocking if x is not None]
    evidence = []
    if boundary:
        evidence.append(("boundary warnings", f"{int(sum(boundary)):,} "
                         f"({int(sum(blocking)):,} blocking in "
                         f"{sum(1 for x in blocking if x > 0)} cases)"))
    pv = s.get("path_validity")
    if isinstance(pv, dict):
        evidence.append(("paths that reach the sink",
                         f"{fmt_count(pv.get('valid_paths'))} / {fmt_count(pv.get('findings'))}"))
    cert = s.get("certificate")
    if isinstance(cert, dict):
        evidence.append(("certificates checked",
                         f"{fmt_count(cert.get('checked'))} / {fmt_count(cert.get('findings'))}"))
    if evidence:
        out.append("<h3>Evidence</h3>")
        out.append(table(["measure", "value"],
                         [([text(k), v], "") for k, v in evidence]))

    if per_cwe:
        rows = []
        for group in per_cwe:
            if not isinstance(group, dict):
                continue
            name = group.get("name")
            m = group.get("metrics") if isinstance(group.get("metrics"), dict) else {}
            counts = [num(m.get(k)) or 0 for k in ("tp", "fn", "tn", "fp", "unknown", "error", "skipped")]
            rows.append(([
                text(name),
                fmt_count(sum(counts)),
                fmt_count(m.get("tp")),
                fmt_count(m.get("fn")),
                fmt_count(m.get("tn")),
                fmt_count(m.get("fp")),
                fmt_count(m.get("unknown")),
                fmt_defined(m.get("tpr_defined"),
                            m.get("tpr_bp"), m.get("tpr")),
                fmt_defined(m.get("fpr_defined"),
                            m.get("fpr_bp"), m.get("fpr")),
                fmt_defined(m.get("youden_defined"),
                            m.get("youden_bp"), m.get("youden")),
                fmt_bp(None, m.get("precision")),
                fmt_count(group.get("findings")),
                fmt_count(group.get("valid_paths")),
                fmt_count(group.get("checked")),
            ], ""))
        out.append("<h3>Per CWE</h3>")
        out.append(table(["CWE", "cases", "TP", "FN", "TN", "FP", "unknown",
                          "TPR", "FPR", "J", "precision", "findings", "paths", "checked"],
                         rows,
                         caption=("A CWE with no safe case has no defined FPR (shown as "
                                  "—); recall figures on a single case are anecdotal.")))

    if not cases:
        out.append('<p class="empty">The baseline records no cases.</p>')

    out.append(provenance([("file", f"<code>{SCRY}</code>")]))
    return "\n".join(out)


STYLE = """
:root{
  color-scheme: light dark;
  --bg:#fdfdfb; --fg:#1d1d1b; --muted:#5f5e58; --line:#dcdbd2;
  --card:#f5f4ee; --accent:#7a4a00; --good:#1b6b3a; --bad:#8a2b1f;
}
@media (prefers-color-scheme: dark){
  :root{ --bg:#171715; --fg:#ecebe4; --muted:#a5a49c; --line:#3a3934;
         --card:#22221f; --accent:#e0a95c; --good:#7fd39b; --bad:#f08a7c; }
}
*{box-sizing:border-box}
html{background:var(--bg);color:var(--fg)}
body{margin:0;font:16px/1.55 system-ui,-apple-system,"Segoe UI",sans-serif}
a{color:var(--accent)}
code{font:0.92em ui-monospace,SFMono-Regular,Menlo,monospace}
.skip-link{position:absolute;left:-9999px}
.skip-link:focus{left:1rem;top:1rem;background:var(--card);padding:.4rem .7rem;z-index:9}
.site-header{display:flex;gap:1rem;align-items:center;justify-content:space-between;
  flex-wrap:wrap;padding:.9rem 1.25rem;border-bottom:1px solid var(--line)}
.brand{font-weight:700;text-decoration:none;color:inherit}
.brand-mark{color:var(--accent)}
.site-nav ul,.site-footer ul{display:flex;gap:1rem;list-style:none;margin:0;padding:0;flex-wrap:wrap}
.site-nav a,.site-footer a{text-decoration:none}
.site-nav a[aria-current]{text-decoration:underline;text-underline-offset:.2em}
main{max-width:64rem;margin:0 auto;padding:1.5rem 1.25rem 4rem}
h1{font-size:clamp(2rem,5vw,2.8rem);line-height:1.1;margin:.4rem 0 .6rem}
h2{margin-top:2.6rem;padding-top:.4rem;border-top:1px solid var(--line)}
h3{margin-top:1.6rem;font-size:1rem;letter-spacing:.02em;text-transform:uppercase;color:var(--muted)}
.lede{max-width:60ch;color:var(--muted)}
.meta{display:grid;grid-template-columns:max-content 1fr;gap:.15rem 1rem;margin:1rem 0;
  font-size:.9rem;color:var(--muted)}
.meta dt{font-weight:600}
.meta dd{margin:0;overflow-wrap:anywhere}
.table-wrap{overflow-x:auto;margin:.6rem 0 1rem;border:1px solid var(--line);border-radius:.4rem}
table{border-collapse:collapse;width:100%;font-size:.9rem;font-variant-numeric:tabular-nums}
th,td{padding:.42rem .6rem;text-align:right;white-space:nowrap;border-bottom:1px solid var(--line)}
th{background:var(--card);font-weight:600}
th:first-child,td:first-child{text-align:left}
tbody tr:last-child td{border-bottom:0}
tr.changed td{background:color-mix(in srgb,var(--bad) 10%,transparent)}
tr.single td{font-style:italic}
td.empty{color:var(--muted);text-align:left}
.caption{font-size:.85rem;color:var(--muted);max-width:70ch}
.warn{border-left:3px solid var(--bad);background:color-mix(in srgb,var(--bad) 8%,transparent);
  padding:.6rem .8rem;border-radius:.2rem}
.generated{font-size:.85rem;color:var(--muted)}
pre{background:var(--card);border:1px solid var(--line);border-radius:.4rem;
  padding:.8rem 1rem;overflow-x:auto;font-size:.88rem}
pre code{white-space:pre}
.site-footer{border-top:1px solid var(--line);padding:1.2rem 1.25rem 2.5rem;
  max-width:64rem;margin:0 auto;font-size:.9rem;color:var(--muted)}
.site-footer .small{font-size:.85rem}
"""


def render(root: str) -> str:
    a = load(root, STDLIB_A)
    b = load(root, STDLIB_B)
    s = load(root, SCRY)
    body = "\n".join([stdlib_section(a, b), scry_section(s)])
    return f"""<!doctype html>
<!-- generated-bench-page: written by web/build-bench.py; do not edit by hand. -->
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Wiz — benchmarks</title>
<meta name="description" content="Standard-library timings and the Scry taint benchmark, generated from the JSON checked into the repository.">
<meta name="color-scheme" content="light dark">
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Crect width='64' height='64' rx='14' fill='%231d1d1b'/%3E%3Ctext x='32' y='45' font-size='40' font-family='system-ui,sans-serif' fill='%23fdfdfb' text-anchor='middle'%3E%CE%BB%3C/text%3E%3C/svg%3E">
<style>{STYLE}</style>
</head>
<body>
<a class="skip-link" href="#main">Skip to content</a>
<header class="site-header">
  <a class="brand" href="../" aria-label="Wiz home"><span class="brand-mark" aria-hidden="true">λ</span> Wiz</a>
  <nav class="site-nav" aria-label="Main">
    <ul>
      <li><a href="../docs/">Docs</a></li>
      <li><a href="../playground/">Playground</a></li>
      <li><a href="../bench/" aria-current="page">Benchmarks</a></li>
      <li><a class="external" href="https://github.com/wiz-pl/wiz">GitHub<span class="external-mark" aria-hidden="true"> ↗</span></a></li>
    </ul>
  </nav>
</header>
<main id="main">
  <h1>Benchmarks</h1>
  <p class="lede">
    What the standard library costs and what the Scry taint checker finds, recorded as
    JSON and rendered here. Timings are <strong>environment-dependent</strong>: the same
    build on a different machine, kernel or load gives different absolute numbers.
    Compare two builds by interleaving them, not by comparing absolute times. Values that
    come from a single sample are labelled as such.
  </p>
  <p class="generated">Generated by <code>web/build-bench.py</code> from the JSON in
    <code>bench/</code> and <code>scry/bench/</code>. Every number is read from those
    files; the page is checked in so a stale rendering is a diff, and CI verifies that
    regenerating it is a no-op.</p>
{body}
  <h2 id="reproduce">How to reproduce</h2>
  <p class="lede">
    The standard-library harness is checked in with its recorded data: it builds
    <code>bench/stdlib-bench.wiz</code> and runs each mode in its own process. The Scry
    figures are the Scry checker’s <code>bench</code> command over its corpus manifest;
    <code>scry/bench/baseline.json</code> is the baseline that run is compared with.
  </p>
  <pre><code># Standard library: build the A side (the compiler from the commit you compare
# against), then interleave it with the B side.
$OLD_WIZ build bench/stdlib-bench.wiz -o bench/.build/bench-base
scripts/stdlib-bench.py --bin bench/.build/bench-base --reps 15 \\
    --json bench/stdlib-baseline.json
scripts/stdlib-bench.py --baseline-bin bench/.build/bench-base --reps 15 \\
    --json bench/stdlib-bench.json

# A recorded run compared with a later run by medians (weaker: no pairing).
scripts/stdlib-bench.py --baseline bench/stdlib-baseline.json

# Scry taint corpus: metrics, not timing. Writes build/bench.json and .md.
cd scry &amp;&amp; grail run scry -- bench --no-timing
cd scry &amp;&amp; grail run scry -- bench --update-baseline bench/baseline.json

# Regenerate this page; CI runs the --check form, which must be a no-op.
python3 web/build-bench.py
python3 web/build-bench.py --check</code></pre>
  <p class="caption">
    Sizes are fixed in the benchmark program and passed to it, so a sample does exactly
    the work its JSON says. Nix users can run everything inside the development shell.
    Absolute times on a shared machine move by several percent; the paired ratios are the
    number to read.
  </p>
</main>
<footer class="site-footer">
  <nav aria-label="Footer">
    <ul>
      <li><a href="../">Home</a></li>
      <li><a href="../docs/">Docs</a></li>
      <li><a href="../playground/">Playground</a></li>
      <li><a href="https://github.com/wiz-pl/wiz/tree/master/bench">Benchmark harness</a></li>
      <li><a href="https://github.com/wiz-pl/wiz">GitHub</a></li>
    </ul>
  </nav>
  <p class="small">No cookies, no analytics, no third-party scripts.</p>
</footer>
</body>
</html>
"""


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description="Generate the benchmark page from the checked-in JSON.")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if the checked-in page is out of date (write nothing)")
    ap.add_argument("--root", default=ROOT, help="repository root (default: this checkout)")
    ap.add_argument("--out", default=None, help="output file (default: web/bench/index.html)")
    args = ap.parse_args(argv)

    out = args.out or os.path.join(args.root, "web", "bench", "index.html")
    page = render(args.root)

    if args.check:
        try:
            with open(out, encoding="utf-8") as f:
                current = f.read()
        except FileNotFoundError:
            print(f"build-bench: {out} is missing; run python3 web/build-bench.py",
                  file=sys.stderr)
            return 1
        if current == page:
            print(f"build-bench: {os.path.relpath(out, args.root)} is up to date")
            return 0
        print(f"build-bench: {os.path.relpath(out, args.root)} is stale; "
              "run python3 web/build-bench.py", file=sys.stderr)
        diff = list(difflib.unified_diff(
            current.splitlines(), page.splitlines(),
            fromfile="checked-in", tofile="regenerated", lineterm="", n=2))
        for line in diff[:80]:
            print(line, file=sys.stderr)
        if len(diff) > 80:
            print(f"... {len(diff) - 80} more diff lines", file=sys.stderr)
        return 1

    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, "w", encoding="utf-8", newline="\n") as f:
        f.write(page)
    print(f"build-bench: wrote {os.path.relpath(out, args.root)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
