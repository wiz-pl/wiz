#!/usr/bin/env python3
"""Gate a nightly standard-library benchmark on paired A/B ratios.

`scripts/stdlib-bench.py --baseline-bin OLD` alternates one run of an older
benchmark executable with one run of the current build, and writes a JSON file
whose ``ab.results`` holds every per-pair ratio for every mode.  This script
turns that file into a pass/fail decision and a job-summary table:

    scripts/bench-threshold.py --json bench-out/stdlib-bench.json \\
        --fail-on 10 --min-samples 5

A mode is a regression when the **median of its paired ratios** is worse than
``--fail-on`` percent and it has at least ``--min-samples`` pairs.  Absolute
times are never compared: they move with the machine, other jobs and the phase
of the moon.  A mode whose checksum changed is not comparable and is never
gated (the benchmark program's work changed); the A/B harness normally refuses
such a pair, apart from modes explicitly allowed with ``--allow-checksum``.

Inputs:

* ``--json``: the run written by ``scripts/stdlib-bench.py`` (required, except
  for ``--self-test`` and ``--print-sizes``).
* ``--baseline``: the checked-in ``bench/stdlib-baseline.json``.  Only its
  per-mode sizes ``n`` are enforced (the nightly must do the same work as the
  reference run); its medians are not used for the gate.  ``--print-sizes``
  prints the ``MODE=N`` lines for the harness's ``--size``.
* ``--scry``: the JSON written by ``scry bench --json``.  Reported in the
  summary and the history, but not gated here: ``scry bench
  --fail-on-regression`` owns that decision.

Outputs:

* a Markdown table on stdout and, with ``--markdown FILE``, appended to that
  file (the workflow passes ``$GITHUB_STEP_SUMMARY``);
* with ``--history FILE``, one JSON line appended per run (``bench/history.jsonl``,
  an artifact, never committed);
* with ``--annotate-json``, the run JSON gains its ``environment`` object
  (machine id, runner label, CPU affinity, CPU model) so a stored run says
  where it was measured.

Exit status: 0 no regression (including "not enough samples to gate" when no
``--baseline`` was given, i.e. nothing to compare against), 1 a mode is worse than the
threshold, 2 bad or incomplete input (including a gated run with a ``--baseline`` that
had too few samples, or a baseline mode the run dropped: neither is a pass).

``--self-test`` exercises the decision with synthetic pairs (worse, same,
better, too few samples, an outlier, a checksum change, bad input) and needs
no files.
"""
from __future__ import annotations

import argparse
import json
import os
import platform
import statistics
import sys
import tempfile
import time

SCHEMA = 1
DEFAULT_FAIL_ON = 10.0
DEFAULT_MIN_SAMPLES = 5
# "worse than 10%" must not fail on a ratio that is exactly 1.10: floating
# point makes (1.10 - 1) * 100 == 10.000000000000009.
EPS = 1e-9


class InputError(Exception):
    """A missing or malformed input file."""


def load_json(path):
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        raise InputError(f"{path}: no such file")
    except json.JSONDecodeError as e:
        raise InputError(f"{path}: not valid JSON: {e}")
    if not isinstance(data, dict):
        raise InputError(f"{path}: expected a JSON object")
    return data


def fmt_ms(ns):
    if not isinstance(ns, (int, float)) or isinstance(ns, bool):
        return "\u2014"
    ms = ns / 1e6
    if ms >= 100:
        return f"{ms:,.0f}"
    if ms >= 10:
        return f"{ms:.1f}"
    return f"{ms:.2f}"


def fmt_pct(x):
    return "\u2014" if x is None else f"{x:+.1f}%"


def fmt_ratio(x):
    return "\u2014" if x is None else f"{x:.3f}\u00d7"


def fmt_rate(x):
    return "\u2014" if x is None else f"{x:.1f}%"


def number(x):
    """A finite float, or None.  Booleans are not numbers here."""
    if isinstance(x, bool) or not isinstance(x, (int, float)):
        return None
    x = float(x)
    if x != x or x in (float("inf"), float("-inf")):
        return None
    return x


class Row:
    """One benchmark mode's paired comparison."""

    def __init__(self, mode, n, a_ns, b_ns, samples, checksums_equal, min_samples):
        self.mode = mode
        self.n = n
        self.a_ns = a_ns
        self.b_ns = b_ns
        self.samples = samples
        self.checksums_equal = checksums_equal
        self.min_samples = min_samples
        self.ratio = statistics.median(samples) if samples else None
        self.pct = (self.ratio - 1.0) * 100.0 if self.ratio is not None else None
        self.enough = len(samples) >= min_samples
        self.comparable = checksums_equal
        self.worse = False  # set by evaluate(), which knows the threshold

    @property
    def verdict(self):
        if not self.comparable:
            return "not comparable (checksum changed)"
        if not self.samples:
            return "no pairs"
        if not self.enough:
            return f"few samples ({len(self.samples)}<{self.min_samples})"
        return "REGRESSION" if self.worse else "ok"

    @property
    def gated(self):
        return self.comparable and self.enough


class Report:
    def __init__(self, rows, errors, fail_on, min_samples, has_baseline=False):
        self.rows = rows
        self.errors = errors
        self.fail_on = fail_on
        self.min_samples = min_samples
        self.has_baseline = has_baseline
        self.regressions = [r.mode for r in rows if r.worse]
        gated = [r for r in rows if r.gated]
        self.gated = gated
        self.worst = max(gated, key=lambda r: r.pct) if gated else None
        if errors:
            self.status = "error"
        elif self.regressions:
            self.status = "regress"
        elif not gated:
            self.status = "no-gate"
        else:
            self.status = "pass"

    @property
    def exit_code(self):
        # Against a baseline, "nothing could be gated" is an incomplete measurement,
        # not a pass: a night that compares nothing must not look green.
        if self.status == "no-gate" and self.has_baseline:
            return 2
        return {"error": 2, "regress": 1}.get(self.status, 0)


def mode_order(doc, ab):
    """The modes in the run's order, then any A/B-only mode."""
    results = doc.get("results")
    order = list(results) if isinstance(results, dict) else []
    for mode in ab:
        if mode not in order:
            order.append(mode)
    return order


def evaluate(doc, fail_on, min_samples, baseline=None):
    """Apply the paired-ratio rule.  Pure: no file I/O, no sys.exit."""
    errors = []
    ab = doc.get("ab")
    if not isinstance(ab, dict) or not isinstance(ab.get("results"), dict) or not ab["results"]:
        errors.append(
            "no paired A/B results (`ab.results`): run scripts/stdlib-bench.py "
            "with --baseline-bin OLD")
        return Report([], errors, fail_on, min_samples)

    results = doc.get("results") if isinstance(doc.get("results"), dict) else {}
    if baseline is not None:
        base_results = baseline.get("results") if isinstance(baseline.get("results"), dict) else {}
        # The baseline is the list of modes the run must cover: a mode that vanished
        # from the run would otherwise simply never be checked (intersecting the two
        # maps hides exactly the regression that drops it).
        run_modes = set(results) | set(ab["results"])
        for mode in sorted(base_results):
            if mode not in run_modes:
                errors.append(
                    f"{mode}: in the baseline but not in this run; a mode dropped from "
                    "the run is not a pass (update the baseline deliberately)")
                continue
            if not isinstance(results.get(mode), dict):
                continue
            got = number(results[mode].get("n"))
            want = number(base_results[mode].get("n"))
            if got is not None and want is not None and got != want:
                errors.append(
                    f"{mode}: n={int(got)}, the checked-in baseline uses n={int(want)}")

    rows = []
    for mode in mode_order(doc, ab["results"]):
        rec = ab["results"].get(mode)
        if not isinstance(rec, dict):
            continue
        raw = rec.get("samples_ratio")
        samples = []
        if isinstance(raw, list):
            samples = [float(x) for x in raw if number(x) is not None]
        fallback = number(rec.get("median_ratio"))
        checksums = rec.get("checksums_equal")
        if not isinstance(checksums, bool):
            checksums = True
        n = None
        if isinstance(results.get(mode), dict):
            n = number(results[mode].get("n"))
        row = Row(mode, int(n) if n is not None else None,
                  number(rec.get("baseline_median_ns")), number(rec.get("median_ns")),
                  samples, checksums, min_samples)
        if row.ratio is None and fallback is not None:
            row.ratio = fallback
            row.pct = (fallback - 1.0) * 100.0
        row.worse = (row.gated and row.pct is not None
                     and row.pct > fail_on + EPS)
        rows.append(row)
    return Report(rows, errors, fail_on, min_samples, has_baseline=baseline is not None)


def cpu_model():
    try:
        with open("/proc/cpuinfo", encoding="utf-8", errors="replace") as f:
            for line in f:
                if line.lower().startswith("model name"):
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return platform.processor() or "unknown"


def environment(args):
    return {
        "machine": args.machine or platform.node(),
        "runner": args.runner or os.environ.get("RUNNER_NAME", ""),
        "cpuset": args.cpuset or "all",
        "cpus": os.cpu_count(),
        "cpu_model": cpu_model(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "run_id": os.environ.get("GITHUB_RUN_ID", ""),
        "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT", ""),
        "workflow": os.environ.get("GITHUB_WORKFLOW", ""),
    }


def annotate(doc, path):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(doc, f, indent=2, sort_keys=True)
        f.write("\n")


def markdown(report, meta, scry=None):
    lines = ["", "### Standard-library A/B benchmark", ""]
    if meta.get("commit") or meta.get("branch"):
        lines.append(
            f"- commit `{meta.get('commit') or '?'}` on `{meta.get('branch') or '?'}`; "
            f"{meta.get('runs') or '?'} pairs per mode; threshold **+{report.fail_on:g}%** "
            f"on the median paired ratio; at least {report.min_samples} pairs")
    else:
        lines.append(
            f"- threshold **+{report.fail_on:g}%** on the median paired ratio; "
            f"at least {report.min_samples} pairs")
    lines.append(
        f"- machine `{meta.get('machine') or '?'}`; runner `{meta.get('runner') or '?'}`; "
        f"cpuset `{meta.get('cpuset') or 'all'}`; CPU `{meta.get('cpu_model') or '?'}`")
    lines.append("")

    if report.rows:
        lines.append("| mode | n | A (ms) | B (ms) | ratio | change | pairs | verdict |")
        lines.append("|---|---:|---:|---:|---:|---:|---:|---|")
        for r in report.rows:
            lines.append(
                f"| `{r.mode}` | {r.n if r.n is not None else '\u2014'} | "
                f"{fmt_ms(r.a_ns)} | {fmt_ms(r.b_ns)} | {fmt_ratio(r.ratio)} | "
                f"{fmt_pct(r.pct)} | {len(r.samples)} | {r.verdict} |")
        lines.append("")

    if report.status == "regress":
        names = ", ".join(f"`{m}`" for m in report.regressions)
        lines.append(
            f"**FAIL**: {len(report.regressions)} of {len(report.gated)} gated "
            f"mode(s) worse than +{report.fail_on:g}%: {names}.")
    elif report.status == "pass":
        worst = report.worst
        tail = (f" (worst: `{worst.mode}` {worst.pct:+.1f}%)" if worst else "")
        lines.append(
            f"**PASS**: no gated mode is worse than +{report.fail_on:g}%{tail}.")
    elif report.status == "no-gate":
        tail = (" With a baseline that is a failure: the run measured nothing "
                "the gate could decide." if report.has_baseline else "")
        lines.append(
            f"**NO GATE**: no mode had {report.min_samples} comparable pairs; "
            "the threshold was not applied." + tail)
    else:
        lines.append("**ERROR**: " + "; ".join(report.errors))

    if scry:
        lines.append("")
        lines.extend(scry_markdown(scry))
    return "\n".join(lines) + "\n"


def scry_markdown(scry):
    doc, exit_code = scry["doc"], scry["exit_code"]
    lines = ["### Scry taint corpus", ""]
    corpus = doc.get("corpus") if isinstance(doc.get("corpus"), dict) else {}
    overall = doc.get("overall") if isinstance(doc.get("overall"), dict) else {}
    lines.append(
        f"- status `{doc.get('status') or '?'}`"
        + (f" ({doc['reason']})" if doc.get("reason") else "")
        + f"; {corpus.get('cases', '?')} cases, {corpus.get('files', '?')} files")
    lines.append(
        f"- TP {overall.get('tp', '?')} / FN {overall.get('fn', '?')} / "
        f"TN {overall.get('tn', '?')} / FP {overall.get('fp', '?')} / "
        f"unknown {overall.get('unknown', '?')}; "
        f"TPR {fmt_rate(100 * overall.get('tpr', 0))} / "
        f"FPR {fmt_rate(100 * overall.get('fpr', 0))}")
    base = doc.get("baseline") if isinstance(doc.get("baseline"), dict) else {}
    changes = base.get("changes") if isinstance(base.get("changes"), list) else []
    lines.append(
        f"- baseline `{base.get('status', '?')}` at `{base.get('path', '?')}`, "
        f"{'matches' if base.get('matches') else 'MISMATCH'}, {len(changes)} change(s)")
    if changes:
        lines.append("")
        lines.append("| scope | name | field | before | after |")
        lines.append("|---|---|---|---|---|")
        for c in changes[:10]:
            lines.append(
                f"| `{c.get('scope', '?')}` | `{c.get('name', '?')}` | "
                f"`{c.get('field', '?')}` | `{c.get('before', '?')}` | "
                f"`{c.get('after', '?')}` |")
    if exit_code not in (None, 0):
        lines.append("")
        lines.append("**FAIL**: `scry bench --fail-on-regression` exited "
                     f"{exit_code}; the corpus metrics changed.")
    else:
        lines.append("")
        lines.append("**PASS**: the Scry corpus matches the checked-in baseline.")
    return lines


def history_entry(report, meta, doc, scry=None, baseline=None):
    entry = {
        "schema": SCHEMA,
        "created": doc.get("created") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "recorded": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "commit": doc.get("commit") or "",
        "branch": doc.get("branch") or "",
        "baseline_commit": (baseline or {}).get("commit") or "",
        "baseline_reps": (baseline or {}).get("reps"),
        "machine": meta.get("machine") or "",
        "runner": meta.get("runner") or "",
        "cpuset": meta.get("cpuset") or "all",
        "run_id": meta.get("run_id") or "",
        "run_attempt": meta.get("run_attempt") or "",
        "runs": meta.get("runs"),
        "fail_on": report.fail_on,
        "min_samples": report.min_samples,
        "status": report.status,
        "modes": len(report.rows),
        "gated": len(report.gated),
        "regressions": report.regressions,
        "worst": ({"mode": report.worst.mode, "ratio": round(report.worst.ratio, 6),
                   "pct": round(report.worst.pct, 3)} if report.worst else None),
        "errors": report.errors,
    }
    if scry:
        d = scry["doc"]
        base = d.get("baseline") if isinstance(d.get("baseline"), dict) else {}
        entry["scry"] = {
            "status": d.get("status") or "",
            "exit": scry["exit_code"],
            "matches": bool(base.get("matches")),
            "changes": len(base.get("changes") or []),
            "cases": (d.get("corpus") or {}).get("cases"),
        }
    return entry


def append_history(path, entry):
    parent = os.path.dirname(os.path.abspath(path))
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps(entry, sort_keys=True, separators=(",", ":")) + "\n")


def print_sizes(baseline):
    results = baseline.get("results") if isinstance(baseline.get("results"), dict) else {}
    if not results:
        raise InputError("baseline has no results")
    for mode in sorted(results):
        n = number(results[mode].get("n"))
        if n is None:
            raise InputError(f"baseline: {mode} has no size n")
        print(f"{mode}={int(n)}")


def _synth(ratios, checksums_equal=True, n=1000):
    med = statistics.median(ratios) if ratios else 1.0
    return {
        "created": "2026-01-01T00:00:00Z",
        "commit": "0" * 40,
        "branch": "master",
        "results": {"m": {"n": n, "median_ns": 1_000_000, "checksum": "1"}},
        "ab": {"results": {"m": {
            "samples_ratio": list(ratios),
            "median_ratio": med,
            "baseline_median_ns": 1_000_000,
            "median_ns": int(1_000_000 * med),
            "checksums_equal": checksums_equal,
        }}},
    }


def self_test():
    cases = []

    def case(name):
        def wrap(fn):
            cases.append((name, fn))
            return fn
        return wrap

    @case("worse: median +20% over 15 pairs")
    def _():
        r = evaluate(_synth([1.20] * 15), 10, 5)
        assert r.status == "regress", r.status
        assert r.regressions == ["m"], r.regressions
        assert r.exit_code == 1, r.exit_code

    @case("same: median 1.00 over 15 pairs")
    def _():
        r = evaluate(_synth([0.98, 1.02] * 7 + [1.0]), 10, 5)
        assert r.status == "pass", r.status
        assert abs(r.worst.pct) < 1e-9, r.worst.pct
        assert r.exit_code == 0, r.exit_code

    @case("better: median -20% over 15 pairs")
    def _():
        r = evaluate(_synth([0.80] * 15), 10, 5)
        assert r.status == "pass", r.status
        assert abs(r.worst.pct + 20.0) < 1e-9, r.worst.pct
        assert r.exit_code == 0, r.exit_code

    @case("too few: +50% but only 2 pairs")
    def _():
        r = evaluate(_synth([1.50] * 2), 10, 5)
        assert r.status == "no-gate", r.status
        assert r.regressions == [], r.regressions
        assert r.rows[0].verdict.startswith("few samples"), r.rows[0].verdict
        # no baseline: there is nothing to be green about, so this is not a failure
        assert r.exit_code == 0, r.exit_code

    @case("too few with a baseline: no-gate exits 2")
    def _():
        base = {"results": {"m": {"n": 1000}}}
        r = evaluate(_synth([1.50] * 2), 10, 5, baseline=base)
        assert r.status == "no-gate", r.status
        assert r.has_baseline, r.has_baseline
        assert r.exit_code == 2, r.exit_code
        text = markdown(r, {"machine": "m", "runner": "r"})
        assert "With a baseline that is a failure" in text, text

    @case("dropped mode: a baseline mode missing from the run is an error")
    def _():
        base = {"results": {"m": {"n": 1000}, "gone": {"n": 1000}}}
        r = evaluate(_synth([1.0] * 15), 10, 5, baseline=base)
        assert r.status == "error", r.status
        assert any("gone" in e and "not in this run" in e for e in r.errors), r.errors
        assert r.exit_code == 2, r.exit_code

    @case("dropped mode: a run of other modes only does not hide it")
    def _():
        doc = _synth([1.0] * 15)
        doc["results"] = {"other": {"n": 1000, "median_ns": 1_000_000, "checksum": "1"}}
        doc["ab"]["results"] = {"other": doc["ab"]["results"]["m"]}
        base = {"results": {"m": {"n": 1000}}}
        r = evaluate(doc, 10, 5, baseline=base)
        assert r.status == "error", r.status
        assert any("m:" in e and "not in this run" in e for e in r.errors), r.errors
        assert r.exit_code == 2, r.exit_code

    @case("boundary: exactly +10% does not exceed +10%")
    def _():
        r = evaluate(_synth([1.10] * 15), 10, 5)
        assert r.status == "pass", r.status
        assert r.exit_code == 0, r.exit_code

    @case("outlier: one +50% pair among 15 does not move the median")
    def _():
        r = evaluate(_synth([1.0] * 14 + [1.5]), 10, 5)
        assert r.status == "pass", r.status
        assert r.exit_code == 0, r.exit_code

    @case("checksum change: not comparable, not gated")
    def _():
        r = evaluate(_synth([1.50] * 15, checksums_equal=False), 10, 5)
        assert r.status == "no-gate", r.status
        assert r.rows[0].verdict.startswith("not comparable"), r.rows[0].verdict
        assert r.exit_code == 0, r.exit_code

    @case("no ab results: input error")
    def _():
        doc = {"results": {"m": {"n": 1000}}, "ab": {"results": {}}}
        r = evaluate(doc, 10, 5)
        assert r.status == "error", r.status
        assert r.exit_code == 2, r.exit_code

    @case("size mismatch: input error")
    def _():
        base = {"results": {"m": {"n": 999}}}
        r = evaluate(_synth([1.0] * 15), 10, 5, baseline=base)
        assert r.status == "error", r.status
        assert any("n=" in e for e in r.errors), r.errors

    @case("history: one JSON line per run")
    def _():
        r = evaluate(_synth([1.20] * 15), 10, 5)
        meta = {"machine": "m", "runner": "r", "cpuset": "2-3", "runs": 15}
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "history.jsonl")
            append_history(path, history_entry(r, meta, _synth([])))
            append_history(path, history_entry(r, meta, _synth([])))
            with open(path, encoding="utf-8") as f:
                lines = f.read().splitlines()
        assert len(lines) == 2, len(lines)
        first = json.loads(lines[0])
        assert first["schema"] == SCHEMA, first
        assert first["status"] == "regress", first
        assert first["regressions"] == ["m"], first

    @case("markdown: table and verdict")
    def _():
        r = evaluate(_synth([1.20] * 15), 10, 5)
        text = markdown(r, {"machine": "m", "runner": "r", "cpuset": "0-3",
                            "runs": 15, "commit": "abc", "branch": "master"})
        assert "| mode | n |" in text, text
        assert "**FAIL**" in text, text
        assert "`m`" in text, text

    passed = 0
    for name, fn in cases:
        try:
            fn()
        except AssertionError as e:
            print(f"FAIL  {name}: {e}")
        else:
            print(f"ok    {name}")
            passed += 1
    print(f"self-test: {passed}/{len(cases)} passed")
    return 0 if passed == len(cases) else 1


def main(argv=None):
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", help="JSON written by scripts/stdlib-bench.py")
    ap.add_argument("--baseline", help="checked-in bench/stdlib-baseline.json")
    ap.add_argument("--fail-on", type=float, default=DEFAULT_FAIL_ON,
                    help=f"regression threshold in percent (default {DEFAULT_FAIL_ON:g})")
    ap.add_argument("--min-samples", type=int, default=DEFAULT_MIN_SAMPLES,
                    help=f"pairs a mode needs before it is gated (default {DEFAULT_MIN_SAMPLES})")
    ap.add_argument("--runs", type=int, help="pairs per mode, recorded in the history")
    ap.add_argument("--machine", help="machine id recorded in the JSON and history")
    ap.add_argument("--runner", help="runner label recorded in the history")
    ap.add_argument("--cpuset", help="CPU affinity of the measurement")
    ap.add_argument("--annotate-json", action="store_true",
                    help="write the environment object into the --json file")
    ap.add_argument("--markdown", metavar="FILE",
                    help="append the Markdown table to FILE (e.g. $GITHUB_STEP_SUMMARY)")
    ap.add_argument("--history", metavar="FILE",
                    help="append one JSON line to FILE (bench/history.jsonl)")
    ap.add_argument("--scry", metavar="FILE",
                    help="JSON written by scry bench --json (reported, not gated)")
    ap.add_argument("--scry-exit", type=int, default=None,
                    help="scry bench's exit status (recorded and reported)")
    ap.add_argument("--print-sizes", action="store_true",
                    help="print the baseline's MODE=N lines and exit")
    ap.add_argument("--self-test", action="store_true",
                    help="exercise the rule with synthetic pairs and exit")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    try:
        if args.print_sizes:
            if not args.baseline:
                raise InputError("--print-sizes needs --baseline")
            print_sizes(load_json(args.baseline))
            return 0
        if not args.json:
            raise InputError("--json is required")
        if args.fail_on < 0:
            raise InputError("--fail-on must not be negative")
        if args.min_samples < 1:
            raise InputError("--min-samples must be at least 1")

        doc = load_json(args.json)
        baseline = load_json(args.baseline) if args.baseline else None
        scry = None
        if args.scry:
            scry = {"doc": load_json(args.scry), "exit_code": args.scry_exit}
        meta = environment(args)
        if args.runs is not None:
            meta["runs"] = args.runs
        meta["commit"] = doc.get("commit") or ""
        meta["branch"] = doc.get("branch") or ""

        if args.annotate_json:
            doc["environment"] = meta
            annotate(doc, args.json)

        report = evaluate(doc, args.fail_on, args.min_samples, baseline)
        text = markdown(report, meta, scry)
        sys.stdout.write(text)
        if args.markdown:
            parent = os.path.dirname(os.path.abspath(args.markdown))
            if parent:
                os.makedirs(parent, exist_ok=True)
            with open(args.markdown, "a", encoding="utf-8") as f:
                f.write(text)
        if args.history:
            append_history(args.history,
                           history_entry(report, meta, doc, scry, baseline))

        if os.environ.get("GITHUB_ACTIONS") == "true":
            if report.status == "regress":
                names = ", ".join(report.regressions)
                print(f"::error title=performance regression::"
                      f"{len(report.regressions)} mode(s) worse than "
                      f"+{report.fail_on:g}%: {names}")
            elif report.status == "error":
                print("::error title=bench threshold input::" + "; ".join(report.errors))
            elif report.status == "no-gate":
                if report.has_baseline:
                    print("::error title=bench: no gate::"
                          f"no mode had {report.min_samples} comparable pairs and a "
                          "baseline was given; the run measured nothing to gate")
                else:
                    print("::warning title=bench: too few samples::"
                          f"no mode had {report.min_samples} comparable pairs; "
                          "the threshold was not applied")
        return report.exit_code
    except InputError as e:
        print(f"bench-threshold: {e}", file=sys.stderr)
        if os.environ.get("GITHUB_ACTIONS") == "true":
            print(f"::error title=bench threshold input::{e}")
        return 2
    except Exception as e:  # a bug or an unexpected shape, not a regression
        print(f"bench-threshold: {type(e).__name__}: {e}", file=sys.stderr)
        if os.environ.get("GITHUB_ACTIONS") == "true":
            print(f"::error title=bench threshold error::{type(e).__name__}: {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
