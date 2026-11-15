#!/usr/bin/env python3
"""Merge the per-file SARIF logs and JSON reports from scan.sh.

Each `scry taint` run writes a complete SARIF log: in diff mode it keeps results on
unchanged lines with `baselineState: unchanged` so an upload cannot mark a pre-existing
alert as fixed. This script unions the `results` arrays (one run per file would make
GitHub reject the log) and counts what was shown, suppressed and unlocated.

Usage:
  merge.py --out-sarif OUT --out-counts COUNTS --out-summary SUMMARY
           --base BASE [--inputs DIR] [--empty]
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import sys

SCHEMA = (
    "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/"
    "Schemata/sarif-schema-2.1.0.json"
)


def die(message: str) -> None:
    print(f"scry: error: {message}", file=sys.stderr)
    raise SystemExit(1)


def numbered(directory: str, suffix: str) -> list[str]:
    paths = glob.glob(os.path.join(directory, f"*{suffix}"))
    return sorted(
        (p for p in paths if re.fullmatch(r"\d+", os.path.basename(p)[: -len(suffix)])),
        key=lambda p: int(os.path.basename(p).split(".", 1)[0]),
    )


def empty_tally() -> dict[str, int]:
    return {"shown": 0, "suppressed": 0, "unlocated": 0}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-sarif", required=True)
    ap.add_argument("--out-counts", required=True)
    ap.add_argument("--out-summary", required=True)
    ap.add_argument("--base", required=True)
    ap.add_argument("--inputs", default="")
    ap.add_argument("--empty", action="store_true")
    args = ap.parse_args()

    inputs = args.inputs or os.path.dirname(os.path.abspath(args.out_counts))
    sarif_paths = numbered(inputs, ".sarif")
    json_paths = numbered(inputs, ".json")
    if not args.empty and len(sarif_paths) != len(json_paths):
        die(
            f"{len(json_paths)} JSON report(s) but {len(sarif_paths)} SARIF log(s): "
            "an analysis step did not complete"
        )

    filtered = args.base != "all"
    total = {"findings": empty_tally(), "boundary": empty_tally(), "memory": empty_tally()}
    results: list[dict] = []
    rules: list[dict] = []
    rule_ids: set[str] = set()
    truncated = False
    parse_errors = 0
    rows: list[tuple[str, dict, dict, dict, bool]] = []

    for path in json_paths:
        try:
            with open(path, encoding="utf-8") as fh:
                report = json.load(fh)
        except (OSError, json.JSONDecodeError) as exc:
            die(f"cannot read {path}: {exc}")
        name = report.get("file", os.path.basename(path))
        diff = report.get("diff")
        tally = {}
        for category in ("findings", "boundary", "memory"):
            if diff:
                tally[category] = diff.get(category, empty_tally())
            else:
                count = int(report.get("counts", {}).get(category, 0))
                tally[category] = {"shown": count, "suppressed": 0, "unlocated": 0}
            for key in ("shown", "suppressed", "unlocated"):
                total[category][key] += int(tally[category].get(key, 0))
        truncated = truncated or bool(report.get("truncated"))
        parse_errors += int(report.get("parseErrors", 0))
        rows.append((name, tally["findings"], tally["boundary"], tally["memory"], bool(diff)))

    for path in sarif_paths:
        try:
            with open(path, encoding="utf-8") as fh:
                log = json.load(fh)
        except (OSError, json.JSONDecodeError) as exc:
            die(f"cannot read {path}: {exc} (the upload step must never see this file)")
        runs = log.get("runs")
        if not isinstance(runs, list) or not runs:
            die(f"{path}: no SARIF runs")
        if log.get("version") != "2.1.0":
            die(f"{path}: SARIF version is not 2.1.0")
        for run in runs:
            driver = run.get("tool", {}).get("driver", {})
            for rule in driver.get("rules", []) or []:
                rid = rule.get("id")
                if rid and rid not in rule_ids:
                    rule_ids.add(rid)
                    rules.append(rule)
            results.extend(run.get("results", []) or [])

    driver: dict = {"name": "scry", "version": "0.1.0", "rules": rules}
    if results:
        first = None
        for path in sarif_paths:
            with open(path, encoding="utf-8") as fh:
                first = json.load(fh)["runs"][0]
            break
        if first:
            driver = dict(first.get("tool", {}).get("driver", driver))
            driver["rules"] = rules
    sarif = {
        "$schema": SCHEMA,
        "version": "2.1.0",
        "runs": [{"tool": {"driver": driver}, "columnKind": "utf16CodeUnits", "results": results}],
    }
    os.makedirs(os.path.dirname(os.path.abspath(args.out_sarif)), exist_ok=True)
    with open(args.out_sarif, "w", encoding="utf-8") as fh:
        json.dump(sarif, fh, separators=(",", ":"))
        fh.write("\n")

    gate = sum(
        total[c]["shown"] + total[c]["unlocated"] for c in ("findings", "boundary", "memory")
    )
    counts = {
        "base": args.base,
        "filtered": filtered,
        "empty": args.empty,
        "files": len(rows),
        "findings": total["findings"],
        "boundary": total["boundary"],
        "memory": total["memory"],
        "gate": gate,
        "results": len(results),
        "sarif": args.out_sarif,
        "truncated": truncated,
        "parseErrors": parse_errors,
    }
    with open(args.out_counts, "w", encoding="utf-8") as fh:
        json.dump(counts, fh)
        fh.write("\n")

    lines: list[str] = ["## Scry", ""]
    if args.empty:
        where = "the whole tree" if not filtered else f"`{args.base}`"
        lines += [
            f"No C files to analyse against {where}. Nothing was uploaded: an empty "
            "SARIF would mark every existing alert as fixed.",
            "",
        ]
    else:
        label = "whole tree (no diff filter)" if not filtered else f"diff `{args.base}`"
        shown_head = "reported (shown)" if not filtered else "introduced (shown)"
        lines += [
            f"{len(rows)} C file(s) analysed, {label}.",
            "",
            f"| | {shown_head} | unchanged (suppressed) | no source line |",
            "|---|---:|---:|---:|",
        ]
        for label, key in (
            ("findings", "findings"),
            ("lowering warnings", "boundary"),
            ("memory warnings", "memory"),
        ):
            t = total[key]
            lines.append(
                f"| {label} | {t['shown']} | {t['suppressed']} | {t['unlocated']} |"
            )
        lines += [
            "",
            f"**{gate} result(s) {'on changed lines' if filtered else 'reported'}**; "
            f"{sum(total[c]['suppressed'] for c in total)} suppressed as pre-existing.",
            "",
        ]
        if rows:
            lines.append("<details><summary>Files</summary>")
            lines.append("")
            lines.append("| file | findings | warnings | suppressed |")
            lines.append("|---|---:|---:|---:|")
            for name, find, bound, mem, _ in rows:
                warnings = bound["shown"] + bound["unlocated"] + mem["shown"] + mem["unlocated"]
                suppressed = find["suppressed"] + bound["suppressed"] + mem["suppressed"]
                if not (find["shown"] or warnings or suppressed):
                    continue
                lines.append(f"| `{name}` | {find['shown']} | {warnings} | {suppressed} |")
            lines += ["", "</details>", ""]
        if truncated:
            lines += [
                "> A fixpoint or the CST limit truncated at least one analysis; the "
                "report is partial (`scry/budget/*`).",
                "",
            ]
        if parse_errors:
            lines += [
                f"> {parse_errors} parse error node(s) were recovered with "
                "`allow-errors`; findings in those files are approximate.",
                "",
            ]
        if filtered:
            lines += [
                "> scry reports **introduced** results: findings whose sink, or a path "
                "step, is on a line this diff changes. No introduced finding is not "
                "proof the analysed code has none: the suppressed count above is the "
                "rest of this run's results.",
                "",
            ]
        else:
            lines += [
                "> No diff filter was applied: this is every result scry found for the "
                "analysed files. It is a may-analysis over a C subset, so a clean run "
                "is not proof of absence.",
                "",
            ]
        lines += [
            "> The analysis is C only and one translation unit at a time; a changed "
            "header alone is not analysed.",
            "",
        ]
    with open(args.out_summary, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
