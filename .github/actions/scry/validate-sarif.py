#!/usr/bin/env python3
"""Reject a SARIF log that must not be uploaded.

`github/codeql-action/upload-sarif` is happy to receive a syntactically valid but empty
file; uploading one would tell code scanning that every previous alert in the category
is fixed. This guard runs before the upload step and fails loudly on the three cases
that produce such a file: missing, empty (a truncated write, or `: > out.sarif`), and
invalid/foreign JSON.
"""
from __future__ import annotations

import json
import os
import sys


def die(message: str) -> None:
    print(f"scry: refusing to upload SARIF: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> int:
    if len(sys.argv) != 2:
        die("usage: validate-sarif.py FILE")
    path = sys.argv[1]
    try:
        size = os.path.getsize(path)
    except OSError as exc:
        die(f"{path}: {exc.strerror}")
    if size == 0:
        die(f"{path} is empty")
    try:
        with open(path, encoding="utf-8") as fh:
            log = json.load(fh)
    except json.JSONDecodeError as exc:
        die(f"{path} is not JSON: {exc}")
    except OSError as exc:
        die(f"{path}: {exc.strerror}")

    if not isinstance(log, dict):
        die(f"{path} is not a SARIF object")
    if log.get("version") != "2.1.0":
        die(f"{path} has version {log.get('version')!r}, not '2.1.0'")
    runs = log.get("runs")
    if not isinstance(runs, list) or not runs:
        die(f"{path} has no runs")
    for i, run in enumerate(runs):
        if not isinstance(run, dict):
            die(f"{path}: run {i} is not an object")
        driver = run.get("tool", {}).get("driver")
        if not isinstance(driver, dict) or not driver.get("name"):
            die(f"{path}: run {i} has no tool.driver.name")
        if not isinstance(run.get("results", []), list):
            die(f"{path}: run {i} results is not an array")
    print(f"scry: SARIF ok ({size} bytes, {len(runs)} run(s), "
          f"{sum(len(r.get('results', [])) for r in runs)} result(s))")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
