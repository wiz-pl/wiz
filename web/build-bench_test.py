#!/usr/bin/env python3
"""Tests for ``web/build-bench.py``.

The generator is tested against synthetic fixture trees, never the real data, so a
change to the checked-in JSON does not make the tests fail (the page's freshness is a
separate check: ``web/build-bench.py --check``).  Covered: an empty data set, one row,
missing fields, a single-sample run, and the ``--check`` no-op and stale cases.

    python3 web/build-bench_test.py
"""
from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True  # keep the checkout clean when loading build-bench.py

HERE = os.path.dirname(os.path.abspath(__file__))


def _load_generator():
    path = os.path.join(HERE, "build-bench.py")
    spec = importlib.util.spec_from_file_location("build_bench", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


bb = _load_generator()


def stdlib(created="2026-01-02T03:04:05Z", host="fixture-host", reps=3,
           results=None, ab=None):
    doc = {
        "schema": 1,
        "created": created,
        "generator": "scripts/stdlib-bench.py",
        "commit": "0123456789abcdef0123456789abcdef01234567",
        "branch": "fixture",
        "host": host,
        "reps": reps,
        "warmup": 1,
        "results": results if results is not None else {},
    }
    if ab is not None:
        doc["ab"] = {"baseline_bin": "bench/.build/bench-base", "results": ab}
    return doc


def mode_record(median_ns, samples, n=1000, checksum="1", cv=0.05):
    return {
        "mode": "array-fold", "n": n, "checksum": checksum,
        "median_ns": median_ns, "mean_ns": median_ns,
        "min_ns": min(samples), "max_ns": max(samples),
        "samples_ns": samples, "cv": cv, "spread": 0.1,
        "variance_ns2": 1.0, "stdev_ns": 1.0,
    }


EMPTY_A = stdlib(results={})
EMPTY_B = stdlib(results={})
EMPTY_SCRY = {"format": "scry-bench-baseline", "version": 1, "cases": [],
              "overall": {}, "per_cwe": []}

ONE_A = stdlib(results={
    "array-fold": mode_record(20_000_000, [20_000_000, 21_000_000, 19_000_000]),
})
ONE_B = stdlib(results={
    "array-fold": mode_record(15_000_000, [15_000_000, 15_500_000, 14_500_000]),
}, ab={
    "array-fold": {
        "baseline_median_ns": 20_000_000,
        "median_ns": 15_000_000,
        "median_ratio": 0.75,
        "min_ratio": 0.70,
        "max_ratio": 0.80,
        "samples_ratio": [0.80, 0.75, 0.70],
        "checksums_equal": True,
    },
})

ONE_SCRY = {
    "format": "scry-bench-baseline", "version": 1, "corpus": "bench/corpus",
    "cases": [
        {"id": "s0/one", "expect": "unsafe", "outcome": "tp", "findings": 1,
         "expected": 1, "matched": 1, "extra": 0, "boundary": 2,
         "blocking_boundary": 1, "unknown": False},
        {"id": "s0/two", "expect": "safe", "outcome": "tn", "findings": 0,
         "boundary": 0, "blocking_boundary": 0},
    ],
    "overall": {
        "tp": 1, "fn": 0, "tn": 1, "fp": 0, "unknown": 0, "error": 0, "skipped": 0,
        "tpr": 1.0, "tpr_bp": 10000, "tpr_defined": True,
        "fpr": 0.0, "fpr_bp": 0, "fpr_defined": True,
        "youden": 1.0, "youden_bp": 10000, "youden_defined": True,
        "precision": 1.0, "f1": 1.0,
    },
    "per_cwe": [{
        "name": "CWE-78",
        "metrics": {
            "tp": 1, "fn": 0, "tn": 1, "fp": 0, "unknown": 0, "error": 0,
            "skipped": 0, "tpr": 1.0, "tpr_bp": 10000, "tpr_defined": True,
            "fpr": 0.0, "fpr_bp": 0, "fpr_defined": False,
            "youden": 1.0, "youden_bp": 10000, "youden_defined": False,
            "precision": 1.0,
        },
        "findings": 1, "valid_paths": 1, "checked": 1,
    }],
    "path_validity": {"findings": 2, "valid_paths": 2, "reach_sink": 2},
    "certificate": {"findings": 2, "checked": 2},
}


class Fixture(unittest.TestCase):
    def root(self, a=None, b=None, scry=None):
        root = tempfile.mkdtemp(prefix="bench-page-")
        self.addCleanup(_rmtree, root)
        for rel, data in (
            (os.path.join("bench", "stdlib-baseline.json"), a),
            (os.path.join("bench", "stdlib-bench.json"), b),
            (os.path.join("scry", "bench", "baseline.json"), scry),
        ):
            if data is None:
                continue
            path = os.path.join(root, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f)
        return root

    def render(self, a, b, scry):
        return bb.render(self.root(a, b, scry))


def _rmtree(path):
    import shutil
    shutil.rmtree(path, ignore_errors=True)


class EmptyData(Fixture):
    def test_empty_tables_are_labelled(self):
        page = self.render(EMPTY_A, EMPTY_B, EMPTY_SCRY)
        self.assertIn("no results recorded", page)
        self.assertIn("The baseline records no cases.", page)
        self.assertTrue(page.startswith("<!doctype html>"))
        self.assertTrue(page.rstrip().endswith("</html>"))

    def test_render_is_deterministic(self):
        first = self.render(EMPTY_A, EMPTY_B, EMPTY_SCRY)
        second = self.render(EMPTY_A, EMPTY_B, EMPTY_SCRY)
        self.assertEqual(first, second)

    def test_absent_results_object_is_empty(self):
        page = self.render({}, {}, {})
        self.assertIn("no results recorded", page)
        self.assertIn("not recorded", page)


class OneRow(Fixture):
    def test_ab_row_and_delta(self):
        page = self.render(ONE_A, ONE_B, ONE_SCRY)
        self.assertIn("<td>20.0 ms</td>", page)
        self.assertIn("<td>15.0 ms</td>", page)
        self.assertIn("-25.0%", page)          # (15 - 20) / 20
        self.assertIn("0.750×", page)
        self.assertIn("0.700–0.800×", page)
        self.assertIn("<td>same</td>", page)

    def test_provenance_is_shown(self):
        page = self.render(ONE_A, ONE_B, ONE_SCRY)
        self.assertIn("2026-01-02T03:04:05Z", page)
        self.assertIn("fixture-host", page)
        self.assertIn("0123456789abcdef", page)

    def test_scry_metrics(self):
        page = self.render(ONE_A, ONE_B, ONE_SCRY)
        self.assertIn("100.00%", page)         # TPR from basis points
        self.assertIn("2 (1 blocking in 1 cases)", page)
        self.assertIn("<td>CWE-78</td>", page)
        # fpr_defined/youden_defined false renders as an em dash, not 0.00%.
        self.assertIn("<td>—</td>", page)

    def test_interleaved_caption_is_explicit(self):
        page = self.render(ONE_A, ONE_B, ONE_SCRY)
        self.assertIn("interleaved samples", page)

    def test_medians_only_when_no_ab(self):
        b = stdlib(results={
            "array-fold": mode_record(15_000_000, [15_000_000, 15_500_000]),
        })
        page = self.render(ONE_A, b, ONE_SCRY)
        self.assertIn("not interleaved", page)


class MissingFields(Fixture):
    def test_missing_median_and_cv(self):
        a = stdlib(results={"array-fold": {"n": 10, "samples_ns": [1, 2, 3]}})
        b = stdlib(results={"array-fold": {"n": 10, "samples_ns": [1, 2, 3]}})
        page = self.render(a, b, EMPTY_SCRY)
        self.assertIn("—", page)
        self.assertIn("no results recorded", page)  # the Scry table is empty

    def test_missing_ab_range(self):
        b = stdlib(results={"array-fold": mode_record(1_000_000, [1_000_000])},
                   ab={"array-fold": {"baseline_median_ns": 2_000_000,
                                      "median_ns": 1_000_000,
                                      "median_ratio": 0.5,
                                      "checksums_equal": False}})
        page = self.render(ONE_A, b, ONE_SCRY)
        self.assertIn("0.500×", page)
        self.assertIn("changed", page)  # checksums_equal false is called out
        self.assertIn("Not like-for-like", page)

    def test_missing_created_and_host(self):
        a = {"results": {}}
        b = {"results": {}}
        page = self.render(a, b, EMPTY_SCRY)
        self.assertIn("not recorded", page)

    def test_missing_file_is_an_error(self):
        root = tempfile.mkdtemp(prefix="bench-page-")
        self.addCleanup(_rmtree, root)
        with self.assertRaises(SystemExit) as caught:
            bb.render(root)
        self.assertIn("bench/stdlib-baseline.json", str(caught.exception))


class SingleRun(Fixture):
    def test_one_sample_is_labelled(self):
        a = stdlib(reps=1, results={"array-fold": mode_record(10, [10])})
        b = stdlib(reps=1, results={"array-fold": mode_record(10, [10])})
        page = self.render(a, b, EMPTY_SCRY)
        self.assertIn("single run", page)

    def test_one_side_single_is_labelled(self):
        b = stdlib(reps=1, results={"array-fold": mode_record(10, [10])})
        page = self.render(ONE_A, b, EMPTY_SCRY)
        self.assertIn("single run", page)


class CheckMode(Fixture):
    def setUp(self):
        self.tree = self.root(ONE_A, ONE_B, ONE_SCRY)
        self.out = os.path.join(self.tree, "web", "bench", "index.html")
        os.makedirs(os.path.dirname(self.out), exist_ok=True)

    def run_main(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = bb.main(["--root", self.tree, "--out", self.out, *args])
        return status, out.getvalue() + err.getvalue()

    def test_write_then_check_is_a_noop(self):
        status, _ = self.run_main()
        self.assertEqual(status, 0)
        self.assertTrue(os.path.exists(self.out))
        status, output = self.run_main("--check")
        self.assertEqual(status, 0)
        self.assertIn("up to date", output)

    def test_stale_page_fails_check(self):
        self.assertEqual(self.run_main()[0], 0)
        with open(self.out, "a", encoding="utf-8") as f:
            f.write("<!-- hand edit -->\n")
        status, output = self.run_main("--check")
        self.assertEqual(status, 1)
        self.assertIn("stale", output)

    def test_missing_page_fails_check(self):
        status, output = self.run_main("--check")
        self.assertEqual(status, 1)
        self.assertIn("missing", output)

    def test_check_writes_nothing(self):
        self.assertEqual(self.run_main()[0], 0)
        before = os.path.getmtime(self.out)
        self.assertEqual(self.run_main("--check")[0], 0)
        self.assertEqual(os.path.getmtime(self.out), before)


if __name__ == "__main__":
    unittest.main(verbosity=2)
