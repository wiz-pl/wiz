"""Tests for the static notebook exporter (no Jupyter, no kernel).

Run from a checkout::

    python3 -m unittest discover -s tools/jupyter/tests -v

These tests are pure Python: they read checked-in fixture notebooks and compare
the rendered text.  The ``--check`` case exports the tour in ``docs/notebooks/``
(its page is generated for the site, not committed) and checks it against a
second render.
"""

from __future__ import annotations

import contextlib
import io
import json
import os
import re
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOL_DIR = HERE.parent
ROOT = TOOL_DIR.parent.parent
if str(TOOL_DIR) not in sys.path:
    sys.path.insert(0, str(TOOL_DIR))

from wiz_kernel import export  # noqa: E402

FIXTURES = HERE / "fixtures"


def render(name: str, fmt: str = "html") -> str:
    return export.render(export.load_notebook(FIXTURES / name), fmt)


class ExporterHtmlTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.html = render("mixed.ipynb")

    def test_markdown_cell(self):
        self.assertIn("<strong>bold</strong>", self.html)
        self.assertIn("<code>inline code</code>", self.html)
        self.assertIn('<a href="https://example.com">link</a>', self.html)
        self.assertIn('<code class="language-wiz">def f (n : Nat) : Nat := n + 1</code>',
                      self.html)

    def test_code_and_stream_output(self):
        self.assertIn('<code class="language-wiz">def answer : Nat := 41 + 1', self.html)
        self.assertIn('<pre class="output stream stream-stdout">42', self.html)
        self.assertIn("In&nbsp;[2]:", self.html)

    def test_execute_result_and_error(self):
        self.assertIn('<span class="prompt out-prompt">Out&nbsp;[3]:</span>', self.html)
        self.assertIn('<pre class="output-text">42</pre>', self.html)
        self.assertIn("WizError: type mismatch", self.html)
        self.assertIn("expected Nat, got Bool", self.html)
        # the traceback's lines stay separate
        self.assertIn("def bad : Nat := true\n", self.html)
        self.assertIn("\n                    ^", self.html)

    def test_html_output_is_sanitised(self):
        self.assertIn('<div class="output-html"><div class="wiz-scry">', self.html)
        self.assertIn("command-injection", self.html)
        self.assertNotIn("<script", self.html.lower())
        self.assertNotIn("<iframe", self.html.lower())
        self.assertNotIn("window.pwned", self.html)
        self.assertNotIn("javascript:", self.html.lower())

    def test_self_contained(self):
        lower = self.html.lower()
        self.assertNotIn("<script", lower)
        self.assertNotIn("<link", lower)
        self.assertNotIn('src="http', lower)
        self.assertNotIn("@import", lower)
        self.assertNotIn("<iframe", lower)
        self.assertNotIn("srcdoc", lower)

    def test_widget_note_and_static_widget(self):
        self.assertIn("Interactive widget not exported.", self.html)
        self.assertIn('<div class="widget-title">Panel</div>', self.html)
        self.assertIn("<b>n + 0 = n</b>", self.html)
        self.assertIn("⊢ Nat", self.html)
        self.assertIn("<b>static plot</b>", self.html)
        self.assertNotIn("window.pwned", self.html)

    def test_no_output_cell_has_no_output_container(self):
        html = render("no-output.ipynb")
        self.assertNotIn('<div class="cell-outputs">', html)
        self.assertNotIn('<div class="output-note">', html)
        self.assertIn("def quiet : Nat := 0", html)

    def test_deterministic(self):
        first = render("mixed.ipynb")
        second = render("mixed.ipynb")
        self.assertEqual(first, second)
        self.assertNotRegex(first, r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}")


class ExporterMarkdownTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.markdown = render("mixed.ipynb", "md")

    def test_cells_and_outputs(self):
        self.assertIn("```wiz\ndef answer : Nat := 41 + 1\n```", self.markdown)
        self.assertIn("<!-- stdout -->\n```text\n42\n```", self.markdown)
        self.assertIn("**Out[3]**", self.markdown)
        self.assertIn("**WizError**: type mismatch", self.markdown)
        self.assertIn("expected Nat, got Bool", self.markdown)

    def test_widgets(self):
        self.assertIn("Interactive output not exported.", self.markdown)
        self.assertIn("**Panel**", self.markdown)
        self.assertIn("<b>n + 0 = n</b>", self.markdown)
        self.assertNotIn("<script", self.markdown.lower())
        self.assertNotIn("<iframe", self.markdown.lower())

    def test_not_an_html_page(self):
        self.assertNotIn("<!doctype html>", self.markdown.lower())
        self.assertTrue(self.markdown.startswith("<!-- wiz nb export: mixed.ipynb -->"))

    def test_deterministic(self):
        self.assertEqual(self.markdown, render("mixed.ipynb", "md"))


class SanitizerTest(unittest.TestCase):
    def test_active_content_is_removed(self):
        cleaned = export.sanitize_html(
            '<b onclick="x()">ok</b><script>alert(1)</script>'
            '<style>body{display:none}</style>'
            '<a href="javascript:alert(1)">bad</a>'
            '<img src="https://example.com/a.png">'
            '<img src="data:image/png;base64,AAAA">')
        self.assertIn("<b>ok</b>", cleaned)
        self.assertIn('<a>bad</a>', cleaned)
        self.assertIn('src="data:image/png;base64,AAAA"', cleaned)
        self.assertNotIn("onclick", cleaned)
        self.assertNotIn("<script", cleaned)
        self.assertNotIn("<style", cleaned)
        self.assertNotIn("javascript:", cleaned)
        self.assertNotIn("https://example.com/a.png", cleaned)

    def test_srcdoc_frame_is_inlined(self):
        cleaned = export.sanitize_html(
            '<iframe srcdoc="&lt;b&gt;body&lt;/b&gt;&lt;script&gt;x()&lt;/script&gt;">'
            "</iframe>")
        self.assertIn("<b>body</b>", cleaned)
        self.assertNotIn("<iframe", cleaned)
        self.assertNotIn("<script", cleaned)

    def test_markdown_subset(self):
        rendered = export.markdown_to_html(
            "# Title\n\n- one\n- two\n\n> quote\n\n```\ncode\n```\n")
        self.assertIn("<h1>Title</h1>", rendered)
        self.assertIn("<ul><li>one</li><li>two</li></ul>", rendered)
        self.assertIn("<blockquote><p>quote</p></blockquote>", rendered)
        self.assertIn("<pre class=\"markdown-code\"><code>code</code></pre>", rendered)


class CommandTest(unittest.TestCase):
    def run_main(self, argv: list[str]) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = export.main(argv)
        return status, out.getvalue(), err.getvalue()

    def test_check_noop_and_mismatch(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / "mixed.html"
            status, _, _ = self.run_main(
                ["export", str(FIXTURES / "mixed.ipynb"), "--out", str(target)])
            self.assertEqual(status, 0)
            self.assertTrue(target.is_file())

            before = target.read_bytes()
            status, stdout, stderr = self.run_main(
                ["export", str(FIXTURES / "mixed.ipynb"), "--out", str(target), "--check"])
            self.assertEqual(status, 0, stderr)
            self.assertIn("up to date", stdout)
            self.assertEqual(target.read_bytes(), before, "--check must not write")

            target.write_text(before.decode("utf-8") + "changed\n", encoding="utf-8")
            status, _, stderr = self.run_main(
                ["export", str(FIXTURES / "mixed.ipynb"), "--out", str(target), "--check"])
            self.assertEqual(status, 1)
            self.assertIn("out of date", stderr)
            self.assertIn("-changed", stderr)

    def test_check_missing_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / "missing.html"
            status, _, stderr = self.run_main(
                ["export", str(FIXTURES / "mixed.ipynb"), "--out", str(target), "--check"])
            self.assertEqual(status, 1)
            self.assertIn("missing", stderr)

    def test_out_suffix_selects_markdown(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / "mixed.md"
            status, _, stderr = self.run_main(
                ["export", str(FIXTURES / "mixed.ipynb"), "--out", str(target)])
            self.assertEqual(status, 0, stderr)
            text = target.read_text(encoding="utf-8")
            self.assertTrue(text.startswith("<!-- wiz nb export: mixed.ipynb -->"))
            self.assertNotIn("<!doctype html>", text.lower())

    def test_malformed_json(self):
        status, _, stderr = self.run_main(
            ["export", str(FIXTURES / "malformed.ipynb"), "--out", os.devnull])
        self.assertEqual(status, 2)
        self.assertIn("error:", stderr)
        self.assertIn("malformed.ipynb", stderr)
        self.assertIn("not valid JSON", stderr)

    def test_missing_cells_list(self):
        status, _, stderr = self.run_main(
            ["export", str(FIXTURES / "no-cells.ipynb"), "--out", os.devnull])
        self.assertEqual(status, 2)
        self.assertIn("no \"cells\" list", stderr)

    def test_example_is_current(self):
        notebook = ROOT / "docs" / "notebooks" / "tour.ipynb"
        if not notebook.is_file():  # pragma: no cover - the checkout always has it
            self.skipTest("the example notebook is not in this tree")
        # the page is generated, not committed: export it, then --check against it
        with tempfile.TemporaryDirectory() as tmp:
            page = str(Path(tmp) / "tour.html")
            status, _, stderr = self.run_main(["export", str(notebook), "--out", page])
            self.assertEqual(status, 0, stderr)
            status, stdout, stderr = self.run_main(
                ["export", str(notebook), "--out", page, "--check"])
        self.assertEqual(status, 0, stderr)
        self.assertIn("up to date", stdout)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
