"""The guided tour as a notebook: its export and its live run.

The notebook in ``docs/notebooks/tour.ipynb`` is the source; ``tour.html`` is its
export, generated for the site (``tools/jupyter/export-notebooks.sh``), not
committed.  The first test needs no Jupyter and holds the export deterministic.
The second executes every code cell with the Wiz kernel and checks that the
stored outputs (and so the page) are what a fresh run produces.  It skips cleanly when ``nbclient``/``nbformat`` or a Wiz executable
is missing.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
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
from wiz_kernel.backends import find_wiz  # noqa: E402

NOTEBOOK = ROOT / "docs" / "notebooks" / "tour.ipynb"

try:  # the run test is the only part that needs Jupyter
    import nbformat
    from nbclient import NotebookClient
    HAVE_NBCLIENT = True
except ImportError:  # pragma: no cover - the skip path
    HAVE_NBCLIENT = False


class TourExportTest(unittest.TestCase):
    def test_export_is_deterministic(self):
        first = export.render(export.load_notebook(NOTEBOOK), "html")
        second = export.render(export.load_notebook(NOTEBOOK), "html")
        self.assertEqual(first, second)

    def test_every_section_is_a_chapter(self):
        notebook = export.load_notebook(NOTEBOOK)
        headings = [line for cell in notebook.cells if cell.kind == "markdown"
                    for line in cell.source.splitlines() if line.startswith("## ")]
        for section in ("0: a program", "1: values and functions",
                        "2: inductive types and pattern matching", "3: structures",
                        "4: type classes and numerals", "5: dependent types",
                        "6: propositions and proofs",
                        "7: quantities and linear resources", "8: codata",
                        "9: the C FFI", "10: hardware", "11: packages",
                        "12: taint analysis with scry"):
            self.assertIn("## " + section, headings)


@unittest.skipUnless(HAVE_NBCLIENT, "nbclient and nbformat are not installed")
class TourNotebookRunTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.wiz = find_wiz(os.environ.get("WIZ_TEST_WIZ"))
        if cls.wiz is None:
            raise unittest.SkipTest("no wiz executable (set $WIZ or $WIZ_TEST_WIZ)")
        cls._require_a_toolchain_that_can_check_the_tour()
        from wiz_kernel.install import build_spec
        cls.tmp = tempfile.mkdtemp(prefix="wiz-tour-notebook-")
        kernel_dir = Path(cls.tmp) / "share" / "jupyter" / "kernels" / "wiz-kernel"
        kernel_dir.mkdir(parents=True)
        spec = build_spec(python=sys.executable, wiz=cls.wiz, backend="batch")
        (kernel_dir / "kernel.json").write_text(json.dumps(spec, indent=2) + "\n",
                                                encoding="utf-8")
        cls.old_jupyter_path = os.environ.get("JUPYTER_PATH")
        os.environ["JUPYTER_PATH"] = str(Path(cls.tmp) / "share" / "jupyter")
        try:
            cls.fresh = nbformat.read(NOTEBOOK, as_version=4)
            client = NotebookClient(
                cls.fresh, kernel_name="wiz-kernel", timeout=300, allow_errors=False,
                resources={"metadata": {"path": str(ROOT)}})
            client.execute()
        except BaseException:
            cls._restore()
            shutil.rmtree(cls.tmp, ignore_errors=True)
            raise

    @classmethod
    def _require_a_toolchain_that_can_check_the_tour(cls) -> None:
        """Skip on a toolchain older than the tour's examples.

        The tour uses `calc` (section 6) and `lib/Scry` (section 12).  A `wiz`
        installed from an older commit cannot check them; that is a missing
        feature, not a broken notebook, so say so and skip.
        """
        probe = ("import Nat\nimport Scry.Taint\n\n"
                 "def probe (a b : Nat) (h : a ≤ b) : a ≤ b :=\n"
                 "  calc a ≤ b := h\n")
        with tempfile.TemporaryDirectory(prefix="wiz-tour-probe-") as tmp:
            path = Path(tmp) / "probe.wiz"
            path.write_text(probe, encoding="utf-8")
            done = subprocess.run([cls.wiz, "check", str(path)],
                                  capture_output=True, text=True, timeout=120)
        if done.returncode != 0:
            detail = (done.stdout + done.stderr).strip().splitlines()
            reason = detail[0] if detail else f"wiz check exited {done.returncode}"
            raise unittest.SkipTest(
                f"the Wiz toolchain at {cls.wiz} cannot check the tour's examples: "
                f"{reason} (set $WIZ_TEST_WIZ to a newer build)")

    @classmethod
    def _restore(cls) -> None:
        if cls.old_jupyter_path is None:
            os.environ.pop("JUPYTER_PATH", None)
        else:
            os.environ["JUPYTER_PATH"] = cls.old_jupyter_path

    @classmethod
    def tearDownClass(cls) -> None:
        cls._restore()
        shutil.rmtree(getattr(cls, "tmp", ""), ignore_errors=True)

    def test_every_code_cell_matches_a_fresh_run(self):
        committed = nbformat.read(NOTEBOOK, as_version=4)
        self.assertEqual(len(committed.cells), len(self.fresh.cells))
        for index, (stored, fresh) in enumerate(zip(committed.cells, self.fresh.cells), 1):
            if stored.cell_type != "code":
                continue
            with self.subTest(cell=index):
                self.assertEqual(stored.execution_count, fresh.execution_count)
                self.assertEqual(stored.outputs, fresh.outputs)

    def test_the_exported_page_matches_a_fresh_run(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / NOTEBOOK.name
            nbformat.write(self.fresh, path)
            page = export.render(export.load_notebook(path), "html")
        self.assertEqual(export.render(export.load_notebook(NOTEBOOK), "html"), page)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
