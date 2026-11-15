"""A notebook run through ``nbclient``: a widget display survives the real Jupyter
execution path and lands as an ``application/vnd.wiz.widget+json`` output.

No browser and no comm events here (nbclient has no front end); the comm round trip is
``test_widgets.py``. Skipped cleanly when ``nbclient``/``nbformat`` or a ``wiz``
executable is missing.
"""

from __future__ import annotations

import os
import shutil
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL_DIR = os.path.dirname(HERE)
ROOT = os.path.dirname(os.path.dirname(TOOL_DIR))
if TOOL_DIR not in sys.path:
    sys.path.insert(0, TOOL_DIR)

try:
    import nbformat
    from nbclient import NotebookClient
    HAVE_NBCLIENT = True
except ImportError:  # pragma: no cover - the skip path
    HAVE_NBCLIENT = False

from wiz_kernel.backends import find_wiz  # noqa: E402
from wiz_kernel.widgets import MIME, SCHEMA  # noqa: E402

DEFINITIONS = """import Web.Widget

def onEvent (e : Widget.Event) (ws : List Widget.Widget) : List Widget.Widget :=
  List.map (fun w => match String.eq w.id e.widget with
    | .true => Widget.setValue w e.value
    | .false => w) ws
"""

DISPLAY = """Widget.display [Widget.sliderRange "gain" "input" "0.50" "onEvent" "0" "1" "0.05"]
"""


@unittest.skipUnless(HAVE_NBCLIENT, "nbclient and nbformat are not installed")
class WidgetNotebookTest(unittest.TestCase):
    def setUp(self) -> None:
        self.wiz = find_wiz(os.environ.get("WIZ_TEST_WIZ"))
        if self.wiz is None:
            self.skipTest("no wiz executable (set $WIZ or $WIZ_TEST_WIZ)")
        self.tmp = tempfile.mkdtemp(prefix="wiz-widget-nb-")
        self.workspace = os.path.join(self.tmp, "ws")
        os.makedirs(self.workspace, exist_ok=True)
        spec_dir = os.path.join(self.tmp, "kernels", "wiz-kernel")
        os.makedirs(spec_dir, exist_ok=True)
        argv = [sys.executable, "-m", "wiz_kernel", "-f", "{connection_file}",
                "--cwd", self.workspace, "--backend", "auto",
                "--toolchain-arg=-I", f"--toolchain-arg={os.path.join(ROOT, 'lib')}"]
        with open(os.path.join(spec_dir, "kernel.json"), "w", encoding="utf-8") as handle:
            import json
            json.dump({"argv": argv, "display_name": "Wiz (test)",
                       "language": "wiz"}, handle)
        self._old_jupyter_path = os.environ.get("JUPYTER_PATH")
        paths = [self.tmp]
        if self._old_jupyter_path:
            paths.append(self._old_jupyter_path)
        os.environ["JUPYTER_PATH"] = os.pathsep.join(paths)

    def tearDown(self) -> None:
        if self._old_jupyter_path is None:
            os.environ.pop("JUPYTER_PATH", None)
        else:
            os.environ["JUPYTER_PATH"] = self._old_jupyter_path
        shutil.rmtree(getattr(self, "tmp", ""), ignore_errors=True)

    def test_widget_display_is_a_mime_bundle(self):
        import json

        notebook = nbformat.v4.new_notebook(cells=[
            nbformat.v4.new_code_cell(DEFINITIONS),
            nbformat.v4.new_code_cell(DISPLAY),
        ])
        env = dict(os.environ)
        env["PYTHONPATH"] = TOOL_DIR + os.pathsep + env.get("PYTHONPATH", "")
        client = NotebookClient(
            notebook, kernel_name="wiz-kernel", timeout=300, startup_timeout=120,
            resources={"metadata": {"path": self.workspace}})
        client.execute(env=env)

        outputs = notebook.cells[1].outputs
        results = [o for o in outputs if o.get("output_type") == "execute_result"]
        self.assertTrue(results, json.dumps(outputs)[:2000])
        data = results[0].get("data") or {}
        self.assertIn(MIME, data, json.dumps(data)[:1000])
        bundle = data[MIME]
        self.assertEqual(bundle.get("schema"), SCHEMA)
        self.assertEqual(bundle["widgets"][0]["id"], "gain")
        self.assertIn("wiz-widgets", data["text/html"])
        self.assertIn("data-wiz-widget-comm=", data["text/html"])


if __name__ == "__main__":
    unittest.main()
