"""Protocol-level tests for Wiz notebook widgets (no browser).

They start the kernel the way Jupyter does (a connection file and ``-f``) and talk to
it over raw ZeroMQ, so the whole path is covered: ``Widget.display`` -> the kernel's
``WIZ_WIDGET:`` detection -> ``comm_open`` -> a slider event on the comm ->
``Widget.handle`` re-entering the session -> a ``comm_msg`` with patches.

Run from a checkout::

    python3 -m unittest discover -s tools/jupyter/tests -v

Skipped cleanly without ``pyzmq`` or a ``wiz`` executable. ``$WIZ_TEST_WIZ`` and
``$WIZ_TEST_BACKEND`` work as in ``test_kernel.py``; the widget tests pass the
checkout's ``lib/`` as an extra module root (``--toolchain-arg=-I``).
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL_DIR = os.path.dirname(HERE)
ROOT = os.path.dirname(os.path.dirname(TOOL_DIR))
if TOOL_DIR not in sys.path:
    sys.path.insert(0, TOOL_DIR)

try:
    import zmq  # noqa: F401
    HAVE_ZMQ = True
except ImportError:  # pragma: no cover - the skip path
    HAVE_ZMQ = False

from wiz_kernel.backends import find_wiz  # noqa: E402
from wiz_kernel.widgets import MIME, PREFIX, SCHEMA, TARGET  # noqa: E402

WIDGET_DEFINITIONS = """import Web.Widget

def onEvent (e : Widget.Event) (ws : List Widget.Widget) : List Widget.Widget :=
  List.map (fun w => match String.eq w.id e.widget with
    | .true => Widget.setValue w e.value
    | .false => w) ws
"""

WIDGET_DISPLAY = """Widget.display [Widget.sliderRange "gain" "input" "0.50" "onEvent" "0" "1" "0.05"]
"""


@unittest.skipUnless(HAVE_ZMQ, "pyzmq is not installed")
class WidgetProtocolTest(unittest.TestCase):
    backend = os.environ.get("WIZ_TEST_BACKEND", "auto")

    @classmethod
    def setUpClass(cls) -> None:
        from wiz_kernel.selftest import Client, _connection_file

        cls.wiz = find_wiz(os.environ.get("WIZ_TEST_WIZ"))
        if cls.wiz is None:
            raise unittest.SkipTest("no wiz executable (set $WIZ or $WIZ_TEST_WIZ)")
        cls.tmp = tempfile.mkdtemp(prefix="wiz-widget-test-")
        cls.workspace = os.path.join(cls.tmp, "ws")
        os.makedirs(cls.workspace, exist_ok=True)
        connection_file, config = _connection_file(cls.tmp)
        env = dict(os.environ)
        env["PYTHONPATH"] = TOOL_DIR + os.pathsep + env.get("PYTHONPATH", "")
        command = [sys.executable, "-m", "wiz_kernel", "-f", connection_file,
                   "--backend", cls.backend, "--cwd", cls.workspace,
                   "--toolchain-arg=-I", f"--toolchain-arg={os.path.join(ROOT, 'lib')}"]
        cls.process = subprocess.Popen(command, cwd=cls.workspace, env=env,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        cls.client = Client(config)
        deadline = time.time() + 240
        while True:
            try:
                msg_id = cls.client.send("kernel_info_request", {})
                cls.info = cls.client.reply(msg_id, timeout=10)
                break
            except TimeoutError:
                if cls.process.poll() is not None:
                    error = b""
                    try:
                        error = cls.process.stderr.read() or b""
                    except OSError:
                        pass
                    raise RuntimeError(
                        "the widget kernel exited: "
                        + error.decode("utf-8", "replace")[-2000:])
                if time.time() > deadline:
                    raise
        cls.backend_name = (cls.info.content.get("metadata") or {}).get("wiz_backend")
        reply, _ = cls.client.execute(WIDGET_DEFINITIONS, timeout=600)
        if reply.content.get("status") != "ok":
            raise RuntimeError(f"widget definitions failed: {reply.content}")

    @classmethod
    def tearDownClass(cls) -> None:
        if hasattr(cls, "client"):
            try:
                msg_id = cls.client.send("shutdown_request", {"restart": False})
                cls.client.reply(msg_id, timeout=20)
            except Exception:
                pass
            cls.client.close()
        if getattr(cls, "process", None) is not None:
            if cls.process.poll() is None:
                cls.process.terminate()
                try:
                    cls.process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    cls.process.kill()
            for pipe in (cls.process.stdout, cls.process.stderr):
                try:
                    pipe.close()
                except Exception:
                    pass
        shutil.rmtree(getattr(cls, "tmp", ""), ignore_errors=True)

    # -- helpers -------------------------------------------------------

    @classmethod
    def display(cls):
        """Run the widget cell and return (comm bundle, comm id, whole iopub)."""
        reply, iopub = cls.client.execute(WIDGET_DISPLAY, timeout=600)
        assert reply.content.get("status") == "ok", reply.content
        opens = [m for m in iopub if m.msg_type == "comm_open"]
        assert opens, [m.msg_type for m in iopub]
        opened = opens[0]
        assert opened.content.get("target_name") == TARGET
        bundle = opened.content.get("data") or {}
        return bundle, opened.content.get("comm_id"), iopub

    @classmethod
    def send_event(cls, comm_id: str, payload: dict, timeout: float = 600.0):
        msg_id = cls.client.send("comm_msg", {"comm_id": comm_id, "data": payload})
        messages = cls.client.iopub_until(
            lambda m: m.msg_type == "comm_msg", msg_id=msg_id, timeout=timeout)
        return [m for m in messages if m.msg_type == "comm_msg"][-1]

    # -- tests ---------------------------------------------------------

    def test_display_opens_a_comm_and_returns_the_bundle(self):
        bundle, comm_id, iopub = self.display()
        self.assertTrue(comm_id)
        self.assertEqual(bundle.get("schema"), SCHEMA)
        self.assertEqual(bundle.get("count"), 1)
        self.assertEqual(bundle["widgets"][0]["id"], "gain")
        self.assertEqual(bundle["widgets"][0]["kind"], "slider")
        self.assertEqual(bundle["widgets"][0]["callback"], "onEvent")
        self.assertIn("wiz_widgets", self.info.content.get("metadata") or {})

        result = [m for m in iopub if m.msg_type == "execute_result"][0]
        data = result.content.get("data") or {}
        self.assertIn(MIME, data)
        self.assertEqual(data[MIME].get("comm_id"), comm_id)
        self.assertIn("wiz-widgets", data["text/html"])
        self.assertIn(f'data-wiz-widget-comm="{comm_id}"', data["text/html"])
        self.assertIn("gain (slider)", data["text/plain"])
        # The display string itself does not leak into the cell's stream.
        self.assertNotIn(PREFIX, "".join(
            m.content.get("text", "") for m in iopub if m.msg_type == "stream"))

    def test_slider_event_round_trips_to_patches(self):
        _, comm_id, _ = self.display()
        update = self.send_event(comm_id, {
            "method": "event", "widget_id": "gain", "event": "input", "value": "0.75"})
        data = update.content.get("data") or {}
        self.assertEqual(data.get("method"), "update")
        self.assertIn("0.75", data["bundle"]["html"])
        ops = [p.get("op") for p in data["patches"]]
        self.assertIn("text", ops)
        text = [p for p in data["patches"] if p.get("op") == "text"][-1]
        self.assertEqual(text.get("text"), "0.75")
        self.assertEqual(data["bundle"].get("schema"), SCHEMA)
        self.assertEqual(data["bundle"]["widgets"][0]["value"], "0.75")

    def test_an_explicit_eval_display_is_found_in_the_stream(self):
        reply, iopub = self.client.execute(
            '#eval Widget.display [Widget.text "name" "input" "ada" "onEvent"]')
        self.assertEqual(reply.content.get("status"), "ok", reply.content)
        opens = [m for m in iopub if m.msg_type == "comm_open"]
        self.assertTrue(opens, [m.msg_type for m in iopub])
        self.assertEqual(opens[0].content["data"]["widgets"][0]["kind"], "text")
        self.assertNotIn(PREFIX, "".join(
            m.content.get("text", "") for m in iopub if m.msg_type == "stream"))

    def test_a_second_event_uses_the_updated_bundle(self):
        _, comm_id, _ = self.display()
        self.send_event(comm_id, {"method": "event", "widget_id": "gain",
                                  "event": "input", "value": "0.75"})
        update = self.send_event(comm_id, {"method": "event", "widget_id": "gain",
                                           "event": "input", "value": "0.25"})
        data = update.content.get("data") or {}
        self.assertEqual(data["bundle"]["widgets"][0]["value"], "0.25")
        # From 0.75 to 0.25 is a text change, not a re-insert of the widget.
        ops = [p.get("op") for p in data["patches"]]
        self.assertNotIn("insert", ops)
        self.assertIn("text", ops)

    def test_an_unknown_widget_is_an_error_on_the_comm(self):
        _, comm_id, _ = self.display()
        update = self.send_event(comm_id, {"method": "event", "widget_id": "nope",
                                           "event": "input", "value": "1"})
        data = update.content.get("data") or {}
        self.assertEqual(data.get("method"), "error")
        self.assertIn("nope", data.get("error", ""))

    def test_comm_info_lists_the_open_widget(self):
        _, comm_id, _ = self.display()
        msg_id = self.client.send("comm_info_request", {"target_name": TARGET})
        reply = self.client.reply(msg_id, timeout=60)
        comms = reply.content.get("comms") or {}
        self.assertIn(comm_id, comms)
        self.assertEqual(comms[comm_id]["target_name"], TARGET)

    def test_comm_close_is_acknowledged_and_forgotten(self):
        _, comm_id, _ = self.display()
        msg_id = self.client.send("comm_close", {"comm_id": comm_id, "data": {}})
        messages = self.client.iopub_until(
            lambda m: m.msg_type == "comm_close", msg_id=msg_id, timeout=60)
        closed = [m for m in messages if m.msg_type == "comm_close"][-1]
        self.assertEqual(closed.content.get("comm_id"), comm_id)
        msg_id = self.client.send("comm_info_request", {"target_name": TARGET})
        reply = self.client.reply(msg_id, timeout=60)
        self.assertNotIn(comm_id, reply.content.get("comms") or {})
