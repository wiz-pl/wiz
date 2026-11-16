# Wiz Jupyter kernel

An opt-in Jupyter kernel for Wiz, living in this checkout: it speaks the Jupyter
wire protocol itself (`pyzmq` is its only dependency) and drives the toolchain —
a persistent `wiz repl` when the toolchain has one, otherwise a `wiz check`
batch fallback — plus cell magics for `%%scry` (taint findings),
`%%sh` (shell), `%%time` (wall clock and peak RSS) and `%%scry --progress`
(live progress for long analyses), and interactive widgets (`Web.Widget` +
Jupyter comms, rendered by `static/widget.js` on the React framework's patch
applier). `tools/jupyter/wiz-nb export FILE.ipynb` turns a notebook's stored
outputs into a self-contained static HTML page or Markdown.

```sh
python3 -m wiz_kernel install --user          # from this directory
jupyter console --kernel wiz-kernel
tools/jupyter/wiz-nb export docs/notebooks/tour.ipynb
```

Install, backends, magics, widgets, export, limits and tests: **[docs/tools/jupyter.md](../../docs/tools/jupyter.md)**.

Quick tests:

```sh
sh tools/jupyter/run-tests.sh                       # protocol, self-test, widget front end
python3 -m unittest discover -s tools/jupyter/tests -v   # protocol (jupyter_client)
PYTHONPATH=tools/jupyter python3 -m wiz_kernel --self-test
WIZ=wiz web/widget/test.sh                          # widget VDOM + patches (Node)
node tools/jupyter/static/widget_test.mjs           # widget front end (headless Chrome if installed)
python3 -m unittest discover -s tools/jupyter/tests -p 'test_export.py' -v
```

Not part of the dev shell, `lake`, or CI's default test groups. The widget
front-end test's Node fallback always runs; its headless-browser step is skipped
with a message when no Chrome/Chromium is installed (and still exits 0).
