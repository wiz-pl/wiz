# Wiz Jupyter kernel

An opt-in Jupyter kernel for Wiz, living in this checkout: it speaks the Jupyter
wire protocol itself (`pyzmq` is its only dependency) and drives the toolchain —
a persistent `wiz repl` when the toolchain has one, otherwise a `wiz check`
batch fallback — plus a `%%scry` cell magic that renders `scry taint --json`
findings for a cell's C source. `tools/jupyter/wiz-nb export FILE.ipynb` turns a
notebook's stored outputs into a self-contained static HTML page or Markdown.

```sh
python3 -m wiz_kernel install --user          # from this directory
jupyter console --kernel wiz-kernel
tools/jupyter/wiz-nb export docs/notebooks/tour.ipynb
```

Install, backends, magics, export and limits: **[docs/tools/jupyter.md](../../docs/tools/jupyter.md)**.

Quick tests:

```sh
python3 -m unittest discover -s tools/jupyter/tests -v   # protocol (jupyter_client)
PYTHONPATH=tools/jupyter python3 -m wiz_kernel --self-test
python3 -m unittest discover -s tools/jupyter/tests -p 'test_export.py' -v
```

Not part of the dev shell, `lake`, or CI's default test groups.
