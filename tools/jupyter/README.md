# Wiz Jupyter kernel

An opt-in Jupyter kernel for Wiz, living in this checkout: it speaks the Jupyter
wire protocol itself (`pyzmq` is its only dependency) and drives the toolchain —
a persistent `wiz repl` when the toolchain has one, otherwise a `wiz check`
batch fallback — plus completion and inspection from a lazily started
`wiz lsp`, and a `%%scry` cell magic that renders `scry taint --json` findings
for a cell's C source.

```sh
python3 -m wiz_kernel install --user          # from this directory
jupyter console --kernel wiz-kernel
```

Install, backends, magics, limits and tests: **[docs/tools/jupyter.md](../../docs/tools/jupyter.md)**.

Quick tests:

```sh
python3 -m unittest discover -s tools/jupyter/tests -v   # protocol (jupyter_client)
PYTHONPATH=tools/jupyter python3 -m wiz_kernel --self-test
```

Not part of the dev shell, `lake`, or CI's default test groups.
