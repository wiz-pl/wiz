"""A Jupyter kernel for Wiz.

The kernel speaks Jupyter's wire protocol itself (ZeroMQ + HMAC: see
:mod:`wiz_kernel.wire`) and drives the Wiz toolchain: a persistent ``wiz repl``
when the toolchain has one, otherwise a ``wiz check`` batch fallback.  See
``tools/jupyter/README.md`` and ``docs/tools/jupyter.md``.
"""

__version__ = "0.1.0"
