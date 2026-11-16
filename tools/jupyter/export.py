#!/usr/bin/env python3
"""A thin entry point for the notebook exporter.

    python3 tools/jupyter/export.py export FILE.ipynb [--to html|md] [--out FILE]

The implementation lives in :mod:`wiz_kernel.export`; this file exists so the
command can be run from a checkout without installing the package.
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from wiz_kernel.export import main  # noqa: E402

if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
