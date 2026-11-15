"""Entry point: ``python -m wiz_kernel``.

    python -m wiz_kernel -f CONNECTION_FILE [--wiz PATH] [--backend auto|repl|batch]
    python -m wiz_kernel install [--user|--prefix DIR|--sys-prefix]
    python -m wiz_kernel uninstall [...]
    python -m wiz_kernel --self-test [--wiz PATH] [--backend ...]
"""

from __future__ import annotations

import argparse
import signal
import sys

from . import __version__


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] in ("install", "uninstall"):
        from . import install
        return install.main(argv)
    if "--self-test" in argv:
        argv.remove("--self-test")
        from . import selftest
        return selftest.main(argv)

    parser = argparse.ArgumentParser(
        prog="python -m wiz_kernel",
        description="A Jupyter kernel for Wiz (the kernel is started by Jupyter with "
                    "`-f CONNECTION_FILE`).")
    parser.add_argument("-f", "--connection-file", required=True,
                        help="Jupyter's connection file")
    parser.add_argument("--wiz", metavar="PATH",
                        help="the Wiz executable (default: $WIZ, then `wiz` on PATH, "
                             "then a checkout's .lake/build/bin/wiz)")
    parser.add_argument("--backend", choices=["auto", "repl", "batch"], default="auto",
                        help="auto: `wiz repl` when the toolchain has it, else the "
                             "`wiz check` batch fallback")
    parser.add_argument("--cwd", metavar="DIR",
                        help="the Wiz working directory (default: the process's cwd)")
    parser.add_argument("--toolchain-arg", action="append", default=[], metavar="ARG",
                        help="an argument for the wiz command line, e.g. "
                             "--toolchain-arg=--no-cache (repeatable)")
    parser.add_argument("--lsp-command", metavar="CMD",
                        help="the language server command (default: `<wiz> -I <cwd> lsp`; "
                             "also $WIZ_KERNEL_LSP)")
    parser.add_argument("--no-lsp", action="store_true",
                        help="do not start a language server; completion and inspection "
                             "then answer empty/found=false with the reason in metadata")
    parser.add_argument("--version", action="version", version=f"wiz-kernel {__version__}")
    args = parser.parse_args(argv)

    from .kernel import Kernel
    kernel = Kernel(args.connection_file, backend=args.backend, wiz=args.wiz,
                    cwd=args.cwd, toolchain_args=args.toolchain_arg,
                    lsp_command=args.lsp_command, lsp_enabled=not args.no_lsp)

    def terminate(signum, frame):  # noqa: ARG001
        kernel.running = False

    signal.signal(signal.SIGTERM, terminate)
    signal.signal(signal.SIGINT, terminate)
    try:
        kernel.start()
    except KeyboardInterrupt:
        pass
    finally:
        kernel.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
