"""Install/uninstall the ``wiz-kernel`` kernelspec.

    python -m wiz_kernel install [--user | --prefix DIR | --sys-prefix]
                                [--wiz PATH] [--backend auto|repl|batch]
                                [--python PYTHON] [--dry-run]

The written ``kernel.json`` runs *this* Python (``sys.executable``) with
``-m wiz_kernel -f {connection_file}`` and puts ``tools/jupyter`` on
``PYTHONPATH``, so the kernel also works from a checkout without installing the
package.  ``env.WIZ`` pins the toolchain when ``--wiz`` is given.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import sys

KERNEL_NAME = "wiz-kernel"
TOOL_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def user_data_dir() -> str:
    if sys.platform == "darwin":
        return os.path.expanduser("~/Library/Jupyter")
    if os.name == "nt":  # pragma: no cover - not a Wiz platform
        base = os.environ.get("APPDATA")
        return os.path.join(base or os.path.expanduser("~"), "jupyter")
    base = os.environ.get("XDG_DATA_HOME") or os.path.expanduser("~/.local/share")
    return os.path.join(base, "jupyter")


def data_dirs() -> dict[str, str]:
    return {
        "user": user_data_dir(),
        "sys-prefix": os.path.join(sys.prefix, "share", "jupyter"),
    }


def template() -> dict:
    """The checked-in ``wiz-kernel/kernel.json`` (the shape of the spec)."""
    path = os.path.join(TOOL_DIR, "wiz-kernel", "kernel.json")
    try:
        with open(path, encoding="utf-8") as handle:
            return json.load(handle)
    except OSError:
        return {"argv": ["python3", "-m", "wiz_kernel", "-f", "{connection_file}"],
                "display_name": "Wiz", "language": "wiz", "interrupt_mode": "message"}


def build_spec(*, python: str | None = None, wiz: str | None = None,
               backend: str | None = None) -> dict:
    spec = template()
    python = python or sys.executable
    argv = [python, "-m", "wiz_kernel", "-f", "{connection_file}"]
    if backend and backend != "auto":
        argv += ["--backend", backend]
    spec["argv"] = argv
    env = dict(spec.get("env") or {})
    pythonpath = [TOOL_DIR]
    if env.get("PYTHONPATH"):
        pythonpath.append(env["PYTHONPATH"])
    env["PYTHONPATH"] = os.pathsep.join(dict.fromkeys(pythonpath))
    if wiz:
        env["WIZ"] = os.path.abspath(os.path.expanduser(wiz))
    spec["env"] = env
    spec["display_name"] = spec.get("display_name") or "Wiz"
    spec["language"] = "wiz"
    spec["interrupt_mode"] = "message"
    return spec


def spec_dir(prefix: str | None = None, user: bool = True, sys_prefix: bool = False) -> str:
    if prefix:
        base = os.path.join(os.path.abspath(os.path.expanduser(prefix)), "share", "jupyter")
    elif sys_prefix:
        base = data_dirs()["sys-prefix"]
    else:
        base = user_data_dir()
    return os.path.join(base, "kernels", KERNEL_NAME)


def install(args: argparse.Namespace) -> int:
    spec = build_spec(python=args.python, wiz=args.wiz, backend=args.backend)
    directory = spec_dir(prefix=args.prefix, user=True, sys_prefix=args.sys_prefix)
    target = os.path.join(directory, "kernel.json")
    if args.dry_run:
        print(target)
        print(json.dumps(spec, indent=2))
        return 0
    if os.path.exists(target) and not args.force:
        with open(target, encoding="utf-8") as handle:
            try:
                existing = json.load(handle)
            except json.JSONDecodeError:
                existing = None
        if existing != spec:
            print(f"{target} exists and differs; pass --force to replace it", file=sys.stderr)
            return 1
    os.makedirs(directory, exist_ok=True)
    with open(target, "w", encoding="utf-8") as handle:
        json.dump(spec, handle, indent=2)
        handle.write("\n")
    print(f"installed the {KERNEL_NAME} kernelspec: {target}")
    print("try: jupyter console --kernel wiz-kernel")
    return 0


def uninstall(args: argparse.Namespace) -> int:
    directory = spec_dir(prefix=args.prefix, user=True, sys_prefix=args.sys_prefix)
    if os.path.isdir(directory):
        shutil.rmtree(directory)
        print(f"removed {directory}")
    else:
        print(f"nothing at {directory}")
    return 0


def main(argv: list[str]) -> int:
    command = argv[0] if argv else "install"
    parser = argparse.ArgumentParser(prog=f"python -m wiz_kernel {command}",
                                     description=__doc__.splitlines()[0])
    where = parser.add_mutually_exclusive_group()
    where.add_argument("--user", action="store_true",
                       help="the user's Jupyter data directory (the default)")
    where.add_argument("--sys-prefix", action="store_true",
                       help="the running Python's prefix (for a venv)")
    where.add_argument("--prefix", metavar="DIR",
                       help="install under DIR/share/jupyter")
    parser.add_argument("--wiz", metavar="PATH", help="the Wiz executable to pin ($WIZ)")
    parser.add_argument("--backend", choices=["auto", "repl", "batch"], default="auto",
                       help="the driver the kernel should use (default: auto)")
    parser.add_argument("--python", metavar="PATH",
                       help="the Python that runs the kernel (default: this one)")
    parser.add_argument("--force", action="store_true", help="replace a different kernel.json")
    parser.add_argument("--dry-run", action="store_true", help="print, do not write")
    args = parser.parse_args(argv[1:])
    if command == "install":
        return install(args)
    if command == "uninstall":
        return uninstall(args)
    print(f"unknown command {command!r} (install or uninstall)", file=sys.stderr)
    return 2
