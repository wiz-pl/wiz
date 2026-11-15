#!/usr/bin/env python3
"""Run one command and report wall time and peak RSS.

Usage: cve_measure.py --out FILE --err FILE -- CMD [ARG...]

The child writes its stdout to FILE and stderr to ERR.  The measurement JSON
is the only thing on this process's stdout:

    {"exit": 0, "ms": 12, "rss_kb": 3456, "signal": null}

`rss_kb` is ru_maxrss from wait4() for this child alone (KiB on Linux).
"""
import json
import os
import sys
import time


def main() -> int:
    args = sys.argv[1:]
    out = None
    err = None
    while args and args[0] != "--":
        if args[0] == "--out":
            out = args[1]
            args = args[2:]
        elif args[0] == "--err":
            err = args[1]
            args = args[2:]
        else:
            break
    if args and args[0] == "--":
        args = args[1:]
    if not args:
        print("cve_measure: no command", file=sys.stderr)
        return 2

    pid = os.fork()
    if pid == 0:
        try:
            if out is not None:
                fd = os.open(out, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
                os.dup2(fd, 1)
                os.close(fd)
            if err is not None:
                fd = os.open(err, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
                os.dup2(fd, 2)
                os.close(fd)
            os.execv(args[0], args)
        except Exception as exc:  # noqa: BLE001 - exec failure must not be silent
            print("cve_measure: %s" % exc, file=sys.stderr)
            os._exit(127)

    start = time.monotonic()
    _, status, usage = os.wait4(pid, 0)
    elapsed = time.monotonic() - start

    if os.WIFEXITED(status):
        code = os.WEXITSTATUS(status)
        sig = None
    else:
        code = None
        sig = os.WTERMSIG(status)

    print(json.dumps({
        "exit": code,
        "signal": sig,
        "ms": int(round(elapsed * 1000)),
        "rss_kb": int(usage.ru_maxrss),
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
