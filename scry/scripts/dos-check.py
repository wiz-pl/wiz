#!/usr/bin/env python3
"""Resource-limit regression tests for scry (findings scrydos-01 and scrydos-02).

Both checks run the real CLI as a child process, so the numbers are the ones a user
sees, and both are small enough for CI:

* memory: a few-MiB C file (a string literal for `taint`, a comment for `parse
  --stats`) must stay below `--max-ratio` times its own size in peak RSS
  (`ru_maxrss` from `wait4`). The old `FS.readFile` -> `String` (`List Char`, two cons
  cells per character) path was ~100x; the budget catches a return to it.
* scaling: `a++;` statement counts 16, 64, 128 and 256 must each finish inside a
  generous per-size wall-clock budget. The findings measured 12.85 s for 128 (about
  n^3.5) and 256 did not finish in a useful time; the budgets here fail that shape and
  pass the linear preparation the fix introduced.

Run it through grail (it builds the CLI first):

    cd scry && grail build dos-check

or directly with an already-built binary:

    python3 scry/scripts/dos-check.py --scry scry/.grail/bin/scry

A missing binary is a skip (exit 0), like the other scry scale checks, so a bare
checkout stays green. Exit status: 0 pass/skip, 1 a limit was exceeded.
"""

import argparse
import json
import os
import signal
import sys
import tempfile
import time


def wait4_measured(cmd, timeout):
    """Run `cmd` in its own process group; return (status, maxrss Bytes, wall seconds).

    Returns (None, None, wall) when the timeout fired (the group was killed)."""
    import subprocess
    start = time.monotonic()
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        p = subprocess.Popen(cmd, stdout=out, stderr=err, start_new_session=True)
        deadline = start + timeout
        while True:
            wpid, status, ru = os.wait4(p.pid, os.WNOHANG)
            if wpid == p.pid:
                wall = time.monotonic() - start
                out.seek(0)
                err.seek(0)
                stdout = out.read().decode("utf-8", "replace")
                stderr = err.read().decode("utf-8", "replace")
                maxrss = ru.ru_maxrss
                if sys.platform != "darwin":
                    maxrss *= 1024
                p.returncode = 0
                return status, maxrss, wall, stdout, stderr
            if time.monotonic() >= deadline:
                try:
                    os.killpg(os.getpgid(p.pid), signal.SIGKILL)
                except ProcessLookupError:
                    pass
                os.wait4(p.pid, 0)
                p.returncode = -signal.SIGKILL
                return None, None, time.monotonic() - start, "", "timeout"


def exit_code(status):
    if status is None:
        return None
    if os.WIFEXITED(status):
        return os.WEXITSTATUS(status)
    if os.WIFSIGNALED(status):
        return -os.WTERMSIG(status)
    return None


def write_file(directory, name, text):
    path = os.path.join(directory, name)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    return path


def mem_string_case(path, size):
    # A single huge token: the old nodeText slice made a List Char of the whole literal,
    # so `taint` paid ~100x the input in RSS. The lowering never reads the token value
    # (a string literal is havoc'd), so this is the parse + lowering + analysis path.
    return 'int main(void) {\n  const char *s = "' + ("a" * size) + '";\n  return s[0];\n}\n'


def mem_comment_case(path, size):
    return "/*" + ("x" * size) + "*/\nint main(void) { return 0; }\n"


def scale_case(n):
    # The findings' shape: one exported function with a parameter source and n `a++;`
    # statements (128 statements is the report's 525-byte, 12.85 s case).
    return "int f(int a){" + ("a++;" * n) + "}\n"


def check_memory(scry, tmp, max_ratio, size, verbose):
    # Two shapes: `taint` (parse + store + lower + analysis) on a string literal, and
    # `parse --stats` (the `parseBlock` path that used to trim the whole file).
    cases = [
        ("mem-string", "taint", mem_string_case, ["taint", "--json"]),
        ("mem-comment", "parse", mem_comment_case, ["parse", "--stats"]),
    ]
    ok = True
    for label, kind, gen, args in cases:
        path = write_file(tmp, label + ".c", gen(label, size))
        input_bytes = os.path.getsize(path)
        cmd = [scry] + args[:1] + [path] + args[1:]
        status, rss, wall, stdout, stderr = wait4_measured(cmd, timeout=60)
        code = exit_code(status)
        ratio = (rss / input_bytes) if rss is not None else float("inf")
        print("dos: %s %s bytes ratio=%.2f wall=%.2fs rss=%s" % (
            label, "%d" % input_bytes, ratio, wall,
            "timeout" if rss is None else "%.1f MiB" % (rss / (1024 * 1024))))
        if code != 0:
            print("dos: %s FAILED (exit %s)%s" % (
                label, code, ("\n" + stderr[-2000:]) if stderr else ""))
            ok = False
        elif ratio > max_ratio:
            print("dos: %s FAILED (RSS ratio %.2f > %.2f)" % (label, ratio, max_ratio))
            ok = False
        elif verbose:
            print(stderr[-1000:])
    return ok


def check_scaling(scry, tmp, budgets, total_budget):
    ok = True
    total = 0.0
    for n, budget in budgets:
        path = write_file(tmp, "scale-%d.c" % n, scale_case(n))
        status, rss, wall, stdout, stderr = wait4_measured(
            [scry, "taint", path, "--json"], timeout=budget)
        code = exit_code(status)
        total += wall
        print("dos: scale %3d statements %6d bytes wall=%dms budget=%.1fs%s" % (
            n, os.path.getsize(path), round(wall * 1000), budget,
            "" if rss is None else " rss=%.1f MiB" % (rss / (1024 * 1024))))
        if code is None:
            print("dos: scale %d FAILED (over %.1fs)" % (n, budget))
            ok = False
        elif code != 0:
            print("dos: scale %d FAILED (exit %s)%s" % (n, code,
                                                         ("\n" + stderr[-2000:]) if stderr else ""))
            ok = False
        else:
            try:
                rep = json.loads(stdout)
            except ValueError as e:
                print("dos: scale %d FAILED (bad JSON: %s)" % (n, e))
                ok = False
                continue
            if rep.get("truncated") is True:
                print("dos: scale %d FAILED (truncated run)" % n)
                ok = False
    if total > total_budget:
        print("dos: scale FAILED (total %.2fs > %.1fs)" % (total, total_budget))
        ok = False
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--scry", default=".grail/bin/scry",
                    help="the scry binary (default: .grail/bin/scry, run from scry/)")
    ap.add_argument("--mem", action="store_true", help="only the memory-ratio check")
    ap.add_argument("--scale", action="store_true", help="only the scaling check")
    ap.add_argument("--mem-bytes", type=int, default=3 * 1024 * 1024,
                    help="size of each generated memory-test input (default 3 MiB)")
    ap.add_argument("--max-ratio", type=float, default=20.0,
                    help="max peak RSS / input bytes (default 20)")
    ap.add_argument("--scale-total", type=float, default=20.0,
                    help="total wall-clock budget for the scaling cases (default 20 s)")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    scry = os.path.abspath(args.scry)
    if not os.path.isfile(scry) or not os.access(scry, os.X_OK):
        print("dos: skip (%s is absent or not executable; build it with "
              "`grail build scry`)" % args.scry)
        return 0

    run_mem = args.mem or not args.scale
    run_scale = args.scale or not args.mem
    budgets = [(16, 2.0), (64, 3.0), (128, 6.0), (256, 8.0)]

    ok = True
    with tempfile.TemporaryDirectory(prefix="scrydos-") as tmp:
        if run_mem:
            ok = check_memory(scry, tmp, args.max_ratio, args.mem_bytes, args.verbose) and ok
        if run_scale:
            ok = check_scaling(scry, tmp, budgets, args.scale_total) and ok
    print("dos: PASS" if ok else "dos: FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
