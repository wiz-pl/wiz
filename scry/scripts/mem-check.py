#!/usr/bin/env python3
"""A resident-memory regression for the native C store (scrydos-01).

A single large token must not be materialised as a Wiz `String` (`List Char`, two
cons cells per character) anywhere on the read/parse/lower path. The defect this
guards: `FS.readFile` returned the whole file as a `String`, and `Scry.Cst.ofStore`
built more copies while mapping spans, so a 4 MiB string literal peaked at 1.15 GiB
resident (8 MiB at 1.8 GiB), independent of `--max-nodes` (the literal is one node).

The source is generated in a temporary directory and every case is run as a child
process under wait4(2); `ru_maxrss` is that child's peak RSS (KiB on Linux), so the
number is not the test driver's own memory.

    mem-check.py --scry .grail/bin/scry [--mib 1,2,4] [--limit-mib 96]

Exit 0 when every case is below the limit, 1 when one is not, 2 on usage error and
3 when the scry binary is absent (the golden test prints a skip line then).
"""
import argparse
import os
import resource
import shutil
import sys
import tempfile
import time


def run_child(argv, timeout=180.0):
    """Run argv, return (exit code, peak RSS KiB, wall seconds).

    The child is exec'd directly and reaped with wait4, so ru_maxrss covers it and
    the children it waited for. Output is discarded: the caller checks the code and
    the memory, and a failure prints the command to reproduce.
    """
    t0 = time.monotonic()
    pid = os.fork()
    if pid == 0:
        try:
            devnull = os.open(os.devnull, os.O_RDWR)
            os.dup2(devnull, 1)
            os.dup2(devnull, 2)
            os.execvp(argv[0], argv)
        except OSError:
            os._exit(127)
    deadline = t0 + timeout
    while True:
        done, status, ru = os.wait4(pid, os.WNOHANG)
        if done == pid:
            return (os.waitstatus_to_exitcode(status), ru.ru_maxrss,
                    time.monotonic() - t0)
        if time.monotonic() > deadline:
            try:
                os.kill(pid, 9)
            except ProcessLookupError:
                pass
            _, _, ru = os.wait4(pid, 0)
            return (-9, ru.ru_maxrss, time.monotonic() - t0)
        time.sleep(0.01)


def write_literal(path, mib):
    """A valid C function whose initialiser is one mib-MiB string literal."""
    n = mib * 1024 * 1024
    with open(path, "wb") as f:
        f.write(b'int main(void) { char *s = "')
        chunk = b"A" * 65536
        while n > 0:
            k = min(n, len(chunk))
            f.write(chunk[:k])
            n -= k
        f.write(b'"; return 0; }\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--scry", default=".grail/bin/scry")
    ap.add_argument("--mib", default="1,2,4",
                    help="comma-separated literal sizes in MiB (default 1,2,4)")
    ap.add_argument("--limit-mib", type=int, default=96,
                    help="peak RSS limit for each run (default 96 MiB)")
    args = ap.parse_args()

    if not os.path.isfile(args.scry):
        print("mem: skip (%s absent)" % args.scry)
        return 3

    sizes = [int(x) for x in args.mib.split(",") if x != ""]
    limit_kib = args.limit_mib * 1024
    tmp = tempfile.mkdtemp(prefix="scry-mem-")
    failures = 0
    try:
        for mib in sizes:
            path = os.path.join(tmp, "literal-%d.c" % mib)
            write_literal(path, mib)
            size_kib = os.path.getsize(path) // 1024
            # `taint` is the whole pipeline (read, parse, store, lower, analyse).
            # `--max-nodes` is the wrong dimension for one giant token, so it is
            # deliberately not the guard: run at the default and check the memory.
            for label, cmd in (
                ("taint", [args.scry, "taint", path, "--json"]),
                ("parse --stats", [args.scry, "parse", "--stats", path]),
            ):
                code, rss, wall = run_child(cmd)
                if code != 0:
                    print("mem: %d MiB string literal, %s: exit %d (%s)"
                          % (mib, label, code, " ".join(cmd)), file=sys.stderr)
                    failures += 1
                    continue
                if rss > limit_kib:
                    print("mem: %d MiB string literal, %s: %d MiB peak RSS "
                          "exceeds %d MiB (%s)"
                          % (mib, label, rss // 1024, args.limit_mib,
                             " ".join(cmd)), file=sys.stderr)
                    failures += 1
                    continue
                print("mem: %d MiB string literal, %s: ok (< %d MiB)"
                      % (mib, label, args.limit_mib))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if failures:
        print("mem: %d case(s) failed" % failures, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
