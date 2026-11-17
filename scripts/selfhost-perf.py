#!/usr/bin/env python3
"""Measure and profile the self-hosted compiler on one input (see selfhost-perf.sh).

Two kinds of number come out of this file:

* wall time and peak RSS of the *plain* -O1 build, `check` and `build` separately
  (median of --reps runs, with every sample printed).  These are the numbers to
  compare across commits: `check` is load + parse + elaborate, `build` adds the
  code generation and the write.

* a phase table and a function table from a second build compiled with
  `-finstrument-functions` (scripts/selfhost-perf-prof.c).  The phase split reads
  the *inclusive* time of the driver functions `loadGraph` (read the file, discover
  the modules), `parseCommandAt` (the parser, called once per command from
  `stepCommand`), `runGraph` (all modules elaborated: parse + elaboration + kernel
  checking), `cOf` (diagnostics, comments, `genProgramArgs` and `docsText`) and
  `writeOut`.  It scales each phase by the plain build's median wall time, so the
  instrumentation's cost cancels; the function table reports shares and exact call
  counts, not absolute seconds.

Symbol addresses are resolved from the binary's own ELF symbol table (static
functions included; no `nm` needed), so the profiled binary is linked `-no-pie`.
"""
import argparse
import json
import os
import re
import shutil
import statistics
import struct
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def say(*a):
    print(*a, flush=True)


# ----------------------------------------------------------------------------------
# Measuring: wall time and the process tree's peak RSS

def tree_rss(procs, root):
    total = 0
    for pid, (ppid, rss) in procs.items():
        p = pid
        for _ in range(64):
            if p == root:
                total += rss
                break
            nxt = procs.get(p)
            if nxt is None or p <= 1:
                break
            p = nxt[0]
    return total


def snapshot():
    procs = {}
    page = os.sysconf("SC_PAGE_SIZE")
    for name in os.listdir("/proc"):
        if not name.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % name, "rb") as f:
                data = f.read()
        except OSError:
            continue
        r = data.rfind(b")")
        if r < 0:
            continue
        parts = data[r + 2:].split()
        if len(parts) < 22:
            continue
        try:
            procs[int(name)] = (int(parts[1]), int(parts[21]) * (page // 1024))
        except ValueError:
            continue
    return procs


def measure(argv, cwd, stdout_path=None, env=None):
    """Run argv to completion; return (seconds, peak_kib, exit code)."""
    start = time.monotonic()
    out = open(stdout_path, "wb") if stdout_path else subprocess.DEVNULL
    try:
        p = subprocess.Popen(argv, cwd=cwd, stdout=out, stderr=subprocess.PIPE,
                             env=env)
        peak = 0
        while p.poll() is None:
            peak = max(peak, tree_rss(snapshot(), p.pid))
            time.sleep(0.005)
        err = p.stderr.read().decode("utf-8", "replace")
        return time.monotonic() - start, peak, p.returncode, err
    finally:
        if stdout_path:
            out.close()


def run_checked(argv, cwd, env, what):
    secs, peak, code, err = measure(argv, cwd, None, env)
    if code != 0:
        say("selfhost-perf: %s failed (exit %d): %s" % (what, code, " ".join(argv)))
        if err.strip():
            say(err.rstrip())
        sys.exit(1)
    return secs, peak


# ----------------------------------------------------------------------------------
# The instrumented run's output

def parse_profile(path):
    """(total-ticks, elapsed-seconds, {address: (calls, excl, incl)})."""
    total_ticks = elapsed = None
    funcs = {}
    with open(path) as f:
        for line in f:
            parts = line.split()
            if not parts:
                continue
            if parts[0] == "ticks":
                total_ticks, elapsed = int(parts[1]), float(parts[2])
            elif parts[0] == "fn":
                funcs[int(parts[1], 16)] = (int(parts[2]), int(parts[3]), int(parts[4]))
    if elapsed is None or not total_ticks:
        raise SystemExit("selfhost-perf: %s has no `ticks` line" % path)
    return total_ticks, elapsed, funcs


# ----------------------------------------------------------------------------------
# ELF64 symbol table (STT_FUNC), no binutils needed

def elf_functions(path):
    with open(path, "rb") as f:
        data = f.read()
    if data[:4] != b"\x7fELF":
        raise SystemExit("selfhost-perf: %s is not an ELF file" % path)
    if data[4] != 2:
        raise SystemExit("selfhost-perf: %s is not ELF64" % path)
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 0x3A)
    if not shoff or not shnum:
        raise SystemExit("selfhost-perf: %s has no section headers (stripped?)" % path)

    def section(i):
        off = shoff + i * shentsize
        name, typ, flags, addr, soff, size, link, info, align, entsize = \
            struct.unpack_from("<IIQQQQIIQQ", data, off)
        return dict(name=name, type=typ, addr=addr, off=soff, size=size,
                    link=link, entsize=entsize)

    secs = [section(i) for i in range(shnum)]
    symtab = next((s for s in secs if s["type"] == 2), None)  # SHT_SYMTAB
    if symtab is None:
        raise SystemExit("selfhost-perf: %s has no .symtab (do not strip it)" % path)
    strtab = secs[symtab["link"]]
    syms = {}
    entsize = symtab["entsize"] or 24
    for off in range(symtab["off"], symtab["off"] + symtab["size"], entsize):
        st_name, st_info, st_other, st_shndx, st_value, st_size = \
            struct.unpack_from("<IBBHQQ", data, off)
        if (st_info & 0xF) != 2 or st_value == 0:  # STT_FUNC
            continue
        end = data.index(b"\0", strtab["off"] + st_name)
        name = data[strtab["off"] + st_name:end].decode("latin-1")
        syms[st_value] = name
    return syms


MANGLE = re.compile(r"_(\d+)_")


def demangle(name):
    return MANGLE.sub(lambda m: chr(int(m.group(1))), name)


def lookup_all(syms, name):
    """Every symbol a Wiz name may have been compiled to: the bare C name, `d_<name>`
    (a direct call) and `w_<name>` (the boxed wrapper)."""
    out = []
    for prefix in ("", "d_", "w_"):
        want = prefix + name
        for a, n in syms.items():
            if n == want or n.startswith(want + "."):
                out.append(a)
    return out


def lookup(syms, name):
    addrs = lookup_all(syms, name)
    return addrs[0] if addrs else None


def secs_of(funcs, addr, total_ticks, elapsed):
    calls, excl, incl = funcs.get(addr, (0, 0, 0))
    return calls, excl * elapsed / total_ticks, incl * elapsed / total_ticks


# ----------------------------------------------------------------------------------
# Reporting

def fmt(x, w=9, p=2):
    return ("%*.*f" % (w, p, x))


def report(args):
    binary = os.path.abspath(args.binary)
    prof = os.path.abspath(args.profile_binary) if args.profile_binary else None
    inp = args.input
    workdir = os.path.abspath(args.out)
    os.makedirs(workdir, exist_ok=True)
    env = dict(os.environ)
    env.update({k: v for k, v in (kv.split("=", 1) for kv in args.env)})
    cwd = os.path.abspath(args.cwd)

    st = os.stat(os.path.join(cwd, inp))
    with open(os.path.join(cwd, inp), "rb") as f:
        nlines = f.read().count(b"\n")
    say("input     %s (%d lines, %d bytes)" % (inp, nlines, st.st_size))
    say("selfhost  %s (-O1)" % binary)

    def cmd(sub, extra=()):
        return [binary, sub, "--no-cache", "-I", "lib", inp, *extra]

    cfile = os.path.join(workdir, "Frontend.c")
    phases = {}
    for sub in ("check", "build"):
        extra = ["-o", cfile] if sub == "build" else []
        runs = []
        for i in range(args.reps):
            argv = cmd(sub, extra)
            if args.dry:
                say("+ " + " ".join(argv))
                continue
            runs.append(run_checked(argv, cwd, env, sub))
        if not runs:
            continue
        walls = [r[0] for r in runs]
        peaks = [r[1] for r in runs]
        med = statistics.median(walls)
        phases[sub] = med
        say("%-8s  median %s s   [%s]   peak %d MiB" % (
            sub, fmt(med, 7), " ".join("%.2f" % w for w in walls),
            max(peaks) // 1024))
    if os.path.exists(cfile):
        size = os.path.getsize(cfile)
        md5 = subprocess.run(["md5sum", cfile], capture_output=True, text=True).stdout.split()[0]
        say("C output  %s (%d bytes, md5 %s)" % (os.path.relpath(cfile, cwd), size, md5))

    if not prof or args.dry:
        return

    # The instrumented runs.
    prof_file = os.path.join(workdir, "prof-check.txt")
    prof_build = os.path.join(workdir, "prof-build.txt")
    prof_c = os.path.join(workdir, "prof-Frontend.c")
    prof_env = dict(env)
    for path, sub, extra, where in ((prof_file, "check", [], None),
                                    (prof_build, "build", ["-o", prof_c], None)):
        argv = [os.path.abspath(prof), sub, "--no-cache", "-I", "lib", inp, *extra]
        say("profiling %s ..." % sub)
        secs, peak, code, err = measure(argv, cwd, path, prof_env)
        if code != 0:
            say("selfhost-perf: profiled %s failed (exit %d)" % (sub, code))
            if err.strip():
                say(err.rstrip())
            sys.exit(1)

    syms = elf_functions(prof)
    words = {a: demangle(n) for a, n in syms.items()}

    t_check, e_check, f_check = parse_profile(prof_file)
    t_build, e_build, f_build = parse_profile(prof_build)

    def table(total_ticks, elapsed, funcs, total_wall, label):
        rows = []

        def add(name, disp):
            cands = lookup_all(syms, name)
            if not cands:
                return None
            a = max(cands, key=lambda x: funcs.get(x, (0, 0, 0))[2])
            calls, excl, incl = secs_of(funcs, a, total_ticks, elapsed)
            rows.append((disp, a, calls, excl, incl))
            return incl

        load = add("loadGraph", "load")
        run = add("runGraph", "elaborate")
        add("parseCommandAt", "  parse")
        emit = add("cOf", "emit")
        write = add("writeOut", "write")
        used = sum(v for v in (load, run, emit, write) if v)
        other = max(0.0, total_wall - used)
        say("")
        say("phase table (%s; seconds scaled to the plain run's median of %s s)"
            % (label, fmt(total_wall, 5)))
        say("  %-12s %10s %8s" % ("phase", "s", "%"))
        for disp, a, calls, excl, incl in rows:
            say("  %-12s %10.2f %7.1f%%" % (disp, incl, 100.0 * incl / total_wall if total_wall else 0))
        if other > 0.005:
            say("  %-12s %10.2f %7.1f%%" % ("other", other, 100.0 * other / total_wall if total_wall else 0))
        say("  %-12s %10.2f" % ("total", total_wall))

    if "check" in phases:
        table(t_check, e_check, f_check, phases["check"], "check")
    if "build" in phases:
        table(t_build, e_build, f_build, phases["build"], "build")

    def top(total_ticks, elapsed, funcs, label, n=15):
        rows = []
        for a, (calls, excl, incl) in funcs.items():
            name = words.get(a)
            if name is None:
                continue
            rows.append((excl * elapsed / total_ticks, incl * elapsed / total_ticks,
                         calls, name))
        rows.sort(reverse=True)
        say("")
        say("top functions by exclusive time (%s; -O1 -fno-inline -finstrument-functions)" % label)
        say("  %-42s %10s %8s %8s" % ("function", "calls", "excl s", "excl %"))
        total = sum(r[0] for r in rows) or 1.0
        for excl, incl, calls, name in rows[:n]:
            say("  %-42s %10d %8.2f %7.1f%%" % (name[:42], calls, excl, 100.0 * excl / total))
        return rows

    if "check" in phases:
        top(t_check, e_check, f_check, "check")
    if "build" in phases:
        top(t_build, e_build, f_build, "build")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--binary", required=True, help="the plain -O1 selfhost compiler")
    ap.add_argument("--profile-binary", help="the -finstrument-functions build")
    ap.add_argument("--input", default="selfhost/Frontend.wiz")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--cwd", default=ROOT)
    ap.add_argument("--out", default=os.path.join(ROOT, ".lake", "selfhost-perf"))
    ap.add_argument("--env", action="append", default=[], metavar="K=V")
    ap.add_argument("--no-profile", action="store_true")
    ap.add_argument("--dry", action="store_true")
    report(ap.parse_args())


if __name__ == "__main__":
    main()
