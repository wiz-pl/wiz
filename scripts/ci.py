#!/usr/bin/env python3
"""Helpers for .github/workflows/ci.yml.

  scripts/ci.py matrix [--only JSON] [BIN]
                                     the shards of .github/test-shards.json as a JSON
                                     matrix (one line, for $GITHUB_OUTPUT); each shard's
                                     selectors are joined by newlines, "heavy"
                                     says whether it may use the self-hosted runner, and
                                     "jobs" how many cases it runs at a time (`--jobs`);
                                     with --only ["NAME",…], only those shards (and
                                     their parts) A shard with
                                     "split": N becomes N shards NAME-1 … NAME-N, its
                                     cases balanced by .github/test-timings.json (needs
                                     the test driver BIN; default .lake/build/bin/tests).
                                     A shard with "parts": N becomes N shards NAME-1 …
                                     NAME-N that select the same cases and carry
                                     "part": "i/N" for the driver's `--part i/N`, which
                                     splits one case's work by index inside the case
                                     (selfhost-libdiff)
  scripts/ci.py check-shards [BIN]   check that every test case is run by exactly one
                                     shard (after splitting; the N jobs of a `parts`
                                     shard count as that one shard, because the case
                                     partitions its own files), and that every selector
                                     of a shard selects something. A group that no
                                     selector picks goes to the shard it names
                                     (`Group.shard`) or to the shard with
                                     "default": true (`resolved`)
  scripts/ci.py libdiff-union TXT JSONL..
                                     prove that the selfhost-libdiff `parts` cover the
                                     corpus once: the part.txt headers agree on the
                                     total, the parts are 1..N, the records' files are
                                     .github/libdiff-corpus.txt with no duplicate, the
                                     verdicts sum to the total (a whole run's summary,
                                     recomputed) and none is `bounded`
  scripts/ci.py plan [BIN]           the split shards' parts with their estimated times
  scripts/ci.py changes BASE [HEAD]  what a change needs (path filters): reads the files
                                     that differ between BASE and HEAD (git diff
                                     BASE HEAD; CI: a PR's merge commit and its first
                                     parent) and prints GitHub outputs: code=true
                                     unless only docs changed, docs=true when a doc
                                     changed, web=true when a browser-facing file
                                     (`web/*`) changed, and shards=[NAMES], the shards of
                                     .github/test-shards.json to run (each shard's
                                     "inputs", see `needed_shards`). `changes --all`
                                     prints everything
  scripts/ci.py summary TITLE FILE.. a Markdown summary for $GITHUB_STEP_SUMMARY of
                                     `lake test` logs (*.log: pass/fail, failing cases)
                                     and `--timings` files (*.jsonl: a table of every
                                     case's time with group and shard totals; with
                                     several shards, a table of the shards and the
                                     slowest cases)
  scripts/ci.py baseline JSONL..     a new .github/test-timings.json (stdout) from
                                     `--timings` files, e.g. the `test-timings`
                                     artifact of a CI run (the split shards' cases)
  scripts/ci.py balance [--factor F] [--baseline-out FILE] [--strict] JSONL..
                                     check a run's shard balance from its `--timings`
                                     files: the longest shard's test time is at most F
                                     (default 1.5) times the median shard's, every case
                                     of a split shard is in .github/test-timings.json,
                                     and no shared program is built by two parts of one
                                     split shard. Prints GitHub warning annotations and
                                     a Markdown report (stdout); on drift, writes the
                                     regenerated baseline to FILE. Exits 0 (1 with
                                     --strict when there is drift)
  scripts/ci.py check-skips [--max-ratio F] [--allow FILE] LOG|JSONL..
                                     a green run must have tested something: fail when
                                     a group skipped wholesale, when a skip names a tool
                                     the CI dev shell must provide (cc, GMP, GC, yosys,
                                     node, nix, …), when a group's unexplained skipped
                                     ratio is over F (default 0.25, of the group's
                                     cases in all shards), or when the logs parse no
                                     records at all. A skip excused by an entry of
                                     .github/skip-allowlist.json (same group and case
                                     exactly, a reason the skip's starts with, and an
                                     expiry still in the future) is explained (reported,
                                     not failed); anything else that skips wholesale is a
                                     failure. Reads `lake test` logs and `--timings`
                                     files. `--self-test` checks the rule on synthetic
                                     logs and exits 1 if it is wrong

Selectors are the arguments of `lake test --`: `=NAME` selects the group NAME,
`=NAME#I,J` the cases I and J of it, anything else is a prefix of group names (see
Tests/Main.lean).
"""
import datetime as dt
import fnmatch, json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SHARDS = os.path.join(ROOT, ".github", "test-shards.json")
TIMINGS = os.path.join(ROOT, ".github", "test-timings.json")
SKIPS = os.path.join(ROOT, ".github", "skip-allowlist.json")
DEFAULT_BIN = os.path.join(ROOT, ".lake/build/bin/tests")
NOTE_USES = "uses "
NOTE_BUILT = "built "

# A skip whose reason names one of these says the CI dev shell (flake.nix,
# `devShells.default`) lacks a tool the suite needs: a failure for every group, not an
# environment skip, because CI runs every step in that shell. Matched as a lowercase
# substring (so "no node" also covers "no nodejs"). A tool that is only needed on some
# machines (iverilog, an ARM toolchain) is not here: the allow-list excuses it instead.
REQUIRED_TOOLS = [
    ("no toolchain", "cc and GMP (the C toolchain)"),
    # `=selfhost-libdiff`'s sweep says this when `selfhostCompiler` cannot find gmp.h;
    # with the case split into parts, only that case skips, so the group's ratio would
    # hide it (1 of 5 cases per part): the reason alone must fail the lint.
    ("no c toolchain", "cc and GMP (the C toolchain)"),
    ("no garbage collector", "Boehm GC (--gc-cflags)"),
    ("no yosys", "yosys"),
    ("no node", "node"),
    ("no nix", "nix"),
    ("no llc", "llc (LLVM)"),
    ("no z3", "z3"),
    ("no cadical", "cadical"),
    ("no wiz binary", "the wiz binary"),
    ("no grail beside", "grail beside the test driver"),
]


def shards():
    with open(SHARDS) as f:
        return json.load(f)


def resolved(binary):
    """The shards of .github/test-shards.json, with each group that no shard's selectors
    pick added (as `=NAME`) to the shard that the group names (`Group.shard`, `tests
    --list-shards`), else to the shard marked `"default": true`. So a new group needs no
    edit here; selectors still win over a group's own choice."""
    ss = shards()
    names = {s["name"]: s for s in ss}
    defaults = [s for s in ss if s.get("default")]
    if len(defaults) != 1:
        sys.exit(f"{SHARDS}: exactly one shard must have \"default\": true (found {len(defaults)})")
    out = subprocess.run([binary, "--list-shards"], capture_output=True, text=True, check=True,
                         cwd=ROOT).stdout
    for line in out.split("\n"):
        if not line:
            continue
        g, _, hint = line.partition("\t")
        if any(selects(g, sel) for s in ss for sel in s["select"]):
            continue
        if hint and hint not in names:
            sys.exit(f"group {g!r} asks for the shard {hint!r}, which .github/test-shards.json lacks")
        (names[hint] if hint else defaults[0]).setdefault("added", []).append(f"={g}")
    for s in ss:
        s["select"] = s["select"] + s.pop("added", [])
    return ss


def selects(group, sel):
    return group == sel[1:].split("#")[0] if sel.startswith("=") else group.startswith(sel)


def list_cases(binary, sels):
    """The cases that the selectors pick: [(group, index, name)]."""
    out = subprocess.run([binary, "--list-cases", *sels], capture_output=True, text=True,
                         check=True, cwd=ROOT).stdout
    return [(g, int(i), n) for g, i, n in (l.split("\t", 2) for l in out.split("\n") if l)]


def baseline():
    """.github/test-timings.json: {"cases": {group: {case: {"seconds": S, "uses": [R]}}},
    "builds": {R: S}}; a case's seconds leave out the builds it did."""
    try:
        with open(TIMINGS) as f:
            return json.load(f)
    except FileNotFoundError:
        return {"cases": {}, "builds": {}}


def estimate(cases, base):
    """[(group, index, name, seconds, uses)], from the baseline."""
    out = []
    for g, i, n in cases:
        known = base["cases"].get(g, {})
        if n in known:
            out.append((g, i, n, known[n]["seconds"], tuple(known[n].get("uses", []))))
        else:
            # a new case: the group's median time, and the programs that most of the
            # group's cases use (wrongly assumed, it only sits with their users)
            ts = sorted(c["seconds"] for c in known.values()) or [1.0]
            sets = [tuple(c.get("uses", [])) for c in known.values()]
            uses = max(sorted(set(sets)), key=sets.count) if sets else ()
            out.append((g, i, n, ts[len(ts) // 2], uses))
    return out


def part_cost(items, builds):
    uses = {r for it in items for r in it[4]}
    return sum(it[3] for it in items) + sum(builds.get(r, 0.0) for r in uses)


def partition(items, n, builds):
    """Split the cases into n parts with the smallest longest part (estimated). The
    cases that use the same shared programs (the self-hosted checker or compiler: the
    first case that needs one builds it) stay together, so each program is built by one
    part only; the other cases fill the parts up. Greedy, longest first, then single
    moves while they help; deterministic."""
    clusters = {}
    for it in items:
        clusters.setdefault(it[4], []).append(it)
    # the units to place: a cluster per set of programs, and each remaining case
    units = [c for uses, c in clusters.items() if uses] + [[it] for it in clusters.get((), [])]
    units.sort(key=lambda u: (-part_cost(u, builds), u[0][0], u[0][1]))
    parts = [[] for _ in range(n)]
    cost = lambda us: part_cost([it for u in us for it in u], builds)
    for u in units:
        k = min(range(n), key=lambda k: (cost(parts[k] + [u]), k))
        parts[k].append(u)
    improved = True
    while improved:
        improved = False
        span = max(cost(p) for p in parts)
        for a in sorted(range(n), key=lambda k: -cost(parts[k])):
            for u in parts[a]:
                for b in range(n):
                    if b == a:
                        continue
                    pa = [x for x in parts[a] if x is not u]
                    trial = [pa if j == a else p + [u] if j == b else p for j, p in enumerate(parts)]
                    if max(cost(p) for p in trial) < span - 1e-9:
                        parts, improved = trial, True
                        break
                if improved:
                    break
            if improved:
                break
    return [sorted((it for u in p for it in u), key=lambda it: (it[0], it[1])) for p in parts]


def part_selectors(items):
    """The selectors of a part: `=GROUP#I,J,…` per group, in the groups' order."""
    groups = []
    for g, i, *_ in items:
        if not groups or groups[-1][0] != g:
            groups.append((g, []))
        groups[-1][1].append(i)
    return [f"={g}#{','.join(map(str, ixs))}" for g, ixs in groups]


def expanded(binary, base=None):
    """The shards with each split shard replaced by its parts: [(name, selectors,
    estimated seconds or None, jobs, part)]; `jobs` is the shard's "--jobs" (None unless
    the shard says "jobs": N: the number of cases of a parallel-opted-in group it runs at
    a time). A shard without "jobs" is run without `--jobs`, so a case that has an auto
    mode (selfhost-libdiff) can tell "not given" from "--jobs 1". `part` is the "i/n"
    for the driver's `--part` (None unless the shard says "parts": N), which splits one
    case's work by index inside the case; every part selects the same cases and there is
    no case to balance (the estimated cost is None)."""
    out = []
    for s in resolved(binary):
        n = s.get("split", 1)
        jobs = s.get("jobs")
        nparts = s.get("parts", 1)
        if not isinstance(nparts, int) or isinstance(nparts, bool) or nparts < 1:
            sys.exit(f"{SHARDS}: shard {s['name']!r}: \"parts\" must be an integer >= 1")
        if nparts > 1:
            if n > 1:
                sys.exit(f"{SHARDS}: shard {s['name']!r} has both \"split\" and \"parts\": "
                         "one splits cases, the other splits a case's work")
            for i in range(1, nparts + 1):
                out.append((f"{s['name']}-{i}", s["select"], None, jobs, f"{i}/{nparts}"))
            continue
        if n <= 1:
            out.append((s["name"], s["select"], None, jobs, None))
            continue
        base = base or baseline()
        items = estimate(list_cases(binary, s["select"]), base)
        for k, p in enumerate(partition(items, n, base["builds"]), 1):
            if p:
                out.append((f"{s['name']}-{k}", part_selectors(p), part_cost(p, base["builds"]),
                            jobs, None))
    return out


def matrix(binary, only=None):
    shard_list = expanded(binary)  # first: it validates "parts"
    # "heavy": true shards (and the parts of a split or `parts` one) may run on the
    # self-hosted runner (vars.WIZ_RUNNER_HEAVY, docs/ci-runner.md)
    heavy = {s["name"] for s in shards() if s.get("heavy")}
    split = {s["name"] for s in shards() if s.get("split", 1) > 1}
    parts = {s["name"] for s in shards() if s.get("parts", 1) > 1}
    def is_heavy(n):
        base = n.rsplit("-", 1)[0]
        return n in heavy or (base in (split | parts) and base in heavy)
    def wanted(n):
        base = n.rsplit("-", 1)[0]
        return only is None or n in only or (base in (split | parts) and base in only)
    print(json.dumps({"shard": [{"name": n, "select": "\n".join(sel), "heavy": is_heavy(n),
                                 "jobs": jobs, "part": part}
                                for n, sel, _, jobs, part in shard_list if wanted(n)]}, ensure_ascii=False))


def plan(binary):
    base = baseline()
    for name, sel, est, _, _ in expanded(binary, base):
        if est is None:
            continue
        cases = list_cases(binary, sel)
        uses = sorted({r for *_, u in estimate(cases, base) for r in u})
        print(f"{name}: {len(cases)} cases, ~{est:.0f} s estimated"
              + (f" (builds {', '.join(uses)})" if uses else ""))
        for g, i, n in cases:
            print(f"    {g} #{i} {n}")
    return 0


def check_shards(binary):
    out = subprocess.run([binary, "--list"], capture_output=True, text=True, check=True).stdout
    groups = [g for g in out.split("\n") if g]
    errors = []
    names = set()
    for s in shards():
        if s["name"] in names:
            errors.append(f"shard name {s['name']!r} is used twice")
        names.add(s["name"])
        for sel in s["select"]:
            if not any(selects(g, sel) for g in groups):
                errors.append(f"shard {s['name']!r}: selector {sel!r} selects no group")
    runs = {(g, i): [] for g, i, _ in list_cases(binary, [])}
    parts = expanded(binary)
    # A `parts` shard runs the same case in all of its N jobs by construction (the case
    # partitions its own file list with `--part i/n`), so for "each case in exactly one
    # shard" count the N jobs as the one shard they came from. Without this, a split
    # case would be reported as run by six shards.
    parts_bases = {s["name"] for s in shards() if s.get("parts", 1) > 1}
    def shard_base(name):
        return split_of(name, parts_bases) or name
    names_seen = set()
    for name, sel, *_ in parts:
        if name in names_seen:
            errors.append(f"shard {name!r} is used twice")
        names_seen.add(name)
        for g, i, _ in set(list_cases(binary, sel)):  # a case selected twice within a shard still runs once
            runs[(g, i)].append(name)
    for g in groups:
        missing = [i for (h, i), by in runs.items() if h == g and not by]
        if missing:
            errors.append(f"group {g!r}: {'all' if len(missing) == sum(1 for h, _ in runs if h == g) else len(missing)} "
                          f"of its cases are in no shard")
    for (g, i), by in runs.items():
        distinct = sorted({shard_base(n) for n in by})
        if len(distinct) > 1:
            errors.append(f"case {g} #{i} is run by several shards: {', '.join(distinct)}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    # a split shard's cases without a baseline entry are balanced by guesswork; warn
    # (a new case has no time until a CI run measured it, so this cannot be an error)
    base = baseline()
    for s in resolved(binary):
        if s.get("split", 1) > 1:
            new = [n for g, _, n in list_cases(binary, s["select"]) if n not in base["cases"].get(g, {})]
            if new:
                warn(f"{len(new)} cases of the split shard {s['name']!r} are unbalanced: not in "
                     f".github/test-timings.json (estimated at their group's median)", "Shard balance")
    print(f"ok: {len(groups)} groups, {len(runs)} cases, each in exactly one of {len(parts)} shards")
    return 0


# Path filters (`changes`). Files only people read: a change of only these runs no build
# and no tests.
DOCS = ["docs/*", "*.md", "LICENSE", "COPYING*"]
# Browser-facing sources: the playground, the infoview and site scripts, their Node
# tests and the Wiz programs they are built from. The `web` job (`ci.yml`) builds the
# Wasm modules and runs the browser-free half of web/test.sh when one of these changes;
# the Chromium half of that script stays local.
WEB = ["web/*"]
# Files every shard depends on: the Lean sources (compiler, tests, grail), the
# build and its toolchain, the C runtime, CI itself, and the web/ tree — its Wiz
# sources and JS hosts are read by test groups (`web/Web.wiz`, `web/framework/gen.wiz`,
# `web/wasm-host.mjs`), and a change there is checked by the `web` job rather than by
# one shard, so it sends every shard to be safe. A change to any runs every shard.
EVERYTHING = ["*.lean", "lakefile.*", "lean-toolchain", "lake-manifest.json", "flake.*",
              ".envrc", "runtime/*", "c/*", "scripts/*", ".github/*", "grail.wiz",
              "web/*"]


def matches(path, globs):
    """fnmatch with `*` crossing `/` (so `docs/*` is the whole tree, `*.md` any file)."""
    return any(fnmatch.fnmatchcase(path, g) for g in globs)


def lib_closure(paths):
    """`paths` plus the lib/ files they import, transitively (`import A.B` is
    lib/A/B.wiz)."""
    out, todo = set(), list(paths)
    while todo:
        p = todo.pop()
        if p in out:
            continue
        out.add(p)
        try:
            text = open(os.path.join(ROOT, p)).read()
        except OSError:
            continue
        for m in re.finditer(r"^import ([\w.]+)", text, re.M):
            todo.append("lib/" + m.group(1).replace(".", "/") + ".wiz")
    return out


def needed_shards(files):
    """The shards a change needs: all of them when a file of EVERYTHING changed; else a
    shard with "inputs" (globs; lib/ files among them bring the lib/ files they import)
    when one of its inputs changed, and a shard without "inputs" when anything but docs
    changed. Nothing for a docs-only change."""
    code = [f for f in files if not matches(f, DOCS)]
    ss = shards()
    if any(matches(f, EVERYTHING) for f in code):
        return [s["name"] for s in ss]
    out = []
    for s in ss:
        if "inputs" not in s:
            if code:
                out.append(s["name"])
            continue
        globs = list(s["inputs"])
        plain = [g for g in globs if not any(c in g for c in "*?[")]
        globs += sorted(lib_closure(plain))
        if any(matches(f, globs) for f in code):
            out.append(s["name"])
    return out


def changes(args):
    if args[:1] == ["--all"]:
        names = [s["name"] for s in shards()]
        print("code=true")
        print("docs=true")
        print("web=true")
        print(f"shards={json.dumps(names)}")
        return 0
    base, head = args[0], (args[1] if len(args) > 1 else "HEAD")
    out = subprocess.run(["git", "diff", "--name-only", base, head], capture_output=True,
                         text=True, check=True, cwd=ROOT).stdout
    files = [f for f in out.split("\n") if f]
    names = needed_shards(files)
    code = any(not matches(f, DOCS) for f in files)
    docs = any(matches(f, DOCS) for f in files)
    web = any(matches(f, WEB) for f in files)
    print(f"code={'true' if code else 'false'}")
    print(f"docs={'true' if docs else 'false'}")
    print(f"web={'true' if web else 'false'}")
    print(f"shards={json.dumps(names)}")
    print(f"{len(files)} files changed; code: {code}; docs: {docs}; web: {web}; "
          f"shards: {', '.join(names) or 'none'}", file=sys.stderr)
    return 0


GROUP = re.compile(r"^── (.*?) \((.*)\)$")
PASS = re.compile(r"^  ✓ (.*?)(?: \([\d.]+ s\))?$")
FAIL = re.compile(r"^  ✗ (.*?)(?: \([\d.]+ s\))?$")
SKIP = re.compile(r"^  ⊘ (.*?)(?: \([\d.]+ s\))?$")
TIME = re.compile(r"^  \((.*): ([\d.]+) s(?:;.*)?\)$")
TOTAL = re.compile(r"^(\d+) passed, (\d+) failed(?:, (\d+) skipped)?$")


def parse_log(path):
    """(groups, total) of one `lake test` log; groups: [name, passed, failed, seconds,
    [(case, detail)]]; total: (passed, failed, skipped), or None if the driver did not finish."""
    groups, total = [], None
    lines = open(path, encoding="utf-8", errors="replace").read().split("\n")
    for i, line in enumerate(lines):
        if m := GROUP.match(line):
            groups.append([m.group(1), 0, 0, None, []])
        elif groups and (PASS.match(line) or SKIP.match(line)):
            groups[-1][1] += 1
        elif groups and (m := FAIL.match(line)):
            groups[-1][2] += 1
            detail = []
            for l in lines[i + 1:i + 6]:
                if not l.startswith("      "):
                    break
                detail.append(l.strip())
            groups[-1][4].append((m.group(1), " ".join(detail)[:300].replace("`", "'")))
        elif groups and (m := TIME.match(line)):
            groups[-1][3] = m.group(2)
        elif m := TOTAL.match(line):
            total = (int(m.group(1)), int(m.group(2)), int(m.group(3) or 0))
    return groups, total


def read_timings(paths):
    """The records of `--timings` files, in order."""
    out = []
    for p in paths:
        with open(p, encoding="utf-8") as f:
            out += [json.loads(l) for l in f if l.strip()]
    return out


def md(text):
    return str(text).replace("|", "\\|").replace("\n", " ")


def secs(x):
    return f"{x:.3f}"


def by_key(records, key):
    """The records grouped by a field, in order of first appearance."""
    out = {}
    for r in records:
        out.setdefault(r[key], []).append(r)
    return out


def timing_table(records):
    """Every case with its time, a subtotal per group and the total."""
    out = ["| group | case | | seconds |", "|---|---|:-:|---:|"]
    for g, rs in by_key(records, "group").items():
        for r in rs:
            out.append(f"| {md(g)} | {md(r['case'])} | {'✓' if r['ok'] else '✗'} | {secs(r['seconds'])} |")
        out.append(f"| **{md(g)}** | **{len(rs)} cases** | | **{secs(sum(r['seconds'] for r in rs))}** |")
    out.append(f"| **total** | **{len(records)} cases** | | **{secs(sum(r['seconds'] for r in records))}** |")
    return out


def shard_table(records):
    """A line per shard (its groups, cases and time) and the grand total."""
    out = ["| shard | groups | cases | passed | failed | seconds |", "|---|---:|---:|---:|---:|---:|"]
    for sh, rs in sorted(by_key(records, "shard").items(), key=lambda kv: -sum(r["seconds"] for r in kv[1])):
        ok = sum(r["ok"] for r in rs)
        out.append(f"| {md(sh) or '(none)'} | {len(by_key(rs, 'group'))} | {len(rs)} | {ok} | {len(rs) - ok} | "
                   f"{secs(sum(r['seconds'] for r in rs))} |")
    ok = sum(r["ok"] for r in records)
    out.append(f"| **total** | **{len({(r['shard'], r['group']) for r in records})}** | **{len(records)}** | **{ok}** | "
               f"**{len(records) - ok}** | **{secs(sum(r['seconds'] for r in records))}** |")
    return out


def group_table(records):
    """A line per group of each shard, a subtotal per shard and the grand total."""
    out = ["| shard | group | cases | seconds |", "|---|---|---:|---:|"]
    for sh, rs in by_key(records, "shard").items():
        for g, gs in by_key(rs, "group").items():
            out.append(f"| {md(sh)} | {md(g)} | {len(gs)} | {secs(sum(r['seconds'] for r in gs))} |")
        out.append(f"| **{md(sh)}** | **total** | **{len(rs)}** | **{secs(sum(r['seconds'] for r in rs))}** |")
    out.append(f"| **all shards** | **total** | **{len(records)}** | **{secs(sum(r['seconds'] for r in records))}** |")
    return out


def slowest_table(records, n=15):
    out = ["| | shard | group | case | seconds |", "|---:|---|---|---|---:|"]
    for k, r in enumerate(sorted(records, key=lambda r: -r["seconds"])[:n], 1):
        out.append(f"| {k} | {md(r['shard'])} | {md(r['group'])} | {md(r['case'])} | {secs(r['seconds'])} |")
    return out


def summary(title, files):
    logs = [f for f in files if not f.endswith(".jsonl")]
    records = read_timings([f for f in files if f.endswith(".jsonl")])
    groups, passed, failed, skipped, unfinished = [], 0, 0, 0, []
    for log in logs:
        g, total = parse_log(log)
        groups += g
        if total is None:
            unfinished.append(os.path.basename(log))
        else:
            passed, failed, skipped = passed + total[0], failed + total[1], skipped + total[2]
    out = [f"### {title}", ""]
    mark = "✅" if failed == 0 and not unfinished and logs else "❌"
    out.append(f"{mark} **{passed} passed, {failed} failed" + (f", {skipped} skipped" if skipped else "") + "**"
               + (f" in {secs(sum(r['seconds'] for r in records))} s of test time" if records else ""))
    if unfinished:
        out.append(f"\n**The test driver did not finish** in: {', '.join(unfinished)} (see the log).")
    if not logs:
        out.append("\nNo test logs.")
    fails = [(g[0], c, d) for g in groups for c, d in g[4]]
    if fails:
        out += ["", "<details open><summary>failing cases</summary>", ""]
        out += [f"- **{g}**: {c}" + (f" — `{d}`" if d else "") for g, c, d in fails[:200]]
        out += ["", "</details>"]
    shards = by_key(records, "shard")
    if len(shards) > 1:
        out += ["", "#### Shards", ""] + shard_table(records)
        out += ["", "#### The 15 slowest cases", ""] + slowest_table(records)
        out += ["", "<details><summary>groups</summary>", ""] + group_table(records) + ["", "</details>"]
        out += ["", "<details><summary>every case</summary>", ""]
        for sh, rs in shards.items():
            out += ["", f"##### {md(sh)}", ""] + timing_table(rs)
        out += ["", "</details>"]
    elif records:
        out += [""] + timing_table(records)
    else:
        out += ["", "| group | passed | failed | time |", "|---|---:|---:|---:|"]
        for name, p, f, t, _ in groups:
            out.append(f"| {name} | {p} | {f} | {t + ' s' if t else ''} |")
    print("\n".join(out))
    return 0


def warn(msg, title):
    """A warning: a GitHub annotation in Actions, a plain line on stderr otherwise."""
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"::warning title={title}::{msg}", file=sys.stderr)
    else:
        print(f"warning: {msg}", file=sys.stderr)


def error(msg, title):
    """An error annotation: the step fails (the caller exits nonzero)."""
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"::error title={title}::{msg}", file=sys.stderr)
    else:
        print(f"error: {msg}", file=sys.stderr)


def split_of(shard, split):
    """The split shard that a shard (job) name belongs to, or None."""
    for n in split:
        if shard == n or re.fullmatch(re.escape(n) + r"-\d+", shard):
            return n
    return None


def balance(args):
    factor, out, strict, paths = 1.5, None, False, []
    it = iter(args)
    for a in it:
        if a == "--factor":
            factor = float(next(it))
        elif a == "--baseline-out":
            out = next(it)
        elif a == "--strict":
            strict = True
        else:
            paths.append(a)
    records = read_timings(paths)
    if not records:
        print("No case timings: the shard balance was not checked.")
        return 0
    totals = {sh: sum(r["seconds"] for r in rs) for sh, rs in by_key(records, "shard").items()}
    ranked = sorted(totals.items(), key=lambda kv: -kv[1])
    ts = sorted(totals.values())
    median = (ts[(len(ts) - 1) // 2] + ts[len(ts) // 2]) / 2
    longest, top = ranked[0]
    problems = []
    if median > 0 and top > factor * median:
        problems.append(f"the longest shard {longest} ({top:.0f} s of tests) is {top / median:.1f}x the "
                        f"median shard ({median:.0f} s), over the limit of {factor}x")
    base = baseline()
    split = [s["name"] for s in shards() if s.get("split", 1) > 1]
    new = sorted({(r["group"], r["case"]) for r in records if split_of(r["shard"], split)
                  and r["case"] not in base["cases"].get(r["group"], {})})
    if new:
        problems.append(f"{len(new)} cases unbalanced: not in .github/test-timings.json")
    built = {}
    for r in records:
        if (n := split_of(r["shard"], split)):
            for note in r.get("notes", []):
                if note.startswith(NOTE_BUILT):
                    built.setdefault((n, note[len(NOTE_BUILT):].rsplit(" ", 1)[0]), set()).add(r["shard"])
    for (n, res), parts in sorted(built.items()):
        if len(parts) > 1:
            problems.append(f"the {res} is built by {len(parts)} parts of {n} ({', '.join(sorted(parts))}): "
                            f"its users are split, the baseline is stale")
    for p in problems:
        warn(p, "Shard balance")
    lines = ["### Shard balance", ""]
    lines.append(("⚠️ **Out of balance**: " + "; ".join(problems) + ".") if problems else
                 f"✅ Balanced: the longest shard ({longest}, {top:.0f} s) is {top / max(median, 1e-9):.2f}x the "
                 f"median ({median:.0f} s); limit {factor}x.")
    lines += ["", "| shard | seconds of tests | × median |", "|---|---:|---:|"]
    lines += [f"| {md(sh)} | {t:.0f} | {t / max(median, 1e-9):.2f} |" for sh, t in ranked]
    if new:
        lines += ["", "<details><summary>cases not in the baseline</summary>", ""]
        lines += [f"- {md(g)}: {md(c)}" for g, c in new[:200]] + ["", "</details>"]
    if problems and out:
        import contextlib, io
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            make_baseline(paths)
        with open(out, "w", encoding="utf-8") as f:
            f.write(buf.getvalue())
        lines += ["", f"A regenerated baseline from this run is in `{out}`."]
    print("\n".join(lines))
    return 1 if problems and strict else 0


# --- The `selfhost-libdiff` parts (`libdiff-union`) ----------------------------------
# The corpus one whole run compares: `libDiffFiles` sorts every `*.wiz` under lib/ and
# scry/. The manifest makes the union check prove coverage of *that* list, so a split
# that quietly drops a file (or a change to `libDiffFiles` that trims the corpus) fails
# instead of passing with a smaller, self-consistent total.
LIBDIFF_CORPUS = os.path.join(ROOT, ".github", "libdiff-corpus.txt")
PART_HEADER = re.compile(
    r"part=(\d+)/(\d+) files=(\d+) total=(\d+) ok=(\d+) rejected=(\d+) "
    r"diverging=(\d+) bounded=(\d+) workers=(\d+)")
PART_KEYS = ["part", "parts", "files", "total", "ok", "rejected", "diverging",
             "bounded", "workers"]
VERDICTS = ("ok", "rejected", "diverging", "bounded")


def part_header(path):
    """The fields of a `.lake/libdiff/part.txt` header, or None if it is not one."""
    try:
        with open(path, encoding="utf-8") as f:
            text = f.read().strip()
    except OSError:
        return None
    m = PART_HEADER.fullmatch(text)
    return dict(zip(PART_KEYS, map(int, m.groups()))) if m else None


def part_stem(path):
    """`logs/libdiff-selfhost-libdiff-2.jsonl` -> `selfhost-libdiff-2`."""
    b = os.path.basename(path)
    for ext in (".jsonl", ".txt"):
        if b.endswith(ext):
            b = b[:-len(ext)]
    return b[len("libdiff-"):] if b.startswith("libdiff-") else b


def libdiff_counts(recs):
    """The counts `libDiffSummarize` computes, from the union of the parts' records."""
    out = {k: 0 for k in VERDICTS}
    out["host_ok_self_error"] = out["host_error_self_ok"] = 0
    out["same_code"] = out["same_span"] = out["same_message"] = 0
    by_construct, by_code, blockers = {}, {}, []
    for r in recs:
        v = r.get("verdict", "")
        if v in VERDICTS:
            out[v] += 1
        host, self_ = r.get("host") or {}, r.get("self") or {}
        if v == "rejected":
            code = self_.get("code", "")
            by_code[code] = by_code.get(code, 0) + 1
            # `libDiffStep`: "" means same code, span and message; "span" keeps the
            # code; "message" keeps the code and the span
            d = r.get("divergence", "")
            if d in ("", "span", "message"):
                out["same_code"] += 1
            if d in ("", "message"):
                out["same_span"] += 1
            if d == "":
                out["same_message"] += 1
        elif v == "diverging":
            if host.get("accepted") and not self_.get("accepted"):
                out["host_ok_self_error"] += 1
                k = r.get("class", "")
                by_construct[k] = by_construct.get(k, 0) + 1
                blockers.append((r.get("file", ""), k, (self_.get("msg") or "")[:110]))
            elif not host.get("accepted") and self_.get("accepted"):
                out["host_error_self_ok"] += 1
    rank = lambda k: by_construct.get(k, 0)
    blockers.sort(key=lambda b: (-rank(b[1]), b[0]))
    return out, by_construct, by_code, blockers[:10]


def libdiff_union_self_test():
    """Check the union rule on synthetic part artifacts, without a CI run: a clean
    three-part split, a duplicate file, a missing file, a bounded record, a wrong total,
    a missing part, and a header that disagrees with its records."""
    import contextlib, io, tempfile
    global LIBDIFF_CORPUS
    saved, corpus = LIBDIFF_CORPUS, [f"g/{i}.wiz" for i in range(7)]

    def write(d, n, drop=None, dup=None, bounded=None, total=7, header_shift=0):
        for i in range(1, n + 1):
            files = [f for k, f in enumerate(corpus) if k % n == i - 1]
            if drop in files:
                files.remove(drop)
            if dup is not None and dup[1] == i:
                files.append(dup[0])
            recs = []
            for f in files:
                v = "bounded" if f == bounded else "rejected" if f.endswith("1.wiz") else \
                    "diverging" if f.endswith("2.wiz") else "ok"
                recs.append({"file": f, "verdict": v, "divergence": "", "class": "",
                             "host": {"accepted": v != "rejected"},
                             "self": {"accepted": v != "rejected", "code": "e"}})
            c = {k: sum(1 for r in recs if r["verdict"] == k) for k in VERDICTS}
            with open(os.path.join(d, f"p-{i}.jsonl"), "w") as f:
                f.write("".join(json.dumps(r) + "\n" for r in recs))
            with open(os.path.join(d, f"p-{i}.txt"), "w") as f:
                f.write(f"part={i}/{n} files={len(recs) + header_shift} total={total} "
                        f"ok={c['ok']} rejected={c['rejected']} diverging={c['diverging']} "
                        f"bounded={c['bounded']} workers=1\n")

    trials = [
        ("a clean three-part split", True, dict(n=3)),
        ("a file in two parts", False, dict(n=3, dup=(corpus[0], 2))),
        ("a file in no part", False, dict(n=3, drop=corpus[1])),
        ("a bounded record", False, dict(n=3, bounded=corpus[3])),
        ("a wrong total", False, dict(n=3, total=8)),
        ("a part that wrote nothing", False, dict(n=3, nopart=3)),
        ("a header that disagrees with its records", False, dict(n=3, header_shift=1)),
    ]
    bad = 0
    with tempfile.TemporaryDirectory() as d:
        corpus_path = os.path.join(d, "corpus.txt")
        with open(corpus_path, "w") as f:
            f.write("\n".join(corpus) + "\n")
        LIBDIFF_CORPUS = corpus_path
        for k, (name, want, kw) in enumerate(trials):
            sub = os.path.join(d, f"t{k}")
            os.mkdir(sub)
            kw = dict(kw)
            nopart = kw.pop("nopart", None)
            write(sub, **kw)
            if nopart:
                for ext in (".jsonl", ".txt"):
                    try:
                        os.remove(os.path.join(sub, f"p-{nopart}{ext}"))
                    except FileNotFoundError:
                        pass
            paths = [os.path.join(sub, f) for f in sorted(os.listdir(sub))]
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
                rc = libdiff_union(paths)
            ok = (rc == 0) == want
            bad += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {name}: exit {rc}"
                  + ("" if ok else f", expected {'success' if want else 'failure'}"))
    LIBDIFF_CORPUS = saved
    print(f"libdiff-union self-test: {len(trials)} checks, {len(trials) - bad} ok")
    return 1 if bad else 0


def libdiff_union(args):
    """Prove that the `parts` of =selfhost-libdiff cover the corpus once.

    Reads the shards' `logs/libdiff-*.txt` (the `part.txt` header: part=i/n, files,
    total and the verdict counts) and `logs/libdiff-*.jsonl` (one record per file), and
    checks: the headers agree on n and total, the parts are 1..n exactly once, every
    header's files equal its records and its verdict counts, the records' `file`s are
    the corpus in `.github/libdiff-corpus.txt` with no duplicate, the verdicts sum to
    the total (a whole run's summary, recomputed from the union), and no record is
    `bounded` (a bounded file was not compared: lower `jobs`, do not accept it). The
    aggregated summary is printed in the same shape as a single run's, so it can be
    compared with the last single-case run before switching.

    With one part (1/1) it is the whole-run check over that one part.
    """
    if args == ["--self-test"]:
        return libdiff_union_self_test()
    if not args:
        error("no part artifacts (was the shard's log written?)", "selfhost-libdiff")
        return 1
    problems, headers, records = [], {}, {}
    for p in args:
        stem = part_stem(p)
        if p.endswith(".txt"):
            h = part_header(p)
            if h is None:
                problems.append(f"{p}: not a part header (expected 'part=i/n files=K total=T "
                                f"ok=... rejected=... diverging=... bounded=...')")
            elif stem in headers:
                problems.append(f"{p}: a second header for part {stem}")
            else:
                headers[stem] = h
        elif p.endswith(".jsonl"):
            if stem in records:
                problems.append(f"{p}: a second record file for part {stem}")
            else:
                try:
                    records[stem] = read_timings([p])
                except (OSError, json.JSONDecodeError) as e:
                    problems.append(f"{p}: cannot read the records: {e}")
                    records[stem] = []
        else:
            problems.append(f"{p}: neither a .txt header nor a .jsonl record file")

    n_parts = {h["parts"] for h in headers.values()}
    if not headers:
        problems.append("no part headers: cannot tell which parts ran or what the whole is")
    elif len(n_parts) != 1:
        problems.append(f"the parts disagree on n: {sorted(n_parts)}")
    else:
        n = n_parts.pop()
        got = sorted(h["part"] for h in headers.values())
        if got != list(range(1, n + 1)):
            problems.append(f"the parts are {got}, not 1..{n}: a part is missing or ran twice")
    totals = {h["total"] for h in headers.values()}
    total = next(iter(totals)) if len(totals) == 1 else None
    if len(totals) > 1:
        problems.append(f"the parts disagree on the corpus size: {sorted(totals)}")
    try:
        with open(LIBDIFF_CORPUS, encoding="utf-8") as f:
            corpus = [l for l in f.read().split("\n") if l and not l.startswith("#")]
    except FileNotFoundError:
        corpus = None
        problems.append(f"{LIBDIFF_CORPUS} is missing")

    all_recs, seen = [], {}
    for stem in sorted(set(headers) | set(records)):
        h, recs = headers.get(stem), records.get(stem)
        if h is None:
            problems.append(f"part {stem}: records but no part.txt (killed before the report?)")
        if recs is None:
            recs = []
            if h is not None and h["files"] != 0:
                problems.append(f"part {stem}: its header says {h['files']} files but it wrote no records")
        if h is not None:
            if len(recs) != h["files"]:
                problems.append(f"part {stem}: {len(recs)} records, header says {h['files']}")
            counts, _, _, _ = libdiff_counts(recs)
            for k in VERDICTS:
                if counts[k] != h[k]:
                    problems.append(f"part {stem}: {counts[k]} {k} records, header says {h[k]}")
        for r in recs:
            f = r.get("file", "")
            if not f:
                problems.append(f"part {stem}: a record names no file")
            elif f in seen:
                problems.append(f"{f} is in part {seen[f]} and part {stem}")
            else:
                seen[f] = stem
            if r.get("verdict") not in VERDICTS:
                problems.append(f"{f or '?'}: verdict {r.get('verdict')!r} is not one of "
                                f"{', '.join(VERDICTS)}")
        all_recs += recs

    if total is not None and len(seen) != total:
        problems.append(f"the parts cover {len(seen)} distinct files, not the {total} of a whole run")
    if corpus is not None:
        missing = sorted(set(corpus) - set(seen))
        extra = sorted(set(seen) - set(corpus))
        if missing:
            problems.append(f"{len(missing)} file(s) of .github/libdiff-corpus.txt are in no part: "
                            + ", ".join(missing[:8]) + (" …" if len(missing) > 8 else ""))
        if extra:
            problems.append(f"{len(extra)} file(s) the parts checked are not in "
                            f".github/libdiff-corpus.txt: " + ", ".join(extra[:8])
                            + (" …" if len(extra) > 8 else "")
                            + " (add them to the manifest in the same change)")
    bounded = sorted(r.get("file", "?") for r in all_recs if r.get("verdict") == "bounded")
    if bounded:
        problems.append(f"{len(bounded)} bounded record(s): a run hit its time or memory bound, so the "
                        f"file was not compared: " + ", ".join(bounded[:8])
                        + (" …" if len(bounded) > 8 else "") + " (lower \"jobs\", do not accept it)")
    agg, by_construct, by_code, blockers = libdiff_counts(all_recs)
    classified = sum(agg[k] for k in VERDICTS)
    if classified != len(all_recs):
        problems.append(f"{len(all_recs) - classified} record(s) have no verdict")
    if total is not None and classified != total:
        problems.append(f"the verdicts sum to {classified}, not the {total} files of a whole run")
    # the identities `libDiffSummarize` guarantees for one run: a by-construct row per
    # host-accepts/self-rejects file, and a by-code row per both-reject file
    if sum(by_construct.values()) != agg["host_ok_self_error"]:
        problems.append(f"the by-construct table sums to {sum(by_construct.values())}, not the "
                        f"{agg['host_ok_self_error']} gap files")
    if agg["host_ok_self_error"] + agg["host_error_self_ok"] > agg["diverging"]:
        problems.append("the host/self acceptance counts exceed the diverging count")
    if sum(by_code.values()) != agg["rejected"]:
        problems.append(f"the by-code table sums to {sum(by_code.values())}, not the "
                        f"{agg['rejected']} rejected files")

    lines = ["### selfhost-libdiff parts", ""]
    if problems:
        lines.append(f"❌ **{len(problems)} problem(s): the parts do not cover the one case they replace.**")
        lines += [f"- {p}" for p in problems]
        error("; ".join(problems[:6]) + (" …" if len(problems) > 6 else ""), "selfhost-libdiff")
        print("\n".join(lines))
        return 1
    lines.append(f"✅ **{len(seen)} files, each checked once** by {len(headers)} part(s); "
                 f"{agg['bounded']} bounded. This is the whole-run summary, recomputed from the union.")
    lines += ["", "| part | files | ok | rejected | diverging | bounded | workers |",
              "|---|---:|---:|---:|---:|---:|---:|"]
    for stem in sorted(headers, key=lambda s: headers[s]["part"]):
        h = headers[stem]
        lines.append(f"| {h['part']}/{h['parts']} | {h['files']} | {h['ok']} | {h['rejected']} | "
                     f"{h['diverging']} | {h['bounded']} | {h['workers']} |")
    lines.append(f"| **total** | **{len(seen)}** | **{agg['ok']}** | **{agg['rejected']}** | "
                 f"**{agg['diverging']}** | **{agg['bounded']}** | |")
    lines += ["", f"ok: {agg['ok']}",
              f"rejected: {agg['rejected']} (both reject; {agg['same_code']} same code, "
              f"{agg['same_span']} same span, {agg['same_message']} same message)",
              f"diverging: {agg['diverging']} (host accepts, self rejects: "
              f"{agg['host_ok_self_error']}; host rejects, self accepts: "
              f"{agg['host_error_self_ok']})",
              f"bounded: {agg['bounded']}"]
    if by_construct:
        lines += ["", "by missing construct (files whose verdicts differ):", ""]
        lines += [f"- {k or '(none)'}: {v}" for k, v in
                  sorted(by_construct.items(), key=lambda kv: (-kv[1], kv[0]))]
    if by_code:
        lines += ["", "by error class (both reject):", ""]
        lines += [f"- {k or '(no code)'}: {v}" for k, v in
                  sorted(by_code.items(), key=lambda kv: (-kv[1], kv[0]))]
    if blockers:
        lines += ["", "top 10 blockers (host accepts, self-hosted frontend rejects):", ""]
        lines += [f"{i}. {md(f)} — {md(k)} — {md(m)}" for i, (f, k, m) in enumerate(blockers, 1)]
    print("\n".join(lines))
    return 0


# --- Skip lint (`check-skips`) -------------------------------------------------------
SKIP_DETAIL = re.compile(r"^      skipped \((.*)\)$")
NO_REASON = "(the case printed no reason)"


def allowlist(path=SKIPS, today=None):
    """The entries of .github/skip-allowlist.json that may skip in CI, each with the
    reason it may skip for, an owner and the one `case` it excuses, plus an `expires`
    date (YYYY-MM-DD). A malformed entry is an error: an allow-list without an owner is a
    place for skips to hide, one without a case excuses a whole group, and one without an
    expiry is never revisited (an expired entry has to be renewed with a new reason, as
    the flaky quarantine's do). The reason matches as a prefix of the skip's reason — a
    skip usually carries detail after the entry's words — but the case matches exactly."""
    with open(path, encoding="utf-8") as f:
        doc = json.load(f)
    today = today or dt.date.today()
    out = []
    for e in doc.get("groups", []):
        for k in ("group", "reason", "owner", "case"):
            if not str(e.get(k, "")).strip():
                sys.exit(f"{path}: the entry {json.dumps(e)} lacks {k!r}")
        raw = e.get("expires")
        if not isinstance(raw, str) or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", raw):
            sys.exit(f"{path}: the entry {json.dumps(e)} needs an 'expires' date as a "
                     f"YYYY-MM-DD string")
        try:
            expires = dt.date.fromisoformat(raw)
        except ValueError:
            sys.exit(f"{path}: the entry {json.dumps(e)} has an invalid 'expires' date {raw!r}")
        if expires <= today:
            sys.exit(f"{path}: the entry {json.dumps(e)} expired on {raw}; fix the case or "
                     f"renew the entry with a new reason")
        out.append(dict(e, expires=raw))
    return out


def skip_records(paths):
    """{(shard, group, case): (skipped, reason)} from `lake test` logs and `--timings`
    files (both describe the run: a log keeps the reason a case printed, including the
    old style; a --timings file the `skipped` note). A concrete reason wins over none."""
    recs = {}

    def put(key, skipped, why):
        old = recs.get(key)
        if old is None:
            recs[key] = (skipped, why)
        else:
            recs[key] = (old[0] or skipped,
                         old[1] if old[1] not in (None, NO_REASON) else why or old[1])

    for p in paths:
        if p.endswith(".jsonl"):
            for r in read_timings([p]):
                why = next((n[len("skipped "):] for n in r.get("notes", [])
                            if n.startswith("skipped ")), None)
                put((r["shard"], r["group"], r["case"]), why is not None, why)
            continue
        shard = os.path.basename(p)
        for ext in (".log", ".txt"):
            if shard.endswith(ext):
                shard = shard[:-len(ext)]
        group = None
        lines = open(p, encoding="utf-8", errors="replace").read().split("\n")
        i = 0
        while i < len(lines):
            line = lines[i]
            if m := GROUP.match(line):
                group = m.group(1)
            elif group and (m := SKIP.match(line)):
                why = NO_REASON
                if i + 1 < len(lines) and (d := SKIP_DETAIL.match(lines[i + 1])):
                    why = d.group(1)
                put((shard, group, m.group(1)), True, why)
                i += 1
            elif group and (m := PASS.match(line) or FAIL.match(line)):
                put((shard, group, m.group(1)), False, None)
            i += 1
    return recs


def allowed_entry(allowed, group, case, why):
    """The allow-list entry that explains this skip, or None: the same group, the same
    case exactly, and a reason the skip's starts with. The case is not optional: an entry
    that named no case would excuse every case of the group."""
    low = (why or "").lower()
    for e in allowed:
        if (e["group"] == group and e["case"] == case
                and low.startswith(e["reason"].lower())):
            return e
    return None


def analyze(recs, allowed, max_ratio):
    """(errors, warnings, lines) for the skip rule on one run's records: a group that
    skipped wholesale in a shard is an error unless it is allow-listed with that reason;
    a skip that names a tool the dev shell must provide is an error always; a GROUP's
    unexplained skipped ratio (over all its cases, in every shard) may not be over
    max_ratio. The ratio is per group, not per shard, so moving a group's cases between
    shards (a refreshed timings file) cannot flip it. Explained skips are reported."""
    shards_ = {}
    for (shard, group, case), (skipped, why) in recs.items():
        shards_.setdefault(shard, {}).setdefault(group, []).append((case, skipped, why if skipped else None))

    def explained(group, case, why):
        """None when the skip is explained, else (kind, text): 'tool' for a tool the CI
        dev shell must provide, 'unlisted' for a group, case or reason the allow-list lacks."""
        low = (why or "").lower()
        for pattern, tool in REQUIRED_TOOLS:
            # a clause of its own ("no node", "no iverilog, no yosys"), not a phrase in a
            # longer reason ("`lake` has no toolchain outside a checkout")
            if re.search(r"(?:^|, |; )" + re.escape(pattern), low):
                return ("tool", f"the dev shell must provide {tool} (`{why}`)")
        if allowed_entry(allowed, group, case, why) is not None:
            return None
        return ("unlisted", f"`{why}`")

    errors, warnings, rows, details = [], [], [], []
    total = len(recs)
    skipped = sum(1 for s, _ in recs.values() if s)
    # what each skip is: an error (reported here), a warning (unexplained but tolerated,
    # counted by its group's ratio), or fine (allow-listed)
    verdicts = {}
    for shard in sorted(shards_):
        for group, cs in sorted(shards_[shard].items()):
            skipped_cases = [(c, w) for c, s, w in cs if s]
            whole = len(skipped_cases) == len(cs)
            by_why = {}
            for c, w in skipped_cases:
                v = explained(group, c, w)
                verdicts[(shard, group, c)] = v
                # one summary line per (reason, verdict); a case-named entry may excuse
                # one case of a reason and not another
                kind = "ok" if v is None else v[0]
                by_why.setdefault((w, kind), []).append((c, v))
            for (why, kind), items in sorted(by_why.items(), key=lambda kv: (kv[0][0] or "", kv[0][1])):
                n = len(items)
                the = "all %d cases" % len(cs) if whole and n == len(cs) else "%d of %d cases" % (n, len(cs))
                v = items[0][1]
                if kind == "ok":
                    owners = sorted({allowed_entry(allowed, group, c, why)["owner"] for c, _ in items})
                    details.append(f"- ✅ **{md(group)}**: {the} in `{md(shard)}` — `{md(why)}` "
                                   f"(allow-listed: {md('; '.join(owners))})")
                elif kind == "tool":
                    msg = f"**{md(group)}**: {the} skipped in shard `{md(shard)}` — {v[1]}"
                    errors.append(msg)
                    details.append(f"- ❌ {msg}")
                elif whole:
                    msg = (f"**{md(group)}**: all {len(cs)} cases skipped in shard `{md(shard)}` — "
                           f"{v[1]}; not explained by .github/skip-allowlist.json")
                    errors.append(msg)
                    details.append(f"- ❌ {msg}")
                    for c, _ in items:
                        verdicts[(shard, group, c)] = ("error", v[1])
                else:
                    warnings.append(f"**{md(group)}**: {the} skipped in shard `{md(shard)}`: {v[1]}")
                    details.append(f"- ⚠️ **{md(group)}**: {the} in `{md(shard)}` — {v[1]}")
    groups_ = {}
    for (shard, group, case), (s, _) in recs.items():
        groups_.setdefault(group, []).append((shard, case, s))
    for group in sorted(groups_):
        cases = groups_[group]
        sk = [(sh, c) for sh, c, s in cases if s]
        if not sk:
            continue
        unexcused = [k for k in sk if (verdicts.get((k[0], group, k[1])) or ("ok",))[0] == "unlisted"]
        shards_of = ", ".join(sorted({sh for sh, _, _ in cases}))
        ratio = len(unexcused) / len(cases)
        rows.append(f"| {md(group)} | {md(shards_of)} | {len(cases)} | {len(sk)} | {len(unexcused)} | {ratio:.0%} |")
        if ratio > max_ratio:
            msg = (f"group `{md(group)}`: {len(unexcused)} of {len(cases)} cases skipped without an "
                   f"allow-list reason ({ratio:.0%}), over the {max_ratio:.0%} limit")
            errors.append(msg)
            details.append(f"- ❌ {msg}")
        elif not unexcused and len(sk) / len(cases) > max_ratio and all(
                verdicts.get((sh, group, c)) is None for sh, c in sk):
            warnings.append(f"group `{md(group)}`: {len(sk)} of {len(cases)} cases skipped "
                            f"({len(sk) / len(cases):.0%}), over the {max_ratio:.0%} limit, but every "
                            f"one is allow-listed")
    lines = ["### Skip lint", ""]
    if errors:
        lines.append(f"❌ **The skip lint failed, with {len(errors)} problem"
                     f"{'s' if len(errors) > 1 else ''}.**")
    elif not skipped:
        lines.append(f"✅ No skips: all {total} cases ran.")
    else:
        lines.append(f"✅ {skipped} of {total} cases skipped, each explained (allow-listed or an "
                     f"environment skip); a skipped case is not a pass.")
    if details:
        lines += [""] + details[:300]
    if rows:
        lines += ["", "| group | shards | cases | skipped | unexplained | unexplained ratio |",
                  "|---|---|---:|---:|---:|---:|"]
        lines += rows
    return errors, warnings, lines


def self_test():
    """Check the skip rule on synthetic logs, without running the suite: clean,
    all-skip, partial skips (below and over the ratio), an allow-listed group, an
    allow-listed group whose reason also names a tool the shell must provide, a shard
    reshuffle that leaves the per-group verdict alone, a group over the ratio across
    shards, a case-named entry, and a `--timings` file. Exits 1 if an expectation is wrong."""
    import tempfile

    def log(groups):
        """[(group, [case or (case, skip reason)])] as a `lake test` log."""
        out = []
        for g, cs in groups:
            out.append(f"── {g} (fixture)")
            for c in cs:
                if isinstance(c, tuple):
                    out += [f"  ⊘ {c[0]} (0.010 s)", f"      skipped ({c[1]})"]
                else:
                    out.append(f"  ✓ {c} (0.010 s)")
            out.append(f"  ({g}: 0.010 s; cases 0.010 s)")
        return "\n".join(out) + "\n"

    def timing(shard, group, cases):
        """[(case, skip reason or None)] as a --timings file."""
        return "".join(json.dumps({"shard": shard, "group": group, "index": i, "case": c,
                                   "seconds": 0.01, "ok": True,
                                   "notes": [f"skipped {w}"] if w else []}) + "\n"
                       for i, (c, w) in enumerate(cases))

    pass10 = [f"case {i}" for i in range(10)]
    pass30 = [f"other {i}" for i in range(30)]

    def eps(lo, hi, skips):
        """cases lo..hi-1 of group eps, those in `skips` skipped for an unlisted reason"""
        return [(f"e{i}", "fixture parity difference") if i in skips else f"e{i}" for i in range(lo, hi)]
    trials = [
        ("clean", {"core.log": log([("alpha", pass10), ("beta", pass10[:3])])}, 0, None),
        ("all skip (no node)", {"library-2.log": log([("wasm", [(f"m{i}", "no node") for i in range(25)]),
                                                      ("other", pass10)])}, 1, "node"),
        ("partial, allow-listed", {"library-1.log": log([("hdl", pass10[:9] + [("sim", "no iverilog")]),
                                                         ("other", pass10)])}, 0, None),
        ("partial, unlisted and under the ratio",
         {"core.log": log([("alpha", pass10[:9] + [("odd", "fixture reason")]), ("beta", pass10)])}, 0, None),
        ("unlisted ratio over the limit",
         {"core.log": log([("gamma", [(f"c{i}", "some reason") for i in range(5)] + pass10[:5])])}, 1, "50%"),
        ("unlisted whole group",
         {"core.log": log([("delta", [(f"c{i}", "some reason") for i in range(3)])])}, 1,
         "not explained by .github/skip-allowlist.json"),
        ("allow-listed whole group",
         {"library-3.log": log([("tower", [("from source", "no source toolchain: `lake` has no toolchain "
                                                         "outside a checkout (elan has no default)")]),
                                ("other", pass10)])}, 0, None),
        ("allow-listed group, tool missing from the shell",
         {"library-1.log": log([("hdl", [(f"syn{i}", "no yosys") for i in range(3)])])}, 1, "yosys"),
        ("allow-listed reason with a required tool too",
         {"library-1.log": log([("hdl", [("memories", "no iverilog, no yosys")])])}, 1, "yosys"),
        # the same run in two shard layouts: 4 of eps's 20 cases skip (20%). Measured per
        # shard, layout A put all four in a 10-case shard (40%, a failure) and layout B
        # two in each (20%); per group both are 20%, so a reshuffle cannot flip the verdict
        ("reshuffle A: a group's skips in one shard",
         {"selfhost-1.log": log([("eps", eps(0, 10, {0, 1, 2, 3}))]),
          "selfhost-2.log": log([("eps", eps(10, 20, set()))])}, 0, None),
        ("reshuffle B: the same group spread over two shards",
         {"selfhost-1.log": log([("eps", eps(0, 10, {0, 1}))]),
          "selfhost-2.log": log([("eps", eps(10, 20, {10, 11}))])}, 0, None),
        # 6 of eps's 20 cases (30%) skip, 3 in each shard among 30 other passing cases
        # (each shard 3 of 40, 8%): the group is over the limit wherever its cases run
        ("group over the ratio across shards",
         {"selfhost-1.log": log([("eps", eps(0, 10, {0, 1, 2})), ("other", pass30)]),
          "selfhost-2.log": log([("eps", eps(10, 20, {10, 11, 12})), ("more", pass30)])}, 1,
         "group `eps`: 6 of 20"),
        # an entry that names a case excuses that case only: z1 has the same reason and
        # stays unexplained (1 of 3, 33%)
        ("case-named entry excuses its case only",
         {"selfhost-1.log": log([("zeta", [("z0", "parity: named"), ("z1", "parity: named"), "z2"])])}, 1,
         "group `zeta`: 1 of 3"),
        # the split sweep skips alone (its group's other cases pass), so the ratio cannot
        # be what fails it: the reason names a tool the CI dev shell must provide
        ("a skipped libdiff sweep (no C toolchain)",
         {"selfhost-libdiff-1.log": log([("selfhost-libdiff",
                                          [("the library through both compilers",
                                            "no C toolchain (no self-hosted compiler)"),
                                           "part i/n: the parts partition the file list"])])},
         1, "cc and GMP"),
        ("--timings file", {"library-2.jsonl": timing("library-2", "wasm",
                                                      [(f"m{i}", "no node") for i in range(25)])}, 1, "node"),
    ]
    allowed = {"groups": [{"group": "hdl", "case": "sim", "reason": "no iverilog",
                           "owner": "HDL fixtures", "expires": "2099-01-01"},
                          {"group": "tower", "case": "from source",
                           "reason": "no source toolchain", "owner": "tower fixtures",
                           "expires": "2099-01-01"},
                          {"group": "zeta", "case": "z0", "reason": "parity:",
                           "owner": "zeta fixtures", "expires": "2099-01-01"}]}
    # an entry needs a case and a live expiry: a group-level entry excuses every case,
    # and one without a date is never revisited
    loader_trials = [
        ("a live, case-scoped entry loads",
         {"group": "zeta", "case": "z0", "reason": "parity:", "owner": "zeta", "expires": "2099-01-01"},
         True, None),
        ("an entry without a case is rejected",
         {"group": "zeta", "reason": "parity:", "owner": "zeta", "expires": "2099-01-01"},
         False, "case"),
        ("an entry without expires is rejected",
         {"group": "zeta", "case": "z0", "reason": "parity:", "owner": "zeta"}, False, "expires"),
        ("an expiry that is not YYYY-MM-DD is rejected",
         {"group": "zeta", "case": "z0", "reason": "parity:", "owner": "zeta", "expires": "soon"},
         False, "YYYY-MM-DD"),
        ("an expired entry is rejected",
         {"group": "zeta", "case": "z0", "reason": "parity:", "owner": "zeta", "expires": "2020-01-01"},
         False, "expired"),
    ]
    bad = 0
    with tempfile.TemporaryDirectory() as d:
        apath = os.path.join(d, "allow.json")
        with open(apath, "w", encoding="utf-8") as f:
            json.dump(allowed, f)
        for k, (name, files, want_errors, needle) in enumerate(trials):
            sub = os.path.join(d, f"t{k}")
            os.mkdir(sub)
            paths = []
            for fn, text in files.items():
                p = os.path.join(sub, fn)
                with open(p, "w", encoding="utf-8") as f:
                    f.write(text)
                paths.append(p)
            errors, _, _ = analyze(skip_records(paths), allowlist(apath), 0.25)
            ok = len(errors) == want_errors and (needle is None or any(needle in e for e in errors))
            bad += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {name}: {len(errors)} error(s)"
                  + ("" if ok else f", expected {want_errors}" + (f" mentioning {needle!r}" if needle else "")
                     + f": {errors}"))
        for k, (name, entry, want_ok, needle) in enumerate(loader_trials):
            p = os.path.join(d, f"allow-loader-{k}.json")
            with open(p, "w", encoding="utf-8") as f:
                json.dump({"groups": [entry]}, f)
            try:
                allowlist(p)
                ok, why = want_ok, "loaded"
            except SystemExit as e:
                ok, why = not want_ok and (needle is None or needle in str(e)), str(e)
            bad += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {name}: {why}")
        # a log the lint cannot parse is not "all 0 cases ran": no records is a failure
        empty = os.path.join(d, "empty.log")
        open(empty, "w", encoding="utf-8").close()
        rc = check_skips([empty], annotate=False)
        ok = rc != 0
        bad += not ok
        print(f"{'ok  ' if ok else 'FAIL'} an empty record set exits non-zero (check-skips: {rc})")
        # the repository's own allow-list must load, with an owner, a case and an expiry
        # on every entry
        try:
            real = allowlist()
            ok = True
        except (OSError, SystemExit, json.JSONDecodeError) as e:
            real, ok = [], False
            print(f"FAIL .github/skip-allowlist.json: {e}")
        bad += not ok
        if ok:
            print(f"ok   .github/skip-allowlist.json: {len(real)} entr{'y' if len(real) == 1 else 'ies'}")
    checks = len(trials) + len(loader_trials) + 2
    print(f"skip lint self-test: {checks} checks, {checks - bad} ok")
    return 1 if bad else 0


def check_skips(args, annotate=True):
    max_ratio, allow, paths, selftest = 0.25, SKIPS, [], False
    it = iter(args)
    for a in it:
        if a == "--max-ratio":
            max_ratio = float(next(it))
        elif a == "--allow":
            allow = next(it)
        elif a == "--self-test":
            selftest = True
        elif a.startswith("--"):
            sys.exit(f"check-skips: unknown flag {a}")
        else:
            paths.append(a)
    if selftest:
        return self_test()
    if not paths:
        print(__doc__, file=sys.stderr)
        return 2
    recs = skip_records(paths)
    if not recs:
        # a log that parsed no records proves nothing: "all 0 cases ran" would be a green
        # gate over an empty or unreadable log
        msg = "no test results: the skip lint checked nothing (was a log written?)"
        print(msg, file=sys.stderr)
        if annotate:
            error(msg, "Skips")
        return 1
    errors, warnings, lines = analyze(recs, allowlist(allow), max_ratio)
    print("\n".join(lines))
    for w in warnings:
        warn(w, "Skips")
    for e in errors:
        error(e, "Skips")
    return 1 if errors else 0


def make_baseline(paths):
    """.github/test-timings.json from `--timings` records (see `baseline`); a case seen
    more than once keeps its largest time, a build its largest. Only the shards with
    "split" count."""
    cases, builds = {}, {}
    split = [s["name"] for s in shards() if s.get("split", 1) > 1]
    for r in read_timings(paths):
        # only the split shards' cases are balanced (and other shards may use the same
        # programs with other build times)
        if not split_of(r["shard"], split):
            continue
        uses = sorted({n[len(NOTE_USES):] for n in r.get("notes", []) if n.startswith(NOTE_USES)})
        built = 0.0
        for n in r.get("notes", []):
            if n.startswith(NOTE_BUILT):
                res, t = n[len(NOTE_BUILT):].rsplit(" ", 1)
                builds[res] = round(max(builds.get(res, 0.0), float(t)), 3)
                built += float(t)
        own = round(max(r["seconds"] - built, 0.0), 3)
        old = cases.setdefault(r["group"], {}).get(r["case"])
        if old is None or old["seconds"] < own:
            cases[r["group"]][r["case"]] = {"seconds": own, **({"uses": uses} if uses else {})}
    # one case per line, sorted, so that the file diffs and merges well
    dump = lambda x: json.dumps(x, ensure_ascii=False)
    out = ['{', f' "builds": {dump(dict(sorted(builds.items())))},', ' "cases": {']
    for k, (g, cs) in enumerate(sorted(cases.items())):
        out.append(f'  {dump(g)}: {{')
        lines = [f'   {dump(n)}: {dump(c)}' for n, c in sorted(cs.items())]
        out += [l + "," for l in lines[:-1]] + lines[-1:]
        out.append('  }' + ("," if k < len(cases) - 1 else ""))
    out += [' }', '}']
    print("\n".join(out))
    return 0


def main(args):
    if args[:2] == ["matrix", "--only"] and len(args) >= 3:
        matrix(args[3] if len(args) > 3 else DEFAULT_BIN, set(json.loads(args[2])))
        return 0
    if args[:1] == ["changes"] and len(args) >= 2:
        return changes(args[1:])
    if args[:1] == ["libdiff-union"]:
        return libdiff_union(args[1:])
    binary = args[1] if len(args) > 1 else DEFAULT_BIN
    if args[:1] == ["matrix"]:
        matrix(binary)
        return 0
    if args[:1] == ["check-shards"]:
        return check_shards(binary)
    if args[:1] == ["check-skips"]:
        return check_skips(args[1:])
    if args[:1] == ["plan"]:
        return plan(binary)
    if args[:1] == ["summary"] and len(args) >= 2:
        return summary(args[1], args[2:])
    if args[:1] == ["balance"]:
        return balance(args[1:])
    if args[:1] == ["baseline"] and len(args) >= 2:
        return make_baseline(args[1:])
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
