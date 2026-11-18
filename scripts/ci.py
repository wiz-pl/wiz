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
                                     the test driver BIN; default .lake/build/bin/tests)
  scripts/ci.py check-shards [BIN]   check that every test case is run by exactly one
                                     shard (after splitting), and that every selector
                                     of a shard selects something. A group that no
                                     selector picks goes to the shard it names
                                     (`Group.shard`) or to the shard with
                                     "default": true (`resolved`)
  scripts/ci.py plan [BIN]           the split shards' parts with their estimated times
  scripts/ci.py changes BASE [HEAD]  what a change needs (path filters): reads the files
                                     that differ between BASE and HEAD (git diff
                                     BASE HEAD; CI: a PR's merge commit and its first
                                     parent) and prints GitHub outputs: code=true
                                     unless only docs changed, docs=true when a doc
                                     changed, and shards=[NAMES], the shards of
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
  scripts/ci.py fetch-runs [--branch REGEX] N DIR
                                     download the last N completed (not cancelled) CI
                                     runs that have a `test-timings` artifact into
                                     DIR/RUN_ID/ (timings.jsonl, and jobs.json from the
                                     jobs API), the input of `rebalance`; --branch: only
                                     runs whose branch matches REGEX (whole name, e.g.
                                     'master|integration/.*'); needs `gh`
  scripts/ci.py rebalance [--jobs N] [--assume TSV] [--write] [--bin BIN] RUN..
                                     re-derive the split shards from measured times:
                                     each RUN is one run's `--timings` file (the
                                     `test-timings` artifact) or a `fetch-runs`
                                     directory; a case's time is its median over the
                                     runs. With jobs.json, a shard's prediction is
                                     scaled by its measured wall time over its case
                                     sum (`--jobs` overlaps cases), and a shard that is
                                     not split is its median wall time. Prints the new baseline's
                                     summary, the "split" count of each split shard and
                                     the predicted time of every job (min/median/max);
                                     with --write, writes .github/test-timings.json and
                                     the "split" counts of .github/test-shards.json.
                                     The case list is the test driver's (--bin, default
                                     .lake/build/bin/tests, when it exists), else the
                                     last JSONL's. --assume TSV: `GROUP<TAB>CASE<TAB>S`
                                     rows for cases no run has measured yet (S seconds,
                                     or `drop`: a case that is gone). --jobs N: at most
                                     N test jobs in all (default: as many as now); the
                                     split counts grow greedily, a part at a time to the
                                     shard with the longest part, until the budget is
                                     used or another part would not shorten it. Exits
                                     with an error if the parts do not cover every case
                                     of the split shards exactly once
  scripts/ci.py check-skips [--max-ratio F] [--allow FILE] LOG|JSONL..
                                     a green run must have tested something: fail when
                                     a group skipped wholesale, when a skip names a tool
                                     the CI dev shell must provide (cc, GMP, GC, yosys,
                                     node, nix, …), or when a group's unexplained skipped
                                     ratio is over F (default 0.25, of the group's
                                     cases in all shards). A skip in a group of
                                     .github/skip-allowlist.json whose reason matches
                                     (and whose case, when the entry names one) is
                                     explained (reported, not failed); anything else that
                                     skips wholesale is a failure. Reads `lake test`
                                     logs and `--timings` files. `--self-test` checks the
                                     rule on synthetic logs and exits 1 if it is wrong

Selectors are the arguments of `lake test --`: `=NAME` selects the group NAME,
`=NAME#I,J` the cases I and J of it, anything else is a prefix of group names (see
Tests/Main.lean).
"""
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
    estimated seconds or None, jobs)]; `jobs` is the shard's "--jobs" (None unless the
    shard says "jobs": N: the number of cases of a parallel-opted-in group it runs at a
    time). A shard without "jobs" is run without `--jobs`, so a case that has an auto
    mode (selfhost-libdiff) can tell "not given" from "--jobs 1".)"""
    out = []
    for s in resolved(binary):
        n = s.get("split", 1)
        jobs = s.get("jobs")
        if n <= 1:
            out.append((s["name"], s["select"], None, jobs))
            continue
        base = base or baseline()
        items = estimate(list_cases(binary, s["select"]), base)
        for k, p in enumerate(partition(items, n, base["builds"]), 1):
            if p:
                out.append((f"{s['name']}-{k}", part_selectors(p), part_cost(p, base["builds"]), jobs))
    return out


def matrix_entries(binary, only=None):
    # "heavy": true shards (and the parts of a split one) may run on the self-hosted
    # runner (vars.WIZ_RUNNER_HEAVY, docs/ci-runner.md)
    heavy = {s["name"] for s in shards() if s.get("heavy")}
    split = {s["name"] for s in shards() if s.get("split", 1) > 1}
    def is_heavy(n):
        base = n.rsplit("-", 1)[0]
        return n in heavy or (base in split and base in heavy)
    def wanted(n):
        return only is None or n in only or (n.rsplit("-", 1)[0] in split and n.rsplit("-", 1)[0] in only)
    return [{"name": n, "select": "\n".join(sel), "heavy": is_heavy(n), "jobs": jobs}
            for n, sel, _, jobs in expanded(binary) if wanted(n)]


def matrix(binary, only=None):
    print(json.dumps({"shard": matrix_entries(binary, only)}, ensure_ascii=False))


def plan(binary):
    base = baseline()
    for name, sel, est, _ in expanded(binary, base):
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
    for name, sel, _, _ in parts:
        for g, i, _ in set(list_cases(binary, sel)):  # a case selected twice within a shard still runs once
            runs[(g, i)].append(name)
    for g in groups:
        missing = [i for (h, i), by in runs.items() if h == g and not by]
        if missing:
            errors.append(f"group {g!r}: {'all' if len(missing) == sum(1 for h, _ in runs if h == g) else len(missing)} "
                          f"of its cases are in no shard")
    for (g, i), by in runs.items():
        if len(by) > 1:
            errors.append(f"case {g} #{i} is run by several shards: {', '.join(by)}")
    # end to end: the jobs of the full matrix (what CI runs when every shard is needed),
    # with their selectors read back from the matrix's newline-joined form, run every
    # case of the listing exactly once and nothing else
    if not errors:
        jobs = matrix_entries(binary)
        seen = {}
        for e in jobs:
            for g, i, _ in set(list_cases(binary, e["select"].split("\n"))):
                seen.setdefault((g, i), []).append(e["name"])
        lost = sorted(k for k in runs if k not in seen)
        extra = sorted(k for k in seen if k not in runs)
        twice = sorted(k for k, by in seen.items() if len(by) > 1)
        if lost:
            errors.append(f"the matrix runs {len(lost)} cases of the listing in no job "
                          f"(first: {lost[0][0]} #{lost[0][1]})")
        if extra:
            errors.append(f"the matrix runs {len(extra)} cases that the listing lacks")
        if twice:
            errors.append(f"the matrix runs {len(twice)} cases in several jobs "
                          f"(first: {twice[0][0]} #{twice[0][1]}: {', '.join(seen[twice[0]])})")
        if {g for g, _ in seen} != {g for g, _ in runs}:
            errors.append("the matrix's groups differ from the listing's")
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
    print(f"ok: {len(groups)} groups, {len(runs)} cases, each in exactly one of {len(parts)} shards "
          f"(the matrix's {len(jobs)} jobs run them all, once)")
    return 0


FAKE_DRIVER = r'''#!/usr/bin/env python3
"""A stand-in for the test driver (`check-shards --self-test`): answers --list,
--list-shards and --list-cases from LISTING (group, index, name, shard hint)."""
import json, sys
LISTING = json.loads(%r)
def sel(group, s):
    return group == s[1:].split("#")[0] if s.startswith("=") else group.startswith(s)
def picks(g, i, s):
    if not sel(g, s):
        return False
    return "#" not in s or i in [int(x) for x in s.split("#", 1)[1].split(",")]
a = sys.argv[1:]
groups = list(dict.fromkeys(g for g, _, _, _ in LISTING))
if a == ["--list"]:
    print("\n".join(groups))
elif a == ["--list-shards"]:
    hint = {g: h for g, _, _, h in LISTING}
    print("\n".join(f"{g}\t{hint[g]}" for g in groups))
elif a[:1] == ["--list-cases"]:
    for g, i, n, _ in LISTING:
        if not a[1:] or any(picks(g, i, s) for s in a[1:]):
            print(f"{g}\t{i}\t{n}")
else:
    sys.exit(2)
'''


def fake_driver(directory, listing):
    """Write a stand-in test driver answering from LISTING [(group, index, name, shard
    hint)] (see FAKE_DRIVER) into DIRECTORY; its path."""
    path = os.path.join(directory, "tests")
    with open(path, "w", encoding="utf-8") as f:
        f.write(FAKE_DRIVER % json.dumps(listing))
    os.chmod(path, 0o755)
    return path


def check_shards_self_test():
    """`check-shards` on stand-in drivers and shard files: a good layout (with a split
    shard and a group that only its own shard hint places) passes, and a dropped case,
    a case in two shards and a selector that selects nothing fail. Exits 1 if an
    expectation is wrong."""
    import contextlib, io, tempfile
    global SHARDS, TIMINGS
    listing = ([("alpha", i, f"a{i}", "") for i in range(5)]
               + [("beta", i, f"b{i}", "") for i in range(7)]
               + [("gamma", i, f"c{i}", "") for i in range(3)]
               + [("delta", 0, "d0", "solo")])
    good = [{"name": "solo", "select": []},
            {"name": "big", "split": 3, "default": True, "select": ["=beta", "=gamma"]},
            {"name": "small", "select": ["alp"]}]
    trials = [
        ("good", listing, good, 0),
        ("a case the shards drop", listing,
         [{"name": "solo", "select": []},
          {"name": "big", "split": 3, "default": True, "select": ["=beta#0,1,2,3,4,5", "=gamma"]},
          {"name": "small", "select": ["alp"]}], 1),
        ("a case in two shards", listing,
         [{"name": "solo", "select": []},
          {"name": "big", "split": 3, "default": True, "select": ["=beta", "=gamma"]},
          {"name": "small", "select": ["alp", "=gamma#1"]}], 1),
        ("a selector that selects nothing", listing,
         [{"name": "solo", "select": []},
          {"name": "big", "split": 2, "default": True, "select": ["=beta", "=gamma", "=epsilon"]},
          {"name": "small", "select": ["alp"]}], 1),
    ]
    saved, wrong = (SHARDS, TIMINGS), []
    try:
        for name, lst, config, want in trials:
            with tempfile.TemporaryDirectory() as d:
                SHARDS, TIMINGS = os.path.join(d, "shards.json"), os.path.join(d, "timings.json")
                with open(SHARDS, "w") as f:
                    json.dump(config, f)
                with open(TIMINGS, "w") as f:
                    json.dump({"cases": {"beta": {f"b{i}": {"seconds": 10.0 + i} for i in range(7)}},
                               "builds": {}}, f)
                binary = fake_driver(d, lst)
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                    got = check_shards(binary)
                print(f"{'ok ' if got == want else 'BAD'} {name}: exit {got} (expected {want})")
                if got != want:
                    wrong.append(name)
    finally:
        SHARDS, TIMINGS = saved
    return 1 if wrong else 0


# Path filters (`changes`). Files only people read: a change of only these runs no build
# and no tests.
DOCS = ["docs/*", "*.md", "LICENSE", "COPYING*"]
# Files every shard depends on: the Lean sources (compiler, tests, grail), the
# build and its toolchain, the C runtime, CI itself. A change to any runs every shard.
EVERYTHING = ["*.lean", "lakefile.*", "lean-toolchain", "lake-manifest.json", "flake.*",
              ".envrc", "runtime/*", "c/*", "scripts/*", ".github/*", "grail.wiz"]


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
        print(f"shards={json.dumps(names)}")
        return 0
    base, head = args[0], (args[1] if len(args) > 1 else "HEAD")
    out = subprocess.run(["git", "diff", "--name-only", base, head], capture_output=True,
                         text=True, check=True, cwd=ROOT).stdout
    files = [f for f in out.split("\n") if f]
    names = needed_shards(files)
    code = any(not matches(f, DOCS) for f in files)
    docs = any(matches(f, DOCS) for f in files)
    print(f"code={'true' if code else 'false'}")
    print(f"docs={'true' if docs else 'false'}")
    print(f"shards={json.dumps(names)}")
    print(f"{len(files)} files changed; code: {code}; docs: {docs}; "
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


# --- Skip lint (`check-skips`) -------------------------------------------------------
SKIP_DETAIL = re.compile(r"^      skipped \((.*)\)$")
NO_REASON = "(the case printed no reason)"


def allowlist(path=SKIPS):
    """The groups of .github/skip-allowlist.json that may skip in CI, each with the
    reason it may skip for and an owner, and optionally the one case it excuses. A malformed entry is an error: an allow-list
    without an owner is a place for skips to hide."""
    with open(path, encoding="utf-8") as f:
        doc = json.load(f)
    out = []
    for e in doc.get("groups", []):
        for k in ("group", "reason", "owner"):
            if not str(e.get(k, "")).strip():
                sys.exit(f"{path}: the entry {json.dumps(e)} lacks {k!r}")
        if "case" in e and not str(e["case"]).strip():
            sys.exit(f"{path}: the entry {json.dumps(e)} has an empty 'case'")
        out.append(e)
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
    """The allow-list entry that explains this skip, or None: same group, a reason the
    skip's starts with, and, when the entry names a case, that case exactly."""
    low = (why or "").lower()
    for e in allowed:
        if (e["group"] == group and low.startswith(e["reason"].lower())
                and ("case" not in e or e["case"] == case)):
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
                           f"{v[1]}; not in .github/skip-allowlist.json")
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
         "not in .github/skip-allowlist.json"),
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
        ("--timings file", {"library-2.jsonl": timing("library-2", "wasm",
                                                      [(f"m{i}", "no node") for i in range(25)])}, 1, "node"),
    ]
    allowed = {"groups": [{"group": "hdl", "reason": "no iverilog", "owner": "HDL fixtures"},
                          {"group": "tower", "reason": "no source toolchain", "owner": "tower fixtures"},
                          {"group": "zeta", "case": "z0", "reason": "parity:", "owner": "zeta fixtures"}]}
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
        # the repository's own allow-list must load, with an owner on every entry
        try:
            real = allowlist()
            ok = True
        except (OSError, SystemExit, json.JSONDecodeError) as e:
            real, ok = [], False
            print(f"FAIL .github/skip-allowlist.json: {e}")
        bad += not ok
        if ok:
            print(f"ok   .github/skip-allowlist.json: {len(real)} entr{'y' if len(real) == 1 else 'ies'}")
    print(f"skip lint self-test: {len(trials) + 1} checks, {len(trials) + 1 - bad} ok")
    return 1 if bad else 0


def check_skips(args):
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
        print("No test results: the skip lint checked nothing (was a log written?).")
        return 0
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
    print(baseline_json({"cases": cases, "builds": builds}))
    return 0


def baseline_json(base):
    """.github/test-timings.json's text: one case per line, sorted, so that the file
    diffs and merges well."""
    cases, builds = base["cases"], base["builds"]
    dump = lambda x: json.dumps(x, ensure_ascii=False)
    out = ['{', f' "builds": {dump(dict(sorted(builds.items())))},', ' "cases": {']
    for k, (g, cs) in enumerate(sorted(cases.items())):
        out.append(f'  {dump(g)}: {{')
        lines = [f'   {dump(n)}: {dump(c)}' for n, c in sorted(cs.items())]
        out += [l + "," for l in lines[:-1]] + lines[-1:]
        out.append('  }' + ("," if k < len(cases) - 1 else ""))
    out += [' }', '}']
    return "\n".join(out)


# --- Rebalance (`rebalance`) ---------------------------------------------------------
def median(xs):
    xs = sorted(xs)
    return (xs[(len(xs) - 1) // 2] + xs[len(xs) // 2]) / 2


def run_medians(paths):
    """Per-case and per-build medians over runs (one `--timings` file per run):
    ({(group, case): (seconds, own seconds, uses, shard)}, {program: seconds},
    {shard: seconds per run}). A case's `own` time leaves out the builds it did; a
    failed case counts only if no run passed it. `shard` is the job the case ran in
    last (its split shard's name for a part)."""
    split = [s["name"] for s in shards() if s.get("split", 1) > 1]
    seen, builds, totals, ratios, walls = {}, {}, {}, {}, {}
    for p in paths:
        run_builds, run_sums = {}, {}
        for r in read_timings([timings_of(p)]):
            run_sums[r["shard"]] = run_sums.get(r["shard"], 0.0) + r["seconds"]
            built = 0.0
            for n in r.get("notes", []):
                if n.startswith(NOTE_BUILT):
                    res, t = n[len(NOTE_BUILT):].rsplit(" ", 1)
                    run_builds[res] = max(run_builds.get(res, 0.0), float(t))
                    built += float(t)
            uses = tuple(sorted({n[len(NOTE_USES):] for n in r.get("notes", []) if n.startswith(NOTE_USES)}))
            shard = split_of(r["shard"], split) or r["shard"]
            seen.setdefault((r["group"], r["case"]), []).append(
                (r.get("ok", True), r["seconds"], max(r["seconds"] - built, 0.0), uses, shard))
            totals.setdefault(r["shard"], {}).setdefault(p, 0.0)
            totals[r["shard"]][p] += r["seconds"]
        for res, t in run_builds.items():
            builds.setdefault(res, []).append(t)
        run_walls = job_walls(p)
        for job, w in run_walls.items():
            walls.setdefault(split_of(job, split) or job, []).append(w)
        fam = {}
        for job, w in run_walls.items():
            if job in run_sums:
                f = fam.setdefault(split_of(job, split) or job, [0.0, 0.0])
                f[0] += w
                f[1] += run_sums[job]
        for sh, (w, c) in fam.items():
            if c > 0:
                ratios.setdefault(sh, []).append(w / c)
    cases = {}
    for k, rs in seen.items():
        ok = [r for r in rs if r[0]] or rs
        cases[k] = (median([r[1] for r in ok]), median([r[2] for r in ok]),
                    max((r[3] for r in ok), key=len), ok[-1][4])
    return (cases, {r: median(ts) for r, ts in builds.items()},
            {sh: median(list(v.values())) for sh, v in totals.items()},
            {sh: median(v) for sh, v in ratios.items()},
            {sh: median(v) for sh, v in walls.items() if sh not in split})


def timings_of(p):
    """A run's `--timings` file: P itself, or P/timings.jsonl (`fetch-runs`)."""
    return os.path.join(p, "timings.jsonl") if os.path.isdir(p) else p


def job_walls(p):
    """{job: seconds of its `tests -- …` step} of the successful test jobs of a
    `fetch-runs` directory's jobs.json ({} without one)."""
    from datetime import datetime
    path = os.path.join(p, "jobs.json") if os.path.isdir(p) else None
    if not path or not os.path.exists(path):
        return {}
    t = lambda x: datetime.fromisoformat(x.replace("Z", "+00:00"))
    out = {}
    with open(path, encoding="utf-8") as f:
        jobs = json.load(f).get("jobs", [])
    for j in jobs:
        if not j["name"].startswith("test (") or j.get("conclusion") != "success":
            continue
        for st in j.get("steps", []):
            if st["name"].startswith("tests -- ") and st.get("started_at") and st.get("completed_at"):
                out[j["name"][len("test ("):-1]] = (t(st["completed_at"]) - t(st["started_at"])).total_seconds()
    return out


def fetch_runs(args):
    branch = None
    if args[:1] == ["--branch"] and len(args) >= 2:
        branch, args = re.compile(args[1]), args[2:]
    if len(args) != 2:
        sys.exit("usage: scripts/ci.py fetch-runs [--branch REGEX] N DIR")
    n, out = int(args[0]), args[1]
    gh = lambda *a: subprocess.run(["gh", *a], capture_output=True, text=True, check=True).stdout
    repo = os.environ.get("WIZ_REPO", "wiz-pl/wiz")
    got, page = 0, 1
    while got < n and page <= 10:
        runs = json.loads(gh("api", f"repos/{repo}/actions/workflows/ci.yml/runs?status=completed&per_page=100&page={page}"))
        page += 1
        if not runs["workflow_runs"]:
            break
        for r in runs["workflow_runs"]:
            if got >= n:
                break
            if r["conclusion"] in ("cancelled", "skipped"):
                continue
            if branch and not branch.fullmatch(r["head_branch"] or ""):
                continue
            d = os.path.join(out, str(r["id"]))
            try:
                gh("run", "download", str(r["id"]), "-R", repo, "-n", "test-timings", "-D", d)
            except subprocess.CalledProcessError:
                continue  # no test-timings artifact (the run stopped before its result job)
            with open(os.path.join(d, "jobs.json"), "w", encoding="utf-8") as f:
                f.write(gh("api", f"repos/{repo}/actions/runs/{r['id']}/jobs?filter=latest&per_page=100"))
            got += 1
            print(d)
    return 0 if got else 1


def rebalance(args):
    jobs, assume, write, binary, paths = None, None, False, DEFAULT_BIN, []
    it = iter(args)
    for a in it:
        if a == "--jobs":
            jobs = int(next(it))
        elif a == "--assume":
            assume = next(it)
        elif a == "--write":
            write = True
        elif a == "--bin":
            binary = next(it)
        else:
            paths.append(a)
    if not paths:
        sys.exit("rebalance: no --timings files")
    cases, builds, shard_secs, ratios, walls = run_medians(paths)
    config = shards()
    split = {s["name"]: s for s in config if s.get("split", 1) > 1}
    # the current case list: the driver's, or the last run's
    if os.path.exists(binary):
        listed = {}
        for s in resolved(binary):
            for g, i, n in list_cases(binary, s["select"]):
                listed[(g, n)] = s["name"]
        source = binary
    else:
        listed = {}
        for r in read_timings([timings_of(paths[-1])]):
            listed[(r["group"], r["case"])] = split_of(r["shard"], list(split)) or r["shard"]
        source = paths[-1]
    assumed = set()
    if assume:
        with open(assume, encoding="utf-8") as f:
            for line in f:
                if not line.strip() or line.startswith("#"):
                    continue
                g, n, t = line.rstrip("\n").split("\t")
                if t == "drop":
                    listed.pop((g, n), None)
                    continue
                if (g, n) in cases:
                    continue  # measured: the measurement wins
                # an unmeasured case goes to its group's shard
                sh = next((s for (gg, _), s in listed.items() if gg == g), None)
                if sh is None:
                    sys.exit(f"rebalance: --assume names the group {g!r}, which no shard runs")
                listed[(g, n)] = sh
                cases[(g, n)] = (float(t), float(t), (), sh)
                assumed.add((g, n))
    missing = sorted(k for k, sh in listed.items() if sh in split and k not in cases)
    # the new baseline: the split shards' current cases
    base = {"cases": {}, "builds": {r: round(t, 3) for r, t in sorted(builds.items())}}
    for (g, n), sh in listed.items():
        if sh in split and (g, n) in cases:
            _, own, uses, _ = cases[(g, n)]
            base["cases"].setdefault(g, {})[n] = {"seconds": round(own, 3), **({"uses": list(uses)} if uses else {})}
    # each split shard's items, as `estimate` gives them (index: the listing's order)
    items = {name: [] for name in split}
    known = {}
    for (g, n), sh in listed.items():
        if sh in split:
            known.setdefault(sh, []).append((g, n))
    for sh, ks in known.items():
        idx = {}
        for g, n in ks:
            idx[g] = idx.get(g, -1) + 1
            items[sh].append((g, idx[g], n))
        items[sh] = estimate(items[sh], base)
    # the jobs that cannot be split: the other shards, and the longest single unit
    fixed = {s["name"]: walls.get(s["name"], shard_secs.get(s["name"], 0.0)) for s in config if s["name"] not in split}
    # a split part's predicted wall: its estimated case sum times the shard's measured
    # wall/case-sum ratio (below 1 when "jobs" runs cases at once)
    ratio = {sh: ratios.get(sh, 1.0) for sh in split}
    cost = lambda sh, p: part_cost(p, base["builds"]) * ratio[sh]
    unit = lambda sh: max((cost(sh, [it]) for it in items[sh]), default=0.0)
    floor = max(list(fixed.values()) + [unit(sh) for sh in split])
    budget = jobs if jobs is not None else len(fixed) + sum(s["split"] for s in split.values())
    counts = {sh: 1 for sh in split}
    parts = {sh: partition(items[sh], 1, base["builds"]) for sh in split}
    longest = lambda sh: max(cost(sh, p) for p in parts[sh])
    # fill the budget: a part at a time to the shard with the longest part, while that
    # shortens it (a job that cannot be split, e.g. a single long case, is no reason to
    # stop: the other shards still get shorter and their spread smaller)
    while len(fixed) + sum(counts.values()) < budget:
        sh = max(split, key=lambda k: (longest(k), k))
        trial = partition(items[sh], counts[sh] + 1, base["builds"])
        if max(cost(sh, p) for p in trial) >= longest(sh) - 1e-9:
            break
        counts[sh] += 1
        parts[sh] = trial
    # nothing dropped: every case of the listing is in exactly one job
    for sh in split:
        got = sorted((g, n) for p in parts[sh] for g, _, n, *_ in p)
        want = sorted(known.get(sh, []))
        if got != want:
            sys.exit(f"rebalance: the parts of {sh} do not cover its cases exactly once")
    ran = {g for g, _ in cases}
    gone = sorted(g for g in ran if g not in {g for g, _ in listed})
    if gone:
        print(f"Note: {len(gone)} groups measured by the runs are not in the case list "
              f"(renamed or removed?): {', '.join(gone)}")
    # the report
    print(f"Runs: {len(paths)} `--timings` files; cases from {source}; budget {budget} jobs.")
    if ratios:
        print("Measured wall/case-sum ratios: " + ", ".join(f"{sh} {r:.2f}" for sh, r in sorted(ratios.items())))
    else:
        print("No jobs.json: predictions are case sums (an overestimate for shards with \"jobs\").")
    if assumed:
        print(f"Assumed (not yet measured): {len(assumed)} cases, {sum(cases[k][1] for k in assumed):.0f} s in all.")
    if missing:
        print(f"Not measured and not assumed: {len(missing)} cases of split shards (estimated at their group's median).")
    print()
    print("| shard | was | now |")
    print("|---|---:|---:|")
    for sh in split:
        print(f"| {sh} | {split[sh]['split']} | {counts[sh]} |")
    def predicted(cs):
        out = dict(fixed)
        for sh in split:
            ps = parts[sh] if cs[sh] == counts[sh] else partition(items[sh], cs[sh], base["builds"])
            for k, p in enumerate(ps, 1):
                out[f"{sh}-{k}"] = cost(sh, p)
        return out
    def spread(ts):
        ts = sorted(ts.values())
        return (f"{len(ts)} jobs: min {ts[0]:.0f}, median {median(ts):.0f}, max {ts[-1]:.0f} "
                f"({ts[-1] / max(median(ts), 1e-9):.2f}x the median)")
    was = predicted({sh: split[sh]["split"] for sh in split})
    now = predicted(counts)
    print()
    print(f"Predicted seconds of tests per job, the current split counts: {spread(was)}")
    print(f"Predicted seconds of tests per job, the new split counts: {spread(now)}")
    print(f"Floor: {floor:.0f} s (the longest job or case that cannot be split)")
    print()
    print("| job | predicted s (current counts) | predicted s (new counts) |")
    print("|---|---:|---:|")
    for n in sorted(set(was) | set(now), key=lambda n: -max(was.get(n, 0), now.get(n, 0))):
        f = lambda d: f"{d[n]:.0f}" if n in d else ""
        print(f"| {md(n)} | {f(was)} | {f(now)} |")
    if write:
        with open(TIMINGS, "w", encoding="utf-8") as f:
            f.write(baseline_json(base) + "\n")
        text = open(SHARDS, encoding="utf-8").read()
        for sh, n in counts.items():
            text, k = re.subn(r'("name": "' + re.escape(sh) + r'",\s*"split": )\d+', lambda m: m.group(1) + str(n), text)
            if k != 1:
                sys.exit(f"rebalance: cannot find the \"split\" of {sh} in {SHARDS}")
        with open(SHARDS, "w", encoding="utf-8") as f:
            f.write(text)
        print()
        print(f"Wrote {os.path.relpath(TIMINGS, ROOT)} and the split counts of {os.path.relpath(SHARDS, ROOT)}.")
    return 0


def main(args):
    if args[:2] == ["matrix", "--only"] and len(args) >= 3:
        matrix(args[3] if len(args) > 3 else DEFAULT_BIN, set(json.loads(args[2])))
        return 0
    if args[:1] == ["changes"] and len(args) >= 2:
        return changes(args[1:])
    binary = args[1] if len(args) > 1 else DEFAULT_BIN
    if args[:1] == ["matrix"]:
        matrix(binary)
        return 0
    if args[:2] == ["check-shards", "--self-test"]:
        return check_shards_self_test()
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
    if args[:1] == ["fetch-runs"]:
        return fetch_runs(args[1:])
    if args[:1] == ["rebalance"]:
        return rebalance(args[1:])
    if args[:1] == ["baseline"] and len(args) >= 2:
        return make_baseline(args[1:])
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
