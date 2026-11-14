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
                                     unless only docs changed, and shards=[NAMES], the
                                     shards of .github/test-shards.json to run (each
                                     shard's "inputs", see `needed_shards`). `changes
                                     --all` prints everything
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

Selectors are the arguments of `lake test --`: `=NAME` selects the group NAME,
`=NAME#I,J` the cases I and J of it, anything else is a prefix of group names (see
Tests/Main.lean).
"""
import fnmatch, json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SHARDS = os.path.join(ROOT, ".github", "test-shards.json")
TIMINGS = os.path.join(ROOT, ".github", "test-timings.json")
DEFAULT_BIN = os.path.join(ROOT, ".lake/build/bin/tests")
NOTE_USES = "uses "
NOTE_BUILT = "built "


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
    estimated seconds or None, jobs)]; `jobs` is the shard's "--jobs" (1 unless the shard
    says "jobs": N: the number of cases of a parallel-opted-in group it runs at a time)."""
    out = []
    for s in resolved(binary):
        n = s.get("split", 1)
        jobs = s.get("jobs", 1)
        if n <= 1:
            out.append((s["name"], s["select"], None, jobs))
            continue
        base = base or baseline()
        items = estimate(list_cases(binary, s["select"]), base)
        for k, p in enumerate(partition(items, n, base["builds"]), 1):
            if p:
                out.append((f"{s['name']}-{k}", part_selectors(p), part_cost(p, base["builds"]), jobs))
    return out


def matrix(binary, only=None):
    # "heavy": true shards (and the parts of a split one) may run on the self-hosted
    # runner (vars.WIZ_RUNNER_HEAVY, docs/ci-runner.md)
    heavy = {s["name"] for s in shards() if s.get("heavy")}
    split = {s["name"] for s in shards() if s.get("split", 1) > 1}
    def is_heavy(n):
        base = n.rsplit("-", 1)[0]
        return n in heavy or (base in split and base in heavy)
    def wanted(n):
        return only is None or n in only or (n.rsplit("-", 1)[0] in split and n.rsplit("-", 1)[0] in only)
    print(json.dumps({"shard": [{"name": n, "select": "\n".join(sel), "heavy": is_heavy(n),
                                 "jobs": jobs}
                                for n, sel, _, jobs in expanded(binary) if wanted(n)]}, ensure_ascii=False))


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
# Files every shard depends on: the Lean sources (compiler, tests, grail), the
# build and its toolchain, the C runtime, CI itself. A change to any runs every shard.
EVERYTHING = ["*.lean", "lakefile.*", "lean-toolchain", "lake-manifest.json", "flake.*",
              "devenv.*", ".envrc", "runtime/*", "c/*", "scripts/*", ".github/*", "grail.wiz"]


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
        print(f"shards={json.dumps(names)}")
        return 0
    base, head = args[0], (args[1] if len(args) > 1 else "HEAD")
    out = subprocess.run(["git", "diff", "--name-only", base, head], capture_output=True,
                         text=True, check=True, cwd=ROOT).stdout
    files = [f for f in out.split("\n") if f]
    names = needed_shards(files)
    code = any(not matches(f, DOCS) for f in files)
    print(f"code={'true' if code else 'false'}")
    print(f"shards={json.dumps(names)}")
    print(f"{len(files)} files changed; code: {code}; shards: {', '.join(names) or 'none'}", file=sys.stderr)
    return 0


GROUP = re.compile(r"^── (.*) \((.*)\)$")
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
    binary = args[1] if len(args) > 1 else DEFAULT_BIN
    if args[:1] == ["matrix"]:
        matrix(binary)
        return 0
    if args[:1] == ["check-shards"]:
        return check_shards(binary)
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
