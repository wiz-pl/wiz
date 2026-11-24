#!/usr/bin/env python3
"""Helpers for .github/workflows/ci.yml.

  scripts/ci.py matrix [--only JSON] [BIN]
                                     the shards of .github/test-shards.json as a JSON
                                     matrix (one line, for $GITHUB_OUTPUT); each shard's
                                     selectors are joined by newlines, "heavy"
                                     says whether it may use the self-hosted runner, and
                                     "jobs" how many cases it runs at a time (`--jobs`);
                                     and "allow-missing-deps": whether the test step sets
                                     WIZ_ALLOW_MISSING_DEPS (a shard whose environment
                                     deliberately lacks an optional tool; see
                                     check-skips). With --only ["NAME",…], only those
                                     shards (and
                                     their parts) A shard with
                                     "split": N becomes N shards NAME-1 … NAME-N, its
                                     cases balanced by .github/test-timings.json (needs
                                     the test driver BIN; default .lake/build/bin/tests).
                                     The shards are ordered by predicted job wall, longest
                                     first (the per-part simulation of `simulated_wall`:
                                     serial groups summed, an in-order `--jobs` pool for
                                     the parallel ones, builds unscaled), because GitHub
                                     starts a matrix in that order and its 20-job cap
                                     leaves the late entries waiting: the expensive work
                                     should start in the first wave. A shard the baseline
                                     cannot estimate goes last, by name.
  scripts/ci.py check-shards [BIN]   check that every test case is run by exactly one
                                     shard (after splitting), that every selector of a
                                     shard selects something, that the plan is total:
                                     every group a shard selects or an entry of
                                     .github/test-shard-exclusions.json (with a reason
                                     and an owner) explains, and that every job's
                                     predicted wall is under the shard budget
                                     (SHARD_BUDGET_S). A group with neither is an
                                     error naming it — the old fallback to a default
                                     shard is gone — and so is an exclusion whose group
                                     does not exist or which a shard selects after all.
                                     Also fails on a .github/skip-allowlist.json entry
                                     whose group or case no case matches.
  scripts/ci.py plan [--json] [BIN]  each shard's (or part's) estimated wall: serial
                                     groups summed, the parallel groups' in-order
                                     `--jobs` pool, builds unscaled; then the longest
                                     predicted job wall and its margins to the shard
                                     budget and the job timeout; exits 1 when a shard
                                     is over the budget. --json prints the same as JSON
                                     plus the calibration of `PARALLEL_CONTENTION`
                                     against the measured 8-part and 12-part library
                                     runs.
  scripts/ci.py changes BASE [HEAD]  what a change needs (path filters): reads the files
                                     that differ between BASE and HEAD (git diff
                                     BASE HEAD; CI: a PR's merge commit and its first
                                     parent) and prints GitHub outputs: code=true
                                     unless only docs or the STC metatheory changed,
                                     docs=true when a doc changed, web=true when a
                                     browser-facing file (`web/*`) changed, stc=true
                                     when `STC.lean` or `STC/` changed (the `stc` job
                                     typechecks that library, which nothing else
                                     imports), subset_NAME=true for each build subset
                                     of `.github/repo-subsets.json` that a changed file
                                     belongs to (`scripts/repo-subsets.py`: lean,
                                     runtime, wizlib, packages, tests, docs), and
                                     shards=[NAMES], the shards of
                                     .github/test-shards.json to run (each shard's
                                     "inputs", see `needed_shards`). A changed file no
                                     subset claims (`scripts/`, `flake.*`,
                                     `selfhost/`, ...), and any `.github/` edit, sets
                                     every subset: it is a build input the table has
                                     not classified, so every subset job runs.
                                     `changes --all` prints everything
  scripts/ci.py subset-key NAME [--with NAME] [--scope S] [--suffix S]
                                     the Actions cache key and restore prefix for a
                                     subset job (`$GITHUB_OUTPUT` lines `key=` and
                                     `prefix=`): `subset-v1-<name>[-<name>...]-<os>-
                                     <arch>-<toolchain12>`, then `-<scope>` (in key and
                                     prefix), the subset sha(s) `-<sha12>` (one per
                                     name), and `-<suffix>` (key only). <sha12> is the
                                     subset's `sha256` from .github/repo-subsets.json;
                                     the prefix stops before the subset hashes, so a
                                     later run restores its own subset's previous
                                     entry and recompiles what changed.
  scripts/ci.py check-ci-shaped [--self-test] [CI_YML] [CI_SHAPED]
                                     every `lib.` call in ci.yml has a row in
                                     .github/ci-shaped.nix, the expression set
                                     `scripts/touched-derivations.sh` selects from:
                                     CI calls `lib.selfhostWith { wiz; tests; }` and
                                     `lib.towerWith wiz`, and evaluating `.#X` never
                                     touches that path, so a row per call site is what
                                     makes "the derivation changed" visible to the
                                     selector. A call with no row is an error (the
                                     selector would silently not look), a row whose
                                     call ci.yml no longer makes is a warning
                                     (`lib.withLakeCache` is scripts/lake-cache.sh's and
                                     has no ci.yml call on purpose). `--self-test`
                                     checks the rule on a synthetic pair of files
  scripts/ci.py timings [--warn-ratio F] [--max-ratio F] LOG|JSONL..
                                     the effective timeout of every case line the test
                                     driver prints (`[n/f/t] ✓ name (12.3 s / limit
                                     300 s)`) and of every `--timings` record
                                     ("limit"), and a warning per case that used more
                                     than F (default 0.8) of its limit: a raised
                                     timeout that never took effect (an option after
                                     the subcommand) is then a visible no-op, not a
                                     reflex. Exits 1 with --max-ratio FRACTION when a
                                     case is over FRACTION of its limit (the gate);
                                     the 80 % warning alone does not fail
  scripts/ci.py summary TITLE FILE.. a Markdown summary for $GITHUB_STEP_SUMMARY of
                                     `lake test` logs (*.log: pass/fail, failing cases)
                                     and `--timings` files (*.jsonl: a table of every
                                     case's time with group and shard totals; with
                                     several shards, a table of the shards and the
                                     slowest cases)
  scripts/ci.py baseline JSONL..     a new .github/test-timings.json (stdout) from
                                     `--timings` files, e.g. the `test-timings`
                                     artifact of a CI run (every shard's cases, so
                                     `plan` and `matrix` price the unsplit ones too)
  scripts/ci.py balance [--factor F] [--baseline-out FILE] [--strict] JSONL..
                                     check a run's shard balance from its `--timings`
                                     files: the longest shard's test time is at most F
                                     (default 1.5) times the median shard's, every case
                                     of a split shard is in .github/test-timings.json,
                                     and no shared program is built by two parts of one
                                     split shard (a "split-cases" shard excepted: its
                                     parts each build it by design). Prints GitHub warning
                                     annotations and
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
                                     not split is its median wall time. That measured
                                     ratio is rebalance's own planner only (it has the
                                     run's real walls); it is no longer written to the
                                     shard, because plan/matrix simulate each part
                                     (see `simulated_wall`).
                                     Prints the new baseline's
                                     summary, the "split" count of each split shard and
                                     the predicted time of every job (min/median/max);
                                     with --write, writes .github/test-timings.json and
                                     the "split" counts of
                                     .github/test-shards.json.
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
                                     node, nix, …), when a skip that a
                                     `--allow-missing-deps` run recorded as a missing
                                     dependency (`missing-dep` note) is not named by an
                                     allow-list entry, when a group's unexplained skipped
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
import fnmatch, hashlib, json, os, platform, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SHARDS = os.path.join(ROOT, ".github", "test-shards.json")
TIMINGS = os.path.join(ROOT, ".github", "test-timings.json")
SKIPS = os.path.join(ROOT, ".github", "skip-allowlist.json")
EXCLUSIONS = os.path.join(ROOT, ".github", "test-shard-exclusions.json")
REPO_SUBSETS = os.path.join(ROOT, ".github", "repo-subsets.json")
WORKFLOW = os.path.join(ROOT, ".github", "workflows", "ci.yml")
CI_SHAPED = os.path.join(ROOT, ".github", "ci-shaped.nix")
DEFAULT_BIN = os.path.join(ROOT, ".lake/build/bin/tests")
NOTE_USES = "uses "
NOTE_BUILT = "built "
# The `tests` job's timeout (`.github/workflows/ci.yml`) and the shard budget that
# `plan` and `check-shards` enforce: a shard's predicted job wall must stay under the
# budget, which leaves time for the job's setup before the tests step and for the
# model's error. A shard over the budget is split, not given a longer timeout: a
# timeout is a cancelled job with a partial log (`balance` then cannot see it).
# docs/ci-runner.md "The shard budget".
JOB_TIMEOUT_S = 120 * 60
SHARD_BUDGET_S = 75 * 60

# The per-part simulation (`simulated_wall`) multiplies only the parallel groups' pool
# by this. Sharing the runner's vCPUs inflates a case's time, so the pool can be slower
# than the sum of the case times says; the factor is measured, not guessed.
#
# Calibration, with each run's own `test-timings` artifact (the per-case seconds the
# baseline would hold after a refresh; comparing through a stale committed baseline
# measures its staleness, not the model). Measured walls are `tests` job walls in
# minutes; the model's are its prediction from those per-case times:
#
#   8-part run 45191566067 (train11 9ee24e52b):
#     library-1 65.8/64.0  library-2 83.5/84.3  library-3 73.8/72.3
#     library-4 90.3/87.9 (CANCELLED at 90.3: censored, a lower bound)
#     library-5 79.6/80.8  library-6 85.0/85.0  library-7 54.8/54.0
#     library-8 62.0/59.9                      residuals -3.5 % .. +1.4 %
#   12-part run 45210110113 (train11 77632f10a):
#     library-12 49.5/48.4                     residual -2.2 %
#
# The least-squares factor on the parallel pool is 1.010 for the 8-part run and 1.035
# for library-12: there is no systematic under-prediction to correct (the measured job
# walls include about a minute of setup before the tests step, which the model does not),
# so the constant stays 1.0. `plan --json` prints the table with residuals so a later
# reader can see whether it still holds.
PARALLEL_CONTENTION = 1.0
CALIBRATION = {
    # run: {shard: (measured tests-job wall min, simulated wall min, censored)}
    "45191566067 (8 library parts, train11 9ee24e52b)": {
        "library-1": (65.8, 64.0, False), "library-2": (83.5, 84.3, False),
        "library-3": (73.8, 72.3, False),
        "library-4": (90.3, 87.9, True),  # cancelled at 90.3: a lower bound
        "library-5": (79.6, 80.8, False), "library-6": (85.0, 85.0, False),
        "library-7": (54.8, 54.0, False), "library-8": (62.0, 59.9, False),
    },
    "45210110113 (12 library parts, train11 77632f10a)": {
        "library-12": (49.5, 48.4, False),
    },
}

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


class ShardPlanError(Exception):
    """The shard plan is not total: a group is in no shard and no exclusion says why, an
    exclusion is stale, or a selector names nothing. `check-shards` reports it as an
    error, and `matrix`/`plan` refuse to build a plan that would silently lose cases."""


def exclusions(path=None):
    """The groups that run in no CI shard, each with `group`, `reason` and `owner` (and
    optional `why`). The plan is total only when every case-listed group is selected by a
    shard's selectors or named here: a group that is in neither is an error, not a
    fallback to a default shard. A malformed entry is an error; `check-shards` fails on an
    entry whose group does not exist, or which a shard selects after all (a stale entry)."""
    path = path or EXCLUSIONS
    try:
        with open(path, encoding="utf-8") as f:
            doc = json.load(f)
    except FileNotFoundError:
        return []
    out = []
    for e in doc.get("groups", []):
        for k in ("group", "reason", "owner"):
            if not str(e.get(k, "")).strip():
                raise ShardPlanError(f"{path}: the entry {json.dumps(e)} lacks {k!r}")
        out.append(dict(e))
    return out


def check_group_plan(groups, hints=None):
    """The plan's group-totality errors: a group (from `tests --list`) that no shard
    selects and no exclusion explains; an exclusion whose group does not exist; an
    exclusion a shard selects after all. `hints` maps a group to its `Group.shard` hint,
    only to make the first error more useful. Empty when the plan is total."""
    ss = shards()
    excl = {e["group"]: e for e in exclusions()}
    hints = hints or {}
    errors = []
    if not groups:
        return ["no test groups listed: the listing is empty, so the plan proves nothing"]
    for g in groups:
        picked = [s["name"] for s in ss if any(selects(g, sel) for sel in s["select"])]
        if g in excl:
            if picked:
                errors.append(
                    f"{EXCLUSIONS}: {g!r} is excluded, but the shard(s) {', '.join(picked)} "
                    f"select it; either delete the exclusion or the selector")
        elif not picked:
            where = f"; its Group.shard hint names {hints[g]!r}" if hints.get(g) else ""
            errors.append(
                f"{SHARDS}: no shard selects the group {g!r}{where}. Add '={g}' to a "
                f"shard's select list, or an entry for it in {EXCLUSIONS} saying why it "
                f"runs nowhere")
    for g in excl:
        if g not in groups:
            errors.append(
                f"{EXCLUSIONS}: the exclusion names {g!r}, which is not a test group "
                f"(`tests --list-shards`)")
    return errors


def resolved(binary):
    """The shards of .github/test-shards.json, checked to be total: every group that
    `tests --list-shards` reports must be selected by a shard's selectors or named in
    .github/test-shard-exclusions.json. There is no default-shard fallback: a new group
    that nobody wired is an error naming the group (and its `Group.shard` hint, if any),
    not a case that quietly joins another shard's queue."""
    ss = shards()
    out = subprocess.run([binary, "--list-shards"], capture_output=True, text=True, check=True,
                         cwd=ROOT).stdout
    groups, hints = [], {}
    for line in out.split("\n"):
        if not line:
            continue
        g, _, hint = line.partition("\t")
        groups.append(g)
        hints[g] = hint
    errors = check_group_plan(groups, hints)
    if errors:
        raise ShardPlanError("\n".join(errors))
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


def partition(items, n, builds, split_cases=False):
    """Split the cases into n parts with the smallest longest part (estimated). The
    cases that use the same shared programs (the self-hosted checker or compiler: the
    first case that needs one builds it) stay together, so each program is built by one
    part only; the other cases fill the parts up. With `split_cases`, each case is its own
    unit instead: a shard of sibling cases over disjoint inputs (the `selfhost-libdiff`
    file parts) wants them spread over the jobs, and `part_cost` charges every part the
    build it then pays. Greedy, longest first, then single moves while they help;
    deterministic."""
    clusters = {}
    for it in items:
        clusters.setdefault(it[4], []).append(it)
    # the units to place: a cluster per set of programs, and each remaining case
    units = ([[it] for it in items] if split_cases else
             [c for uses, c in clusters.items() if uses] + [[it] for it in clusters.get((), [])])
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
    """The shards with each split shard replaced by its parts: [(name, selectors, items,
    jobs)]; `items` is `estimate`'s [(group, index, name, seconds, uses)] for the cases
    of the shard (or part), in listing order, and `jobs` is the shard's "--jobs" (None
    unless the shard says "jobs": N: the number of cases of a parallel-opted-in group it
    runs at a time). A shard without "jobs" is run without `--jobs`, so a case that has
    an auto mode (selfhost-libdiff) can tell "not given" from "--jobs 1". A shard with
    "split-cases": true hands each case to `partition` on its own rather than keeping the
    cases that use one shared program together (see `partition`)."""
    out = []
    base = base or baseline()
    for s in resolved(binary):
        n = s.get("split", 1)
        jobs = s.get("jobs")
        if n <= 1:
            out.append((s["name"], s["select"], estimate(list_cases(binary, s["select"]), base), jobs))
            continue
        items = estimate(list_cases(binary, s["select"]), base)
        split_cases = bool(s.get("split-cases"))
        for k, p in enumerate(partition(items, n, base["builds"], split_cases), 1):
            if p:
                out.append((f"{s['name']}-{k}", part_selectors(p), p, jobs))
    return out


_PARALLEL_GROUPS = {}


def parallel_groups(binary):
    """The groups that opt in to `--jobs N` (`Group.parallel`): `tests --list-parallel`
    prints their names, one per line. Only these run cases through `Group.runJobs`; a
    group that did not opt in runs its cases one at a time even when the shard passes
    `--jobs` (a case may still use the count itself, and its measured seconds already
    include that)."""
    key = os.path.abspath(binary)
    if key not in _PARALLEL_GROUPS:
        try:
            out = subprocess.run([binary, "--list-parallel"], capture_output=True,
                                 text=True, check=True, cwd=ROOT).stdout
        except (OSError, subprocess.CalledProcessError) as e:
            raise ShardPlanError(
                f"{binary} does not answer `--list-parallel` ({e}): the per-part wall "
                f"simulation needs the groups' `Group.parallel` flags. Rebuild the test "
                f"driver (`lake build wiz tests`)")
        _PARALLEL_GROUPS[key] = {g for g in out.split("\n") if g}
    return _PARALLEL_GROUPS[key]


def simulated_wall(items, jobs, builds, parallel):
    """The predicted job wall of a shard or part, in seconds, from `estimate`'s cases.

    The driver runs the shard's groups one after another, with a barrier between them
    (`Tests/Main.lean:375-378`): a group's cases finish before the next group starts. A
    group that opted in (`parallel`) and a shard that passes `--jobs N` run their cases
    through `Group.runJobs`, an in-order pool of N child processes (`Tests/Harness.lean`):
    cases start in index order and results are collected in start order, so case i starts
    when case i-N is collected -- slot i % N, not "whichever slot is free first" (a long
    case at the head holds the next start). The pool's wall is its last slot. A serial
    group is the sum of its cases. The programs the part builds (`uses`) do not overlap
    the case that pays them, so their seconds are added once, unscaled: a build is not
    parallelised and must not be discounted by `PARALLEL_CONTENTION`."""
    by_group = {}
    for g, i, n, s, uses in items:
        by_group.setdefault(g, []).append(s)
    serial = pool = 0.0
    for g, secs in by_group.items():
        if jobs and jobs > 1 and g in parallel and len(secs) > 1:
            slots = [0.0] * jobs
            for k, s in enumerate(secs):
                slots[k % jobs] += s
            pool += max(slots)
        else:
            serial += sum(secs)
    used = {r for *_, u in items for r in u}
    return serial + PARALLEL_CONTENTION * pool + sum(builds.get(r, 0.0) for r in used)


def predicted_costs(binary, base=None):
    """{job name: predicted job wall seconds} for every job of the full matrix, from
    `simulated_wall` over the shard's cases and the programs it builds. None when a
    shard selects no case (`matrix` sorts it last). This is the model the shard budget
    guards and the cost `matrix` orders by."""
    base = base or baseline()
    parallel = parallel_groups(binary)
    out = {}
    for name, sel, items, jobs in expanded(binary, base):
        out[name] = simulated_wall(items, jobs, base["builds"], parallel) if items else None
    return out


def matrix_entries(binary, only=None):
    """The shards' matrix entries, longest first (see the ordering note below)."""
    # "heavy": true shards (and the parts of a split one) may run on the self-hosted
    # runner (vars.WIZ_RUNNER_HEAVY, docs/ci-runner.md)
    heavy = {s["name"] for s in shards() if s.get("heavy")}
    split = {s["name"] for s in shards() if s.get("split", 1) > 1}
    # a shard that may report a missing dependency as a skip (`--allow-missing-deps`):
    # only a shard whose environment deliberately lacks an optional tool, and only with
    # an allow-list entry per case (scripts/ci.py check-skips)
    allow_missing = {s["name"] for s in shards() if s.get("allow-missing-deps")}
    def is_heavy(n):
        base = n.rsplit("-", 1)[0]
        return n in heavy or (base in split and base in heavy)
    def allows_missing(n):
        base = n.rsplit("-", 1)[0]
        return n in allow_missing or (base in split and base in allow_missing)
    def wanted(n):
        return only is None or n in only or (n.rsplit("-", 1)[0] in split and n.rsplit("-", 1)[0] in only)
    base = baseline()
    parallel = parallel_groups(binary)
    def cost(name, items, jobs):
        """Predicted job wall seconds from `simulated_wall` (serial groups summed, the
        parallel groups' in-order `--jobs` pool, builds unscaled). `None` when the shard
        selects no case at all (`check-shards` reports that): it goes last."""
        return simulated_wall(items, jobs, base["builds"], parallel) if items else None
    rows = [(n, sel, jobs, cost(n, items, jobs))
            for n, sel, items, jobs in expanded(binary, base) if wanted(n)]
    # GitHub starts a matrix in its listed order and the 20-concurrent-job cap leaves the
    # late entries waiting (`test (prop)` started 16 minutes after the wave did), so the
    # longest shards come first: the expensive work is in the first wave, not the tail.
    rows.sort(key=lambda r: (r[3] is None, -(r[3] or 0.0), r[0]))
    return [{"name": n, "select": "\n".join(sel), "heavy": is_heavy(n), "jobs": jobs,
             "allow-missing-deps": allows_missing(n)}
            for n, sel, jobs, _ in rows]


def matrix(binary, only=None):
    print(json.dumps({"shard": matrix_entries(binary, only)}, ensure_ascii=False))


def budget_report(costs):
    """Print the longest predicted job wall and its margins to the shard budget and the
    job timeout; return 1 when a job is over the budget. `plan` and `check-shards` share
    this guard so a red baseline stops the `lean` job before the matrix starts, rather
    than timing a shard out (a cancelled job's partial log hides the case that hung)."""
    timed = {n: t for n, t in costs.items() if t is not None}
    if not timed:
        print("the shard plan has no estimate: it proves nothing about the budget",
              file=sys.stderr)
        return 1
    name, top = max(timed.items(), key=lambda kv: (kv[1], kv[0]))
    margin, timeout_margin = SHARD_BUDGET_S - top, JOB_TIMEOUT_S - top
    print(f"Longest predicted job: {name} {top:.0f} s ({top / 60:.1f} min); "
          f"shard budget {SHARD_BUDGET_S} s ({SHARD_BUDGET_S / 60:.0f} min): "
          f"margin {margin:.0f} s ({margin / 60:.1f} min); "
          f"job timeout {JOB_TIMEOUT_S} s ({JOB_TIMEOUT_S / 60:.0f} min): "
          f"margin {timeout_margin:.0f} s ({timeout_margin / 60:.1f} min)")
    over = sorted(((t, n) for n, t in timed.items() if t > SHARD_BUDGET_S), reverse=True)
    for t, n in over:
        print(f"{n}: predicted {t:.0f} s ({t / 60:.1f} min), over the "
              f"{SHARD_BUDGET_S / 60:.0f}-minute shard budget "
              f"(docs/ci-runner.md \"The shard budget\"); split the shard or refresh "
              f".github/test-timings.json", file=sys.stderr)
    return 1 if over else 0


def plan(binary, as_json=False):
    base = baseline()
    parallel = parallel_groups(binary)
    rows = []
    costs = {}
    for name, sel, items, jobs in expanded(binary, base):
        wall = simulated_wall(items, jobs, base["builds"], parallel) if items else None
        costs[name] = wall
        case_sum = sum(it[3] for it in items)
        used = sorted({r for *_, u in items for r in u})
        builds = sum(base["builds"].get(r, 0.0) for r in used)
        rows.append({"name": name, "cases": len(items), "case_sum_s": round(case_sum, 1),
                     "builds_s": round(builds, 1), "jobs": jobs, "builds": used,
                     "predicted_wall_s": None if wall is None else round(wall, 1)})
        if as_json or wall is None:
            continue
        if jobs and jobs > 1:
            text = (f"~{wall:.0f} s predicted wall (~{case_sum:.0f} s cases + "
                    f"{builds:.0f} s builds, --jobs {jobs})")
        else:
            text = f"~{wall:.0f} s estimated (~{case_sum:.0f} s cases + {builds:.0f} s builds)"
        print(f"{name}: {len(items)} cases, {text}"
              + (f" (builds {', '.join(used)})" if used else ""))
        for g, i, n, s, uses in items:
            print(f"    {g} #{i} {n}")
    if as_json:
        timed = {n: t for n, t in costs.items() if t is not None}
        top = max(timed.items(), key=lambda kv: (kv[1], kv[0])) if timed else None
        cal = [{"run": run, "shard": shard, "measured_min": m, "simulated_min": p,
                "residual_pct": round((p - m) / m * 100, 1), "censored": censored}
               for run, walls in CALIBRATION.items()
               for shard, (m, p, censored) in walls.items()]
        print(json.dumps({
            "shards": rows,
            "longest": None if top is None else {
                "name": top[0], "predicted_wall_s": round(top[1], 1),
                "shard_budget_s": SHARD_BUDGET_S, "job_timeout_s": JOB_TIMEOUT_S},
            "over_budget": sorted(n for n, t in timed.items() if t > SHARD_BUDGET_S),
            "parallel_contention": PARALLEL_CONTENTION,
            "calibration": cal,
        }, ensure_ascii=False))
        return 1 if any(t > SHARD_BUDGET_S for t in timed.values()) else 0
    return budget_report(costs)


def check_shards(binary):
    out = subprocess.run([binary, "--list"], capture_output=True, text=True, check=True).stdout
    groups = [g for g in out.split("\n") if g]
    errors = []
    if not groups:
        print("the test driver listed no groups (`--list`): nothing to check", file=sys.stderr)
        return 1
    try:
        excl = {e["group"]: e for e in exclusions()}
    except ShardPlanError as e:
        print(e, file=sys.stderr)
        return 1
    for g in excl:
        if g not in groups:
            errors.append(f"{EXCLUSIONS}: the exclusion names {g!r}, which is not a test group")
    names = set()
    for s in shards():
        if s["name"] in names:
            errors.append(f"shard name {s['name']!r} is used twice")
        names.add(s["name"])
        if not s["select"]:
            errors.append(f"shard {s['name']!r}: no selectors (an empty selector list runs "
                          f"every case, so it is never what was meant)")
        ratio = s.get("wall-ratio")
        if ratio is not None:
            errors.append(f"shard {s['name']!r}: wall-ratio {ratio!r} is obsolete: "
                          f"`plan`/`matrix` simulate each part (`simulated_wall`: the "
                          f"serial groups summed, the parallel groups' in-order `--jobs` "
                          f"pool, builds unscaled), so remove the field")
        for sel in s["select"]:
            picked = [g for g in groups if selects(g, sel)]
            if not picked:
                errors.append(f"shard {s['name']!r}: selector {sel!r} selects no group")
            for g in picked:
                if g in excl:
                    errors.append(f"shard {s['name']!r}: selector {sel!r} selects {g!r}, "
                                  f"which {EXCLUSIONS} excludes")
    # every group must be in a shard or in the exclusion list; `resolved` is also the
    # plan the matrix is built from, so check it here (and report rather than exit)
    try:
        parts = expanded(binary)
    except ShardPlanError as e:
        errors.append(str(e))
        parts = []
    runs = {(g, i): [] for g, i, _ in list_cases(binary, []) if g not in excl}
    for name, sel, items, _ in parts:
        for g, i in {(g, i) for g, i, *_ in items}:  # a case selected twice within a shard still runs once
            runs[(g, i)].append(name)
    for g in groups:
        if g in excl:
            continue
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
    jobs = []
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
    # an allow-list entry whose group or case no longer exists cannot fire: it documents a
    # parity gap that is gone (or renamed), so it is a failure, not a note
    dead = dead_allowlist_entries(allowlist(), binary)
    for e, why in dead:
        errors.append(f"{SKIPS}: the entry {e['group']!r} / {e['case']!r} matches no case: {why}")
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
    # the tail guard: the longest predicted job wall (`simulated_wall`: serial groups
    # summed, the parallel groups' in-order `--jobs` pool, builds unscaled) must stay
    # under SHARD_BUDGET_S. A shard over it is an error, not a warning: the job timeout
    # would cancel it with a partial log, which hides the case that hung (`balance`
    # cannot see a cancelled job).
    costs = predicted_costs(binary, base)
    timed = {n: t for n, t in costs.items() if t is not None}
    if not timed:
        errors.append("no shard has an estimate: the plan proves nothing about the budget")
    over = sorted(((t, n) for n, t in timed.items() if t > SHARD_BUDGET_S), reverse=True)
    for t, n in over:
        errors.append(f"shard {n}: predicted {t:.0f} s ({t / 60:.1f} min), over the "
                      f"{SHARD_BUDGET_S / 60:.0f}-minute shard budget "
                      f"(docs/ci-runner.md \"The shard budget\"); split the shard or "
                      f"refresh .github/test-timings.json")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    longest = max(timed.items(), key=lambda kv: (kv[1], kv[0]))
    excluded = sorted(excl)
    print(f"ok: {len(groups)} groups ({len(excluded)} excluded: {', '.join(excluded) or 'none'}), "
          f"{len(runs)} cases, each in exactly one of {len(parts)} shards "
          f"(the matrix's {len(jobs)} jobs run them all, once); "
          f"{len(allowlist())} allow-list entries all match a case; "
          f"longest predicted job {longest[0]} ~{longest[1]:.0f} s "
          f"({SHARD_BUDGET_S / 60:.0f}-minute budget)")
    return 0


FAKE_DRIVER = r'''#!/usr/bin/env python3
"""A stand-in for the test driver (`check-shards --self-test`): answers --list,
--list-shards, --list-parallel and --list-cases from LISTING (group, index, name,
shard hint, parallel)."""
import json, sys
LISTING = json.loads(%r)
def sel(group, s):
    return group == s[1:].split("#")[0] if s.startswith("=") else group.startswith(s)
def picks(g, i, s):
    if not sel(g, s):
        return False
    return "#" not in s or i in [int(x) for x in s.split("#", 1)[1].split(",")]
a = sys.argv[1:]
groups = list(dict.fromkeys(g for g, *_ in LISTING))
if a == ["--list"]:
    print("\n".join(groups))
elif a == ["--list-shards"]:
    hint = {g: h for g, _, _, h, _ in LISTING}
    print("\n".join(f"{g}\t{hint[g]}" for g in groups))
elif a == ["--list-parallel"]:
    print("\n".join(g for g, _, _, _, par in LISTING if par))
elif a[:1] == ["--list-cases"]:
    for g, i, n, _, _ in LISTING:
        if not a[1:] or any(picks(g, i, s) for s in a[1:]):
            print(f"{g}\t{i}\t{n}")
else:
    sys.exit(2)
'''


def fake_driver(directory, listing):
    """Write a stand-in test driver answering from LISTING [(group, index, name, shard
    hint, parallel)] (see FAKE_DRIVER) into DIRECTORY; its path."""
    path = os.path.join(directory, "tests")
    with open(path, "w", encoding="utf-8") as f:
        f.write(FAKE_DRIVER % json.dumps(listing))
    os.chmod(path, 0o755)
    return path


def check_shards_self_test():
    """`check-shards` on stand-in drivers, shard files and exclusion/allow lists: a good
    layout (with a split shard and an explicitly excluded group) passes; a dropped case,
    a case in two shards, a selector that selects nothing, a group no shard selects (the
    removed default fallback), a stale exclusion, an exclusion for a missing group, an
    exclusion without a reason, an obsolete wall-ratio and an allow-list entry no case
    matches fail. Also checks `simulated_wall` on a synthetic part whose in-order
    `--jobs 2` pool is not the mean (its first, long case holds the next start). Exits 1
    if an expectation is wrong."""
    import contextlib, io, tempfile
    global SHARDS, TIMINGS, EXCLUSIONS, SKIPS
    listing = ([("alpha", i, f"a{i}", "", False) for i in range(5)]
               + [("beta", i, f"b{i}", "", True) for i in range(7)]
               + [("gamma", i, f"c{i}", "", False) for i in range(3)]
               + [("delta", 0, "d0", "solo", False)])
    good = [{"name": "solo", "select": ["=delta"]},
            {"name": "big", "split": 3, "default": True, "select": ["=beta", "=gamma"]},
            {"name": "small", "select": ["alp"]}]
    no_delta = [{"name": "big", "split": 3, "default": True, "select": ["=beta", "=gamma"]},
                {"name": "small", "select": ["alp"]}]
    excl = lambda g, reason="fixture: not run in CI": {"groups": [
        {"group": g, "reason": reason, "owner": "shard self-test"}]}
    live = {"groups": [{"group": "beta", "case": "b0", "reason": "fixture reason",
                        "owner": "shard self-test", "expires": "2099-01-01"}]}
    dead = {"groups": [{"group": "beta", "case": "b99", "reason": "fixture reason",
                        "owner": "shard self-test", "expires": "2099-01-01"}]}
    empty = {"groups": []}
    # (name, listing, shards, exclusions, allow-list, expected exit, needle)
    trials = [
        ("good (a split shard)", listing, good, empty, empty, 0, None),
        ("a case the shards drop", listing,
         [{"name": "solo", "select": ["=delta"]},
          {"name": "big", "split": 3, "default": True, "select": ["=beta#0,1,2,3,4,5", "=gamma"]},
          {"name": "small", "select": ["alp"]}], empty, empty, 1, "in no shard"),
        ("a case in two shards", listing,
         [{"name": "solo", "select": ["=delta"]},
          {"name": "big", "split": 3, "default": True, "select": ["=beta", "=gamma"]},
          {"name": "small", "select": ["alp", "=gamma#1"]}], empty, empty, 1, "several shards"),
        ("a selector that selects nothing", listing,
         [{"name": "solo", "select": ["=delta"]},
          {"name": "big", "split": 2, "default": True, "select": ["=beta", "=gamma", "=epsilon"]},
          {"name": "small", "select": ["alp"]}], empty, empty, 1, "selects no group"),
        ("a shard with no selectors", listing,
         [{"name": "solo", "select": ["=delta"]},
          {"name": "big", "split": 2, "default": True, "select": ["=beta", "=gamma"]},
          {"name": "small", "select": []}], empty, empty, 1, "no selectors"),
        ("a group no shard selects (no default fallback)", listing, no_delta, empty, empty, 1,
         "no shard selects"),
        ("an exclusion says why delta is not run", listing, no_delta, excl("delta"), empty, 0, None),
        ("an exclusion for a group that does not exist", listing, good, excl("epsilon"), empty, 1,
         "not a test group"),
        ("an exclusion a shard contradicts", listing, good, excl("delta"), empty, 1, "excludes"),
        ("an exclusion without a reason", listing, no_delta,
         {"groups": [{"group": "delta", "owner": "shard self-test"}]}, empty, 1, "lacks"),
        ("an allow-list entry no case matches", listing, good, empty, dead, 1,
         "matches no case"),
        ("an allow-list entry that matches a case", listing, good, empty, live, 0, None),
        ("an obsolete wall-ratio (the simulation subsumes it)", listing,
         [{"name": "solo", "select": ["=delta"]},
          {"name": "big", "split": 3, "default": True, "select": ["=beta", "=gamma"]},
          {"name": "small", "select": ["alp"], "wall-ratio": 0.6}], empty, empty, 1,
         "obsolete"),
        ("an empty group listing proves nothing", [], good, empty, empty, 1, "no groups"),
    ]
    saved, wrong = (SHARDS, TIMINGS, EXCLUSIONS, SKIPS), []
    try:
        for k, (name, lst, config, ex, allow, want, needle) in enumerate(trials):
            with tempfile.TemporaryDirectory() as d:
                SHARDS = os.path.join(d, "shards.json")
                TIMINGS = os.path.join(d, "timings.json")
                EXCLUSIONS = os.path.join(d, "exclusions.json")
                SKIPS = os.path.join(d, "allow.json")
                with open(SHARDS, "w") as f:
                    json.dump(config, f)
                with open(EXCLUSIONS, "w") as f:
                    json.dump(ex, f)
                with open(SKIPS, "w") as f:
                    json.dump(allow, f)
                with open(TIMINGS, "w") as f:
                    json.dump({"cases": {"beta": {f"b{i}": {"seconds": 10.0 + i} for i in range(7)}},
                               "builds": {}}, f)
                binary = fake_driver(d, lst)
                err = io.StringIO()
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
                    got = check_shards(binary)
                text = err.getvalue()
                ok = got == want and (needle is None or needle in text)
                print(f"{'ok ' if ok else 'BAD'} {name}: exit {got} (expected {want})"
                      + ("" if ok else f"; stderr: {text.strip()}"))
                if not ok:
                    wrong.append(name)
        # the shard budget (`SHARD_BUDGET_S`): a part over it fails even when every case
        # is in exactly one shard
        with tempfile.TemporaryDirectory() as d:
            SHARDS = os.path.join(d, "shards.json")
            TIMINGS = os.path.join(d, "timings.json")
            EXCLUSIONS = os.path.join(d, "exclusions.json")
            SKIPS = os.path.join(d, "allow.json")
            with open(SHARDS, "w") as f:
                json.dump(good, f)
            for path, doc in ((EXCLUSIONS, empty), (SKIPS, empty)):
                with open(path, "w") as f:
                    json.dump(doc, f)
            with open(TIMINGS, "w") as f:
                json.dump({"cases": {"beta": {
                    f"b{i}": {"seconds": 5000.0 if i == 0 else 10.0 + i} for i in range(7)}},
                    "builds": {}}, f)
            binary = fake_driver(d, listing)
            err = io.StringIO()
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
                got = check_shards(binary)
            text = err.getvalue()
            name = f"a part over the {SHARD_BUDGET_S / 60:.0f}-minute budget"
            ok = got == 1 and "shard budget" in text
            print(f"{'ok ' if ok else 'BAD'} {name}: exit {got} (expected 1)"
                  + ("" if ok else f"; stderr: {text.strip()}"))
            if not ok:
                wrong.append(name)
        # the simulation itself: a synthetic part with known case times and `--jobs 2`.
        # The driver collects results in order, so case i starts when case i-2 is
        # collected: [10,1,1,1,1,1] is 10+1+1 on one slot and 1+1+1 on the other (12 s),
        # not the mean (7.5 s) and not "least-loaded first" (10 s).
        trials = [
            ("in-order `--jobs 2` pool, not the mean",
             [("p", i, f"p{i}", s, ()) for i, s in enumerate([10.0, 1, 1, 1, 1, 1])],
             2, {"p"}, {}, 12.0),
            ("a serial group under `--jobs 2` is summed, not pooled",
             [("s", i, f"s{i}", s, ()) for i, s in enumerate([10.0, 1, 1, 1, 1, 1])],
             2, {"p"}, {}, 15.0),
            ("builds are added unscaled, not pooled",
             [("p", i, f"p{i}", s, ("compiler",) if i == 0 else ())
              for i, s in enumerate([10.0, 1, 1, 1, 1, 1])],
             2, {"p"}, {"compiler": 100.0}, 112.0),
        ]
        for name, items, jobs, par, builds, want in trials:
            got = simulated_wall(items, jobs, builds, par)
            ok = abs(got - want) < 1e-9
            print(f"{'ok ' if ok else 'BAD'} {name}: {got:g} s (expected {want:g})")
            if not ok:
                wrong.append(name)
        # end to end: check-shards reads the simulation, not the case sum (sum 5196 s,
        # old 0.6 * sum = 3118 s; the in-order pool puts 4200 + 3 * 166 on one slot)
        with tempfile.TemporaryDirectory() as d:
            SHARDS = os.path.join(d, "shards.json")
            TIMINGS = os.path.join(d, "timings.json")
            EXCLUSIONS = os.path.join(d, "exclusions.json")
            SKIPS = os.path.join(d, "allow.json")
            with open(SHARDS, "w") as f:
                json.dump([{"name": "solo", "select": ["=delta", "=gamma"]},
                           {"name": "small", "select": ["alp"]},
                           {"name": "pool", "jobs": 2, "select": ["=beta"]}], f)
            for path, doc in ((EXCLUSIONS, empty), (SKIPS, empty)):
                with open(path, "w") as f:
                    json.dump(doc, f)
            with open(TIMINGS, "w") as f:
                json.dump({"cases": {"beta": {
                    f"b{i}": {"seconds": 4200.0 if i == 0 else 166.0} for i in range(7)}},
                    "builds": {}}, f)
            binary = fake_driver(d, listing)
            err = io.StringIO()
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
                got = check_shards(binary)
            text = err.getvalue()
            name = "the budget uses the in-order pool, not the case sum"
            ok = got == 1 and "shard budget" in text
            print(f"{'ok ' if ok else 'BAD'} {name}: exit {got} (expected 1)"
                  + ("" if ok else f"; stderr: {text.strip()}"))
            if not ok:
                wrong.append(name)
    finally:
        SHARDS, TIMINGS, EXCLUSIONS, SKIPS = saved
    return 1 if wrong else 0


# Path filters (`changes`). Files only people read: a change of only these runs no build
# and no tests.
DOCS = ["docs/*", "*.md", "LICENSE", "COPYING*"]
# Browser-facing sources: the playground, the infoview and site scripts, their Node
# tests and the Wiz programs they are built from. The `web` job (`ci.yml`) builds the
# Wasm modules and runs the browser-free half of web/test.sh when one of these changes;
# the Chromium half of that script stays local.
WEB = ["web/*"]
# The attestation tooling is covered by the `attest` job's Python unit tests. It does not
# feed the Lean build, so a change only under scripts/attest must not schedule a shard.
SELF_TESTED = ["scripts/attest/*"]
# Files every shard depends on: the Lean sources (compiler, tests, grail), the
# build and its toolchain, the C runtime, CI itself, and the web/ tree — its Wiz
# sources and JS hosts are read by test groups (`web/Web.wiz`, `web/framework/gen.wiz`,
# `web/wasm-host.mjs`), and a change there is checked by the `web` job rather than by
# one shard, so it sends every shard to be safe. A change to any runs every shard.
EVERYTHING = ["*.lean", "lakefile.*", "lean-toolchain", "lake-manifest.json", "flake.*",
              ".envrc", "runtime/*", "c/*", "scripts/*", ".github/*", "grail.wiz",
              "web/*"]
# The STC metatheory (`STC.lean`, `STC/`) is a separate Lake library, deliberately not a
# default target, and nothing else imports it; `flake.nix` does not copy it into the Nix
# build either (that would rebuild the compiler on every STC edit). An edit there needs
# the `stc` job and nothing else, so STC paths are kept out of EVERYTHING: otherwise the
# `*.lean` entry sends every wiz/grail shard to test a tree none of them reads. The `stc`
# job also runs when `code` is true, since a toolchain or lakefile change can break it.
STC = ["STC.lean", "STC/*"]


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


def is_code_change(files):
    """Whether `files` needs the default Lean build (wiz/grail/tests); docs, self-tested
    scripts and the STC metatheory (its own `stc` job) do not."""
    return any(not matches(f, DOCS + SELF_TESTED + STC) for f in files)


def repo_subsets():
    """The committed subset table (`.github/repo-subsets.json`): name -> path patterns.
    `scripts/repo-subsets.py` is the source of truth and `docs_style` proves the JSON
    describes the tree; reading the generated copy keeps the `changes` job free of a
    second pattern table. A missing or malformed table is an error, never a silent
    "nothing changed"."""
    try:
        with open(REPO_SUBSETS, encoding="utf-8") as f:
            doc = json.load(f)
        return {name: entry["paths"] for name, entry in doc["subsets"].items()}
    except (OSError, ValueError, KeyError, TypeError) as e:
        raise ShardPlanError(f"{REPO_SUBSETS}: cannot read the subset table: {e}")


def subset_flags(files):
    """The `subset_NAME` path filters: for each subset, whether a changed file belongs
    to it. A path that matches several subsets sets all of them (the union over the
    files), so a change touching, say, `Tests/` and `lib/` runs both the Lean build and
    every test shard.

    A changed file no subset claims (`scripts/`, `flake.*`, `selfhost/`, `examples/`,
    `infoview/`, ...) is a build input the table has not classified: it sets every
    subset, exactly as `changes --all` does, so a change can never skip the job that
    would have caught it. A `.github/` edit is in the `docs` subset for the cache-key
    table (`.github/**`), but it changes CI itself, so it also sets every subset; a
    workflow change must exercise every job, not just the docs ones."""
    table = repo_subsets()
    claimed = {f for f in files if any(matches(f, paths) for paths in table.values())}
    unclassified = [f for f in files if f not in claimed or matches(f, [".github/*"])]
    if unclassified:
        return {name: True for name in table}
    return {name: any(matches(f, paths) for f in files) for name, paths in table.items()}


def subset_key(args):
    """The Actions-cache key for one subset job (see the docstring at the top).

    `NAME` is a subset of `.github/repo-subsets.json`; `--with NAME` adds another
    subset the job's cache also reads (the test shards read `tests` and `wizlib`).
    `--scope S` is a correctness input that must match before a restore is offered
    (the driver's compiler key, the self-hosted program inputs); it is in both the
    key and the prefix. `--suffix S` is a content hash that belongs in the exact key
    but not in the restore prefix (the `**/*.wiz` tree the last run saw), so a changed
    file still restores the previous entry and the job overwrites it on success.

    Key:        subset-v1-<name>[-<name>…]-<os>-<arch>-<toolchain12>[-<scope>]-<sha12>[-<sha12>…][-<suffix>]
    Prefix:     subset-v1-<name>[-<name>…]-<os>-<arch>-<toolchain12>[-<scope>]-
    <sha12>     first 12 hex of the subset's `sha256` in .github/repo-subsets.json
    <toolchain12> first 12 hex of sha256(flake.lock + lean-toolchain)
    <os>/<arch> `RUNNER_OS`/`RUNNER_ARCH` (lowercased) under Actions, else uname.
    """
    names, scope, suffix = [], None, None
    it = iter(args)
    for a in it:
        if a == "--with":
            names.append(next(it))
        elif a == "--scope":
            scope = next(it)
        elif a == "--suffix":
            suffix = next(it)
        elif a.startswith("--"):
            raise SystemExit(f"subset-key: unknown option {a!r}")
        else:
            names.append(a)
    if not names:
        raise SystemExit("subset-key: a subset name is required")
    try:
        table = json.load(open(REPO_SUBSETS, encoding="utf-8"))["subsets"]
    except (OSError, ValueError, KeyError, TypeError) as e:
        raise SystemExit(f"{REPO_SUBSETS}: cannot read the subset table: {e}")
    for n in names:
        if n not in table:
            raise SystemExit(f"subset-key: {n!r} is not a subset of {REPO_SUBSETS}")
    try:
        toolchain = hashlib.sha256(
            open(os.path.join(ROOT, "flake.lock"), "rb").read()
            + b"\0"
            + open(os.path.join(ROOT, "lean-toolchain"), "rb").read()
        ).hexdigest()[:12]
    except OSError as e:
        raise SystemExit(f"subset-key: cannot hash the toolchain: {e}")
    osname = (os.environ.get("RUNNER_OS") or platform.system()).lower()
    arch = (os.environ.get("RUNNER_ARCH") or platform.machine()).lower()
    def sha(name):
        return table[name]["sha256"][:12]
    names_part = "-".join(names)
    shas = "-".join(sha(n) for n in names)
    head = f"subset-v1-{names_part}-{osname}-{arch}-{toolchain}"
    key = head
    prefix = head + "-"
    if scope:
        key += f"-{scope}"
        prefix += f"{scope}-"
    key += f"-{shas}"
    if suffix:
        key += f"-{suffix}"
    print(f"key={key}")
    print(f"prefix={prefix}")


def needed_shards(files):
    """The shards a change needs: all of them when a file of EVERYTHING changed; else a
    shard with "inputs" (globs; lib/ files among them bring the lib/ files they import)
    when one of its inputs changed, and a shard without "inputs" when anything but docs,
    scripts/attest or the STC metatheory (the `stc` job, not a shard) changed. Nothing
    for a docs/attest/STC-only change."""
    code = [f for f in files if not matches(f, DOCS + SELF_TESTED + STC)]
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
        print("stc=true")
        for name in repo_subsets():
            print(f"subset_{name}=true")
        print(f"shards={json.dumps(names)}")
        return 0
    base, head = args[0], (args[1] if len(args) > 1 else "HEAD")
    out = subprocess.run(["git", "diff", "--name-only", base, head], capture_output=True,
                         text=True, check=True, cwd=ROOT).stdout
    files = [f for f in out.split("\n") if f]
    names = needed_shards(files)
    code = is_code_change(files)
    docs = any(matches(f, DOCS) for f in files)
    web = any(matches(f, WEB) for f in files)
    stc = any(matches(f, STC) for f in files)
    subsets = subset_flags(files)
    print(f"code={'true' if code else 'false'}")
    print(f"docs={'true' if docs else 'false'}")
    print(f"web={'true' if web else 'false'}")
    print(f"stc={'true' if stc else 'false'}")
    for name in subsets:
        print(f"subset_{name}={'true' if subsets[name] else 'false'}")
    print(f"shards={json.dumps(names)}")
    print(f"{len(files)} files changed; code: {code}; docs: {docs}; web: {web}; "
          f"stc: {stc}; subsets: "
          f"{', '.join(n for n in subsets if subsets[n]) or 'none'}; "
          f"shards: {', '.join(names) or 'none'}", file=sys.stderr)
    return 0


GROUP = re.compile(r"^── (.*?) \((.*)\)$")
# a case line starts with its position in the run (`[n/failed/total] `, or `[n/total] ` in
# older logs; both accepted).  The trailing `(SECONDS s / limit N s)` is the harness's
# effective timeout (Tests/Harness.lean `renderResult`); `limit none` means no limit, and
# older logs have no ` / limit` at all.
POS = r"(?:\[\d+/(?:\d+/)?\d+\] )?"
LIMIT = r"(?: / limit (?:(?P<limit_s>\d+) s|(?P<limit_none>none)))?"
WHEN = rf"(?: \([\d.]+ s{LIMIT}\))?"
PASS = re.compile(rf"^{POS}  ✓ (.*?){WHEN}$")
FAIL = re.compile(rf"^{POS}  ✗ (.*?){WHEN}$")
SKIP = re.compile(rf"^{POS}  ⊘ (.*?){WHEN}$")
# the same line, with the elapsed time and the limit it ran under (`limit none`: none)
CASE_TIME = re.compile(rf"^{POS}  [✓✗⊘] (.*?) \(([\d.]+) s{LIMIT}\)$")
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
    factor, out, strict, jobs_json, paths = 1.5, None, False, None, []
    it = iter(args)
    for a in it:
        if a == "--factor":
            factor = float(next(it))
        elif a == "--baseline-out":
            out = next(it)
        elif a == "--jobs-json":
            jobs_json = next(it)
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
    # The rule is about wall time: CI's wall is its longest job, and a shard that runs
    # cases in parallel (`"jobs": N`) has a wall well below its summed case seconds. When
    # the run's job data is available, gate on each `tests --` step's wall and report the
    # case sums alongside; without it (an old artifact), fall back to the case sums.
    try:
        walls = {sh: w for sh, w in job_walls_of(jobs_json).items() if sh in totals} if jobs_json else {}
    except (OSError, ValueError, KeyError) as e:
        print(f"warning: no job walls from {jobs_json} ({e}); the gate falls back to case sums")
        walls = {}
    if walls:
        wranked = sorted(walls.items(), key=lambda kv: -kv[1])
        wt = sorted(walls.values())
        wmedian = (wt[(len(wt) - 1) // 2] + wt[len(wt) // 2]) / 2
        wlongest, wtop = wranked[0]
        if wmedian > 0 and wtop > factor * wmedian:
            problems.append(f"the longest shard {wlongest} ({wtop / 60:.1f} min of wall) is "
                            f"{wtop / wmedian:.1f}x the median job wall ({wmedian / 60:.1f} min), "
                            f"over the limit of {factor}x")
    else:
        if median > 0 and top > factor * median:
            problems.append(f"the longest shard {longest} ({top:.0f} s of tests) is {top / median:.1f}x the "
                            f"median shard ({median:.0f} s), over the limit of {factor}x")
    base = baseline()
    split = [s["name"] for s in shards() if s.get("split", 1) > 1]
    # a "split-cases" shard spreads its sibling cases over the parts on purpose, so its
    # parts each build the shared program: that is charged in the estimates, not drift
    rebuilt = {s["name"] for s in shards() if s.get("split-cases")}
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
        if len(parts) > 1 and n not in rebuilt:
            problems.append(f"the {res} is built by {len(parts)} parts of {n} ({', '.join(sorted(parts))}): "
                            f"its users are split, the baseline is stale")
    for p in problems:
        warn(p, "Shard balance")
    lines = ["### Shard balance", ""]
    if walls:
        spread = (f"✅ Balanced (job wall): the longest shard ({wlongest}, {wtop / 60:.1f} min) is "
                  f"{wtop / max(wmedian, 1e-9):.2f}x the median job wall ({wmedian / 60:.1f} min); "
                  f"limit {factor}x. Case sums: {top / max(median, 1e-9):.2f}x.")
    else:
        spread = (f"✅ Balanced: the longest shard ({longest}, {top:.0f} s) is "
                  f"{top / max(median, 1e-9):.2f}x the median ({median:.0f} s); limit {factor}x.")
    lines.append(("⚠️ **Out of balance**: " + "; ".join(problems) + ".") if problems else spread)
    if walls:
        lines += ["", "| shard | job wall (min) | × median wall | seconds of tests |", "|---|---:|---:|---:|"]
        lines += [f"| {md(sh)} | {w / 60:.1f} | {w / max(wmedian, 1e-9):.2f} | {totals.get(sh, 0):.0f} |"
                  for sh, w in wranked]
        missing = sorted(set(totals) - set(walls))
        if missing:
            lines += ["", f"No job wall (counted in no ratio): {', '.join(md(s) for s in missing)}."]
    else:
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


def allowlist(path=None, today=None):
    """The entries of .github/skip-allowlist.json that may skip in CI, each with the
    reason it may skip for, an owner and the one `case` it excuses, plus an `expires`
    date (YYYY-MM-DD). A malformed entry is an error: an allow-list without an owner is a
    place for skips to hide, one without a case excuses a whole group, and one without an
    expiry is never revisited (an expired entry has to be renewed with a new reason, as
    the flaky quarantine's do). The reason matches as a prefix of the skip's reason — a
    skip usually carries detail after the entry's words — but the case matches exactly."""
    path = path or SKIPS
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


def dead_allowlist_entries(allowed, binary):
    """[(entry, why)] for allow-list entries that no case matches: the group has no cases,
    or no case of it is named exactly `case`. A dead entry cannot fire — `allowed_entry`
    only consults entries when a skip happens — and it documents a parity gap that no
    longer exists; `check-shards` fails on one so the list cannot rot."""
    names = {}
    out = []
    for e in allowed:
        g = e["group"]
        if g not in names:
            names[g] = [n for _, _, n in list_cases(binary, [f"={g}"])]
        if not names[g]:
            out.append((e, f"the group {g!r} has no cases"))
        elif e["case"] not in names[g]:
            out.append((e, f"no case of {g!r} is named {e['case']!r}"))
    return out


def skip_records(paths):
    """{(shard, group, case): (skipped, reason, missing)} from `lake test` logs and
    `--timings` files (both describe the run: a log keeps the reason a case printed,
    including the old style; a `--timings` file the `skipped` note). A concrete reason
    wins over none; `missing` is whether the case's `--timings` notes say it was a
    missing dependency allowed by `--allow-missing-deps` (a log carries no notes, so the
    two files together are what tells the lint the whole story)."""
    recs = {}

    def put(key, skipped, why, missing=False):
        old = recs.get(key)
        if old is None:
            recs[key] = (skipped, why, missing)
        else:
            recs[key] = (old[0] or skipped,
                         old[1] if old[1] not in (None, NO_REASON) else why or old[1],
                         old[2] or missing)

    for p in paths:
        if p.endswith(".jsonl"):
            for r in read_timings([p]):
                notes = r.get("notes", [])
                why = next((n[len("skipped "):] for n in notes
                            if n.startswith("skipped ")), None)
                missing = any(n.startswith("missing-dep ") for n in notes)
                put((r["shard"], r["group"], r["case"]), why is not None, why, missing)
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
    a skip that names a tool the dev shell must provide is an error always; a skip that a
    `--allow-missing-deps` run recorded as a missing dependency is an error unless the
    allow-list names that case (the flag is not a place to hide an unexpected dependency);
    a GROUP's unexplained skipped ratio (over all its cases, in every shard) may not be
    over max_ratio. The ratio is per group, not per shard, so moving a group's cases
    between shards (a refreshed timings file) cannot flip it. Explained skips are
    reported."""
    shards_ = {}
    for (shard, group, case), (skipped, why, missing) in recs.items():
        shards_.setdefault(shard, {}).setdefault(group, []).append(
            (case, skipped, why if skipped else None, missing))

    def explained(group, case, why, missing):
        """None when the skip is explained, else (kind, text): 'tool' for a tool the CI
        dev shell must provide, 'missing' for a dependency the job allowed with
        `--allow-missing-deps` but did not name in the allow-list, 'unlisted' for a group,
        case or reason the allow-list lacks."""
        low = (why or "").lower()
        for pattern, tool in REQUIRED_TOOLS:
            # a clause of its own ("no node", "no iverilog, no yosys"), not a phrase in a
            # longer reason ("`lake` has no toolchain outside a checkout")
            if re.search(r"(?:^|, |; )" + re.escape(pattern), low):
                return ("tool", f"the dev shell must provide {tool} (`{why}`)")
        if missing:
            if allowed_entry(allowed, group, case, why) is not None:
                return None
            return ("missing", f"a missing dependency was reported as a skip (`{why}`), but "
                               f".github/skip-allowlist.json has no entry naming this case")
        if allowed_entry(allowed, group, case, why) is not None:
            return None
        return ("unlisted", f"`{why}`")

    errors, warnings, rows, details = [], [], [], []
    total = len(recs)
    skipped = sum(1 for s, _, _ in recs.values() if s)
    # what each skip is: an error (reported here), a warning (unexplained but tolerated,
    # counted by its group's ratio), or fine (allow-listed)
    verdicts = {}
    for shard in sorted(shards_):
        for group, cs in sorted(shards_[shard].items()):
            skipped_cases = [(c, w, m) for c, s, w, m in cs if s]
            whole = len(skipped_cases) == len(cs)
            by_why = {}
            for c, w, m in skipped_cases:
                v = explained(group, c, w, m)
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
                elif kind == "missing":
                    msg = (f"**{md(group)}**: {the} skipped in shard `{md(shard)}` — {v[1]}")
                    errors.append(msg)
                    details.append(f"- ❌ {msg}")
                    for c, _ in items:
                        verdicts[(shard, group, c)] = ("error", v[1])
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
    for (shard, group, case), (s, _, _) in recs.items():
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
        lines.append(f"✅ {skipped} of {total} cases skipped, each explained by "
                     f".github/skip-allowlist.json; a skipped case is not a pass.")
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
            for k, c in enumerate(cs, 1):
                pos = f"[{k}/{len(cs)}] "
                if isinstance(c, tuple):
                    out += [f"{pos}  ⊘ {c[0]} (0.010 s)", f"      skipped ({c[1]})"]
                else:
                    out.append(f"{pos}  ✓ {c} (0.010 s)")
            out.append(f"  ({g}: 0.010 s; cases 0.010 s)")
        return "\n".join(out) + "\n"

    def timing(shard, group, cases, missing=False):
        """[(case, skip reason or None)] as a --timings file. `missing`: add the
        `missing-dep` note a `--allow-missing-deps` run records."""
        return "".join(json.dumps({"shard": shard, "group": group, "index": i, "case": c,
                                   "seconds": 0.01, "ok": True,
                                   "notes": ([f"skipped {w}"] if w else []) +
                                            ([f"missing-dep {w}"] if w and missing else [])}) + "\n"
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
        ("--timings file", {"library-2.jsonl": timing("library-2", "wasm",
                                                      [(f"m{i}", "no node") for i in range(25)])}, 1, "node"),
        # `--allow-missing-deps` is not a place to hide an unexpected dependency: each
        # missing-dep skip needs an allow-list entry naming that case, while one that has
        # it (the hdl entry below) is explained.
        ("a flagged missing dependency with no allow-list entry",
         {"library-2.jsonl": timing("library-2", "wasm",
                                    [(f"m{i}", "no ssh-keygen") for i in range(3)], missing=True)}, 1,
         "no entry naming this case"),
        ("a flagged missing dependency that is allow-listed",
         {"library-1.jsonl": timing("library-1", "hdl", [("sim", "no iverilog")], missing=True)}, 0, None),
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
    more than once keeps its largest time, a build its largest. Every shard's cases are
    kept, not only the split ones: `plan` and `matrix` price every shard (a non-split
    shard has no balance constraint, but its entries are what the shard budget and the
    matrix order read, and an unsplit shard merged from parts keeps its prices)."""
    cases, builds = {}, {}
    for r in read_timings(paths):
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


def run_medians(paths, families=None):
    """Per-case and per-build medians over runs (one `--timings` file per run):
    ({(group, case): (seconds, own seconds, uses, shard)}, {program: seconds},
    {shard: seconds per run}, {shard: [(run, wall/case-sum ratio)]},
    {shard: wall seconds}). A case's `own` time leaves out the builds it did; a
    failed case counts only if no run passed it. `shard` is the job the case ran in
    last (its split shard's name for a part). `families` is the shard names whose
    `-N` parts are one shard in the current plan (default: the shards with "split" >
    1); a shard that ran as parts in the runs but is unsplit now (scaling after the
    merge) still gets one combined wall/case-sum ratio."""
    split = [s["name"] for s in shards() if s.get("split", 1) > 1]
    fam_names = split if families is None else families
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
            shard = split_of(r["shard"], fam_names) or r["shard"]
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
                f = fam.setdefault(split_of(job, fam_names) or job, [0.0, 0.0])
                f[0] += w
                f[1] += run_sums[job]
        for sh, (w, c) in fam.items():
            if c > 0:
                ratios.setdefault(sh, []).append((p, w / c))
    cases = {}
    for k, rs in seen.items():
        ok = [r for r in rs if r[0]] or rs
        cases[k] = (median([r[1] for r in ok]), median([r[2] for r in ok]),
                    max((r[3] for r in ok), key=len), ok[-1][4])
    return (cases, {r: median(ts) for r, ts in builds.items()},
            {sh: median(list(v.values())) for sh, v in totals.items()},
            {sh: v for sh, v in ratios.items()},
            {sh: median(v) for sh, v in walls.items() if sh not in split})


def timings_of(p):
    """A run's `--timings` file: P itself, or P/timings.jsonl (`fetch-runs`)."""
    return os.path.join(p, "timings.jsonl") if os.path.isdir(p) else p


def job_walls_of(path):
    """{job: seconds of its `tests -- …` step} from a jobs.json — the API's
    `{"jobs": [...]}`, either `fetch-runs`' saved response or the current run's — for the
    successful `test (...)` jobs."""
    from datetime import datetime
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


def job_walls(p):
    """{job: seconds of its `tests -- …` step} of the successful test jobs of a
    `fetch-runs` directory's jobs.json ({} without one)."""
    path = os.path.join(p, "jobs.json") if os.path.isdir(p) else None
    return job_walls_of(path) if path and os.path.exists(path) else {}


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
    jobs, assume, write, counts_only, binary, paths = None, None, False, False, DEFAULT_BIN, []
    it = iter(args)
    for a in it:
        if a == "--jobs":
            jobs = int(next(it))
        elif a == "--assume":
            assume = next(it)
        elif a == "--write":
            write = True
        elif a == "--counts-only":
            counts_only = True
        elif a == "--bin":
            binary = next(it)
        else:
            paths.append(a)
    if not paths:
        sys.exit("rebalance: no --timings files")
    config = shards()
    # every configured shard is a family: a shard that ran as parts in the runs (a
    # scaling-1/-2 pair, or an older split of the shard) gets one combined ratio, even
    # when it is unsplit now.
    cases, builds, shard_secs, ratios, walls = run_medians(
        paths, [s["name"] for s in config])
    split = {s["name"]: s for s in config if s.get("split", 1) > 1}
    # the current case list: the driver's, or the last run's. A driver copied back from
    # the build node may not run here (it binds that node's ELF interpreter): that is not
    # a reason to refuse, but say what list was used.
    usable = False
    if os.path.exists(binary):
        try:
            usable = subprocess.run([binary, "--list-shards"], capture_output=True, cwd=ROOT).returncode == 0
        except OSError:
            usable = False
    if usable:
        listed = {}
        for s in resolved(binary):
            for g, i, n in list_cases(binary, s["select"]):
                listed[(g, n)] = s["name"]
        source = binary
    else:
        if os.path.exists(binary):
            print(f"Note: {binary} does not run here; using the last run's case list.", file=sys.stderr)
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
    # the new baseline: every current shard's cases, not only the split ones (plan and
    # matrix price every shard, and an unsplit shard merged from parts keeps its prices)
    names = {s["name"] for s in config}
    base = {"cases": {}, "builds": {r: round(t, 3) for r, t in sorted(builds.items())}}
    for (g, n), sh in listed.items():
        if sh in names and (g, n) in cases:
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
    # A part's cost is its job wall, its case sum times the measured wall/case-sum ratio
    # (below 1 when "jobs" runs cases at once). The ratio comes from the most recent run
    # that recorded the shard: the matrix's `jobs` settings have changed over time, so an
    # older run's ratio (e.g. scaling before it ran 3 at once) mispredicts today's wall.
    # A shard with "jobs" but no split (scaling after the merge) still needs the ratio
    # for this planner: it has the run's real walls. The ratio is not written back to the
    # shard any more; `plan`/`matrix` simulate each part (`simulated_wall`).
    ratio = {s["name"]: (ratios[s["name"]][-1][1] if ratios.get(s["name"]) else 1.0)
             for s in config if s.get("jobs") or s["name"] in split}
    cost = lambda sh, p: part_cost(p, base["builds"]) * ratio[sh]
    unit = lambda sh: max((cost(sh, [it]) for it in items[sh]), default=0.0)
    # the jobs that cannot be split: the other shards. A shard with a measured wall is
    # that; a shard that ran as parts (`scaling-1`, `scaling-2`) but is unsplit now is
    # its combined case sum times its measured ratio, because the median of its parts'
    # walls would price the merged job as one of its parts.
    def family_secs(sh):
        parts = [t for j, t in shard_secs.items()
                 if re.fullmatch(re.escape(sh) + r"-\d+", j)]
        return sum(parts) if parts else shard_secs.get(sh, 0.0)
    fixed = {}
    for s in config:
        sh = s["name"]
        if sh in split:
            continue
        fixed[sh] = walls.get(sh, family_secs(sh) * ratio.get(sh, 1.0))
    floor = max(list(fixed.values()) + [unit(sh) for sh in split])
    budget = jobs if jobs is not None else len(fixed) + sum(s["split"] for s in split.values())
    # a "split-cases" shard's parts are cases, not clusters of cases that share programs
    # (the same rule `expanded` uses): otherwise a whole selfhost shard is one unit
    split_cases = {sh: bool(split[sh].get("split-cases")) for sh in split}
    plans = {}

    def parts_at(sh, n):
        if (sh, n) not in plans:
            plans[(sh, n)] = partition(items[sh], n, base["builds"], split_cases[sh])
        return plans[(sh, n)]

    counts = {sh: 1 for sh in split}
    parts = {sh: parts_at(sh, 1) for sh in split}
    longest = lambda sh: max(cost(sh, p) for p in parts[sh])
    # fill the budget: a part at a time to the longest part that still gets shorter (a
    # job that cannot be split, e.g. a single long case, is no reason to stop: the other
    # shards still get shorter and their spread smaller). Every (shard, count) plan is
    # computed once.
    while len(fixed) + sum(counts.values()) < budget:
        options = [(longest(sh), sh) for sh in split
                   if max(cost(sh, p) for p in parts_at(sh, counts[sh] + 1)) < longest(sh) - 1e-9]
        if not options:
            break
        _, sh = max(options)
        counts[sh] += 1
        parts[sh] = parts_at(sh, counts[sh])
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
    if any(ratios.values()):
        print("Wall/case-sum ratios (from each shard's most recent run): "
              + ", ".join(f"{sh} {r:.2f}" for sh, r in sorted(ratio.items())))
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
            ps = parts[sh] if cs[sh] == counts[sh] else parts_at(sh, cs[sh])
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
    print(f"Predicted job wall (s) per job, the current split counts: {spread(was)}")
    print(f"Predicted job wall (s) per job, the new split counts: {spread(now)}")
    print(f"Floor: {floor:.0f} s (the longest job or case that cannot be split)")
    print()
    print("| job | predicted wall s (current counts) | predicted wall s (new counts) |")
    print("|---|---:|---:|")
    for n in sorted(set(was) | set(now), key=lambda n: -max(was.get(n, 0), now.get(n, 0))):
        f = lambda d: f"{d[n]:.0f}" if n in d else ""
        print(f"| {md(n)} | {f(was)} | {f(now)} |")
    if write or counts_only:
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
        wrote = (os.path.relpath(TIMINGS, ROOT) + " and ") if write else ""
        print(f"Wrote {wrote}the split counts of {os.path.relpath(SHARDS, ROOT)}.")
    return 0


# --- The expression set Guard B selects from (`check-ci-shaped`) ---------------------

# A `lib.` call in ci.yml.  CI's seeded builds write it as `f.lib."$sys".selfhostWith`
# inside a shell string (so the quotes are backslash-escaped there) or as
# `lib.towerWith`; the call is the last dotted component, which skips the system part.
LIB_CALL = re.compile(
    r'\blib\.(?:\\?"[^"\\]*\\?"|[A-Za-z0-9_-]+)(?:\.(?:\\?"[^"\\]*\\?"|[A-Za-z0-9_-]+))*')
# A row of ci-shaped.nix: `"lib-<call>-<what>" = …;`
CI_SHAPED_ROW = re.compile(r'"lib-([A-Za-z0-9_-]+)"\s*=')
# the other scripts that call `flake.lib` (their rows are not stale in ci-shaped.nix)
OTHER_CALL_FILES = [os.path.join(ROOT, "scripts", "lake-cache.sh")]


def lib_calls(text):
    """The `lib.NAME` call names in a fragment of ci.yml, with their line numbers."""
    out = []
    for m in LIB_CALL.finditer(text):
        parts = [p.strip('\\"') for p in m.group(0).split(".")[1:]]
        if parts:
            out.append((text[:m.start()].count("\n") + 1, parts[-1]))
    return out


def ci_shaped_rows(text):
    """The `lib-<call>-<what>` row names of ci-shaped.nix (one row per CI call site)."""
    return [m.group(1) for m in CI_SHAPED_ROW.finditer(text)]


def check_ci_shaped(workflow=None, shaped=None):
    """Every `lib.` call in ci.yml has a row in ci-shaped.nix: the selector
    `scripts/touched-derivations.sh` evaluates what this file names, so a call site
    with no row would be invisible to it -- a silent hole, not a failure.
    A row whose call no checkout script calls is stale and warned about (not an error:
    `lib.withLakeCache` is scripts/lake-cache.sh's, `lib.empty-lake` is an argument and
    not a derivation, so neither needs a ci.yml row)."""
    workflow = workflow or WORKFLOW
    shaped = shaped or CI_SHAPED
    try:
        calls = lib_calls(open(workflow, encoding="utf-8").read())
    except OSError as e:
        error(f"cannot read {workflow}: {e}", "ci-shaped")
        return 1
    try:
        rows = ci_shaped_rows(open(shaped, encoding="utf-8").read())
    except OSError as e:
        error(f"cannot read {shaped}: {e}", "ci-shaped")
        return 1
    called = sorted({name for _, name in calls})
    missing = [name for name in called if not any(row.startswith(name + "-") for row in rows)]
    # The other call sites in this repo, so a row for one of them is not `stale`.
    known = set(called)
    for path in OTHER_CALL_FILES:
        try:
            known |= {name for _, name in lib_calls(open(path, encoding="utf-8").read())}
        except OSError:
            pass
    stale = [row for row in rows if not any(row.startswith(name + "-") for name in known)]
    for name in missing:
        where = ", ".join(f"ci.yml:{line}" for line, n in calls if n == name)
        error(f"the `lib.{name}` call at {where} has no row in .github/ci-shaped.nix;"
              f" add one (`\"lib-{name}-<what>\" = (lib.{name} …);`) or the touched-derivations"
              f" selector will never look at it", "ci-shaped")
    if stale:
        warn(f"ci-shaped.nix rows no call site names: {', '.join(stale)}", "ci-shaped")
    if not missing:
        print(f"ci-shaped: {len(called)} `lib.` call(s) in ci.yml, {len(rows)} row(s) in"
              f" .github/ci-shaped.nix — every call has a row")
    return 1 if missing else 0


def check_ci_shaped_self_test():
    """The rule on a synthetic pair of files: a row per call passes, a new call without
    one fails, and a row ci.yml no longer calls only warns."""
    import tempfile
    workflow = """.github/workflows/ci.yml synthetic
      - run: |
          expr="let f = builtins.getFlake \\"$PWD\\"; in f.lib.\\"$sys\\".selfhostWith { wiz = x; tests = y; }"
          other=$(nix build --expr "f.lib.\\"$sys\\".towerWith (builtins.storePath \\"$W\\")")
          nix build .\\#wiz
"""
    shaped_ok = """{ flake, system }:
  {
    "lib-selfhostWith-compiler" = (flake.lib.${system}.selfhostWith {}).compiler;
    "lib-towerWith-wiz" = flake.lib.${system}.towerWith flake.packages.${system}.wiz;
  }
"""
    shaped_new = """{ flake, system }:
  {
    "lib-selfhostWith-compiler" = (flake.lib.${system}.selfhostWith {}).compiler;
    "lib-towerWith-wiz" = flake.lib.${system}.towerWith flake.packages.${system}.wiz;
    "lib-withLakeCache-lake-seed" = 1;
  }
"""
    shaped_missing = """{ flake, system }:
  {
    "lib-selfhostWith-compiler" = (flake.lib.${system}.selfhostWith {}).compiler;
  }
"""
    cases = [
        ("both calls have a row", shaped_ok, 0),
        ("the withLakeCache row is extra, not an error", shaped_new, 0),
        ("a call with no row fails", shaped_missing, 1),
    ]
    with tempfile.TemporaryDirectory(prefix="ci-shaped-selftest-") as tmp:
        wf = os.path.join(tmp, "ci.yml")
        with open(wf, "w", encoding="utf-8") as f:
            f.write(workflow)
        for label, text, want in cases:
            path = os.path.join(tmp, "ci-shaped.nix")
            with open(path, "w", encoding="utf-8") as f:
                f.write(text)
            rc = check_ci_shaped(wf, path)
            if rc != want:
                print(f"ci-shaped self-test FAILED: {label}: exit {rc}, wanted {want}",
                      file=sys.stderr)
                return 1
            print(f"ci-shaped self-test ok: {label}")
    print("ci-shaped self-test passed")
    return 0


# --- Effective limits (`timings`) ---------------------------------------------------

def case_times(files):
    """[(shard, group, case, seconds, limit or None)] from `lake test` logs (the case
    line's `(12.3 s / limit 300 s)`) and `--timings` records ("limit", nullable)."""
    out = []
    for path in files:
        if path.endswith(".jsonl"):
            try:
                records = read_timings([path])
            except OSError as e:
                warn(f"cannot read {path}: {e}", "Test time limit")
                continue
            for r in records:
                limit = r.get("limit")
                out.append((r.get("shard", "") or "", r.get("group", ""), r.get("case", ""),
                            float(r.get("seconds") or 0), limit))
            continue
        group = ""
        try:
            text = open(path, encoding="utf-8", errors="replace").read()
        except OSError as e:
            warn(f"cannot read {path}: {e}", "Test time limit")
            continue
        for line in text.split("\n"):
            if m := GROUP.match(line):
                group = m.group(1)
            elif m := CASE_TIME.match(line):
                limit = int(m.group("limit_s")) if m.group("limit_s") else None
                out.append((os.path.basename(path), group, m.group(1),
                            float(m.group(2)), limit))
    return out


def timings(files, warn_ratio=0.8, max_ratio=None):
    """The effective timeout of every case, and a warning for each case that used more
    than `warn_ratio` of it.  `max_ratio` makes that a gate (exit 1).

    This is the anti-reflex half of Guard C: a timeout raised where it never takes
    effect (an option after the subcommand -- the hdl case, 9ee24e52b) leaves this
    ratio at 100 %, so the no-op is visible instead of looking like a fix."""
    rows = case_times(files)
    with_limit = [r for r in rows if r[4]]
    no_limit = [r for r in rows if not r[4]]
    if not rows:
        print("timings: no case lines with a time in these files")
        return 0
    hot = []
    for shard, group, case, seconds, limit in with_limit:
        ratio = seconds / limit if limit else 0.0
        if ratio >= warn_ratio:
            hot.append((ratio, shard, group, case, seconds, limit))
    hot.sort(reverse=True)
    for ratio, shard, group, case, seconds, limit in hot:
        msg = (f"{group}: {case}" if group else case) + (
            f" used {seconds:.1f} s of its {limit} s limit ({ratio * 100:.0f} %)")
        warn(msg, "Test time limit")
    print(f"timings: {len(rows)} case(s); {len(with_limit)} under a limit,"
          f" {len(no_limit)} without one; {len(hot)} at or over {warn_ratio * 100:.0f} %")
    if with_limit:
        print("| % of limit | seconds | limit | group | case |")
        print("|---:|---:|---:|---|---|")
        for shard, group, case, seconds, limit in sorted(
                with_limit, key=lambda r: -(r[3] / r[4]))[:25]:
            print(f"| {seconds / limit * 100:.0f} % | {seconds:.1f} | {limit}"
                  f" | {md(group)} | {md(case)} |")
    if no_limit:
        print(f"timings: {len(no_limit)} case(s) ran with no limit (pass `--test-timeout N` to"
              f" the driver); a timeout that never took effect cannot be seen for them")
    if max_ratio is not None:
        over = [(r, s, g, c, sec, lim) for r, s, g, c, sec, lim in hot if r > max_ratio]
        for ratio, _, group, case, seconds, limit in over:
            error(f"{group}: {case} used {seconds:.1f} s of its {limit} s limit"
                  f" ({ratio * 100:.0f} %, over the gate of {max_ratio * 100:.0f} %)",
                  "Test time limit")
        return 1 if over else 0
    return 0


def _main(args):
    if args[:2] == ["matrix", "--only"] and len(args) >= 3:
        matrix(args[3] if len(args) > 3 else DEFAULT_BIN, set(json.loads(args[2])))
        return 0
    if args[:1] == ["changes"] and len(args) >= 2:
        return changes(args[1:])
    if args[:1] == ["subset-key"]:
        subset_key(args[1:])
        return 0
    if args[:1] == ["plan"]:
        rest = args[1:]
        as_json = rest[:1] == ["--json"]
        if as_json:
            rest = rest[1:]
        return plan(rest[0] if rest else DEFAULT_BIN, as_json=as_json)
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
    if args[:2] == ["check-ci-shaped", "--self-test"]:
        return check_ci_shaped_self_test()
    if args[:1] == ["check-ci-shaped"]:
        rest = args[1:]
        if len(rest) > 2:
            print("usage: ci.py check-ci-shaped [CI_YML] [CI_SHAPED]", file=sys.stderr)
            return 2
        return check_ci_shaped(rest[0] if rest else None, rest[1] if len(rest) > 1 else None)
    if args[:1] == ["timings"]:
        rest, warn_ratio, max_ratio = args[1:], 0.8, None
        paths = []
        it = iter(rest)
        for a in it:
            if a == "--warn-ratio":
                warn_ratio = float(next(it))
            elif a == "--max-ratio":
                max_ratio = float(next(it))
            else:
                paths.append(a)
        return timings(paths, warn_ratio, max_ratio)
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


def main(args):
    """Run the command; a shard plan that is not total (`ShardPlanError`) is an error with
    its explanation, never a matrix with quietly missing cases."""
    try:
        return _main(args)
    except ShardPlanError as e:
        print(e, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
