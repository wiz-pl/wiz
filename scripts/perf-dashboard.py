#!/usr/bin/env python3
"""Performance dashboard for Wiz: perf-history.tsv -> one self-contained HTML page.

    perf-dashboard.py [--history TSV] [--timings FILE_OR_DIR]… [--commit SHA] [--at ISO]
                      [--repo DIR] [--out HTML | --html HTML] [--gap MINUTES]

Defaults: /workspace/wiz-tools/perf-history.tsv, /workspace/wiz-lang-solutions,
/workspace/wiz-notes/perf-dashboard.html, 90 minutes.

* `--timings` ingests CI `test-timings.jsonl` artifacts (what `lake test --timings`
  writes and `scripts/ci.py summary` reads: one JSON record per case with `shard`,
  `group`, `index`, `case`, `seconds`, `ok`, `notes`). A run is one file; a directory
  (e.g. a `gh run download -n test-timings` tree) is searched for `*.jsonl`. A run has
  no date or commit of its own: they come from a `<file>.meta.json` sidecar, the
  records' optional `date`/`commit` fields, a 7–40 digit hex commit in the file name,
  else `--commit`/`--at`, else the file's mtime and an empty commit. The dashboard adds a
  "CI test timings" section: a table of runs, per-group totals with their median over
  runs, the change from the previous run and a sparkline, and the slowest cases. Groups
  are the test driver's group names; a group's total is the sum of its passed cases'
  times (CI runs cases with `--jobs`, so that is test time, not wall time).

* Labels lose their @worktree suffix; rows with a non-zero exit are counted but left out
  of the statistics.
* Commits are ordered by `git log` of the repo (oldest first). A commit that is not in
  that history (a branch tip) is placed just after its merge base with HEAD and marked
  "branch". Titles come from the first-parent merge that brought the commit in
  ("PR #N: <first body line>"), else from the commit's own subject.
* Measurement windows are found from the timestamps: a gap of more than --gap minutes
  between consecutive measurements starts a new window (perf-history.tsv has no window
  column; windows are numbered W1, W2, ... in time order, which need not match the
  coordinator's numbering).
* A/B pairs: a window's rows of one label are split into experiments (interleaved rounds
  A,B,A,B,...: a new commit after the rounds have started begins the next experiment, so
  two unrelated pairs measured one after the other are not compared with each other).
  Within an experiment each commit B is compared with its nearest measured ancestor A (A
  is an ancestor of B and no other measured commit sits between them). Medians of the
  repeated runs; min/max as whiskers.

Pure standard library; the page has inline CSS/JS/SVG and loads nothing from the network.
The output is written atomically (temp file + rename), so it is safe to re-run.
"""
import argparse, csv, math, datetime as dt, html, json, os, re, statistics, subprocess, sys, tempfile

DESCR = {
    "stage1-selfcompile": "stage 1 (self-hosted compiler built by the Lean wiz build) compiling the whole toolchain (self.wiz) to C",
    "stage1-selfcompile-rc": "stage 1 in reference-counting mode",
    "stage2-mid": "stage 2 (stage 1's C + rt.c + Boehm) compiling mid.wiz (Lex+Parse+Kernel)",
    "stage2-full": "stage 2 compiling self.wiz (the fixpoint run)",
    "stage2-mid-rc": "stage 2, RC mode, compiling mid.wiz",
    "stage2-full-rc": "stage 2, RC mode, compiling self.wiz",
    "selfcheck": "self-hosted frontend (built by the Lean wiz build) checking Lex+Parse+Kernel+Frontend",
    "lean-elab-selfhost": "Lean `wiz check --no-cache` of the five selfhost files concatenated (inputs from each commit's own sources)",
    "lean-elab-examples": "Lean `wiz check --no-cache` of every examples/*.wiz, timed together",
    "lean-elab-lib": "Lean `wiz check --no-cache` of lib/*.wiz, timed together",
    "lib-check-all": "`wiz check --no-cache` of lib/*.wiz lib/*/*.wiz",
    "wiz-build-compiler": "`wiz build` of the self-hosted compiler source (compiler.wiz)",
    "suite": "lake test wall time (approximate, not exclusive)",
    "test[selfhost]": "lake test -- '=selfhost' wall time",
    "words": "words benchmark",
}

def git(repo, *args, check=True):
    r = subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError("git %s: %s" % (" ".join(args), r.stderr.strip()))
    return r

class Repo:
    def __init__(self, path):
        self.path = path
        order = git(path, "log", "--format=%H").stdout.split()
        order.reverse()
        self.index = {h: i for i, h in enumerate(order)}
        self.head = order[-1] if order else None
        fp = git(path, "log", "--first-parent", "--format=%H%x1f%s%x1f%b%x1e").stdout
        self.fp = []                                   # oldest first: (hash, subject, body)
        for rec in fp.split("\x1e"):
            rec = rec.strip("\n")
            if not rec: continue
            h, s, b = (rec.split("\x1f") + ["", ""])[:3]
            self.fp.append((h.strip(), s, b))
        self.fp.reverse()
        self._full, self._anc, self._info = {}, {}, {}

    def full(self, short):
        if short not in self._full:
            r = git(self.path, "rev-parse", "--verify", "-q", short + "^{commit}", check=False)
            self._full[short] = r.stdout.strip() or None
        return self._full[short]

    def is_anc(self, a, b):
        if a == b: return False
        k = (a, b)
        if k not in self._anc:
            fa, fb = self.full(a), self.full(b)
            self._anc[k] = bool(fa and fb) and git(self.path, "merge-base", "--is-ancestor", fa, fb, check=False).returncode == 0
        return self._anc[k]

    @staticmethod
    def pr_title(subject, body):
        m = re.match(r"Merge pull request #(\d+) from \S+?/(\S+)", subject)
        if not m: return None
        first = next((l.strip() for l in body.splitlines() if l.strip()), m.group(2))
        return "PR #%s: %s" % (m.group(1), first)

    def info(self, short):
        """(position, title, on_main) of a commit."""
        if short in self._info: return self._info[short]
        f = self.full(short)
        if f is None:
            res = (float("inf"), "(not in repository)", False)
        elif f in self.index:
            # earliest first-parent commit that contains f (ancestry is monotone along it)
            lo, hi = 0, len(self.fp) - 1
            while lo < hi:
                mid = (lo + hi) // 2
                h = self.fp[mid][0]
                if h == f or git(self.path, "merge-base", "--is-ancestor", f, h, check=False).returncode == 0:
                    hi = mid
                else:
                    lo = mid + 1
            h, s, b = self.fp[lo] if self.fp else (f, "", "")
            t = self.pr_title(s, b)
            if h == f:
                title = t or s
            else:
                own = git(self.path, "log", "-1", "--format=%s", f).stdout.strip()
                title = own + (" (in %s)" % t if t else "")
            res = (float(self.index[f]), title, True)
        else:
            mb = git(self.path, "merge-base", f, self.head, check=False).stdout.strip()
            pos = self.index.get(mb, -1) + 0.5
            own = git(self.path, "log", "-1", "--format=%s", f).stdout.strip()
            res = (pos, own, False)
        self._info[short] = res
        return res

def load(path):
    rows = []
    with open(path, newline="") as fh:
        for r in csv.reader(fh, delimiter="\t"):
            if len(r) < 6 or r[0] == "date": continue
            try:
                ts = dt.datetime.fromisoformat(r[0])
                rows.append(dict(ts=ts, commit=r[1], label=r[2].split("@")[0], wt=r[2].partition("@")[2],
                                 secs=float(r[3]), rss=int(r[4]), exit=int(r[5])))
            except ValueError:
                print("perf-dashboard: skipping bad row: %r" % (r,), file=sys.stderr)
    rows.sort(key=lambda r: r["ts"])
    return rows

def windows_of(rows, gap_min):
    ws = []
    for r in rows:
        if not ws or (r["ts"] - ws[-1][-1]["ts"]).total_seconds() > gap_min * 60:
            ws.append([])
        ws[-1].append(r)
    return ws

def stats(rs):
    ok = [r for r in rs if r["exit"] == 0]
    if not ok: return None
    s = [r["secs"] for r in ok]; m = [r["rss"] for r in ok]
    return dict(n=len(ok), bad=len(rs) - len(ok), t=statistics.median(s), tmin=min(s), tmax=max(s),
                m=statistics.median(m), mmin=min(m), mmax=max(m), last=max(r["ts"] for r in rs))

def pct(a, b): return (b - a) / a * 100 if a else 0.0

def experiments(rs):
    """Split one label's rows (time order) into experiments: interleaved rounds A,B,(C,)A,B,...
    A commit not seen yet starts a new experiment once the current one has two or more
    commits and one of them has come round again (the rounds have started)."""
    blocks, seen, rounds = [], set(), False
    for r in rs:
        c = r["commit"]
        if blocks and c not in seen and rounds:
            blocks.append([]); seen, rounds = set(), False
        if not blocks: blocks.append([])
        if c in seen and len(seen) >= 2: rounds = True
        seen.add(c); blocks[-1].append(r)
    return blocks

def comparisons(win, wi, repo):
    out = []
    by = {}
    for r in win: by.setdefault(r["label"], []).append(r)
    groups = []
    for label, rs in by.items():
        for blk in experiments(rs):
            cs = {}
            for r in blk: cs.setdefault(r["commit"], []).append(r)
            groups.append((label, cs))
    for label, cs in groups:
        st = {c: stats(rs) for c, rs in cs.items()}
        st = {c: s for c, s in st.items() if s}
        for b in st:
            ancs = [a for a in st if repo.is_anc(a, b)]
            near = [a for a in ancs if not any(repo.is_anc(a, c) and c != a for c in ancs)]
            for a in near:
                A, B = st[a], st[b]
                out.append(dict(win=wi, label=label, a=a, b=b, A=A, B=B, dt=pct(A["t"], B["t"]), dm=pct(A["m"], B["m"]),
                                overlap=not (B["tmin"] > A["tmax"] or B["tmax"] < A["tmin"])))
    out.sort(key=lambda c: (c["label"], repo.info(c["b"])[0]))
    return out

# ---------------------------------------------------------------- CI test timings

# A commit in an artifact's file name (`test-timings-deadbeef.jsonl`,
# `43522640423-2ebcfd13.jsonl`): 7 to 40 hex digits, not part of a longer word.
_HEX = re.compile(r"(?<![0-9a-fA-F])([0-9a-f]{7,40})(?![0-9a-fA-F])")

def expand_timings(paths):
    """The `*.jsonl` files of `--timings` arguments: a file as it is, a directory
    (recursively, e.g. a downloaded artifact tree) its `*.jsonl` files."""
    out = []
    for p in paths:
        if os.path.isdir(p):
            for root, dirs, files in os.walk(p):
                dirs.sort()
                out += [os.path.join(root, f) for f in sorted(files) if f.endswith(".jsonl")]
        else:
            out.append(p)
    return out

def load_timings(paths, commit=None, at=None):
    """CI runs from `test-timings.jsonl` files, oldest first. A run is a file: its
    timestamp and commit come from a `<name>.meta.json` sidecar, the records' own
    `date`/`commit` fields, a hex commit in the file name, `--commit`/`--at`, else the
    file's mtime and an empty commit."""
    runs = []
    for p in expand_timings(paths):
        recs = []
        with open(p, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line: continue
                try:
                    r = json.loads(line)
                except json.JSONDecodeError:
                    print("perf-dashboard: skipping bad timings line in %s" % p, file=sys.stderr)
                    continue
                if "seconds" not in r or "case" not in r:
                    print("perf-dashboard: skipping record without seconds/case in %s" % p, file=sys.stderr)
                    continue
                recs.append(r)
        if not recs: continue
        meta = {}
        side = os.path.splitext(p)[0] + ".meta.json"
        if os.path.exists(side):
            try:
                with open(side) as fh: meta = json.load(fh)
            except (OSError, json.JSONDecodeError) as e:
                print("perf-dashboard: %s: %s" % (side, e), file=sys.stderr)
        c = (meta.get("commit") or commit
             or next((r.get("commit") for r in recs if r.get("commit")), None))
        if not c:
            # a run downloaded to a directory named after its commit
            # (`gh run download -D eaf2119e`) or a file named after it
            parts, d = [os.path.basename(p)], os.path.dirname(os.path.abspath(p))
            while d and d != os.path.dirname(d):
                parts.append(os.path.basename(d)); d = os.path.dirname(d)
            for part in parts:
                m = _HEX.search(part)
                if m: c = m.group(1); break
        c = c or ""
        when = meta.get("date") or at or next((r.get("date") for r in recs if r.get("date")), None)
        if when:
            try: ts = dt.datetime.fromisoformat(when.replace("Z", "+00:00"))
            except ValueError:
                print("perf-dashboard: %s: not an ISO date: %r (using the file's mtime)" % (p, when), file=sys.stderr)
                ts = None
        else:
            ts = None
        if ts is None:
            ts = dt.datetime.fromtimestamp(os.path.getmtime(p)).astimezone()
        runs.append(dict(file=p, ts=ts, commit=c, cases=recs,
                         shards=sorted({str(r.get("shard", "")) for r in recs})))
    runs.sort(key=lambda r: (r["ts"], r["file"]))
    return runs

def ci_summary(runs):
    """Per group: one entry per run (time order) with its case count, failed count,
    total seconds of the passed cases and its slowest case; per case: its runs."""
    groups, cases = {}, {}
    for run in runs:
        by = {}
        for r in run["cases"]:
            g, n = str(r.get("group", "?")), str(r.get("case", "?"))
            by.setdefault(g, []).append(r)
            cases.setdefault((g, n), []).append(dict(ts=run["ts"], seconds=float(r["seconds"]),
                                                     ok=bool(r.get("ok")), shard=str(r.get("shard", ""))))
        for g, rs in by.items():
            ok = [r for r in rs if r.get("ok")]
            slow = max(ok, key=lambda r: float(r["seconds"]), default=None)
            groups.setdefault(g, []).append(dict(
                ts=run["ts"], commit=run["commit"], seconds=sum(float(r["seconds"]) for r in ok),
                cases=len(rs), failed=len(rs) - len(ok),
                slowest=(str(slow["case"]), float(slow["seconds"])) if slow else None))
    return groups, cases

def spark(values, w=96, h=22):
    """A tiny inline trend line (SVG, no assets): the last point in the series colour."""
    if not values:
        return '<span class="muted">—</span>'
    if len(values) == 1:
        return '<span class="muted sm">%s (1 run)</span>' % fmt_s(values[0])
    lo, hi = min(values), max(values)
    pad, pw, ph = 2.0, w - 4.0, h - 4.0
    xs = [pad + pw * i / (len(values) - 1) for i in range(len(values))]
    ys = [h - pad - ph * ((v - lo) / (hi - lo) if hi > lo else 0.5) for v in values]
    pts = " ".join("%.1f,%.1f" % (x, y) for x, y in zip(xs, ys))
    return ('<svg class="spark" viewBox="0 0 %d %d" role="img" aria-label="trend">'
            '<polyline points="%s"/><circle cx="%.1f" cy="%.1f" r="2.4"/></svg>'
            % (w, h, pts, xs[-1], ys[-1]))

def ci_table(runs, repo):
    """The CI runs: date, commit, shards, cases, failed and case time."""
    h = ['<div class="tw"><table><thead><tr><th>run</th><th>commit</th><th>shards</th>'
         '<th class="r">cases</th><th class="r">failed</th><th class="r">case time</th></tr></thead><tbody>']
    for run in reversed(runs):
        failed = sum(1 for r in run["cases"] if not r.get("ok"))
        total = sum(float(r["seconds"]) for r in run["cases"] if r.get("ok"))
        c = run["commit"]
        title, known = "", False
        if c:
            pos, t, known = repo.info(c)
            title = t if known else "(not in this repository)"
        h.append('<tr%s><td>%s</td><td>%s%s</td><td>%s</td><td class="r">%d</td>'
                 '<td class="r%s">%d</td><td class="r num">%s</td></tr>' % (
                     ' class="reg"' if failed else "",
                     esc(run["ts"].strftime("%Y-%m-%d %H:%M")),
                     ('<code title="%s">%s</code>' % (esc(title), esc(c))) if c else '<span class="muted">unknown</span>',
                     (' <span class="muted">%s</span>' % esc(title)) if title else "",
                     esc(", ".join(s for s in run["shards"] if s) or "—"),
                     len(run["cases"]), " hot" if failed else "", failed, fmt_s(total)))
    h.append("</tbody></table></div>")
    return "".join(h)

def ci_section(runs, repo):
    groups, cases = ci_summary(runs)
    latest = runs[-1]
    h = ['<h2 id="ci">CI test timings</h2>',
         '<p class="muted sm">From <code>test-timings.jsonl</code> artifacts (<code>lake test --timings</code>, '
         'the format <code>scripts/ci.py summary</code> reads): one record per case. %d run%s ingested, '
         'newest %s. A run\'s time is the sum of its passed cases: CI runs cases with <code>--jobs</code>, '
         'so this is test time, not wall time; compare groups over runs here, not runs on different runners.</p>'
         % (len(runs), "" if len(runs) == 1 else "s", esc(latest["ts"].strftime("%Y-%m-%d %H:%M")))]
    ok = [r for r in latest["cases"] if r.get("ok")]
    slowest = max(ok, key=lambda r: float(r["seconds"]), default=None)
    nshards = len([s for s in latest["shards"] if s])
    h.append('<div class="tiles">')
    h.append('<div class="tile"><div class="k">runs</div><div class="v">%d</div><div class="s">%d shard%s in the newest</div></div>'
             % (len(runs), nshards, "" if nshards == 1 else "s"))
    h.append('<div class="tile"><div class="k">cases</div><div class="v">%d</div><div class="s">%d failed in the newest run</div></div>'
             % (len(latest["cases"]), len(latest["cases"]) - len(ok)))
    h.append('<div class="tile"><div class="k">case time</div><div class="v">%s</div><div class="s">sum of the newest run\'s cases</div></div>'
             % fmt_s(sum(float(r["seconds"]) for r in ok)))
    if slowest:
        h.append('<div class="tile"><div class="k">slowest case</div><div class="v">%s</div><div class="s">%s · %s</div></div>'
                 % (fmt_s(float(slowest["seconds"])), esc(str(slowest.get("group", ""))), esc(str(slowest.get("case", "")))))
    h.append('</div>')
    h.append(ci_table(runs, repo))

    # per group: median of its runs, the change from the previous run, a sparkline
    rows = []
    for g, ss in groups.items():
        if not ss: continue
        tot = [s["seconds"] for s in ss]
        prev = tot[-2] if len(tot) > 1 else None
        delta = pct(prev, tot[-1]) if prev else None
        slow = max(((c, rs) for (gg, c), rs in cases.items() if gg == g),
                   key=lambda cr: statistics.median([r["seconds"] for r in cr[1] if r["ok"]] or [0]),
                   default=None)
        slow_med = statistics.median([r["seconds"] for r in slow[1] if r["ok"]]) if slow else None
        rows.append(dict(g=g, total=tot, med=statistics.median(tot), last=tot[-1], delta=delta,
                         cases=ss[-1]["cases"], failed=ss[-1]["failed"], slow=slow[0] if slow else None,
                         slow_med=slow_med))
    rows.sort(key=lambda r: -r["last"])
    h.append('<h3>Groups: median over runs, trend, slowest case</h3>')
    h.append('<p class="muted sm">A group\'s time is the sum of its cases; the median is over the runs ingested. '
             'The sparkline is the group\'s time per run (oldest left, newest right); Δ compares the newest run '
             'with the one before it. A failed case is counted but left out of the times.</p>')
    if not rows:
        h.append('<p class="muted">No passing cases in the runs.</p>')
    else:
        h.append('<div class="tw"><table><thead><tr><th>group</th><th class="r">cases</th>'
                 '<th class="r">median (runs)</th><th class="r">newest</th><th class="r">Δ previous</th>'
                 '<th>trend</th><th class="r">slowest case</th></tr></thead><tbody>')
        for r in rows:
            hot = r["delta"] is not None and r["delta"] >= 5
            h.append('<tr%s><td><a href="#ci-%s">%s</a></td><td class="r">%d%s</td>'
                     '<td class="r num">%s <span class="muted sm">(%d run%s)</span></td>'
                     '<td class="r num">%s</td><td class="r num%s">%s</td><td>%s</td>'
                     '<td class="r">%s%s</td></tr>' % (
                         ' class="reg"' if hot else "",
                         esc(slug(r["g"])), esc(r["g"]), r["cases"],
                         (' <span class="muted sm">%d failed</span>' % r["failed"]) if r["failed"] else "",
                         fmt_s(r["med"]), len(r["total"]), "" if len(r["total"]) == 1 else "s",
                         fmt_s(r["last"]),
                         " hot" if hot else "", fmt_p(r["delta"]) if r["delta"] is not None else '<span class="muted">—</span>',
                         spark(r["total"]),
                         esc(r["slow"] or "—"), (' <span class="muted">%s</span>' % fmt_s(r["slow_med"])) if r["slow_med"] else ""))
        h.append("</tbody></table></div>")

    # the slowest cases, by median over their runs
    allcases = []
    for (g, c), rs in cases.items():
        okrs = [r for r in rs if r["ok"]]
        if not okrs: continue
        allcases.append(dict(g=g, c=c, med=statistics.median([r["seconds"] for r in okrs]),
                             mx=max(r["seconds"] for r in okrs), n=len(okrs),
                             shard=okrs[-1]["shard"]))
    allcases.sort(key=lambda r: -r["med"])
    h.append('<h3>The %d slowest cases</h3>' % min(15, len(allcases)))
    h.append('<div class="tw"><table><thead><tr><th class="r">#</th><th>group</th><th>case</th>'
             '<th class="r">median</th><th class="r">max</th><th class="r">runs</th><th>shard</th></tr></thead><tbody>')
    for k, r in enumerate(allcases[:15], 1):
        h.append('<tr><td class="r muted">%d</td><td><a href="#ci-%s">%s</a></td><td><code>%s</code></td>'
                 '<td class="r num">%s</td><td class="r">%s</td><td class="r">%d</td><td class="muted">%s</td></tr>'
                 % (k, esc(slug(r["g"])), esc(r["g"]), esc(r["c"]), fmt_s(r["med"]), fmt_s(r["mx"]), r["n"], esc(r["shard"])))
    h.append("</tbody></table></div>")
    return "".join(h)

# ---------------------------------------------------------------- rendering

def fmt_s(x): return "%.0f s" % x if x >= 100 else ("%.1f s" % x if x >= 10 else "%.2f s" % x)
def fmt_m(kb):
    return "%.2f GB" % (kb / 1048576) if kb >= 1048576 else "%.0f MB" % (kb / 1024)
def fmt_p(p): return ("+" if p > 0 else "−" if p < 0 else "±") + "%.1f%%" % abs(p)
def esc(s): return html.escape(str(s), quote=True)
def wname(i, w): return "W%d" % (i + 1)
def wrange(w):
    a, b = w[0]["ts"], w[-1]["ts"]
    return "%s %s–%s" % (a.strftime("%Y-%m-%d"), a.strftime("%H:%M"), b.strftime("%H:%M") if a.date() == b.date() else b.strftime("%m-%d %H:%M"))

def nice_ticks(hi, n=4):
    if hi <= 0: return [0, 1]
    raw = hi / n
    mag = 10 ** math.floor(math.log10(raw))
    for step in (1, 2, 2.5, 5, 10):
        s = step * mag
        if hi / s <= n: break
    ticks = [0.0]
    while ticks[-1] < hi - 1e-9: ticks.append(ticks[-1] + s)
    return ticks

def chart(points, key, fmt, unit_div=1.0, unit=" s"):
    """points: list of dict(commit, title, main, s). Median dots + min/max whiskers, y from 0."""
    W, H, L, R, T, B = 480, 240, 50, 10, 10, 58
    k, kmin, kmax = key, key + "min", key + "max"
    hi = max(p["s"][kmax] for p in points) / unit_div
    ticks = nice_ticks(hi)
    top = ticks[-1]
    pw, ph = W - L - R, H - T - B
    n = len(points)
    xs = [L + pw * (i + 0.5) / n for i in range(n)]
    y = lambda v: T + ph - (v / unit_div) / top * ph
    o = ['<svg class="chart" viewBox="0 0 %d %d" role="img" preserveAspectRatio="xMidYMid meet">' % (W, H)]
    for t in ticks:
        yy = T + ph - t / top * ph
        o.append('<line class="grid" x1="%d" x2="%d" y1="%.1f" y2="%.1f"/>' % (L, W - R, yy, yy))
        lab = ("%g" % round(t, 2)) + unit
        o.append('<text class="tick" x="%d" y="%.1f" text-anchor="end" dy="0.32em">%s</text>' % (L - 6, yy, esc(lab)))
    o.append('<line class="axis" x1="%d" x2="%d" y1="%d" y2="%d"/>' % (L, W - R, T + ph, T + ph))
    step = max(1, (n + 9) // 10)                    # at most ~10 commit labels
    if n > 1:
        o.append('<polyline class="trend" points="%s"/>' % " ".join("%.1f,%.1f" % (xs[i], y(p["s"][k])) for i, p in enumerate(points)))
    for i, p in enumerate(points):
        s, x = p["s"], xs[i]
        tip = {"c": p["commit"], "t": p["title"], "b": not p["main"], "n": s["n"], "bad": s["bad"],
               "med": fmt(s[k]), "min": fmt(s[kmin]), "max": fmt(s[kmax])}
        o.append('<g class="pt" data-tip="%s">' % esc(json.dumps(tip)))
        o.append('<rect class="hit" x="%.1f" y="%d" width="%.1f" height="%d"/>' % (x - pw / n / 2, T, pw / n, ph))
        if s[kmax] > s[kmin]:
            o.append('<line class="wh" x1="%.1f" x2="%.1f" y1="%.1f" y2="%.1f"/>' % (x, x, y(s[kmin]), y(s[kmax])))
            for v in (s[kmin], s[kmax]):
                o.append('<line class="wh" x1="%.1f" x2="%.1f" y1="%.1f" y2="%.1f"/>' % (x - 5, x + 5, y(v), y(v)))
        o.append('<circle class="dot%s" cx="%.1f" cy="%.1f" r="5"/>' % (" br" if not p["main"] else "", x, y(s[k])))
        o.append('</g>')
        if i % step == 0 or i == n - 1:
            o.append('<text class="xl%s" transform="translate(%.1f,%d) rotate(-40)" text-anchor="end">%s</text>'
                     % (" br" if not p["main"] else "", x + 3, T + ph + 16, esc(p["commit"])))
    o.append("</svg>")
    return "".join(o)

def cmp_table(cs, wins, show_win=True):
    if not cs: return '<p class="muted">No A/B pairs (no two measured commits of one label where one is an ancestor of the other).</p>'
    h = ['<div class="tw"><table class="cmp"><thead><tr>']
    if show_win: h.append("<th>window</th>")
    h.append('<th>label</th><th class="r">Δ time</th><th class="r">Δ RSS</th><th>A → B</th>'
             '<th class="r">time (median, min–max)</th><th class="r">max RSS</th></tr></thead><tbody>')
    for c in cs:
        A, B = c["A"], c["B"]
        reg_t, reg_m, imp_t = c["dt"] >= 5, c["dm"] >= 5, c["dt"] <= -5
        h.append('<tr class="%s">' % ("reg" if (reg_t or reg_m) else ""))
        if show_win: h.append("<td>%s</td>" % esc(wname(c["win"], None)))
        h.append('<td><a href="#l-%s">%s</a></td>' % (esc(slug(c["label"])), esc(c["label"])))
        mark = ' <span class="badge bad" title="regression ≥ 5%">▲</span>' if reg_t else (' <span class="badge good" title="faster by ≥ 5%">▼</span>' if imp_t else "")
        note = '<div class="muted sm">ranges overlap</div>' if c["overlap"] and abs(c["dt"]) >= 5 else ""
        h.append('<td class="r num%s">%s%s%s</td>' % (" hot" if reg_t else " cool" if imp_t else "", fmt_p(c["dt"]), mark, note))
        h.append('<td class="r num%s">%s%s</td>' % (" hot" if reg_m else "", fmt_p(c["dm"]), ' <span class="badge bad" title="regression ≥ 5%">▲</span>' if reg_m else ""))
        h.append('<td><code title="%s">%s</code> <span class="muted">×%d</span> → <code title="%s">%s</code> <span class="muted">×%d</span></td>' % (
            esc(commit_title(c["a"])), esc(c["a"]), A["n"], esc(commit_title(c["b"])), esc(c["b"]), B["n"]))
        h.append('<td class="r">%s → %s<div class="muted sm">%s–%s / %s–%s</div></td>' % (
            fmt_s(A["t"]), fmt_s(B["t"]), fmt_s(A["tmin"]), fmt_s(A["tmax"]), fmt_s(B["tmin"]), fmt_s(B["tmax"])))
        h.append('<td class="r">%s → %s</td></tr>' % (fmt_m(A["m"]), fmt_m(B["m"])))
    h.append("</tbody></table></div>")
    return "".join(h)

def slug(s): return re.sub(r"[^A-Za-z0-9_-]", "_", s)
_TITLES = {}
def commit_title(c): return _TITLES.get(c, "")

CSS = r"""
:root{color-scheme:light;--bg:#f6f6f4;--surface:#fcfcfb;--border:#e2e1dc;--text:#0b0b0b;--text2:#52514e;--muted:#77756f;
--series:#2a78d6;--branch:#6250d6;--grid:#ebeae6;--axis:#b9b7b0;--bad:#c62f2e;--bad-bg:#fdecec;--good:#007a00;--good-bg:#e8f5e8;--row-bad:#fff3f2}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){color-scheme:dark;--bg:#111110;--surface:#1a1a19;--border:#2f2e2b;
--text:#f0efec;--text2:#c3c2b7;--muted:#97958c;--series:#3987e5;--branch:#9085e9;--grid:#262624;--axis:#4a4945;--bad:#ff7b7a;
--bad-bg:#3a1a1a;--good:#5cc95c;--good-bg:#173017;--row-bad:#2a1616}}
:root[data-theme="dark"]{color-scheme:dark;--bg:#111110;--surface:#1a1a19;--border:#2f2e2b;--text:#f0efec;--text2:#c3c2b7;--muted:#97958c;
--series:#3987e5;--branch:#9085e9;--grid:#262624;--axis:#4a4945;--bad:#ff7b7a;--bad-bg:#3a1a1a;--good:#5cc95c;--good-bg:#173017;--row-bad:#2a1616}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font:15px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif}
main{max-width:1100px;margin:0 auto;padding:20px 16px 60px}
h1{font-size:1.5rem;margin:0 0 4px}h2{font-size:1.2rem;margin:32px 0 10px}h3{font-size:1.02rem;margin:0}
a{color:var(--series)}code{font:0.88em ui-monospace,SFMono-Regular,Menlo,monospace}
.muted{color:var(--muted)}.sm{font-size:.8em}
.card{background:var(--surface);border:1px solid var(--border);border-radius:10px;padding:14px 16px;margin:12px 0}
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px;margin:12px 0}
.tile{background:var(--surface);border:1px solid var(--border);border-radius:10px;padding:10px 14px}
.tile .k{font-size:.8rem;color:var(--text2)}.tile .v{font-size:1.5rem;font-weight:600;font-variant-numeric:tabular-nums}
.tile .s{font-size:.8rem;color:var(--muted);overflow-wrap:anywhere}
.tw{overflow-x:auto;-webkit-overflow-scrolling:touch;border:1px solid var(--border);border-radius:10px;background:var(--surface)}
table{border-collapse:collapse;width:100%;font-size:.88rem}
th,td{padding:6px 10px;border-bottom:1px solid var(--border);text-align:left;vertical-align:top;white-space:nowrap}
th{color:var(--text2);font-weight:600;font-size:.8rem}
td.r,th.r{text-align:right}.num{font-variant-numeric:tabular-nums;font-weight:600}
tr.reg td{background:var(--row-bad)}
.hot{color:var(--bad)}.cool{color:var(--good)}
.badge{display:inline-block;font-size:.72rem;font-weight:600;padding:1px 6px;border-radius:99px;margin-left:4px}
.badge.bad{background:var(--bad-bg);color:var(--bad)}.badge.good{background:var(--good-bg);color:var(--good)}
.charts{display:grid;grid-template-columns:1fr 1fr;gap:12px}
@media (max-width:760px){.charts{grid-template-columns:1fr}}
.charts figure{margin:0}.charts figcaption{font-size:.8rem;color:var(--text2);margin-bottom:2px}
svg.chart{width:100%;height:auto;display:block;overflow:visible}
.grid{stroke:var(--grid);stroke-width:1}.axis{stroke:var(--axis);stroke-width:1}
.tick,.xl{fill:var(--muted);font-size:13px;font-family:ui-monospace,Menlo,monospace}.xl.br{fill:var(--branch)}
.trend{fill:none;stroke:var(--series);stroke-width:2;stroke-opacity:.35}
.wh{stroke:var(--text2);stroke-width:1.5}
.dot{fill:var(--series);stroke:var(--surface);stroke-width:2}.dot.br{fill:var(--branch)}
.hit{fill:transparent}.pt:hover .hit{fill:var(--grid);fill-opacity:.6}
.spark{width:96px;height:22px;display:inline-block;vertical-align:middle}
.spark polyline{fill:none;stroke:var(--series);stroke-width:1.6;stroke-opacity:.55}
.spark circle{fill:var(--series)}
.legend{display:flex;gap:14px;flex-wrap:wrap;font-size:.8rem;color:var(--text2);margin:6px 0}
.legend i{display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:5px;vertical-align:-1px}
details summary{cursor:pointer;color:var(--text2);font-size:.85rem;margin-top:8px}
#tip{position:fixed;pointer-events:none;z-index:9;max-width:min(340px,90vw);background:var(--surface);color:var(--text);
border:1px solid var(--border);border-radius:8px;padding:8px 10px;font-size:.82rem;box-shadow:0 4px 16px rgba(0,0,0,.18);display:none}
#tip b{font-variant-numeric:tabular-nums}
nav.toc{display:flex;flex-wrap:wrap;gap:6px}nav.toc a{font-size:.8rem;text-decoration:none;border:1px solid var(--border);
border-radius:99px;padding:2px 9px;background:var(--surface);color:var(--text2)}
.themebtn{float:right;font:inherit;font-size:.8rem;background:var(--surface);color:var(--text2);border:1px solid var(--border);border-radius:99px;padding:3px 10px;cursor:pointer}
"""

JS = r"""
(function(){
var tip=document.getElementById('tip');
function show(e,g){var d=JSON.parse(g.getAttribute('data-tip'));
 tip.innerHTML='<code>'+d.c+'</code>'+(d.b?' <span class="badge" style="color:var(--branch)">branch</span>':'')+
 '<div class="muted" style="margin:2px 0 6px">'+d.t.replace(/[&<>]/g,function(c){return {'&':'&amp;','<':'&lt;','>':'&gt;'}[c]})+'</div>'+
 'median <b>'+d.med+'</b> · min '+d.min+' · max '+d.max+'<br><span class="muted">'+d.n+' run'+(d.n>1?'s':'')+(d.bad?' ('+d.bad+' failed, excluded)':'')+'</span>';
 tip.style.display='block';move(e);}
function move(e){var x=e.clientX+14,y=e.clientY+14,w=tip.offsetWidth,h=tip.offsetHeight;
 if(x+w>innerWidth-8)x=Math.max(8,e.clientX-w-14); if(y+h>innerHeight-8)y=Math.max(8,e.clientY-h-14);
 tip.style.left=x+'px';tip.style.top=y+'px';}
document.querySelectorAll('.pt').forEach(function(g){
 g.addEventListener('mouseenter',function(e){show(e,g)});g.addEventListener('mousemove',move);
 g.addEventListener('mouseleave',function(){tip.style.display='none'});
 g.addEventListener('click',function(e){show(e,g)});});
document.addEventListener('scroll',function(){tip.style.display='none'},{passive:true});
var b=document.getElementById('theme');b.addEventListener('click',function(){var r=document.documentElement;
 var dark=r.getAttribute('data-theme')?r.getAttribute('data-theme')==='dark':matchMedia('(prefers-color-scheme: dark)').matches;
 r.setAttribute('data-theme',dark?'light':'dark');});
})();
"""

def render(rows, repo, gap, src, runs=None):
    runs = runs or []
    wins = windows_of(rows, gap)
    allc = []
    for i, w in enumerate(wins): allc += comparisons(w, i, repo)
    for r in rows: _TITLES[r["commit"]] = repo.info(r["commit"])[1]
    labels = {}
    for r in rows: labels.setdefault(r["label"], []).append(r)
    order = sorted(labels, key=lambda l: max(r["ts"] for r in labels[l]), reverse=True)

    o = ['<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">',
         '<title>Wiz Perf Dashboard</title><style>%s</style></head><body><main>' % CSS]
    o.append('<button class="themebtn" id="theme" type="button">light / dark</button>')
    o.append('<h1>Wiz performance</h1><p class="muted sm">Generated %s from <code>%s</code> (%d measurements, %d labels, %d windows, gap &gt; %g min splits windows). '
             'Commit order: <code>git log</code> of <code>%s</code>; <span style="color:var(--branch)">violet</span> = branch commit not on it (placed after its merge base).</p>'
             % (esc(dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M %Z")), esc(src), len(rows), len(labels), len(wins), gap, esc(repo.path)))
    if runs:
        o.append('<p class="muted sm">Also ingests <b>%d</b> CI <code>test-timings.jsonl</code> run%s (see <a href="#ci">CI test timings</a>).</p>'
                 % (len(runs), "" if len(runs) == 1 else "s"))

    # latest window
    if wins:
        li = len(wins) - 1; lw = wins[-1]
        lc = [c for c in allc if c["win"] == li]
        regs = sorted([c for c in lc if c["dt"] >= 5 or c["dm"] >= 5], key=lambda c: -max(c["dt"], c["dm"]))
        best = min(lc, key=lambda c: c["dt"], default=None)
        worst = max(lc, key=lambda c: c["dt"], default=None)
        commits = sorted({r["commit"] for r in lw}, key=lambda c: repo.info(c)[0])
        o.append('<h2>Latest window: %s <span class="muted" style="font-weight:400">%s</span></h2>' % (wname(li, lw), esc(wrange(lw))))
        o.append('<div class="tiles">')
        o.append('<div class="tile"><div class="k">measurements</div><div class="v">%d</div><div class="s">%d labels, %d commits</div></div>'
                 % (len(lw), len({r["label"] for r in lw}), len(commits)))
        o.append('<div class="tile"><div class="k">A/B pairs</div><div class="v">%d</div><div class="s">nearest measured ancestor</div></div>' % len(lc))
        o.append('<div class="tile"><div class="k">regressions ≥ 5%%</div><div class="v%s">%d</div><div class="s">time or RSS</div></div>'
                 % (" hot" if regs else "", len(regs)))
        if worst and worst["dt"] > 0:
            o.append('<div class="tile"><div class="k">largest slowdown</div><div class="v hot">%s</div><div class="s">%s · %s → %s</div></div>'
                     % (fmt_p(worst["dt"]), esc(worst["label"]), esc(worst["a"]), esc(worst["b"])))
        if best and best["dt"] < 0:
            o.append('<div class="tile"><div class="k">largest speed-up</div><div class="v cool">%s</div><div class="s">%s · %s → %s</div></div>'
                     % (fmt_p(best["dt"]), esc(best["label"]), esc(best["a"]), esc(best["b"])))
        o.append('</div>')
        o.append('<div class="card sm"><b>Commits in this window</b><ul style="margin:6px 0 0;padding-left:18px">')
        for c in commits:
            p, t, m = repo.info(c)
            o.append('<li><code>%s</code>%s %s</li>' % (esc(c), "" if m else ' <span class="badge" style="color:var(--branch)">branch</span>', esc(t)))
        o.append('</ul></div>')
        o.append('<p class="muted sm">Sorted by Δ time, largest slowdown first. ▲ = regression ≥ 5%, ▼ = faster by ≥ 5%; highlighted rows regress time or RSS by ≥ 5%.</p>')
        o.append(cmp_table(sorted(lc, key=lambda c: -max(c["dt"], c["dm"])), wins, show_win=False))

    # all windows
    o.append('<h2>A/B comparisons by window</h2><p class="muted sm">Each measured commit B against its nearest measured ancestor A in the same experiment (window, label, interleaved rounds). '
             'Medians of repeated runs; the small line under the time gives min–max of A / B. Rows with Δ ≥ +5% (time or RSS) are highlighted.</p>')
    for i in range(len(wins) - 1, -1, -1):
        cs = [c for c in allc if c["win"] == i]
        o.append('<details%s><summary><b>%s</b> %s · %d measurements · %d pairs%s</summary>' % (
            " open" if i == len(wins) - 2 else "", wname(i, wins[i]), esc(wrange(wins[i])), len(wins[i]), len(cs),
            ' · <span class="hot">%d ≥5%%</span>' % sum(1 for c in cs if c["dt"] >= 5 or c["dm"] >= 5) if any(c["dt"] >= 5 or c["dm"] >= 5 for c in cs) else ""))
        o.append(cmp_table(cs, wins, show_win=False) + "</details>")

    # CI test timings (test-timings.jsonl artifacts)
    if runs:
        o.append(ci_section(runs, repo))

    # per label
    o.append('<h2>Benchmarks across commits</h2>')
    o.append('<div class="legend"><span><i style="background:var(--series)"></i>median (commit on master history)</span>'
             '<span><i style="background:var(--branch)"></i>median (branch commit)</span><span>│ whisker: min–max of repeated runs</span>'
             '<span>hover or tap a point for details</span></div>')
    o.append('<nav class="toc">%s</nav>' % "".join('<a href="#l-%s">%s</a>' % (esc(slug(l)), esc(l)) for l in order))
    for l in order:
        rs = labels[l]
        bycommit = {}
        for r in rs: bycommit.setdefault(r["commit"], []).append(r)
        pts = []
        for c, crs in bycommit.items():
            s = stats(crs)
            if not s: continue
            pos, title, main = repo.info(c)
            pts.append(dict(commit=c, title=title, main=main, s=s, pos=pos))
        pts.sort(key=lambda p: (p["pos"], p["s"]["last"]))
        bad = sum(1 for r in rs if r["exit"] != 0)
        o.append('<section class="card" id="l-%s"><h3>%s</h3><div class="muted sm">%s%d runs on %d commits, last %s%s</div>' % (
            esc(slug(l)), esc(l), esc(DESCR[l]) + " · " if l in DESCR else "", len(rs), len(bycommit),
            esc(max(r["ts"] for r in rs).strftime("%Y-%m-%d %H:%M")), " · %d failed runs excluded" % bad if bad else ""))
        if pts:
            o.append('<div class="charts"><figure><figcaption>wall time (s)</figcaption>%s</figure><figure><figcaption>max RSS</figcaption>%s</figure></div>'
                     % (chart(pts, "t", fmt_s), chart(pts, "m", fmt_m, *((1048576.0, " GB") if max(p["s"]["mmax"] for p in pts) >= 1048576 else (1024.0, " MB")))))
        o.append('<details><summary>table</summary><div class="tw"><table><thead><tr><th>commit</th><th>title</th><th class="r">runs</th>'
                 '<th class="r">median</th><th class="r">min–max</th><th class="r">RSS median</th><th class="r">RSS min–max</th></tr></thead><tbody>')
        for p in pts:
            s = p["s"]
            o.append('<tr><td><code>%s</code></td><td style="white-space:normal;min-width:200px">%s%s</td><td class="r">%d</td><td class="r num">%s</td>'
                     '<td class="r">%s–%s</td><td class="r num">%s</td><td class="r">%s–%s</td></tr>' % (
                         esc(p["commit"]), "" if p["main"] else '<span class="badge" style="color:var(--branch)">branch</span> ', esc(p["title"]),
                         s["n"], fmt_s(s["t"]), fmt_s(s["tmin"]), fmt_s(s["tmax"]), fmt_m(s["m"]), fmt_m(s["mmin"]), fmt_m(s["mmax"])))
        o.append('</tbody></table></div></details></section>')
    o.append('<p class="muted sm">Regenerate: <code>python3 /workspace/wiz-tools/perf-dashboard.py</code> (see /workspace/wiz-notes/perf-queue.md).</p>')
    o.append('</main><div id="tip"></div><script>%s</script></body></html>' % JS)
    return "".join(o)

def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--history", default="/workspace/wiz-tools/perf-history.tsv")
    ap.add_argument("--timings", action="append", default=[], metavar="FILE_OR_DIR",
                    help="a CI test-timings.jsonl artifact (or a directory of them); repeatable")
    ap.add_argument("--commit", default=None, help="the commit of the --timings runs, if their files don't say")
    ap.add_argument("--at", default=None, help="the ISO date of the --timings runs, if their files don't say")
    ap.add_argument("--repo", default="/workspace/wiz-lang-solutions")
    ap.add_argument("--out", "--html", dest="out", default="/workspace/wiz-notes/perf-dashboard.html",
                    help="the HTML file to write (--html is a synonym)")
    ap.add_argument("--gap", type=float, default=90, help="minutes between measurements that start a new window (default 90)")
    a = ap.parse_args()
    rows = load(a.history)
    repo = Repo(a.repo)
    runs = load_timings(a.timings, a.commit, a.at) if a.timings else []
    page = render(rows, repo, a.gap, a.history, runs)
    d = os.path.dirname(os.path.abspath(a.out))
    fd, tmp = tempfile.mkstemp(dir=d, prefix=".perf-dashboard.", suffix=".html")
    with os.fdopen(fd, "w") as fh: fh.write(page)
    os.chmod(tmp, 0o644)
    os.replace(tmp, a.out)
    extra = "" if not runs else (", %d CI run%s" % (len(runs), "" if len(runs) == 1 else "s"))
    print("perf-dashboard: wrote %s (%d measurements%s, %d bytes)" % (a.out, len(rows), extra, len(page)))

if __name__ == "__main__":
    main()
