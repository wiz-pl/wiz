#!/usr/bin/env python3
"""Measure flaky tests, rerun failures, and keep a quarantine that expires.

CI's test driver (``.lake/build/bin/tests``) runs every case in its own process and
prints a line per case.  A failure is therefore indistinguishable from a flake unless
the case is run again.  This tool does that rerun and classifies each case:

  always pass          every attempt passed (but a case that failed in the source run
                       and passes every rerun is flaky: it did fail, the failure did not
                       reproduce)
  deterministic fail   no attempt passed
  flaky                at least one pass and one fail
  always skip          every attempt was skipped (a skip is not a pass)
  incomplete           the rerun budget ran out before the case was measured

The attempts use a seed matrix (``--seeds`` or ``--seed-base``/``--repeats``).  A seed
selects the repetition and the shuffled predecessor for the order check; it is also
exported as ``FLAKY_SEED`` to the case's process (the driver does not read it today, but
a future case can).  The driver has no JUnit output, so a prior failing run is read from
its stdout (``--from-log``) or from its ``--timings`` JSONL (``--from-timings``); a
generic JUnit file is also accepted when one was produced elsewhere (``--from-junit``).

Order dependence: a failing (or previously failing) case is run alone, then again in a
suite run after a shuffled predecessor (from the same group by default; see
``--predecessor-scope``).  If it passes alone but fails in sequence, it is reported (and
classified) as flaky with ``order.order_dependent``.

Quarantine: ``.github/flaky-quarantine.json`` lists known flakes with a fixed expiry
date.  An entry is data only; it does not stop the rerun.  When the expiry date arrives
the quarantine check fails CI, so a flake cannot be parked forever.

Usage
  scripts/flaky.py '=rig' '=toolchain'           rerun the selected cases five times
  scripts/flaky.py --from-log logs/*.log         rerun the cases a failed run reported
  scripts/flaky.py --from-timings t.jsonl        ... from the driver's timings
  scripts/flaky.py --shard library --repeats 10  rerun a CI shard's cases
  scripts/flaky.py --check-quarantine            fail if an entry has expired
  scripts/flaky.py --self-test                   test the classifier on fixtures
  scripts/flaky.py --report f.json --json        machine-readable report
  scripts/flaky.py --from-log f.log --summary-md s.md --label shard
                                                a Markdown summary for CI

The tool is cheap enough to run under ``heavy --mem 2G``; ``--budget`` (default 600 s)
caps the total wall time.  Exit status: 0 clean (or only active quarantines), 1 a
deterministic failure, an incomplete measurement, a source failure that only skips, or
an expired quarantine, 2 usage or input error, 3 a flaky case that is not quarantined,
4 the budget ran out before the measurement finished.

Classifier details
  * A skip is not a pass.  It is counted apart; only a pass counts for ``passes``.
  * ``deterministic fail`` means at least one attempt failed and none passed.  A
    mixture of failure and skip is still a deterministic failure.
  * A timeout or a driver error is never a pass.  A timeout beside a pass makes the case
    ``flaky``; timeouts alone, or a mixture of passes and skips, are ``incomplete``
    (there is not enough evidence to call the case either way).
  * ``flaky`` is a measurement, not a verdict about the code.  Quarantine it with an
    expiry and a reason, or fix it.
"""

from __future__ import annotations

import argparse
import contextlib
import datetime as dt
import io
import json
import os
import random
import re
import subprocess
import sys
import tempfile
import time
import zlib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DRIVER = ROOT / ".lake/build/bin/tests"
DEFAULT_QUARANTINE = ROOT / ".github" / "flaky-quarantine.json"
DEFAULT_BUDGET = 600.0
DEFAULT_REPEATS = 5
DEFAULT_TIMEOUT = 600.0
SEED_ENV = "FLAKY_SEED"
TOOL_NAME = "wiz-flaky"
TOOL_VERSION = 1


class FlakyError(Exception):
    """A usage or input error (exit 2)."""


class BudgetExceeded(Exception):
    """The rerun budget ran out."""


@dataclass(frozen=True)
class CaseId:
    group: str
    index: int
    name: str

    @property
    def key(self) -> tuple[str, int]:
        return (self.group, self.index)

    @property
    def label(self) -> str:
        return f"{self.group} #{self.index} {self.name}"


@dataclass
class Attempt:
    seed: int
    mode: str  # "alone" or "sequence"
    status: str  # pass, fail, skip, error, timeout
    seconds: float
    exit: int | None = None
    detail: str = ""
    predecessor: str | None = None
    target_seconds: float | None = None

    def as_json(self) -> dict:
        out = {
            "seed": self.seed,
            "mode": self.mode,
            "status": self.status,
            "seconds": round(self.seconds, 3),
        }
        if self.target_seconds is not None:
            out["target_seconds"] = round(self.target_seconds, 3)
        if self.exit is not None:
            out["exit"] = self.exit
        if self.predecessor:
            out["predecessor"] = self.predecessor
        if self.detail:
            out["detail"] = self.detail
        return out


@dataclass
class QuarantineEntry:
    group: str
    case: str
    expires: dt.date
    reason: str = ""
    owner: str = ""
    issue: str = ""
    index: int | None = None

    def as_json(self) -> dict:
        out = {
            "group": self.group,
            "case": self.case,
            "expires": self.expires.isoformat(),
        }
        if self.index is not None:
            out["index"] = self.index
        if self.reason:
            out["reason"] = self.reason
        if self.owner:
            out["owner"] = self.owner
        if self.issue:
            out["issue"] = self.issue
        return out

    def label(self) -> str:
        ix = f" #{self.index}" if self.index is not None else ""
        return f"{self.group}{ix} {self.case}"


@dataclass
class Quarantine:
    file: Path | None = None
    entries: list[QuarantineEntry] = field(default_factory=list)
    expired: list[QuarantineEntry] = field(default_factory=list)
    expiring: list[QuarantineEntry] = field(default_factory=list)

    def match(self, case: CaseId) -> QuarantineEntry | None:
        for e in self.entries:
            if e.group != case.group or e.case != case.name:
                continue
            if e.index is None or e.index == case.index:
                return e
        return None


@dataclass
class Budget:
    limit: float | None
    start: float = field(default_factory=time.monotonic)
    runs: int = 0
    target_runs: int = 0
    case_seconds: float = 0.0

    @property
    def elapsed(self) -> float:
        return time.monotonic() - self.start

    @property
    def remaining(self) -> float | None:
        if self.limit is None:
            return None
        return self.limit - self.elapsed

    def check(self) -> None:
        left = self.remaining
        if left is not None and left <= 0.05:
            raise BudgetExceeded

    def timeout(self, want: float) -> float:
        self.check()
        left = self.remaining
        if left is None:
            return want
        return min(want, max(0.05, left))

    def note(self, seconds: float, target: bool) -> None:
        self.runs += 1
        if target:
            self.target_runs += 1
        self.case_seconds += max(0.0, seconds)


# ---------------------------------------------------------------------------
# Driver and case discovery


def driver_ok(driver: Path) -> bool:
    return driver.is_file() and os.access(driver, os.X_OK)


def _driver_run(
    driver: Path, args: list[str], driver_args: Iterable[str] = ()
) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            [str(driver), *driver_args, *args],
            cwd=ROOT,
            text=True,
            errors="replace",
            capture_output=True,
        )
    except FileNotFoundError as e:
        raise FlakyError(
            f"the test driver {driver} does not exist; build it with `lake build wiz tests`"
        ) from e


def list_cases(
    driver: Path, selectors: Iterable[str] = (), driver_args: Iterable[str] = ()
) -> list[CaseId]:
    """The cases the driver's selectors pick, in the driver's execution order."""
    p = _driver_run(driver, ["--list-cases", *selectors], driver_args)
    if p.returncode != 0:
        msg = (p.stderr or p.stdout).strip()
        raise FlakyError(f"`{driver} --list-cases {' '.join(selectors)}` failed: {msg}")
    out: list[CaseId] = []
    for line in p.stdout.splitlines():
        parts = line.split("\t", 2)
        if len(parts) != 3:
            continue
        group, index, name = parts
        try:
            i = int(index)
        except ValueError:
            continue
        out.append(CaseId(group, i, name))
    return out


def selectors_from_shard(name: str) -> list[str]:
    path = ROOT / ".github" / "test-shards.json"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as e:
        raise FlakyError(f"{path} does not exist") from e
    except json.JSONDecodeError as e:
        raise FlakyError(f"{path}: {e}") from e
    for shard in data:
        if shard.get("name") == name:
            return list(shard.get("select", []))
    names = ", ".join(s.get("name", "?") for s in data)
    raise FlakyError(f"no shard named {name!r} in {path}; shards: {names}")


# ---------------------------------------------------------------------------
# Prior failing runs


GROUP_RE = re.compile(r"^── (.*) \((.*)\)$")
FAIL_RE = re.compile(r"^  ✗ (.*?)(?: \([\d.]+ s\))?$")
RUN_RESULT_RE = re.compile(r"^(.*) #(\d+): (FAILED|SKIPPED.*)$")


def _case_maps(
    driver: Path, driver_args: Iterable[str] = ()
) -> tuple[dict[tuple[str, str], CaseId], dict[tuple[str, int], CaseId]]:
    all_cases = list_cases(driver, driver_args=driver_args)
    by_name: dict[tuple[str, str], CaseId] = {}
    by_index: dict[tuple[str, int], CaseId] = {}
    for c in all_cases:
        by_name.setdefault((c.group, c.name), c)
        by_index[(c.group, c.index)] = c
    return by_name, by_index


def cases_from_logs(
    driver: Path, paths: Iterable[Path], driver_args: Iterable[str] = ()
) -> list[CaseId]:
    """Failing cases in test-driver logs (the CI ``*.log`` artifacts)."""
    by_name, by_index = _case_maps(driver, driver_args)
    found: list[CaseId] = []
    for path in paths:
        try:
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError as e:
            raise FlakyError(f"cannot read {path}: {e}") from e
        group = None
        for line in lines:
            m = GROUP_RE.match(line)
            if m:
                group = m.group(1)
                continue
            if group is None:
                continue
            m = RUN_RESULT_RE.match(line)
            if m:
                g, index = m.group(1), int(m.group(2))
                c = by_index.get((g, index))
                if c is not None:
                    found.append(c)
                continue
            m = FAIL_RE.match(line)
            if m:
                name = m.group(1)
                c = by_name.get((group, name))
                if c is None:
                    # A group header may have been printed more than once (a rerun);
                    # try the case name in any group as a last resort.
                    matches = [x for (g, n), x in by_name.items() if n == name]
                    if len(matches) == 1:
                        c = matches[0]
                if c is not None:
                    found.append(c)
    return _dedupe(found)


def cases_from_timings(
    driver: Path, paths: Iterable[Path], driver_args: Iterable[str] = ()
) -> list[CaseId]:
    """Failing cases in the driver's ``--timings`` JSONL."""
    by_name, by_index = _case_maps(driver, driver_args)
    found: list[CaseId] = []
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError as e:
            raise FlakyError(f"cannot read {path}: {e}") from e
        for line in text.splitlines():
            if not line.strip():
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            if rec.get("ok", True):
                continue
            try:
                index = int(rec.get("index", -1))
            except (TypeError, ValueError):
                index = -1
            c = by_index.get((str(rec.get("group", "")), index))
            if c is None:
                c = by_name.get((str(rec.get("group", "")), str(rec.get("case", ""))))
            if c is not None:
                found.append(c)
    return _dedupe(found)


def cases_from_junit(
    driver: Path, paths: Iterable[Path], driver_args: Iterable[str] = ()
) -> list[CaseId]:
    """Failing cases in a JUnit XML file, when one was produced by another tool.

    The Wiz test driver itself emits no JUnit; ``--from-log``/``--from-timings`` are the
    native inputs.  This parser accepts the usual ``<testcase classname=... name=...>``
    with a ``<failure>`` or ``<error>`` child.
    """
    import xml.etree.ElementTree as ET

    by_name, by_index = _case_maps(driver, driver_args)
    found: list[CaseId] = []
    for path in paths:
        try:
            root = ET.parse(path).getroot()
        except (OSError, ET.ParseError) as e:
            raise FlakyError(f"cannot read JUnit {path}: {e}") from e
        for tc in root.iter("testcase"):
            if tc.find("failure") is None and tc.find("error") is None:
                continue
            name = tc.get("name", "")
            cls = tc.get("classname", "") or tc.get("class", "")
            candidates: list[CaseId] = []
            for (g, n), c in by_name.items():
                if n != name:
                    continue
                if not cls or cls == g or cls.endswith("." + g) or cls.endswith("/" + g):
                    candidates.append(c)
            if len(candidates) == 1:
                found.append(candidates[0])
                continue
            # A classname may be a suite name; a unique case name is still usable.
            matches = [c for (g, n), c in by_name.items() if n == name]
            if len(matches) == 1:
                found.append(matches[0])
            else:
                print(
                    f"flaky: warning: cannot map JUnit testcase {cls + '/' if cls else ''}{name!r} "
                    f"to a driver case ({len(matches)} matches); skipped",
                    file=sys.stderr,
                )
    return _dedupe(found)


def _flatten(groups: Iterable[Iterable[Path]]) -> list[Path]:
    return [p for group in groups for p in group]


def _dedupe(cases: Iterable[CaseId]) -> list[CaseId]:
    seen = set()
    out = []
    for c in cases:
        if c.key in seen:
            continue
        seen.add(c.key)
        out.append(c)
    return out


# ---------------------------------------------------------------------------
# Running one case (alone, or after a predecessor)


def _last_detail(stdout: str, stderr: str) -> str:
    text = (stderr + "\n" + stdout).strip()
    if not text:
        return ""
    lines = [l.rstrip() for l in text.splitlines() if l.strip()]
    out = "\n".join(lines[-8:])
    if len(out) > 900:
        out = "…" + out[-900:]
    return out


def _status_from_exit(code: int) -> str:
    if code == 0:
        return "pass"
    if code == 3:
        return "skip"
    if code == 1:
        return "fail"
    return "error"


def run_alone(
    driver: Path,
    case: CaseId,
    seed: int,
    budget: Budget,
    timeout: float,
    driver_args: Iterable[str] = (),
) -> Attempt:
    budget.check()
    env = os.environ.copy()
    env[SEED_ENV] = str(seed)
    start = time.monotonic()
    try:
        p = subprocess.run(
            [str(driver), *driver_args, "--run", case.group, str(case.index)],
            cwd=ROOT,
            text=True,
            errors="replace",
            capture_output=True,
            timeout=budget.timeout(timeout),
            env=env,
        )
        seconds = time.monotonic() - start
        status = _status_from_exit(p.returncode)
        detail = "" if status == "pass" else _last_detail(p.stdout, p.stderr)
        budget.note(seconds, target=True)
        return Attempt(seed, "alone", status, seconds, p.returncode, detail)
    except subprocess.TimeoutExpired:
        seconds = time.monotonic() - start
        budget.note(seconds, target=True)
        budget.check()
        return Attempt(
            seed,
            "alone",
            "timeout",
            seconds,
            None,
            f"timed out after {seconds:.1f} s",
        )
    except OSError as e:
        seconds = time.monotonic() - start
        budget.note(seconds, target=True)
        return Attempt(seed, "alone", "error", seconds, None, str(e))


def run_sequence(
    driver: Path,
    target: CaseId,
    predecessor: CaseId,
    seed: int,
    budget: Budget,
    timeout: float,
    driver_args: Iterable[str] = (),
) -> Attempt:
    """Run `predecessor` and `target` in one driver process, in that order."""
    budget.check()
    if predecessor.group == target.group:
        selectors = [f"={target.group}#{predecessor.index},{target.index}"]
    else:
        selectors = [
            f"={predecessor.group}#{predecessor.index}",
            f"={target.group}#{target.index}",
        ]
    env = os.environ.copy()
    env[SEED_ENV] = str(seed)
    with tempfile.TemporaryDirectory(prefix="wiz-flaky-") as td:
        timings = Path(td) / "timings.jsonl"
        start = time.monotonic()
        try:
            p = subprocess.run(
                [
                    str(driver),
                    *driver_args,
                    "--jobs",
                    "1",
                    "--timings",
                    str(timings),
                    "--shard",
                    "flaky-order",
                    *selectors,
                ],
                cwd=ROOT,
                text=True,
                errors="replace",
                capture_output=True,
                timeout=budget.timeout(timeout),
                env=env,
            )
            seconds = time.monotonic() - start
        except subprocess.TimeoutExpired:
            seconds = time.monotonic() - start
            budget.note(seconds, target=True)
            budget.check()
            return Attempt(
                seed,
                "sequence",
                "timeout",
                seconds,
                None,
                f"timed out after {seconds:.1f} s",
                predecessor.label,
            )
        except OSError as e:
            seconds = time.monotonic() - start
            budget.note(seconds, target=True)
            return Attempt(seed, "sequence", "error", seconds, None, str(e), predecessor.label)

        budget.note(seconds, target=True)
        target_record = None
        if timings.exists():
            for line in timings.read_text(encoding="utf-8", errors="replace").splitlines():
                if not line.strip():
                    continue
                try:
                    rec = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if rec.get("group") == target.group and rec.get("index") == target.index:
                    target_record = rec
                    break
        if target_record is None:
            detail = _last_detail(p.stdout, p.stderr)
            return Attempt(
                seed,
                "sequence",
                "error",
                seconds,
                p.returncode,
                f"target did not run (predecessor failed or the driver stopped)\n{detail}",
                predecessor.label,
            )
        notes = target_record.get("notes") or []
        skipped = any(str(n).startswith("skipped ") for n in notes)
        ok = bool(target_record.get("ok"))
        status = "skip" if skipped else ("pass" if ok else "fail")
        detail = "" if status == "pass" else _last_detail(p.stdout, p.stderr)
        target_seconds = float(target_record.get("seconds", 0.0))
        return Attempt(
            seed,
            "sequence",
            status,
            seconds,
            p.returncode,
            detail,
            predecessor.label,
            target_seconds,
        )


# ---------------------------------------------------------------------------
# Classification


def classify(attempts: list[Attempt], planned: int) -> str:
    if not attempts:
        return "incomplete"
    statuses = [a.status for a in attempts]
    passes = statuses.count("pass")
    fails = statuses.count("fail")
    skips = statuses.count("skip")
    errors = statuses.count("error") + statuses.count("timeout")
    if len(attempts) < planned:
        return "incomplete"
    if skips == len(statuses):
        return "always skip"
    if passes and (fails or errors):
        return "flaky"
    if fails and not passes:
        return "deterministic fail" if not errors else "incomplete"
    if errors and not passes:
        return "incomplete"
    if passes and not fails and not errors and not skips:
        return "always pass"
    return "incomplete"


def _counts(attempts: list[Attempt]) -> dict[str, int]:
    out = {"pass": 0, "fail": 0, "skip": 0, "error": 0, "timeout": 0}
    for a in attempts:
        out[a.status] = out.get(a.status, 0) + 1
    return out


def _order_verdict(alone: list[Attempt], sequence: list[Attempt]) -> tuple[bool, str]:
    ac = _counts(alone)
    sc = _counts(sequence)
    if not sequence:
        return False, "not checked"
    if ac["skip"] == len(alone) and not ac["fail"]:
        return False, "skipped alone"
    if sc["skip"] == len(sequence) and not sc["fail"]:
        return False, "skipped in sequence"
    if ac["pass"] and not ac["fail"] and sc["fail"]:
        return True, "fails only in sequence"
    if ac["fail"] and sc["fail"]:
        return False, "fails alone and in sequence"
    if ac["fail"] and not sc["fail"]:
        return False, "fails alone, passes in sequence"
    if not ac["fail"] and not sc["fail"]:
        return False, "not reproduced"
    return False, "mixed"


# ---------------------------------------------------------------------------
# Quarantine


DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def _date(value: str, what: str) -> dt.date:
    if not DATE_RE.match(value):
        raise FlakyError(f"{what}: {value!r} is not a YYYY-MM-DD date")
    try:
        return dt.date.fromisoformat(value)
    except ValueError as e:
        raise FlakyError(f"{what}: {value!r} is not a date") from e


def load_quarantine(
    path: Path | None, today: dt.date, warn_days: int = 7
) -> Quarantine:
    q = Quarantine(file=path)
    if path is None or not path.exists():
        return q
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except OSError as e:
        raise FlakyError(f"cannot read quarantine {path}: {e}") from e
    except json.JSONDecodeError as e:
        raise FlakyError(f"{path}: not JSON: {e}") from e
    if not isinstance(data, dict):
        raise FlakyError(f"{path}: the top level must be an object")
    entries = data.get("entries", [])
    if not isinstance(entries, list):
        raise FlakyError(f"{path}: \"entries\" must be a list")
    for k, raw in enumerate(entries, 1):
        where = f"{path}: entry {k}"
        if not isinstance(raw, dict):
            raise FlakyError(f"{where}: must be an object")
        group = raw.get("group")
        case = raw.get("case")
        expires = raw.get("expires")
        if not isinstance(group, str) or not group:
            raise FlakyError(f"{where}: \"group\" must be a non-empty string")
        if not isinstance(case, str) or not case:
            raise FlakyError(f"{where}: \"case\" must be a non-empty string")
        if not isinstance(expires, str):
            raise FlakyError(f"{where}: \"expires\" must be a YYYY-MM-DD string")
        index = raw.get("index")
        if index is not None and (not isinstance(index, int) or index < 0):
            raise FlakyError(f"{where}: \"index\" must be a non-negative integer")
        entry = QuarantineEntry(
            group=group,
            case=case,
            expires=_date(expires, f"{where} expires"),
            reason=str(raw.get("reason", "")),
            owner=str(raw.get("owner", "")),
            issue=str(raw.get("issue", "")),
            index=index,
        )
        q.entries.append(entry)
        days = (entry.expires - today).days
        if days <= 0:
            q.expired.append(entry)
        elif days <= warn_days:
            q.expiring.append(entry)
    return q


def check_quarantine(path: Path | None, today: dt.date, warn_days: int = 7) -> int:
    if path is None or not path.exists():
        print(f"flaky quarantine: no file at {path} (nothing is quarantined)")
        return 0
    try:
        q = load_quarantine(path, today, warn_days)
    except FlakyError as e:
        print(f"flaky: {e}", file=sys.stderr)
        return 2
    print(f"flaky quarantine: {path} ({len(q.entries)} entries)")
    for e in sorted(q.entries, key=lambda e: (e.expires, e.group, e.case)):
        days = (e.expires - today).days
        if days <= 0:
            state = f"EXPIRED {(-days)} day{'s' if -days != 1 else ''} ago"
        else:
            state = f"expires in {days} day{'s' if days != 1 else ''}"
        extra = ""
        if e.owner:
            extra += f" owner: {e.owner}"
        if e.issue:
            extra += f" issue: {e.issue}"
        if e.reason:
            extra += f" reason: {e.reason}"
        print(f"  {e.expires.isoformat()}  {state:<22}  {e.label()}{extra}", flush=True)
        if days <= 0:
            owner = e.owner or "(no owner recorded)"
            _annotation(
                "error",
                "Flaky quarantine",
                f"quarantined test expired: {e.label()} "
                f"(due {e.expires.isoformat()}; owner: {owner})",
            )
        elif days <= warn_days:
            _annotation(
                "warning",
                "Flaky quarantine",
                f"quarantined test expires in {days} days: {e.label()}",
            )
    if q.expired:
        sys.stdout.flush()
        print(
            f"flaky quarantine: {len(q.expired)} expired entry(ies); fix or re-quarantine with a new expiry",
            file=sys.stderr,
        )
        for e in q.expired:
            print(
                f"  expired: {e.label()} (owner: {e.owner or '(no owner recorded)'}, "
                f"due {e.expires.isoformat()})",
                file=sys.stderr,
            )
        return 1
    if q.entries:
        nxt = min(e.expires for e in q.entries)
        print(f"flaky quarantine: ok; next expiry {nxt.isoformat()} ({(nxt - today).days} days)")
    else:
        print("flaky quarantine: ok; no entries")
    return 0


def _annotation(level: str, title: str, msg: str) -> None:
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"::{level} title={title}::{msg}", file=sys.stderr)
    elif level == "warning":
        print(f"warning: {msg}", file=sys.stderr)


# ---------------------------------------------------------------------------
# Analysis


@dataclass
class AnalyzeOptions:
    repeats: int = DEFAULT_REPEATS
    seeds: list[int] = field(default_factory=lambda: list(range(1, DEFAULT_REPEATS + 1)))
    budget: float | None = DEFAULT_BUDGET
    timeout: float = DEFAULT_TIMEOUT
    order_check: str = "suspects"  # all, suspects, off
    predecessor_scope: str = "group"  # selected, group, all
    order_repeats: int | None = None
    quarantine: Quarantine = field(default_factory=Quarantine)
    source_keys: set[tuple[str, int]] = field(default_factory=set)
    today: dt.date = field(default_factory=dt.date.today)
    selectors: list[str] = field(default_factory=list)
    driver_args: tuple[str, ...] = ()
    label: str = ""


def _predecessor(pool: list[CaseId], target: CaseId, seed: int) -> CaseId | None:
    if not pool:
        return None
    rng = random.Random((seed << 20) ^ zlib.crc32(target.group.encode()) ^ target.index)
    return pool[rng.randrange(len(pool))]


def analyze(driver: Path, cases: list[CaseId], opts: AnalyzeOptions) -> tuple[dict, int]:
    budget = Budget(opts.budget)
    starts = time.monotonic()
    order_repeats = opts.order_repeats if opts.order_repeats is not None else opts.repeats
    order_repeats = min(order_repeats, len(opts.seeds))
    order_seeds = opts.seeds[:order_repeats]
    universe: list[CaseId] | None = None
    positions: dict[tuple[str, int], int] = {}
    if opts.order_check != "off" and cases:
        universe = list_cases(driver, driver_args=opts.driver_args)
        positions = {c.key: i for i, c in enumerate(universe)}

    results: list[dict] = []
    complete = True
    exhausted = False
    for case in cases:
        alone: list[Attempt] = []
        for seed in opts.seeds:
            if budget.remaining is not None and budget.remaining <= 0.05:
                complete = False
                exhausted = True
                break
            try:
                alone.append(
                    run_alone(
                        driver, case, seed, budget, opts.timeout, opts.driver_args
                    )
                )
            except BudgetExceeded:
                complete = False
                exhausted = True
                break
        classification = classify(alone, len(opts.seeds))
        counts = _counts(alone)
        source_failure = case.key in opts.source_keys
        # A case that failed in the source run and passed every rerun did fail: it is
        # flaky (the failure did not reproduce), never "always pass".  This is what makes
        # `--from-log` safe to gate a CI shard on.
        did_not_reproduce = False
        if source_failure and classification == "always pass":
            classification = "flaky"
            did_not_reproduce = True

        order: dict = {
            "checked": False,
            "reason": "not a suspect",
            "alone": counts,
            "sequence": _counts([]),
            "predecessors": [],
            "order_dependent": False,
            "verdict": "not checked",
            "failing_seeds": [],
            "attempts": [],
        }
        suspect = (
            opts.order_check == "all"
            or case.key in opts.source_keys
            or counts["fail"] > 0
            or counts["error"] > 0
            or counts["timeout"] > 0
        )
        if opts.order_check == "off":
            order["reason"] = "order check disabled"
        elif not suspect:
            order["reason"] = "not a suspect (passed every alone run)"
        elif not alone:
            order["reason"] = "no alone runs"
        elif not order_seeds:
            order["reason"] = "no order seeds"
        elif universe is None:
            order["reason"] = "case universe unavailable"
        else:
            pos = positions.get(case.key)
            pool: list[CaseId] = []
            if pos is not None:
                if opts.predecessor_scope == "all":
                    pool = universe[:pos]
                elif opts.predecessor_scope == "group":
                    pool = [c for c in universe[:pos] if c.group == case.group]
                else:  # selected
                    pool = [c for c in cases if positions.get(c.key, 1 << 60) < pos]
                pool.sort(key=lambda c: positions.get(c.key, 1 << 60))
            seq: list[Attempt] = []
            preds: list[str] = []
            for seed in order_seeds:
                if budget.remaining is not None and budget.remaining <= 0.05:
                    complete = False
                    exhausted = True
                    break
                pred = _predecessor(pool, case, seed)
                if pred is None:
                    order["reason"] = "no earlier case in the predecessor scope"
                    break
                preds.append(pred.label)
                try:
                    seq.append(
                        run_sequence(
                            driver,
                            case,
                            pred,
                            seed,
                            budget,
                            opts.timeout,
                            opts.driver_args,
                        )
                    )
                except BudgetExceeded:
                    complete = False
                    exhausted = True
                    break
            if seq:
                dep, verdict = _order_verdict(alone, seq)
                order.update(
                    checked=True,
                    reason="ran alone and after a predecessor",
                    sequence=_counts(seq),
                    predecessors=preds,
                    order_dependent=dep,
                    verdict=verdict,
                    failing_seeds=[a.seed for a in seq if a.status == "fail"],
                    attempts=[a.as_json() for a in seq],
                )
                if dep and classification == "always pass":
                    classification = "flaky"
            elif not order["reason"] or order["reason"] == "not a suspect":
                order["reason"] = "no sequence run completed"

        entry = opts.quarantine.match(case)
        qstate = "not listed"
        if entry is not None:
            if entry.expires <= opts.today:
                qstate = "expired"
            else:
                qstate = "active"
        result = {
            "group": case.group,
            "index": case.index,
            "name": case.name,
            "classification": classification,
            "source_failure": source_failure,
            "did_not_reproduce": did_not_reproduce,
            "passes": counts["pass"],
            "fails": counts["fail"],
            "skips": counts["skip"],
            "errors": counts["error"] + counts["timeout"],
            "planned_attempts": len(opts.seeds),
            "attempts": [a.as_json() for a in alone],
            "failing_seeds": [a.seed for a in alone if a.status == "fail"],
            "order": order,
            "quarantine": {
                "state": qstate,
                "expires": entry.expires.isoformat() if entry else None,
                "reason": entry.reason if entry else None,
            },
        }
        results.append(result)

    elapsed = time.monotonic() - starts
    summary: dict[str, int] = {}
    for r in results:
        summary[r["classification"]] = summary.get(r["classification"], 0) + 1
    expired = opts.quarantine.expired
    verdict_kind = "pass"
    code = 0
    if not complete:
        verdict_kind = "incomplete"
        code = 4
    elif expired:
        verdict_kind = "expired quarantine"
        code = 1
    elif any(r["classification"] == "deterministic fail" for r in results):
        # An active quarantine never masks a deterministic failure: the case failed on
        # every rerun, so the code is broken, not flaky.
        verdict_kind = "deterministic failure"
        code = 1
    elif any(r["classification"] == "incomplete" for r in results):
        verdict_kind = "incomplete"
        code = 1
    elif any(
        r["classification"] == "always skip" and r["source_failure"]
        for r in results
    ):
        # The case failed in the shard and now only skips: a skip is not a pass, so the
        # failure is still unexplained.
        verdict_kind = "skipped after a failure"
        code = 1
    elif any(
        r["classification"] == "flaky" and r["quarantine"]["state"] != "active"
        for r in results
    ):
        verdict_kind = "flaky"
        code = 3

    report = {
        "tool": TOOL_NAME,
        "version": TOOL_VERSION,
        "generated": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
        "driver": str(driver),
        "shard": opts.label,
        "selectors": opts.selectors,
        "repeats": opts.repeats,
        "seeds": opts.seeds,
        "order_check": opts.order_check,
        "predecessor_scope": opts.predecessor_scope,
        "order_repeats": order_repeats,
        "budget_seconds": opts.budget,
        "elapsed_seconds": round(elapsed, 3),
        "runs": budget.runs,
        "target_runs": budget.target_runs,
        "case_seconds": round(budget.case_seconds, 3),
        "complete": complete,
        "budget_exhausted": exhausted,
        "summary": summary,
        "quarantine": {
            "file": str(opts.quarantine.file) if opts.quarantine.file else None,
            "entries": len(opts.quarantine.entries),
            "expired": [e.as_json() for e in opts.quarantine.expired],
            "expiring": [e.as_json() for e in opts.quarantine.expiring],
        },
        "verdict": {"kind": verdict_kind, "code": code},
        "cases": results,
    }
    return report, code


def human_summary(report: dict, stream=sys.stdout) -> None:
    cases = report["cases"]
    if report["seeds"]:
        seeds = report["seeds"]
        shown = ",".join(map(str, seeds)) if len(seeds) <= 8 else f"{seeds[0]}..{seeds[-1]}"
        head = (
            f"Flaky test report: {len(cases)} case{'s' if len(cases) != 1 else ''}, "
            f"{len(seeds)} repeat{'s' if len(seeds) != 1 else ''} (seeds {shown})"
        )
    else:
        head = f"Flaky test report: {len(cases)} cases"
    print(head, file=stream)
    budget = (
        f"{report['budget_seconds']:.0f} s" if report["budget_seconds"] else "unlimited"
    )
    print(
        f"  {report['runs']} driver run{'s' if report['runs'] != 1 else ''}, "
        f"{report['case_seconds']:.1f} s of case time, "
        f"{report['elapsed_seconds']:.1f} s wall (budget {budget})",
        file=stream,
    )
    if not report["complete"]:
        print("  INCOMPLETE: the rerun budget ran out before every case was measured", file=stream)
    order = ["deterministic fail", "flaky", "incomplete", "always skip", "always pass"]
    for classification in order:
        group = [c for c in cases if c["classification"] == classification]
        if not group:
            continue
        print(f"  {classification} ({len(group)}):", file=stream)
        for c in group:
            counts = f"{c['passes']} passed, {c['fails']} failed"
            if c["skips"]:
                counts += f", {c['skips']} skipped"
            if c["errors"]:
                counts += f", {c['errors']} errors"
            if c["failing_seeds"]:
                counts += f"; failing seeds {', '.join(map(str, c['failing_seeds']))}"
            if c.get("did_not_reproduce"):
                counts += "; did not reproduce (it failed in the source run)"
            q = ""
            if c["quarantine"]["state"] == "active":
                q = f" [quarantined until {c['quarantine']['expires']}]"
            elif c["quarantine"]["state"] == "expired":
                q = f" [QUARANTINE EXPIRED {c['quarantine']['expires']}]"
            print(f"    {c['group']} #{c['index']} {c['name']}: {counts}{q}", file=stream)
            o = c["order"]
            if o["checked"]:
                seq = o["sequence"]
                pred = o["predecessors"][0] if o["predecessors"] else "?"
                print(
                    f"      order: alone {o['alone']['pass']}/{sum(o['alone'].values())} passed; "
                    f"sequence {seq['pass']}/{sum(seq.values())} passed after {pred} -> {o['verdict'].upper()}",
                    file=stream,
                )
                if o["order_dependent"]:
                    print(
                        "        ORDER DEPENDENT: it passes alone and fails in sequence",
                        file=stream,
                    )
    q = report["quarantine"]
    if q["entries"]:
        print(
            f"  quarantine: {q['entries']} entr{'y' if q['entries'] == 1 else 'ies'}, "
            f"{len(q['expired'])} expired",
            file=stream,
        )
        for e in q["expired"]:
            print(f"    EXPIRED: {e['group']} {e['case']} (due {e['expires']})", file=stream)
    else:
        print("  quarantine: no entries", file=stream)
    print(f"  verdict: {report['verdict']['kind']} (exit {report['verdict']['code']})", file=stream)


def _md(text: object) -> str:
    return str(text).replace("|", "\\|").replace("\n", " ")


def markdown_summary(report: dict, stream=sys.stdout) -> None:
    """A Markdown section for ``$GITHUB_STEP_SUMMARY``: one row per case with the shard,
    case, class, seed(s) and the quarantine entry's expiry (the CI gate reads this)."""
    cases = report["cases"]
    shard = report.get("shard") or "(shard)"
    print(f"### Flaky classification: {_md(shard)}", file=stream)
    print(file=stream)
    verdict = report["verdict"]
    icon = "✅" if verdict["code"] == 0 else "❌"
    print(f"{icon} **{_md(verdict['kind'])}** (exit {verdict['code']}).", file=stream)
    budget = (
        f"{report['budget_seconds']:.0f} s" if report["budget_seconds"] else "unlimited"
    )
    print(
        f"{report['runs']} driver run{'s' if report['runs'] != 1 else ''}, "
        f"{report['case_seconds']:.1f} s of case time, "
        f"{report['elapsed_seconds']:.1f} s wall (budget {budget}).",
        file=stream,
    )
    if not report["complete"]:
        print(
            "**INCOMPLETE:** the rerun budget ran out before every case was measured.",
            file=stream,
        )
    print(file=stream)
    print("| shard | case | class | seed(s) | quarantine |", file=stream)
    print("|---|---|---|---|---|", file=stream)
    seeds = report["seeds"]
    for c in cases:
        cls = c["classification"]
        if c.get("did_not_reproduce"):
            cls += " (not reproduced)"
        if c["order"].get("order_dependent"):
            cls += " (order dependent)"
        if c["failing_seeds"]:
            seed = ", ".join(str(s) for s in c["failing_seeds"])
        elif seeds:
            seed = f"{seeds[0]}–{seeds[-1]}" if len(seeds) > 1 else str(seeds[0])
        else:
            seed = "—"
        q = c["quarantine"]
        if q["state"] == "active":
            quarantine = f"active until {q['expires']}"
        elif q["state"] == "expired":
            quarantine = f"**EXPIRED {q['expires']}**"
        else:
            quarantine = "—"
        label = f"{c['group']} #{c['index']} {c['name']}"
        print(
            f"| {_md(shard)} | {_md(label)} | {_md(cls)} | {_md(seed)} | {quarantine} |",
            file=stream,
        )
    q = report["quarantine"]
    if q["expired"]:
        print(file=stream)
        print("**Expired quarantine entries:**", file=stream)
        for e in q["expired"]:
            owner = e.get("owner") or "(no owner recorded)"
            print(
                f"- {_md(e['group'])} {_md(e['case'])}: expired {e['expires']} "
                f"(owner: {_md(owner)})",
                file=stream,
            )
    print(file=stream)


# ---------------------------------------------------------------------------
# Self-test fixtures


STUB_DRIVER = r'''#!/usr/bin/env python3
"""A deliberately flaky stand-in for the Wiz test driver, used by scripts/flaky.py
--self-test.  It implements only what the tool calls: --list, --list-shards,
--list-cases, --run, and a suite run with --timings."""
import json
import os
import sys
from pathlib import Path

GROUPS = [("fixtures", [
    (0, "always passes", "pass"),
    (1, "always fails", "fail"),
    (2, "alternates", "alt"),
    (3, "sequence-only", "seq"),
    (4, "always skips", "skip"),
])]
STATE = Path(__file__).with_name("state.json")


def load_state():
    try:
        return json.loads(STATE.read_text())
    except Exception:
        return {}


def save_state(state):
    STATE.write_text(json.dumps(state))


def selects(group, arg):
    if arg.startswith("="):
        return group == arg.split("#", 1)[0][1:]
    return group.startswith(arg)


def selected_indices(arg, n):
    if arg.startswith("=") and "#" in arg:
        return [int(x) for x in arg.split("#", 1)[1].split(",") if x]
    return list(range(n))


def run_case(group, index, name, kind, sequence):
    state = load_state()
    if kind == "alt":
        k = state.get("alt", 0) + 1
        state["alt"] = k
        save_state(state)
        ok = k % 2 == 0
    elif kind == "seq":
        ok = not sequence
    elif kind == "skip":
        print("@@wiz-test-note skipped stub reason")
        return 3, "skip"
    elif kind == "fail":
        ok = False
    else:
        ok = True
    print("  %s %s (0.001 s)" % ("\u2713" if ok else "\u2717", name))
    return (0 if ok else 1), ("pass" if ok else "fail")


def main():
    args = sys.argv[1:]
    # the real driver parses toolchain flags wherever they appear; these fixtures only
    # need `--cache PATH` to be ignored (scripts/flaky.py --driver-arg=--cache ...)
    while "--cache" in args:
        i = args.index("--cache")
        del args[i:i + 2]
    if args == ["--list"]:
        for g, _ in GROUPS:
            print(g)
        return 0
    if args == ["--list-shards"]:
        for g, _ in GROUPS:
            print(g + "\t")
        return 0
    if args and args[0] == "--list-cases":
        sels = args[1:]
        for g, cases in GROUPS:
            if not sels or any(selects(g, s) for s in sels):
                ix = set()
                for s in sels:
                    if selects(g, s):
                        ix.update(selected_indices(s, len(cases)))
                if not ix:
                    ix = set(range(len(cases)))
                for i, n, k in cases:
                    if i in ix:
                        print("%s\t%d\t%s" % (g, i, n))
        return 0

    timings = None
    shard = ""
    rest = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "--timings":
            timings = args[i + 1]
            i += 2
        elif a == "--shard":
            shard = args[i + 1]
            i += 2
        elif a in ("--jobs", "--cache"):
            i += 2
        elif a == "--run":
            rest.append(a)
            i += 1
        elif a.startswith("--"):
            i += 1
        else:
            rest.append(a)
            i += 1

    if rest[:1] == ["--run"]:
        g = rest[1].lstrip("=")
        ix = int(rest[2])
        case = None
        for gg, cases in GROUPS:
            if gg == g:
                for i, n, k in cases:
                    if i == ix:
                        case = (gg, i, n, k)
        if case is None:
            return 2
        gg, i, n, k = case
        print(n)
        code, status = run_case(gg, i, n, k, False)
        if code == 0:
            print("\n%s #%d: passed" % (gg, i))
        elif code == 3:
            print("\n%s #%d: SKIPPED (stub reason)" % (gg, i))
        else:
            print("\n%s #%d: FAILED" % (gg, i))
        return code

    todo = []
    for g, cases in GROUPS:
        if not rest or any(selects(g, s) for s in rest):
            ix = set()
            for s in rest:
                if selects(g, s):
                    ix.update(selected_indices(s, len(cases)))
            if not ix:
                ix = set(range(len(cases)))
            for i, n, k in cases:
                if i in ix:
                    todo.append((g, i, n, k))
    sequence = len(todo) > 1
    failed = 0
    current = None
    for g, i, n, k in todo:
        if g != current:
            print("\u2500\u2500 %s (fixtures)" % g)
            current = g
        code, status = run_case(g, i, n, k, sequence)
        ok = code != 1
        if timings:
            notes = ["skipped stub reason"] if code == 3 else []
            rec = {
                "shard": shard,
                "group": g,
                "index": i,
                "case": n,
                "seconds": 0.001,
                "ok": ok,
                "notes": notes,
            }
            with open(timings, "a") as f:
                f.write(json.dumps(rec) + "\n")
        if code == 1:
            failed += 1
    print("\n%d passed, %d failed" % (len(todo) - failed, failed))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
'''


def _self_test() -> int:
    checks = 0

    def check(cond: bool, msg: str) -> None:
        nonlocal checks
        if not cond:
            raise AssertionError(msg)
        checks += 1

    with tempfile.TemporaryDirectory(prefix="wiz-flaky-selftest-") as td:
        driver = Path(td) / "tests"
        driver.write_text(STUB_DRIVER, encoding="utf-8")
        driver.chmod(0o755)
        today = dt.date(2026, 11, 15)

        all_cases = list_cases(driver, ["=fixtures"])
        check(len(all_cases) == 5, f"fixture driver listed {len(all_cases)} cases, wanted 5")
        check([c.index for c in all_cases] == [0, 1, 2, 3, 4], "fixture case order")

        opts = AnalyzeOptions(
            repeats=5,
            seeds=[1, 2, 3, 4, 5],
            budget=120.0,
            timeout=20.0,
            order_check="all",
            order_repeats=5,
            today=today,
            selectors=["=fixtures"],
        )
        report, code = analyze(driver, all_cases, opts)
        by_name = {c["name"]: c for c in report["cases"]}
        check(by_name["always passes"]["classification"] == "always pass", "always-pass fixture")
        check(by_name["always fails"]["classification"] == "deterministic fail", "always-fail fixture")
        check(by_name["alternates"]["classification"] == "flaky", "alternating fixture is flaky")
        check(by_name["always skips"]["classification"] == "always skip", "skip fixture")
        check(by_name["sequence-only"]["classification"] == "flaky", "sequence-only becomes flaky")
        check(by_name["sequence-only"]["order"]["order_dependent"] is True, "order dependence detected")
        check(by_name["sequence-only"]["order"]["checked"] is True, "order check ran")
        check("no earlier case" in by_name["always passes"]["order"]["reason"],
              "the first case has no predecessor and says so")
        check(code == 1, f"fixture verdict is a deterministic failure (got {code})")
        check(report["complete"] is True, "fixture run completed")

        # --from-log: only the cases the log reports, and a prior failure is a suspect
        # even when every alone run passes (the sequence-only case).
        log = Path(td) / "run.log"
        log.write_text(
            "\u2500\u2500 fixtures (fixtures)\n"
            "  \u2717 alternates (0.001 s)\n"
            "      stub failure\n"
            "  \u2717 sequence-only (0.001 s)\n"
            "      stub failure\n"
            "\n1 passed, 2 failed\n",
            encoding="utf-8",
        )
        from_log = cases_from_logs(driver, [log])
        check({c.name for c in from_log} == {"alternates", "sequence-only"}, "log parser selects failures")
        opts.source_keys = {c.key for c in from_log}
        opts.order_check = "suspects"
        opts.seeds = [1, 2, 3]
        opts.repeats = 3
        opts.order_repeats = 3
        report, code = analyze(driver, from_log, opts)
        by_name = {c["name"]: c for c in report["cases"]}
        check(by_name["sequence-only"]["order"]["order_dependent"] is True, "prior-failure order check")
        check(code == 3, f"flaky-only from-log verdict is 3 (got {code})")

        # --from-timings reads the driver's JSONL.
        timings = Path(td) / "timings.jsonl"
        timings.write_text(
            "\n".join(
                json.dumps(r)
                for r in [
                    {"group": "fixtures", "index": 2, "case": "alternates", "ok": False},
                    {"group": "fixtures", "index": 0, "case": "always passes", "ok": True},
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        from_timings = cases_from_timings(driver, [timings])
        check([c.name for c in from_timings] == ["alternates"], "timings parser selects failures")

        # A JUnit file from another tool is accepted too (the driver emits none itself).
        junit = Path(td) / "junit.xml"
        junit.write_text(
            '<?xml version="1.0"?><testsuite><testcase classname="fixtures" '
            'name="always passes"><failure>nope</failure></testcase></testsuite>',
            encoding="utf-8",
        )
        from_junit = cases_from_junit(driver, [junit])
        check([c.name for c in from_junit] == ["always passes"], "JUnit parser")

        # Quarantine: a fresh entry suppresses the flaky verdict, an expired one fails.
        fresh = Path(td) / "fresh.json"
        fresh.write_text(
            json.dumps(
                {
                    "version": 1,
                    "entries": [
                        {"group": "fixtures", "case": "alternates", "expires": "2026-11-20", "reason": "test"},
                        {"group": "fixtures", "case": "sequence-only", "expires": "2026-11-20", "reason": "test"},
                    ],
                }
            ),
            encoding="utf-8",
        )
        q = load_quarantine(fresh, today)
        check(len(q.entries) == 2 and not q.expired, "fresh quarantine loads")
        opts.quarantine = q
        report, code = analyze(driver, from_log, opts)
        check(code == 0, f"active quarantine suppresses the flaky verdict (got {code})")
        check(all(c["quarantine"]["state"] == "active" for c in report["cases"]), "quarantine matched")

        expired = Path(td) / "expired.json"
        expired.write_text(
            json.dumps(
                {
                    "version": 1,
                    "entries": [
                        {"group": "fixtures", "case": "alternates", "expires": "2026-11-14", "reason": "old"}
                    ],
                }
            ),
            encoding="utf-8",
        )
        q = load_quarantine(expired, today)
        check(len(q.expired) == 1, "expired quarantine detects")
        opts.quarantine = q
        report, code = analyze(driver, from_log, opts)
        check(code == 1, f"expired quarantine fails (got {code})")
        check(report["verdict"]["kind"] == "expired quarantine", "expired verdict kind")
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(io.StringIO()):
            rc = check_quarantine(expired, today)
        check(rc == 1, "--check-quarantine exits 1 on expiry")
        check("EXPIRED" in buf.getvalue(), "--check-quarantine reports the expiry")
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = check_quarantine(fresh, today, warn_days=0)
        check(rc == 0, "--check-quarantine passes fresh entries")

        def quarantine_file(name: str, entries: list[dict]) -> Path:
            p = Path(td) / name
            p.write_text(
                json.dumps({"version": 1, "entries": entries}), encoding="utf-8"
            )
            return p

        def log_file(name: str, case: str) -> Path:
            p = Path(td) / name
            p.write_text(
                "\u2500\u2500 fixtures (fixtures)\n"
                f"  \u2717 {case} (0.001 s)\n"
                "      stub failure\n"
                "\n0 passed, 1 failed\n",
                encoding="utf-8",
            )
            return p

        opts.order_check = "off"
        opts.seeds = [1, 2, 3]
        opts.repeats = 3
        opts.order_repeats = 3
        opts.budget = 120.0
        opts.timeout = 20.0

        # A deterministic failure is never masked by an active quarantine entry.
        det_cases = cases_from_logs(driver, [log_file("deterministic.log", "always fails")])
        det_q = quarantine_file(
            "det-q.json",
            [{"group": "fixtures", "case": "always fails", "expires": "2026-11-20",
              "reason": "test", "owner": "Fixture owner"}],
        )
        opts.source_keys = {c.key for c in det_cases}
        opts.quarantine = load_quarantine(det_q, today)
        report, code = analyze(driver, det_cases, opts)
        check(code == 1, f"an active quarantine does not mask a deterministic fail (got {code})")
        check(report["cases"][0]["classification"] == "deterministic fail", "deterministic classification")
        check(report["cases"][0]["quarantine"]["state"] == "active", "the entry still matches")

        # A source failure that passes every rerun did fail: it is flaky, not always pass.
        pass_cases = cases_from_logs(driver, [log_file("pass.log", "always passes")])
        opts.source_keys = {c.key for c in pass_cases}
        opts.quarantine = Quarantine()
        report, code = analyze(driver, pass_cases, opts)
        check(code == 3, f"an unreproduced source failure is flaky (got {code})")
        check(report["cases"][0]["classification"] == "flaky", "unreproduced source failure classification")
        check(report["cases"][0]["did_not_reproduce"] is True, "unreproduced source failure is marked")
        pass_q = quarantine_file(
            "pass-q.json",
            [{"group": "fixtures", "case": "always passes", "expires": "2026-11-20",
              "reason": "test"}],
        )
        opts.quarantine = load_quarantine(pass_q, today)
        report, code = analyze(driver, pass_cases, opts)
        check(code == 0, f"a quarantined unreproduced failure is green (got {code})")
        check(report["cases"][0]["quarantine"]["state"] == "active", "unreproduced failure matched")
        buf = io.StringIO()
        markdown_summary(report, buf)
        md = buf.getvalue()
        check("| shard | case | class | seed(s) | quarantine |" in md, "Markdown summary table")
        check("flaky (not reproduced)" in md, "Markdown summary shows the classification")
        check("active until 2026-11-20" in md, "Markdown summary shows the expiry")

        # A source failure that now only skips is not a pass, quarantined or not.
        skip_cases = cases_from_logs(driver, [log_file("skip.log", "always skips")])
        opts.source_keys = {c.key for c in skip_cases}
        opts.quarantine = Quarantine()
        report, code = analyze(driver, skip_cases, opts)
        check(code == 1, f"a source failure that only skips fails (got {code})")
        check(report["cases"][0]["classification"] == "always skip", "skip classification")
        skip_q = quarantine_file(
            "skip-q.json",
            [{"group": "fixtures", "case": "always skips", "expires": "2026-11-20",
              "reason": "test"}],
        )
        opts.quarantine = load_quarantine(skip_q, today)
        report, code = analyze(driver, skip_cases, opts)
        check(code == 1, f"a quarantine does not turn a skip into a pass (got {code})")

        # The expiry message names the entry and its owner.
        expired_owner = quarantine_file(
            "expired-owner.json",
            [{"group": "fixtures", "case": "always fails", "expires": "2026-11-14",
              "reason": "old", "owner": "Fixture owner"}],
        )
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(io.StringIO()):
            rc = check_quarantine(expired_owner, today)
        check(rc == 1, "expired entry with an owner fails")
        check("Fixture owner" in buf.getvalue(), "the expiry message names the owner")

        bad = Path(td) / "bad.json"
        bad.write_text('{"entries": [{"group": "fixtures", "case": "x"}]}', encoding="utf-8")
        try:
            load_quarantine(bad, today)
            check(False, "malformed quarantine accepted")
        except FlakyError:
            checks += 1

        # A missing driver is a clean usage error, never a traceback.
        try:
            list_cases(Path(td) / "missing", [])
            check(False, "missing driver accepted")
        except FlakyError:
            checks += 1

        # A tiny budget must stop the measurement and say so (the fixtures are fast,
        # so force it with an already-spent budget).
        opts.quarantine = Quarantine()
        opts.budget = 0.0001
        report, code = analyze(driver, from_log, opts)
        check(code == 4, f"exhausted budget exits 4 (got {code})")
        check(report["complete"] is False, "exhausted budget is incomplete")

    print(f"flaky self-test: ok ({checks} checks)")
    return 0


# ---------------------------------------------------------------------------
# CLI


def _date_arg(value: str) -> dt.date:
    try:
        return _date(value, "--today")
    except FlakyError as e:
        raise argparse.ArgumentTypeError(str(e)) from e


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="flaky.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        allow_abbrev=False,
    )
    p.add_argument("selectors", nargs="*", help="test driver selectors (`=group#0,2`, `group`)")
    p.add_argument("--driver", type=Path, default=DEFAULT_DRIVER, help=f"test driver (default {DEFAULT_DRIVER})")
    p.add_argument("--driver-arg", action="append", default=[], metavar="ARG", help="extra argument for every driver run (repeatable; use --driver-arg=--cache to pass a flag)")
    p.add_argument("--repeats", type=int, default=DEFAULT_REPEATS, help="reruns per case (default 5)")
    p.add_argument("--seeds", help="comma-separated seed list (default 1..repeats)")
    p.add_argument("--seed-base", type=int, default=1, help="first seed when --seeds is absent (default 1)")
    p.add_argument("--budget", type=float, default=DEFAULT_BUDGET, help=f"total rerun seconds, 0 = no limit (default {DEFAULT_BUDGET:.0f})")
    p.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT, help=f"seconds per driver run (default {DEFAULT_TIMEOUT:.0f})")
    p.add_argument("--order-check", choices=["all", "suspects", "off"], default="suspects", help="which cases to run after a predecessor (default suspects)")
    p.add_argument("--predecessor-scope", choices=["selected", "group", "all"], default="group", help="where the shuffled predecessor comes from (default group)")
    p.add_argument("--order-repeats", type=int, help="sequence runs per suspect (default: --repeats)")
    p.add_argument("--from-log", type=Path, action="append", nargs="+", default=[], metavar="LOG", help="prior test-driver stdout log (repeatable)")
    p.add_argument("--from-timings", type=Path, action="append", nargs="+", default=[], metavar="JSONL", help="prior --timings JSONL (repeatable)")
    p.add_argument("--from-junit", type=Path, action="append", nargs="+", default=[], metavar="XML", help="JUnit XML from another tool (repeatable)")
    p.add_argument("--shard", action="append", default=[], metavar="NAME", help="use a .github/test-shards.json shard's selectors")
    p.add_argument("--quarantine", type=Path, default=DEFAULT_QUARANTINE, help=f"quarantine file (default {DEFAULT_QUARANTINE})")
    p.add_argument("--no-quarantine", action="store_true", help="ignore the quarantine file")
    p.add_argument("--check-quarantine", nargs="?", const=DEFAULT_QUARANTINE, type=Path, metavar="FILE", help="check a quarantine file for expired entries and exit")
    p.add_argument("--today", type=_date_arg, help="date for expiry checks (default today)")
    p.add_argument("--warn-days", type=int, default=7, help="warn when an entry is this close to expiry (default 7)")
    p.add_argument("--report", type=Path, metavar="FILE", help="write the machine-readable JSON report")
    p.add_argument("--summary-md", type=Path, metavar="FILE", help="write a Markdown summary (for $GITHUB_STEP_SUMMARY)")
    p.add_argument("--label", default="", metavar="NAME", help="shard label for the report (CI's shard name)")
    p.add_argument("--json", action="store_true", help="print the JSON report to stdout (human summary goes to stderr)")
    p.add_argument("--list", action="store_true", help="list the selected cases and exit")
    p.add_argument("--self-test", action="store_true", help="run the classifier's fixtures")
    return p.parse_args(argv)


def _seeds(args: argparse.Namespace) -> list[int]:
    if args.seeds:
        try:
            seeds = [int(x) for x in args.seeds.split(",") if x.strip()]
        except ValueError:
            raise FlakyError("--seeds must be a comma-separated list of integers")
        if not seeds:
            raise FlakyError("--seeds is empty")
        return seeds
    if args.repeats < 1:
        raise FlakyError("--repeats must be at least 1")
    return list(range(args.seed_base, args.seed_base + args.repeats))


def selected_cases(args: argparse.Namespace, driver: Path) -> tuple[list[CaseId], list[str]]:
    selectors = list(args.selectors)
    for shard in args.shard:
        selectors += selectors_from_shard(shard)
    source = bool(args.from_log or args.from_timings or args.from_junit)
    cases: list[CaseId]
    if source:
        cases = []
        cases += cases_from_logs(driver, _flatten(args.from_log), args.driver_arg)
        cases += cases_from_timings(
            driver, _flatten(args.from_timings), args.driver_arg
        )
        cases += cases_from_junit(driver, _flatten(args.from_junit), args.driver_arg)
        cases = _dedupe(cases)
        if selectors:
            allowed = {
                c.key for c in list_cases(driver, selectors, args.driver_arg)
            }
            cases = [c for c in cases if c.key in allowed]
    else:
        if not selectors:
            raise FlakyError(
                "no cases selected: give test selectors (for example `=rig`) or --from-log/--from-timings"
            )
        cases = list_cases(driver, selectors, args.driver_arg)
    return cases, selectors


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return _self_test()
    today = args.today or dt.date.today()
    if args.check_quarantine is not None:
        return check_quarantine(args.check_quarantine, today, args.warn_days)

    if not driver_ok(args.driver):
        print(
            f"flaky: the test driver {args.driver} is missing or not executable; "
            "build it with `lake build wiz tests`",
            file=sys.stderr,
        )
        return 2

    try:
        seeds = _seeds(args)
        if not (args.budget >= 0):
            raise FlakyError("--budget must be zero (no limit) or a positive number of seconds")
        if not (args.timeout > 0):
            raise FlakyError("--timeout must be positive")
        if args.order_repeats is not None and args.order_repeats < 0:
            raise FlakyError("--order-repeats must be zero or more")
        cases, selectors = selected_cases(args, args.driver)
        if not cases:
            raise FlakyError("the selected inputs contain no failing cases")
        if args.list:
            for c in cases:
                print(f"{c.group}\t{c.index}\t{c.name}")
            return 0
        quarantine = Quarantine(file=args.quarantine)
        if not args.no_quarantine:
            quarantine = load_quarantine(args.quarantine, today, args.warn_days)
        q = set()
        if args.from_log or args.from_timings or args.from_junit:
            q = {c.key for c in cases}
        opts = AnalyzeOptions(
            repeats=len(seeds),
            seeds=seeds,
            budget=None if args.budget <= 0 else args.budget,
            timeout=args.timeout,
            order_check=args.order_check,
            predecessor_scope=args.predecessor_scope,
            order_repeats=args.order_repeats,
            quarantine=quarantine,
            source_keys=q,
            today=today,
            selectors=selectors,
            driver_args=tuple(args.driver_arg),
            label=args.label,
        )
        report, code = analyze(args.driver, cases, opts)
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(
                json.dumps(report, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
        if args.summary_md:
            args.summary_md.parent.mkdir(parents=True, exist_ok=True)
            with args.summary_md.open("w", encoding="utf-8") as f:
                markdown_summary(report, f)
        if args.json:
            print(json.dumps(report, ensure_ascii=False, indent=2))
            human_summary(report, sys.stderr)
        else:
            human_summary(report, sys.stdout)
        return code
    except FlakyError as e:
        print(f"flaky: {e}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("flaky: interrupted", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
