"""Cell magics for the Wiz kernel.

* ``%%scry`` — treat the cell as C source and run ``scry taint --json`` on it,
  rendering the findings.  This is a **per-cell** analysis: the C is written to a
  temp file, analysed and forgotten.  There is no project, no include path, no
  notion of the previous cell.
* ``%%wiz`` — force the cell through the Wiz backend (the default), useful to
  write a cell that starts with a line that looks like a magic.
* ``%backend`` — say which driver is in use (``repl`` or ``batch``) and why.
* ``%wiz`` — a line form: ``%wiz <code>`` is the same as the code without it.
"""

from __future__ import annotations

import html
import json
import os
import re
import shlex
import shutil
import subprocess
import tempfile

from .backends import CellResult, Backend, ErrorReport

_MAGIC_RE = re.compile(r"^%%(?P<name>[A-Za-z0-9_]+)(?:[ \t]+(?P<args>.*))?$")
_LINE_MAGIC_RE = re.compile(r"^%(?P<name>[A-Za-z0-9_]+)(?:[ \t]+(?P<rest>.*))?$")


class MagicError(Exception):
    def __init__(self, ename: str, message: str):
        super().__init__(message)
        self.ename = ename


def backend_summary(backend: Backend, fallback_reason: str | None,
                    lsp_status: str | None = None) -> str:
    lines = [f"backend: {backend.name}", backend.description]
    if fallback_reason:
        lines.append(f"(chosen because `wiz repl` was not available: {fallback_reason})")
    else:
        lines.append("(`wiz repl` is available: this is the stateful driver)")
    if lsp_status is not None:
        lines.append(f"lsp: {lsp_status}")
    return "\n".join(lines)


def handle_magic(code: str, backend: Backend, *,
                 fallback_reason: str | None = None, cwd: str = ".",
                 wiz: str | None = None,
                 lsp_status: str | None = None) -> CellResult | None:
    """Run a magic cell.  Returns None when the cell is ordinary Wiz code."""
    lines = code.splitlines()
    if not lines:
        return None
    first = lines[0]
    match = _MAGIC_RE.match(first)
    if match:
        name = match.group("name")
        args = (match.group("args") or "").strip()
        body = "\n".join(lines[1:])
        if name == "scry":
            return run_scry_magic(body, args, cwd=cwd, wiz=wiz)
        if name == "wiz":
            return backend.execute(body)
        return _error("UnknownMagic", f"unknown cell magic %%{name} (use %%scry or %%wiz)")
    match = _LINE_MAGIC_RE.match(first)
    if match and all(not line.strip() for line in lines[1:]):
        name, rest = match.group("name"), (match.group("rest") or "").strip()
        if name in ("backend", "wiz_backend"):
            return CellResult(result=backend_summary(backend, fallback_reason, lsp_status),
                              backend=backend.name)
        if name == "wiz":
            return backend.execute(rest)
        if name == "scry":
            return _error("UsageError", "%scry is not a line magic: use a %%scry cell")
        return _error("UnknownMagic", f"unknown line magic %{name} (use %backend)")
    return None


def _error(ename: str, message: str) -> CellResult:
    return CellResult(streams=[], errors=[ErrorReport(ename, message, [message])])


# -- scry ---------------------------------------------------------------

def _search_dirs(cwd: str, wiz: str | None) -> list[str]:
    roots: list[str] = []
    here = os.path.abspath(cwd)
    while True:
        roots.append(here)
        parent = os.path.dirname(here)
        if parent == here:
            break
        here = parent
    if wiz:
        here = os.path.dirname(os.path.abspath(wiz))
        for _ in range(5):
            roots.append(here)
            parent = os.path.dirname(here)
            if parent == here:
                break
            here = parent
    seen: set[str] = set()
    return [r for r in roots if not (r in seen or seen.add(r))]


def scry_command(cwd: str, wiz: str | None = None) -> list[str] | None:
    """``$WIZ_SCRY``, ``scry`` on PATH, or a checkout's ``scry/.grail/bin/scry``."""
    configured = os.environ.get("WIZ_SCRY")
    if configured:
        return shlex.split(configured)
    found = shutil.which("scry")
    if found:
        return [found]
    for root in _search_dirs(cwd, wiz):
        for rel in (("scry", ".grail", "bin", "scry"), (".grail", "bin", "scry")):
            candidate = os.path.join(root, *rel)
            if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
                return [candidate]
    return None


def default_rules(cwd: str, command: str | None = None) -> str | None:
    for root in _search_dirs(cwd, command):
        candidate = os.path.join(root, "lib", "Scry", "rules", "default.scry")
        if os.path.isfile(candidate):
            return candidate
    return None


def _location(finding: dict) -> tuple[str, int | None, int | None]:
    loc = finding.get("location") or {}
    uri = loc.get("uri") or ""
    return os.path.basename(uri), loc.get("startLine"), loc.get("startColumn")


def _render_text(report: dict) -> str:
    counts = report.get("counts") or {}
    lines = [
        f"scry taint: {counts.get('findings', 0)} finding(s), "
        f"{counts.get('checked', 0)} checked, {counts.get('unchecked', 0)} unchecked, "
        f"{counts.get('boundary', 0)} boundary warning(s)"
    ]
    for finding in report.get("findings") or []:
        name, line, column = _location(finding)
        where = f" at {name}:{line}:{column}" if line else ""
        derivation = finding.get("derivation") or "unchecked"
        lines.append(f"- [{finding.get('severity', 'warning')}] {finding.get('rule', '?')}"
                     f"{where} ({derivation}): {finding.get('message', '')}")
    for boundary in report.get("boundary") or []:
        name, line, column = _location(boundary)
        where = f" at {name}:{line}:{column}" if line else ""
        lines.append(f"- [boundary]{where} in {boundary.get('function', '?')}: "
                     f"{boundary.get('message', '')}")
    return "\n".join(lines)


def _render_html(report: dict) -> str:
    counts = report.get("counts") or {}

    def rows(key: str, boundary: bool) -> str:
        out = []
        for finding in report.get(key) or []:
            name, line, column = _location(finding)
            where = f"{html.escape(name)}:{line}:{column}" if line else ""
            derivation = html.escape(finding.get("derivation") or "unchecked")
            severity = html.escape(finding.get("severity") or "warning")
            rule = html.escape(finding.get("rule") or "?")
            message = html.escape(finding.get("message") or "")
            if boundary:
                out.append(f"<tr><td>warning</td><td>{rule}</td><td>{where}</td>"
                           f"<td>{message}</td><td>unchecked</td></tr>")
            else:
                out.append(f"<tr><td>{severity}</td><td>{rule}</td><td>{where}</td>"
                           f"<td>{message}</td><td>{derivation}</td></tr>")
        return "".join(out)

    body = rows("findings", False) + rows("boundary", True)
    if not body:
        body = '<tr><td colspan="5">no findings</td></tr>'
    return (
        '<div class="wiz-scry">'
        f"<p><b>scry taint</b>: {counts.get('findings', 0)} finding(s), "
        f"{counts.get('checked', 0)} checked, {counts.get('unchecked', 0)} unchecked, "
        f"{counts.get('boundary', 0)} boundary warning(s)</p>"
        '<table><thead><tr><th>severity</th><th>rule</th><th>location</th>'
        "<th>message</th><th>derivation</th></tr></thead>"
        f"<tbody>{body}</tbody></table></div>"
    )


def run_scry_magic(source: str, args: str, *, cwd: str, wiz: str | None = None,
                   timeout: float | None = None) -> CellResult:
    command = scry_command(cwd, wiz)
    if command is None:
        message = (
            "no scry executable: install one (build the scry package, then put its "
            "binary on PATH) or set WIZ_SCRY, for example "
            "WIZ_SCRY='grail run scry --' from a checkout's scry/ directory")
        return _error("ScryUnavailable", message)
    try:
        extra = shlex.split(args)
    except ValueError as exc:
        return _error("UsageError", f"%%scry: {exc}")
    extra = [a for a in extra if a != "--json"]
    if "--rules" not in extra:
        rules = default_rules(cwd, command[0])
        if rules:
            extra += ["--rules", rules]
    timeout = float(os.environ.get("WIZ_SCRY_TIMEOUT", timeout or 120.0))
    handle = tempfile.NamedTemporaryFile("w", suffix=".c", prefix="wiz-scry-",
                                         delete=False, dir=None)
    try:
        handle.write(source)
        if not source.endswith("\n"):
            handle.write("\n")
        handle.close()
        invocation = [*command, "taint", handle.name, "--json", *extra]
        try:
            done = subprocess.run(invocation, cwd=cwd, capture_output=True, text=True,
                                  timeout=timeout)
        except subprocess.TimeoutExpired:
            return _error("ScryTimeout", f"scry taint timed out after {timeout:.0f}s")
        except OSError as exc:
            return _error("ScryUnavailable", f"cannot run {command[0]}: {exc}")
        report = None
        for line in reversed((done.stdout or "").splitlines()):
            line = line.strip()
            if line.startswith("{"):
                try:
                    report = json.loads(line)
                    break
                except json.JSONDecodeError:
                    continue
        if report is None:
            detail = (done.stderr or done.stdout or "").strip() or "(no output)"
            return _error("ScryError", f"scry taint failed (status {done.returncode}): "
                                       f"{detail}")
        text = _render_text(report)
        data = {"text/plain": text, "text/html": _render_html(report),
                "application/json": report}
        return CellResult(result=text, data=data,
                          metadata={"scry": {"file": report.get("file", handle.name)}})
    finally:
        try:
            os.unlink(handle.name)
        except OSError:
            pass
