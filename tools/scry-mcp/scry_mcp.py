#!/usr/bin/env python3
"""scry-mcp: a read-only MCP server for Scry, the code-analysis platform in `scry/`.

A separate server from `tools/wiz-mcp` (it shares that bridge's transport, path
confinement and environment filtering by importing it). Every tool is read-only
with respect to the workspace:

* `scry_taint` analyses one C file (`scry taint FILE --json --sarif …`), with an
  optional `diff` filter (the bridge runs `git diff` itself, without external diff
  drivers, and hands Scry the saved diff).
* `scry_project` analyses a compile_commands.json project (`scry project DIR
  --taint --json --sarif …`). It runs the host preprocessor (`cc -E`) on the
  project's files. The database's flags are checked against an explicit allowlist
  first: `-I`/`-isystem`/`-iquote`/`-idirafter`/`-include` (their paths must stay
  inside the readable roots), `-D`/`-U` and `-std=`; the driver's `-c`/`-o`/`-M…`
  structure is dropped, and any other flag (`-B<dir>`, `-fplugin=`, `-specs=`,
  `-wrapper`, `@file`, `-Xclang`, `-cc1`, …) is refused by name. That is what
  keeps a repository-supplied database from choosing which program `cc` runs.
* `scry_query`, `scry_explain` and `scry_facts` read a JSON fact store.
* `scry_findings` lists or shows the findings database (`scry findings
  list|show`); it never scans, triages, reproduces or verifies.

`scry dynamic`, `findings repro` (both compile and run code), `findings
scan`/`triage` (they write the database) and the REPL are not offered.

Every run happens in a fresh directory inside the server's private (0700)
temporary directory, which is also the child's HOME and XDG cache: anything Scry
writes lands there, and the SARIF and JSON reports are kept there as resources
(`scry://runs/{id}/sarif`, `…/json`) until the server exits, when the directory
is removed. Findings whose location is outside the readable roots are withheld
(counted, never named), from the result and the SARIF alike.
"""

from __future__ import annotations

import argparse
import atexit
import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
from collections import OrderedDict
from dataclasses import dataclass
from typing import Any, Iterable, Optional

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "wiz-mcp"))

import wiz_mcp as base  # noqa: E402  (the shared transport and policy helpers)
from wiz_mcp import (  # noqa: E402
    ToolError,
    child_env,
    confine,
    envelope_text,
    error_envelope,
    iter_messages,
    log,
    make_envelope,
    reply,
    reply_error,
    resolve_path,
    write_message,
)

SERVER_NAME = "scry"
SERVER_VERSION = "1.0.0"
DEFAULT_TIMEOUT = 300.0
#: Reports kept as resources (the oldest go first).
MAX_RUNS = 20
#: Include directories a compile database may name besides the readable roots.
SYSTEM_INCLUDE_PREFIXES = ("/usr/include", "/usr/local/include", "/nix/store")
#: A `diff` base: a ref, a commit or `HEAD~2`-style; never an option.
DIFF_BASE = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9._/@^~{}-]*$")
FINDING_ID = re.compile(r"^[A-Za-z0-9_.:-]{1,128}$")
FINDING_STATES = ("new", "triaged", "confirmed", "false-positive", "fixed")

INSTRUCTIONS = (
    "Scry static analysis for this workspace, read-only. scry_taint analyses one C file and "
    "scry_project a compile_commands.json project; both return findings (rule, severity, "
    "message, location, path) and keep the SARIF as a resource (scry://runs/{id}/sarif). "
    "Use diff=BASE to report only findings on lines changed since BASE. scry_query, "
    "scry_explain and scry_facts read JSON fact stores; scry_findings lists or shows the "
    "findings database. Nothing is written to the workspace; dynamic analysis and triage "
    "are not available here."
)


@dataclass
class Config:
    workspace: str
    scry: Optional[str] = None
    rules: Optional[str] = None
    timeout: float = DEFAULT_TIMEOUT
    extra_roots: tuple[str, ...] = ()
    pass_env: tuple[str, ...] = ()


# ---------------------------------------------------------------------------
# Locating scry and its rules


def _is_executable(path: str) -> bool:
    return os.path.isfile(path) and os.access(path, os.X_OK)


def resolve_scry(workspace: str, scry: Optional[str]) -> Optional[str]:
    """`--scry`, `$SCRY_BIN`, the workspace's own build (`scry/.grail/bin/scry`), or PATH."""
    candidates = []
    if scry:
        candidates.append(scry if os.path.isabs(scry) or os.sep not in scry else os.path.join(workspace, scry))
    else:
        if os.environ.get("SCRY_BIN"):
            candidates.append(os.environ["SCRY_BIN"])
        candidates.append(os.path.join(workspace, "scry", ".grail", "bin", "scry"))
        candidates.append("scry")
    for candidate in candidates:
        if os.sep not in candidate:
            found = shutil.which(candidate)
            if found and _is_executable(found):
                return found
            continue
        candidate = os.path.normpath(os.path.abspath(candidate))
        if _is_executable(candidate):
            return candidate
    return None


def default_rules(workspace: str, rules: Optional[str]) -> Optional[str]:
    """The default rule pack: `--rules`, the workspace's `lib/Scry/rules/default.scry`, or
    the one in the toolchain library of the `wiz` this workspace would use."""
    if rules:
        return rules if os.path.isabs(rules) else os.path.join(workspace, rules)
    candidates = [os.path.join(workspace, "lib", "Scry", "rules", "default.scry")]
    for wiz in (os.environ.get("WIZ_BIN"), os.path.join(workspace, ".lake", "build", "bin", "wiz"), shutil.which("wiz")):
        if wiz and _is_executable(wiz):
            for root in base.toolchain_roots(wiz):
                lib = os.path.join(root, "lib") if os.path.basename(root) == "wiz" else root
                candidates.append(os.path.join(lib, "Scry", "rules", "default.scry"))
    for candidate in candidates:
        if os.path.isfile(candidate):
            return os.path.normpath(candidate)
    return None


# ---------------------------------------------------------------------------
# Withholding locations outside the readable roots


def _uri_path(uri: Any) -> Optional[str]:
    if not isinstance(uri, str) or not uri:
        return None
    path = base.uri_to_path(uri) if uri.startswith("file:") else uri
    return path if path and os.path.isabs(path) else None


def _finding_paths(finding: dict[str, Any], root: Optional[str]) -> list[str]:
    """The files a JSON finding names (its location and any per-file field)."""
    out = []
    location = finding.get("location")
    if isinstance(location, dict):
        out.append(location.get("uri"))
    out.append(finding.get("file"))
    paths = []
    for value in out:
        if not isinstance(value, str) or not value:
            continue
        if value.startswith("file:"):
            value = base.uri_to_path(value) or ""
        if value and not os.path.isabs(value) and root:
            value = os.path.join(root, value)
        if value:
            paths.append(value)
    return paths


def confine_findings(report: Any, roots: list[str], root: Optional[str] = None) -> int:
    """Drop findings outside `roots` from a Scry JSON report, in place; the count dropped."""
    withheld = 0
    if isinstance(report, dict):
        for key in ("findings", "boundary", "memory"):
            items = report.get(key)
            if isinstance(items, list):
                kept = []
                for item in items:
                    paths = _finding_paths(item, root) if isinstance(item, dict) else []
                    if all(base._allowed(p, roots) for p in paths):
                        kept.append(item)
                    else:
                        withheld += 1
                report[key] = kept
        files = report.get("files")
        if isinstance(files, list):
            for entry in files:
                if isinstance(entry, dict):
                    name = entry.get("file")
                    path = name if not isinstance(name, str) or os.path.isabs(name) or not root else os.path.join(root, name)
                    if isinstance(path, str) and not base._allowed(path, roots):
                        for key in ("findings", "boundary", "memory"):
                            if isinstance(entry.get(key), list):
                                withheld += len(entry[key])
                                entry[key] = []
                        entry["file"] = "(withheld)"
                    else:
                        withheld += confine_findings(entry, roots, root)
    return withheld


def confine_sarif(sarif: Any, roots: list[str], root: Optional[str] = None) -> int:
    withheld = 0
    if not isinstance(sarif, dict):
        return 0
    for run in sarif.get("runs") or []:
        if not isinstance(run, dict):
            continue
        results = run.get("results")
        if isinstance(results, list):
            kept = []
            for result in results:
                uris = []
                for location in (result.get("locations") or []) if isinstance(result, dict) else []:
                    physical = location.get("physicalLocation") if isinstance(location, dict) else None
                    artifact = physical.get("artifactLocation") if isinstance(physical, dict) else None
                    if isinstance(artifact, dict):
                        uris.append(artifact.get("uri"))
                paths = []
                for uri in uris:
                    path = _uri_path(uri) or (os.path.join(root, uri) if isinstance(uri, str) and root else None)
                    if path:
                        paths.append(path)
                if all(base._allowed(p, roots) for p in paths):
                    kept.append(result)
                else:
                    withheld += 1
            run["results"] = kept
        artifacts = run.get("artifacts")
        if isinstance(artifacts, list):
            run["artifacts"] = [
                a for a in artifacts
                if not isinstance(a, dict)
                or not (path := _uri_path((a.get("location") or {}).get("uri")))
                or base._allowed(path, roots)
            ]
    return withheld


# ---------------------------------------------------------------------------
# Compile databases


#: Flags whose value names a path. The value (joined, `-Iinc`, or separate, `-I inc`)
#: must stay inside the readable roots; system include directories are also allowed.
PATH_FLAGS = ("-I", "-isystem", "-iquote", "-idirafter", "-include")
#: Flags whose value is a macro name (`-DFOO=1`, `-U FOO`). They name no path.
MACRO_FLAGS = ("-D", "-U")
#: Flags that select the language version; they change predefined macros, nothing else.
STD_PREFIXES = ("-std=", "--std=")
#: The compile driver's own structure: consumed by Scry, never passed to `cc -E` (so
#: `-o` cannot redirect the preprocessed text to a file and `-M` cannot replace it with
#: make rules). Every real compile database has these.
DROPPED_FLAGS = ("-c", "-M", "-MM", "-MD", "-MMD", "-MP", "-MG", "-s")
#: Driver flags whose value is the next word or attached (`-oFILE`, `-MFdep`).
DROPPED_VALUE_FLAGS = ("-o", "-MF", "-MT", "-MQ", "-MJ")


def _joined(arg: str, flags: Iterable[str]) -> Optional[str]:
    """The value attached to `arg` when it starts with one of `flags` (`-Iinc` → `inc`)."""
    for flag in flags:
        if arg.startswith(flag) and len(arg) > len(flag):
            return arg[len(flag):]
    return None


def _include_paths(args: list[str]) -> list[str]:
    """The include paths of a compile command (`-I`, `-isystem`, `-iquote`, `-idirafter`,
    `-include`), in order, joined or separate."""
    out = []
    i = 0
    while i < len(args):
        arg = args[i]
        if arg in PATH_FLAGS:
            if i + 1 < len(args):
                out.append(args[i + 1])
            i += 2
            continue
        value = _joined(arg, PATH_FLAGS)
        if value is not None:
            out.append(value)
        i += 1
    return out


def _refused(file: str, arg: str) -> str:
    return (f"compile_commands.json: refusing the flag {arg!r} for {file}: it is not on the "
            f"allowlist for cc -E ({', '.join(PATH_FLAGS + MACRO_FLAGS + STD_PREFIXES)}); "
            "the compile driver's -c/-o/-M options are dropped, anything else is refused")


def _value(file: str, arg: str) -> str:
    """A flag's separate value. A value that starts like another option is refused: `cc`
    must never re-read `-I -Bbin` (or an `@file` expansion) as a flag Scry did not see."""
    if arg.startswith(("-", "@")):
        raise ToolError("invalid_args", _refused(file, arg))
    return arg


def _check_flags(file: str, args: list[str]) -> None:
    """Refuse a compile command word outside the preprocessor allowlist.

    `args` excludes the compiler (`argv[0]`). `-I`/`-isystem`/`-iquote`/`-idirafter`/
    `-include` (with their value), `-D`/`-U` and `-std=`/`--std=` are allowed; the
    driver's `-c`/`-o`/`-M…` structure and the source argument are dropped; every other
    word — `-B`, `-fplugin`, `-specs`, `-wrapper`, `@file`, `-Xclang`, `-cc1`,
    `-Xlinker`, `-imacros`, `--sysroot`, any other `-f…`/`-m…` — is refused by name.
    This mirrors `Scry.parseCompdbFlags` in `scry/src/Scry/Project.wiz`.
    """
    i = 0
    while i < len(args):
        arg = args[i]
        if arg.startswith("@"):
            raise ToolError("invalid_args", _refused(file, arg))
        if arg in DROPPED_FLAGS:
            i += 1
            continue
        if arg in DROPPED_VALUE_FLAGS:
            if i + 1 >= len(args):
                raise ToolError("invalid_args", f"compile_commands.json: {arg!r} needs a value")
            i += 2
            continue
        if _joined(arg, DROPPED_VALUE_FLAGS) is not None:
            i += 1
            continue
        if arg in PATH_FLAGS:
            if i + 1 >= len(args):
                raise ToolError("invalid_args", f"compile_commands.json: {arg!r} needs a value")
            _value(file, args[i + 1])
            i += 2
            continue
        if _joined(arg, PATH_FLAGS) is not None:
            i += 1
            continue
        if arg in MACRO_FLAGS:
            if i + 1 >= len(args):
                raise ToolError("invalid_args", f"compile_commands.json: {arg!r} needs a value")
            _value(file, args[i + 1])
            i += 2
            continue
        if _joined(arg, MACRO_FLAGS) is not None:
            i += 1
            continue
        if arg.startswith(STD_PREFIXES):
            i += 1
            continue
        if arg == file or arg == os.path.basename(file) or arg.endswith("/" + file):
            i += 1
            continue
        raise ToolError("invalid_args", _refused(file, arg))


def check_compdb(path: str, roots: list[str]) -> int:
    """Refuse a compile database that reaches outside the readable roots or whose flags
    are not on the `cc -E` allowlist; return its entry count."""
    try:
        with open(path, encoding="utf-8") as handle:
            entries = json.load(handle)
    except (OSError, ValueError) as exc:
        raise ToolError("invalid_args", f"cannot read the compile database {path}: {exc}") from exc
    if not isinstance(entries, list):
        raise ToolError("invalid_args", f"{path} is not a JSON array of compile commands")
    db_dir = os.path.dirname(path)
    for entry in entries:
        if not isinstance(entry, dict):
            raise ToolError("invalid_args", f"{path}: an entry is not an object")
        directory = entry.get("directory") or db_dir
        if not isinstance(directory, str):
            raise ToolError("invalid_args", f"{path}: `directory` must be a string")
        directory = os.path.normpath(os.path.join(db_dir, directory))
        confine(directory, roots, "a compile command's directory")
        file = entry.get("file")
        if not isinstance(file, str):
            raise ToolError("invalid_args", f"{path}: `file` must be a string")
        confine(os.path.normpath(os.path.join(directory, file)), roots, "a compiled file")
        if isinstance(entry.get("arguments"), list):
            args = [str(a) for a in entry["arguments"]]
        elif isinstance(entry.get("command"), str):
            try:
                args = shlex.split(entry["command"])
            except ValueError as exc:
                raise ToolError("invalid_args", f"{path}: unparsable command: {exc}") from exc
        else:
            args = []
        # `args[0]` is the compiler: Scry drops it, so it never reaches `cc -E`.
        _check_flags(file, args[1:])
        for include in _include_paths(args[1:]):
            full = os.path.normpath(os.path.join(directory, include))
            if os.path.realpath(full).startswith(SYSTEM_INCLUDE_PREFIXES):
                continue
            confine(full, roots, "an include path")
    return len(entries)


# ---------------------------------------------------------------------------
# Tools

RO = {"readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False}


def _ann(title: str) -> dict[str, Any]:
    return dict(RO, title=title)


LIMIT_PROPS = {
    "timeout": {"type": "integer", "minimum": 1, "description": "Scry's own analysis budget in seconds (at most the server's)"},
    "max_nodes": {"type": "integer", "minimum": 1},
}

TOOLS: list[dict[str, Any]] = [
    {
        "name": "scry_version",
        "annotations": _ann("Scry version"),
        "description": "The scry executable in use and its version.",
        "inputSchema": {"type": "object", "properties": {}, "additionalProperties": False},
    },
    {
        "name": "scry_taint",
        "annotations": _ann("Taint analysis of a C file"),
        "description": (
            "Run Scry's taint analysis on one C file: findings (rule, severity, message, location, "
            "source-to-sink path), boundary and memory notes, counts, and whether a budget truncated it. "
            "rules: a .scry rule pack (default: the workspace's or toolchain's default.scry). "
            "diff: a git base (e.g. HEAD~1, origin/master) to keep only findings on changed lines. "
            "The SARIF is kept as the resource result.sarif_uri."
        ),
        "inputSchema": {
            "type": "object",
            "properties": dict({
                "path": {"type": "string", "description": "a .c file in the workspace"},
                "rules": {"type": "string"},
                "diff": {"type": "string"},
                "diff_context": {"type": "integer", "minimum": 0, "maximum": 1000},
                "allow_errors": {"type": "boolean", "description": "analyse a file with parse errors"},
            }, **LIMIT_PROPS),
            "required": ["path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "scry_project",
        "annotations": _ann("Taint analysis of a C project"),
        "description": (
            "Run Scry over a C project with a compile_commands.json (cross-file taint): per-file and "
            "project findings, symbols and counts. Runs the host preprocessor (cc -E) on the project's "
            "files; the compile database must stay inside the workspace and its flags must be on the "
            "preprocessor allowlist (-I/-isystem/-iquote/-idirafter/-include, -D/-U, -std=); any other "
            "flag is refused, not stripped. The SARIF is kept as a resource."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string", "description": "the project directory"},
                "compdb": {"type": "string", "description": "the compile database (default: DIR/compile_commands.json)"},
                "rules": {"type": "string"},
                "allow_errors": {"type": "boolean"},
                "skip_broken": {"type": "boolean", "description": "skip translation units that fail to preprocess"},
            },
            "required": ["path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "scry_facts",
        "annotations": _ann("Fact store statistics"),
        "description": "Statistics of a JSON fact store: files, nodes, edges, relations, kinds.",
        "inputSchema": {
            "type": "object",
            "properties": {"path": {"type": "string"}},
            "required": ["path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "scry_query",
        "annotations": _ann("Query a fact store"),
        "description": (
            "Query a JSON fact store: give exactly one of kind (nodes of a CST kind), edge (edges with a "
            "label), edge_src (sources of edges with a label) or rel (a relation's tuples)."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "kind": {"type": "string"},
                "edge": {"type": "string"},
                "edge_src": {"type": "string"},
                "rel": {"type": "string"},
            },
            "required": ["path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "scry_explain",
        "annotations": _ann("Explain a fact-store node"),
        "description": "One node of a JSON fact store: its span, parent, children, edges and relations.",
        "inputSchema": {
            "type": "object",
            "properties": {"path": {"type": "string"}, "node": {"type": "integer", "minimum": 0}},
            "required": ["path", "node"],
            "additionalProperties": False,
        },
    },
    {
        "name": "scry_findings",
        "annotations": _ann("Findings database"),
        "description": (
            "Read the findings database (default scry-workflow/findings.json): action=list (optionally "
            "by state) or action=show with an id (the finding, its history and evidence). Never scans, "
            "triages or reproduces."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "action": {"type": "string", "enum": ["list", "show"]},
                "id": {"type": "string"},
                "state": {"type": "string", "enum": list(FINDING_STATES)},
                "db": {"type": "string"},
            },
            "required": ["action"],
            "additionalProperties": False,
        },
    },
]
TOOL_NAMES = {tool["name"] for tool in TOOLS}


class Server:
    def __init__(self, config: Config) -> None:
        self.config = config
        self.tmp = tempfile.mkdtemp(prefix="scry-mcp-")
        os.chmod(self.tmp, 0o700)
        self.runs: "OrderedDict[str, dict[str, Any]]" = OrderedDict()
        self._counter = 0
        self._lock = threading.Lock()
        self.shutting_down = False

    def close(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    # -- policy --------------------------------------------------------------

    def read_roots(self) -> list[str]:
        roots = [os.path.realpath(self.config.workspace)]
        roots += [os.path.realpath(r) for r in self.config.extra_roots]
        rules = default_rules(self.config.workspace, self.config.rules)
        if rules:
            roots.append(os.path.realpath(os.path.dirname(rules)))
        return roots

    def _path(self, args: dict[str, Any], key: str = "path", what: str = "path") -> str:
        value = args.get(key)
        if not isinstance(value, str) or not value.strip():
            raise ToolError("invalid_args", f"`{key}` must be a non-empty string")
        return confine(resolve_path(self.config.workspace, value), self.read_roots(), what)

    def _rules(self, args: dict[str, Any]) -> str:
        if args.get("rules") is not None:
            return self._path(args, "rules", "rule pack")
        rules = default_rules(self.config.workspace, self.config.rules)
        if rules is None:
            raise ToolError("invalid_args", "no default rule pack (lib/Scry/rules/default.scry) was found; pass `rules`")
        return confine(rules, self.read_roots(), "rule pack")

    def _scry(self) -> str:
        scry = resolve_scry(self.config.workspace, self.config.scry)
        if scry is None:
            raise ToolError(
                "scry_not_found",
                "no scry executable: build it (`grail build` in scry/), or pass --scry PATH or set SCRY_BIN",
            )
        return scry

    # -- running ---------------------------------------------------------------

    def _new_run_dir(self) -> tuple[str, str]:
        with self._lock:
            self._counter += 1
            run_id = f"r{self._counter}"
        directory = os.path.join(self.tmp, run_id)
        os.makedirs(os.path.join(directory, "home"), mode=0o700)
        return run_id, directory

    def _run(self, argv: list[str], run_dir: str, timeout: Optional[float] = None) -> dict[str, Any]:
        """Run scry in `run_dir` (its cwd and HOME), with a filtered environment."""
        timeout = timeout or self.config.timeout
        env = child_env(extra=self.config.pass_env)
        env["HOME"] = os.path.join(run_dir, "home")
        env["XDG_CACHE_HOME"] = os.path.join(run_dir, "home", ".cache")
        env["TMPDIR"] = run_dir
        cmd = [self._scry()] + argv
        try:
            proc = subprocess.Popen(cmd, cwd=run_dir, env=env, stdin=subprocess.DEVNULL,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                    start_new_session=True)
        except OSError as exc:
            raise ToolError("io_error", f"cannot run scry: {exc}") from exc
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            base._kill_process_group(proc)
            proc.communicate()
            raise ToolError("timeout", f"scry did not finish within {timeout:.0f}s (the process group was killed)") from exc
        except BaseException:
            base._kill_process_group(proc)
            proc.wait()
            raise
        return {"exit": proc.returncode, "stdout": stdout or "", "stderr": stderr or ""}

    def _git_diff(self, base_ref: str, file: str, out: str) -> None:
        if not DIFF_BASE.match(base_ref) or ".." in base_ref:
            raise ToolError("invalid_args", "`diff` must be a git ref or commit (e.g. HEAD~1, origin/master)")
        env = child_env()
        env["GIT_CONFIG_NOSYSTEM"] = "1"
        env["GIT_TERMINAL_PROMPT"] = "0"
        try:
            result = subprocess.run(
                ["git", "-C", self.config.workspace, "diff", "--no-ext-diff", "--no-textconv",
                 "--no-color", "-U0", "-M", base_ref, "--", file],
                env=env, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=60,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise ToolError("io_error", f"git diff failed: {exc}") from exc
        if result.returncode != 0:
            raise ToolError("invalid_args", f"git diff {base_ref} failed: {result.stderr.strip()[:500]}")
        with open(out, "w", encoding="utf-8") as handle:
            handle.write(result.stdout)

    def _keep(self, run_id: str, run_dir: str, kind: str, target: str, report: Any, sarif_path: str) -> dict[str, Any]:
        """Confine a report and its SARIF, keep both as resources, and describe the run."""
        roots = self.read_roots()
        root = target if os.path.isdir(target) else None
        withheld = confine_findings(report, roots, root)
        sarif_uri = None
        if os.path.isfile(sarif_path):
            try:
                with open(sarif_path, encoding="utf-8") as handle:
                    sarif = json.load(handle)
                confine_sarif(sarif, roots, root)
                with open(sarif_path, "w", encoding="utf-8") as handle:
                    json.dump(sarif, handle)
                sarif_uri = f"scry://runs/{run_id}/sarif"
            except (OSError, ValueError):
                sarif_uri = None
        json_path = os.path.join(run_dir, "report.json")
        with open(json_path, "w", encoding="utf-8") as handle:
            json.dump(report, handle)
        self.runs[run_id] = {"id": run_id, "kind": kind, "target": target, "json": json_path,
                             "sarif": sarif_path if sarif_uri else None}
        while len(self.runs) > MAX_RUNS:
            old, _ = self.runs.popitem(last=False)
            shutil.rmtree(os.path.join(self.tmp, old), ignore_errors=True)
        return {"run": run_id, "sarif_uri": sarif_uri, "json_uri": f"scry://runs/{run_id}/json", "withheld": withheld}

    def _json_report(self, run: dict[str, Any], what: str) -> Any:
        try:
            return json.loads(run["stdout"])
        except ValueError as exc:
            raise ToolError("scry_error", f"{what} did not produce JSON (exit {run['exit']})",
                            stderr=run["stderr"]) from exc

    # -- tools -----------------------------------------------------------------

    def call_tool(self, name: str, args: dict[str, Any]) -> dict[str, Any]:
        path = args.get("path") if isinstance(args.get("path"), str) else None
        try:
            return self._call_tool(name, args)
        except ToolError as exc:
            return error_envelope(name, exc.kind, exc.message, path=path,
                                  stdout=getattr(exc, "stdout", "") or "", stderr=getattr(exc, "stderr", "") or "")
        except Exception as exc:  # never kill the server
            log(f"scry-mcp: {name} failed: {type(exc).__name__}: {exc}")
            return error_envelope(name, "internal", f"{type(exc).__name__}: {exc}", path=path)

    def _call_tool(self, name: str, args: dict[str, Any]) -> dict[str, Any]:
        for key in args:
            schema = next(t for t in TOOLS if t["name"] == name)["inputSchema"]
            if key not in schema["properties"]:
                raise ToolError("invalid_args", f"unknown argument `{key}`")
        if name == "scry_version":
            run_id, run_dir = self._new_run_dir()
            try:
                run = self._run(["--version"], run_dir, 30)
            finally:
                shutil.rmtree(run_dir, ignore_errors=True)
            return make_envelope(name, ok=run["exit"] == 0, exit_code=run["exit"],
                                 stdout=run["stdout"], stderr=run["stderr"], result={"scry": self._scry()})
        if name == "scry_taint":
            return self._taint(args)
        if name == "scry_project":
            return self._project(args)
        if name in ("scry_facts", "scry_query", "scry_explain"):
            return self._store(name, args)
        if name == "scry_findings":
            return self._findings(args)
        raise ToolError("invalid_args", f"unknown tool {name}")

    def _limits(self, args: dict[str, Any]) -> list[str]:
        out = []
        budget = args.get("timeout")
        if budget is not None:
            if isinstance(budget, bool) or not isinstance(budget, int) or budget < 1:
                raise ToolError("invalid_args", "`timeout` must be a positive integer")
            out += ["--timeout", str(min(budget, int(self.config.timeout)))]
        else:
            out += ["--timeout", str(int(self.config.timeout))]
        nodes = args.get("max_nodes")
        if nodes is not None:
            if isinstance(nodes, bool) or not isinstance(nodes, int) or nodes < 1:
                raise ToolError("invalid_args", "`max_nodes` must be a positive integer")
            out += ["--max-nodes", str(nodes)]
        return out

    def _taint(self, args: dict[str, Any]) -> dict[str, Any]:
        path = self._path(args)
        if not os.path.isfile(path):
            raise ToolError("invalid_args", f"{path} is not a file")
        rules = self._rules(args)
        run_id, run_dir = self._new_run_dir()
        sarif = os.path.join(run_dir, "report.sarif")
        argv = ["taint", path, "--rules", rules, "--json", "--sarif", sarif] + self._limits(args)
        if base._optional_bool(args, "allow_errors"):
            argv.append("--allow-errors")
        diff = args.get("diff")
        if diff is not None:
            if not isinstance(diff, str):
                raise ToolError("invalid_args", "`diff` must be a string")
            if diff == "all":
                argv += ["--diff", "all"]
            else:
                changed = os.path.join(run_dir, "changed.diff")
                self._git_diff(diff, path, changed)
                argv += ["--changed-lines", changed]
            context = args.get("diff_context")
            if context is not None:
                if isinstance(context, bool) or not isinstance(context, int) or not 0 <= context <= 1000:
                    raise ToolError("invalid_args", "`diff_context` must be an integer between 0 and 1000")
                argv += ["--diff-context", str(context)]
        elif args.get("diff_context") is not None:
            raise ToolError("invalid_args", "`diff_context` needs `diff`")
        run = self._run(argv, run_dir)
        if run["exit"] != 0 and not run["stdout"].lstrip().startswith("{"):
            shutil.rmtree(run_dir, ignore_errors=True)
            return make_envelope("scry_taint", ok=False, path=path, exit_code=run["exit"], stdout=run["stdout"],
                                 stderr=run["stderr"], error={"kind": "scry_error", "message": _first_line(run["stderr"])})
        report = self._json_report(run, "scry taint")
        if isinstance(report, dict) and isinstance(report.get("diff"), dict) and diff is not None:
            report["diff"]["argument"] = f"--diff {diff}"  # not the private temp file
        kept = self._keep(run_id, run_dir, "taint", path, report, sarif)
        return make_envelope("scry_taint", ok=run["exit"] == 0, path=path, exit_code=run["exit"],
                             stderr=_quiet(run["stderr"]), result=dict(report, **{"_run": kept}))

    def _project(self, args: dict[str, Any]) -> dict[str, Any]:
        path = self._path(args, what="project directory")
        if not os.path.isdir(path):
            raise ToolError("invalid_args", f"{path} is not a directory")
        compdb = self._path(args, "compdb", "compile database") if args.get("compdb") is not None \
            else os.path.join(path, "compile_commands.json")
        if not os.path.isfile(compdb):
            raise ToolError("invalid_args", f"no compile database at {compdb}")
        confine(compdb, self.read_roots(), "compile database")
        units = check_compdb(compdb, self.read_roots())
        rules = self._rules(args)
        run_id, run_dir = self._new_run_dir()
        sarif = os.path.join(run_dir, "report.sarif")
        argv = ["project", path, "--compdb", compdb, "--taint", "--rules", rules, "--json", "--sarif", sarif]
        if base._optional_bool(args, "allow_errors"):
            argv.append("--allow-errors")
        if base._optional_bool(args, "skip_broken"):
            argv.append("--skip-broken")
        run = self._run(argv, run_dir)
        if not run["stdout"].lstrip().startswith("{"):
            shutil.rmtree(run_dir, ignore_errors=True)
            return make_envelope("scry_project", ok=False, path=path, exit_code=run["exit"], stdout=run["stdout"],
                                 stderr=run["stderr"], error={"kind": "scry_error", "message": _first_line(run["stderr"])})
        report = self._json_report(run, "scry project")
        kept = self._keep(run_id, run_dir, "project", path, report, sarif)
        kept["units"] = units
        return make_envelope("scry_project", ok=run["exit"] == 0, path=path, exit_code=run["exit"],
                             stderr=_quiet(run["stderr"]), result=dict(report, **{"_run": kept}))

    def _store(self, name: str, args: dict[str, Any]) -> dict[str, Any]:
        path = self._path(args)
        if not os.path.isfile(path):
            raise ToolError("invalid_args", f"{path} is not a file")
        if name == "scry_facts":
            argv = ["facts", path]
        elif name == "scry_explain":
            node = args.get("node")
            if isinstance(node, bool) or not isinstance(node, int) or node < 0:
                raise ToolError("invalid_args", "`node` must be a non-negative integer")
            argv = ["explain", path, str(node)]
        else:
            given = [(k, args[k]) for k in ("kind", "edge", "edge_src", "rel") if args.get(k) is not None]
            if len(given) != 1:
                raise ToolError("invalid_args", "give exactly one of kind, edge, edge_src and rel")
            key, value = given[0]
            if not isinstance(value, str) or not value.strip() or value.startswith("-"):
                raise ToolError("invalid_args", f"`{key}` must be a name")
            argv = ["query", path, "--" + key.replace("_", "-"), value]
        _, run_dir = self._new_run_dir()
        try:
            run = self._run(argv, run_dir, min(self.config.timeout, 120))
        finally:
            shutil.rmtree(run_dir, ignore_errors=True)
        ok = run["exit"] == 0
        return make_envelope(name, ok=ok, path=path, exit_code=run["exit"], stdout=run["stdout"], stderr=run["stderr"],
                             error=None if ok else {"kind": "scry_error", "message": _first_line(run["stderr"])})

    def _findings(self, args: dict[str, Any]) -> dict[str, Any]:
        action = args.get("action")
        if action not in ("list", "show"):
            raise ToolError("invalid_args", "`action` must be list or show")
        db = self._path(args, "db", "findings database") if args.get("db") is not None else \
            confine(os.path.join(self.config.workspace, "scry-workflow", "findings.json"), self.read_roots(), "findings database")
        argv = ["findings", action]
        if action == "show":
            finding = args.get("id")
            if not isinstance(finding, str) or not FINDING_ID.match(finding) or finding.startswith("-"):
                raise ToolError("invalid_args", "`show` needs an `id` such as f_db2e1eccee6d902d")
            argv.append(finding)
        elif args.get("id") is not None:
            raise ToolError("invalid_args", "`id` is only for show")
        state = args.get("state")
        if state is not None:
            if action != "list" or state not in FINDING_STATES:
                raise ToolError("invalid_args", f"`state` is for list and one of {', '.join(FINDING_STATES)}")
            argv += ["--state", state]
        if not os.path.isfile(db):
            if action == "list":
                return make_envelope("scry_findings", path=db, result={"findings": [], "withheld": 0, "db": "absent"})
            raise ToolError("not_found", f"no findings database at {db}")
        argv += ["--db", db, "--json"]
        _, run_dir = self._new_run_dir()
        try:
            run = self._run(argv, run_dir, min(self.config.timeout, 120))
        finally:
            shutil.rmtree(run_dir, ignore_errors=True)
        if run["exit"] != 0:
            return make_envelope("scry_findings", ok=False, path=db, exit_code=run["exit"], stderr=run["stderr"],
                                 error={"kind": "scry_error", "message": _first_line(run["stderr"])})
        report = self._json_report(run, "scry findings")
        roots = self.read_roots()
        withheld = 0
        items = report if isinstance(report, list) else [report]
        kept = []
        for item in items:
            source = item.get("source") if isinstance(item, dict) else None
            if isinstance(source, str) and os.path.isabs(source) and not base._allowed(source, roots):
                withheld += 1
            else:
                kept.append(item)
        if action == "show":
            if not kept:
                raise ToolError("path_denied", "that finding's source is outside the readable roots")
            return make_envelope("scry_findings", path=db, result=kept[0])
        return make_envelope("scry_findings", path=db, result={"findings": kept, "withheld": withheld})

    # -- resources -------------------------------------------------------------

    def list_resources(self) -> list[dict[str, Any]]:
        out = []
        for run in reversed(self.runs.values()):
            label = f"{run['kind']} {os.path.relpath(run['target'], self.config.workspace)}"
            if run["sarif"]:
                out.append({"uri": f"scry://runs/{run['id']}/sarif", "name": f"SARIF: {label}",
                            "mimeType": "application/sarif+json"})
            out.append({"uri": f"scry://runs/{run['id']}/json", "name": f"Report: {label}",
                        "mimeType": "application/json"})
        return out

    def read_resource(self, uri: str) -> list[dict[str, Any]]:
        match = re.fullmatch(r"scry://runs/(r[0-9]+)/(sarif|json)", uri)
        if not match or match.group(1) not in self.runs:
            raise ToolError("not_found", f"unknown resource {uri} (runs are kept until the server exits, at most {MAX_RUNS})")
        run = self.runs[match.group(1)]
        path = run["sarif"] if match.group(2) == "sarif" else run["json"]
        if not path:
            raise ToolError("not_found", f"run {run['id']} has no SARIF")
        with open(path, encoding="utf-8") as handle:
            text = handle.read()
        mime = "application/sarif+json" if match.group(2) == "sarif" else "application/json"
        return [{"uri": uri, "mimeType": mime, "text": text}]

    # -- MCP dispatch ------------------------------------------------------------

    def dispatch(self, message: dict[str, Any]) -> tuple[list[dict[str, Any]], bool]:
        method = message.get("method")
        msg_id = message.get("id")
        params = message.get("params") if isinstance(message.get("params"), dict) else {}
        if method == "initialize":
            requested = params.get("protocolVersion")
            version = requested if requested in base.SUPPORTED_PROTOCOLS else base.PROTOCOL_VERSION
            return [reply(msg_id, {
                "protocolVersion": version,
                "capabilities": {"tools": {"listChanged": False},
                                 "resources": {"listChanged": False, "subscribe": False}},
                "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
                "instructions": INSTRUCTIONS,
            })], False
        if method in ("notifications/initialized", "notifications/cancelled"):
            return [], False
        if method == "ping":
            return [reply(msg_id, {})], False
        if method == "tools/list":
            return [reply(msg_id, {"tools": TOOLS})], False
        if method == "resources/list":
            return [reply(msg_id, {"resources": self.list_resources()})], False
        if method == "resources/templates/list":
            return [reply(msg_id, {"resourceTemplates": [
                {"uriTemplate": "scry://runs/{run}/sarif", "name": "A run's SARIF", "mimeType": "application/sarif+json"},
                {"uriTemplate": "scry://runs/{run}/json", "name": "A run's JSON report", "mimeType": "application/json"},
            ]})], False
        if method == "resources/read":
            uri = params.get("uri")
            if not isinstance(uri, str):
                return [reply_error(msg_id, -32602, "resources/read needs a uri")], False
            try:
                return [reply(msg_id, {"contents": self.read_resource(uri)})], False
            except ToolError as exc:
                return [reply_error(msg_id, -32002, f"{exc.kind}: {exc.message}")], False
        if method == "tools/call":
            name = params.get("name")
            arguments = params.get("arguments") or {}
            if not isinstance(name, str) or name not in TOOL_NAMES:
                return [reply_error(msg_id, -32602, f"unknown tool {name!r}")], False
            if not isinstance(arguments, dict):
                return [reply_error(msg_id, -32602, "tools/call arguments must be an object")], False
            envelope = self.call_tool(name, arguments)
            return [reply(msg_id, {"content": [{"type": "text", "text": envelope_text(envelope)}],
                                   "isError": not envelope["ok"], "structuredContent": envelope})], False
        if method == "shutdown":
            self.shutting_down = True
            return [reply(msg_id, {})], False
        if method == "exit":
            return [], True
        if msg_id is not None:
            return [reply_error(msg_id, -32601, f"{method} is not supported")], False
        return [], False

    def serve(self, stdin: Any, stdout: Any) -> None:
        for message in iter_messages(stdin):
            try:
                responses, stop = self.dispatch(message)
            except Exception as exc:
                log(f"scry-mcp: dispatch failed: {type(exc).__name__}: {exc}")
                responses, stop = ([reply_error(message.get("id"), -32603, "internal error")] if "id" in message else []), False
            for response in responses:
                write_message(stdout, response)
            if stop:
                break


def _first_line(text: str) -> str:
    for line in text.splitlines():
        if line.strip():
            return line.strip()[:500]
    return "scry failed"


def _quiet(stderr: str) -> str:
    """Scry's progress lines (`wrote SARIF …`) name the private temp dir; keep the rest."""
    return "\n".join(line for line in stderr.splitlines() if not line.startswith("wrote SARIF"))


def parse_args(argv: Optional[list[str]] = None) -> Config:
    parser = argparse.ArgumentParser(description="Read-only MCP server for Scry (stdio).")
    parser.add_argument("--workspace", default=os.getcwd())
    parser.add_argument("--scry", help="the scry executable (default: $SCRY_BIN, scry/.grail/bin/scry, PATH)")
    parser.add_argument("--rules", help="the default rule pack (default: lib/Scry/rules/default.scry)")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT)
    parser.add_argument("--allow-root", action="append", default=[], metavar="DIR")
    parser.add_argument("--pass-env", action="append", default=[], metavar="NAME")
    args = parser.parse_args(argv)
    workspace = os.path.abspath(os.path.expanduser(args.workspace))
    if not os.path.isdir(workspace):
        parser.error(f"--workspace is not a directory: {workspace}")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    for root in args.allow_root:
        if not os.path.isdir(root):
            parser.error(f"--allow-root is not a directory: {root}")
    return Config(workspace=workspace, scry=args.scry, rules=args.rules, timeout=args.timeout,
                  extra_roots=tuple(os.path.abspath(r) for r in args.allow_root), pass_env=tuple(args.pass_env))


def main(argv: Optional[list[str]] = None) -> int:
    config = parse_args(argv)
    server = Server(config)
    atexit.register(server.close)
    log(f"scry-mcp: workspace={config.workspace} scry={resolve_scry(config.workspace, config.scry) or 'not found'} "
        f"rules={default_rules(config.workspace, config.rules) or 'not found'}")

    def stop(_signum: int, _frame: Any) -> None:
        raise SystemExit(0)

    for sig in (signal.SIGTERM, signal.SIGINT, getattr(signal, "SIGHUP", None)):
        if sig is not None:
            try:
                signal.signal(sig, stop)
            except (ValueError, OSError):
                pass
    try:
        server.serve(sys.stdin, sys.stdout)
    finally:
        server.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
