#!/usr/bin/env python3
"""Split the old monolithic Tests/Elab.lean into one module per test group.

  scripts/migrate-tests.py [ELAB.lean]

Reads ELAB.lean (default: Tests/Elab.lean) in the OLD layout (every group of the module
in the one file, listed in its `def groups`) and writes

  Tests/Elab.lean            the helpers that several groups (or other modules) use
  Tests/Groups/<Name>.lean   one per group: the group, the helpers only it uses, and
                             `builtin_initialize registerGroup <group>` (Tests/Harness.lean)

The split is deterministic: it is how PR "conflict-free test registration" made the new
layout, so a branch that still edits the old file gets the same layout by running it on
its own version (see AGENTS.md, "Test layout"):

  git show HEAD:Tests/Elab.lean > /tmp/old-elab.lean    # your branch's old-layout file
  scripts/migrate-tests.py /tmp/old-elab.lean

How it splits: a top-level declaration (with its doc comment) is a chunk; `namespace X
… end X` (other than Tests.Elab) is one chunk. A `def …Group : Group` chunk goes to its
group's file, named after the definition (`ffiStructGroup` → FfiStruct.lean, `group` →
Elab.lean). Any other chunk goes to the one group whose chunks (transitively) mention
the names it defines, and stays in Tests/Elab.lean if several do, if another module
(Tests/*.lean, scripts/GenSelfhost.lean) mentions them, or if it defines no name
(instances, syntax, attributes). Mentions are found by name, also inside strings, so
the split errs on the side of sharing.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TESTS = os.path.join(ROOT, "Tests")
GROUPS = os.path.join(TESTS, "Groups")

HEADER_SHARED = """import Wiz
import Tests.Harness

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false
"""

HEADER_GROUP = """import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false
"""

IDCHAR = re.compile(r"[\w'.!?]")


def line_states(text):
    """For each line, whether it starts in plain code (not inside a string or comment)."""
    states = []
    i, n = 0, len(text)
    mode = "code"  # code | str | raw | comment
    depth = 0
    hashes = 0
    states.append(True)
    while i < n:
        c = text[i]
        if c == "\n":
            states.append(mode == "code")
            i += 1
            continue
        if mode == "code":
            if text.startswith("--", i):
                j = text.find("\n", i)
                i = n if j < 0 else j
                continue
            if text.startswith("/-", i):
                mode, depth = "comment", 1
                i += 2
                continue
            m = re.match(r'r(#*)"', text[i:i + 20])
            if m and (i == 0 or not IDCHAR.match(text[i - 1])):
                mode, hashes = "raw", len(m.group(1))
                i += len(m.group(0))
                continue
            if c == '"':
                mode = "str"
                i += 1
                continue
            if c == "'" and (i == 0 or not IDCHAR.match(text[i - 1])):
                m = re.match(r"'(\\u\{[0-9a-fA-F]+\}|\\x[0-9a-fA-F]{2}|\\.|[^\\'\n])'", text[i:i + 12])
                if m:
                    i += len(m.group(0))
                    continue
            i += 1
        elif mode == "str":
            if c == "\\":
                i += 2
                continue
            if c == '"':
                mode = "code"
            i += 1
        elif mode == "raw":
            if c == '"' and text.startswith("#" * hashes, i + 1):
                mode = "code"
                i += 1 + hashes
                continue
            i += 1
        else:  # comment
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
                if depth == 0:
                    mode = "code"
            else:
                i += 1
    return states


DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                  r"(def|abbrev|theorem|structure|inductive|class|instance|opaque|axiom)\b\s*([^\s:({\[]*)")
START = re.compile(r"^(def|abbrev|theorem|structure|inductive|class|instance|opaque|axiom|private|protected|"
                   r"noncomputable|partial|unsafe|namespace|end|open|set_option|syntax|macro|macro_rules|elab|"
                   r"attribute|local|scoped|deriving|initialize|section|variable|mutual|example|#eval|#check|@\[)")
LEAD = re.compile(r"^(/--|/-!|--|@\[|open .* in\s*$|set_option .* in\s*$)")


class Chunk:
    def __init__(self, lines):
        self.lines = lines
        self.text = "".join(lines)
        self.names = set()
        self.group = None  # the def name, for a group chunk
        self.dest = None


def chunks_of(text):
    lines = text.splitlines(keepends=True)
    states = line_states(text)
    # the start of each top-level command (with its leading comments)
    starts = []
    for k, l in enumerate(lines):
        if not states[k] or not l[:1].strip():
            continue
        if l.startswith("/-") or l.startswith("--") or START.match(l):
            starts.append(k)
    # a leading comment, attribute or `open … in` belongs to the command after it, unless
    # a blank line separates them (a section header `/-! … -/` belongs to the next
    # command anyway)
    bounds = []
    for s, k in enumerate(starts):
        if s > 0:
            p = starts[s - 1]
            lead = LEAD.match(lines[p]) and not DECL.match(lines[p])
            blank = any(states[j] and not lines[j].strip() for j in range(p, k))
            if lead and (not blank or lines[p].startswith("/-!")):
                continue
        bounds.append(k)
    # the chunks: from each bound to the next; namespace X … end X kept whole
    res = []
    b = 0
    while b < len(bounds):
        lo = bounds[b]
        m = re.match(r"^namespace (\S+)", lines[lo])
        if m and m.group(1) != "Tests.Elab":
            ns = m.group(1)
            hi = next(k for k in range(lo + 1, len(lines)) if states[k] and lines[k].strip() == f"end {ns}")
            # skip the bounds inside
            b2 = b + 1
            while b2 < len(bounds) and bounds[b2] <= hi:
                b2 += 1
            res.append((lo, hi + 1))
            b = b2
            continue
        hi = bounds[b + 1] if b + 1 < len(bounds) else len(lines)
        res.append((lo, hi))
        b += 1
    return lines, res


def tokens(text):
    out = set()
    for t in re.findall(r"[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*", text):
        out.add(t)
        out.update(t.split("."))
    return out


def file_name(defname):
    if defname == "group":
        return "Elab"
    base = defname[:-len("Group")] if defname.endswith("Group") else defname
    return base[:1].upper() + base[1:]


def split(path):
    text = open(path).read()
    lines, spans = chunks_of(text)
    chunks = []
    for lo, hi in spans:
        first = lines[lo]
        # drop the file's header and the namespace Tests.Elab brackets, and `def groups`
        if lo == 0 or re.match(r"^(import|open Wiz\s*$|set_option compiler\.extract_closed)", first):
            continue
        body = lines[lo:hi]
        # strip bracket lines inside the chunk (they end a chunk's tail)
        body = [l for l in body if l.strip() not in ("namespace Tests.Elab", "end Tests.Elab")]
        if not "".join(body).strip():
            continue
        c = Chunk(body)
        decl_line = next((l for l in body if DECL.match(l)), None)
        ns = re.match(r"^namespace (\S+)", body[0])
        if ns:
            c.names.add(ns.group(1))
        elif decl_line:
            d = DECL.match(decl_line)
            kind, name = d.group(1), d.group(2)
            if name and kind != "instance":
                c.names.add(name)
            if re.match(r"^def (\w+) : Group\b", decl_line):
                c.group = name
        chunks.append(c)
    groups_def = [c for c in chunks if "def groups : List Group" in c.text]
    listed = re.findall(r"^\s+(\w+) ::", groups_def[0].text, re.M) if groups_def else []
    chunks = [c for c in chunks if c not in groups_def]
    group_defs = {c.group for c in chunks if c.group}
    if set(listed) != group_defs:
        sys.exit(f"the groups listed in `def groups` {sorted(set(listed) ^ group_defs)} differ from the `: Group` definitions")
    # the names that other modules mention stay shared
    pinned = set()
    for f in sorted(os.listdir(TESTS)):
        p = os.path.join(TESTS, f)
        if f.endswith(".lean") and f not in ("Elab.lean", "Groups.lean") and os.path.abspath(p) != os.path.abspath(path):
            pinned |= tokens(open(p).read())
    gen = os.path.join(ROOT, "scripts", "GenSelfhost.lean")
    if os.path.exists(gen):
        pinned |= tokens(open(gen).read())
    toks = [tokens(c.text) for c in chunks]
    for c in chunks:
        if c.group:
            c.dest = c.group
    # later chunks first: a chunk's users come after it
    for k in range(len(chunks) - 1, -1, -1):
        c = chunks[k]
        if c.group:
            continue
        if not c.names or c.names & pinned:
            c.dest = "shared"
            continue
        users = {chunks[j].dest for j in range(k + 1, len(chunks)) if c.names & toks[j]}
        c.dest = users.pop() if len(users) == 1 else "shared"
        if c.dest is None:  # used by nothing: keep it where it was
            c.dest = "shared"
    # a group chunk must not mention another group's chunks
    for k, c in enumerate(chunks):
        if c.group:
            for j in range(k):
                if chunks[j].dest not in ("shared", c.group) and chunks[j].names & toks[k]:
                    sys.exit(f"{c.group} uses {sorted(chunks[j].names)} of {chunks[j].dest}")
    os.makedirs(GROUPS, exist_ok=True)

    def emit(cs):
        out = []
        for c in cs:
            body = "".join(c.lines).rstrip("\n") + "\n"
            out.append(body)
        return "\n".join(out)

    shared = [c for c in chunks if c.dest == "shared"]
    with open(os.path.join(TESTS, "Elab.lean"), "w") as f:
        f.write(HEADER_SHARED + "\n/-! The helpers of the elaboration tests that several groups use. Each group is a\n"
                "module of its own, `Tests/Groups/<Name>.lean` (see `Tests/Harness.lean`,\n"
                "`registerGroup`). -/\n\nnamespace Tests.Elab\n\n" + emit(shared) + "\nend Tests.Elab\n")
    written = []
    for g in sorted(group_defs):
        cs = [c for c in chunks if c.dest == g]
        fn = file_name(g) + ".lean"
        written.append(fn)
        with open(os.path.join(GROUPS, fn), "w") as f:
            f.write(HEADER_GROUP + "\nnamespace Tests.Elab\n\n" + emit(cs) +
                    f"\nbuiltin_initialize registerGroup {g}\n\nend Tests.Elab\n")
    print(f"Tests/Elab.lean: {len(shared)} shared chunks; {len(written)} group modules in Tests/Groups/")
    return 0


if __name__ == "__main__":
    sys.exit(split(sys.argv[1] if len(sys.argv) > 1 else os.path.join(TESTS, "Elab.lean")))
