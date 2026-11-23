#!/usr/bin/env python3
"""Summarize one llvm-cov run over a Wiz program's generated C.

The driver (`wiz-c-coverage.sh`) builds with `-fprofile-instr-generate
-fcoverage-mapping`, captures the generated `main.c`, runs the program, and writes
`report.txt`, `functions.txt`, `show.txt` and `export.json`. This script reads those
and prints:

  * the whole-file figures llvm-cov itself reports (the runtime is pasted into the
    same file, so these are dominated by runtime code the program never calls);
  * the *generated* section, from the `/* ---- foreign functions ---- */` marker that
    `Wiz/Compiler/C.lean` emits (the runtime is before it, every Wiz declaration after
    it), for regions and lines;
  * how many generated functions executed, and their demangled Wiz names.

There is no line mapping to `.wiz`: `grep -c '^#line' main.c` is 0 for the C backend
(only `Wiz/Compiler/Bpf/C.lean` emits `#line`). The numbers are generated-C coverage.

Usage:
  wiz-c-coverage.py --c main.c --export export.json --show show.txt \
      [--report report.txt] [--exit-code N] [--json]

Exit status: 0 when the inputs parsed, 2 usage/IO.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

MARKER = "/* ---- foreign functions ---- */"


def fail(msg: str) -> "NoReturn":  # type: ignore[name-defined]
    print(f"wiz-c-coverage: {msg}", file=sys.stderr)
    raise SystemExit(2)


def decode(mangled: str) -> str:
    """Undo `Wiz.C.mangle`: `_xx` is a byte in hex; letters and digits stay."""
    # llvm-cov qualifies a function with its file when the binary has more than one
    # source (`main.c:w_steps`); the colon cannot be part of the mangled name.
    mangled = mangled.rsplit(":", 1)[-1]
    for prefix in ("wiz_ext_", "w_"):
        if mangled.startswith(prefix):
            body = mangled[len(prefix) :]
            break
    else:
        return mangled
    out = bytearray()
    i = 0
    while i < len(body):
        if (
            body[i] == "_"
            and i + 3 < len(body)
            and body[i + 3] == "_"
            and all(c in "0123456789abcdefABCDEF" for c in body[i + 1 : i + 3])
        ):
            out.append(int(body[i + 1 : i + 3], 16))
            i += 4
        else:
            out.append(ord(body[i]))
            i += 1
    return out.decode("utf-8", "replace")


def section_line(cpath: Path) -> int:
    for i, line in enumerate(cpath.read_text(encoding="utf-8").splitlines(), 1):
        if MARKER in line:
            return i
    fail(f"no {MARKER!r} marker in {cpath}; is this a C-backend output?")


DEF = re.compile(
    r"^\s*(?:static\s+|WIZ_API\s+)*(?:[A-Za-z_][\w ]*?)\s+"
    r"(\w+)\s*\([^;]*\)\s*\{"
)


def definitions(cpath: Path) -> dict[str, int]:
    """Function name -> 1-based definition line, from the generated C."""
    out: dict[str, int] = {}
    for i, line in enumerate(cpath.read_text(encoding="utf-8").splitlines(), 1):
        m = DEF.match(line)
        if m and m.group(1) not in out:
            out[m.group(1)] = i
    return out


def pct(hit: int, total: int) -> float:
    return 100.0 * hit / total if total else 0.0


def whole_file(export: dict, cpath: Path) -> dict:
    files = export["data"][0]["files"]
    name = str(cpath)
    for f in files:
        if (
            Path(f["filename"]) == cpath
            or f["filename"].endswith(name)
            or Path(f["filename"]).name == cpath.name
        ):
            s = f["summary"]
            return {
                "regions": s["regions"]["count"],
                "regions_hit": s["regions"]["covered"],
                "lines": s["lines"]["count"],
                "lines_hit": s["lines"]["covered"],
                "functions": s["functions"]["count"],
                "functions_hit": s["functions"]["covered"],
            }
    fail(f"{cpath} is not in the export")


def generated(export: dict, cpath: Path, section: int) -> tuple[dict, list[dict]]:
    """Functions whose first region starts at/after the generated marker."""
    fns = export["data"][0]["functions"]
    seen: dict[str, dict] = {}
    for f in fns:
        regions = f.get("regions") or []
        if not regions:
            continue
        # The first region is the function's own body; later regions with fileID > 0
        # are inlined instantiations in other files and are not part of this count.
        if regions[0][0] < section:
            continue
        name = f["name"]
        if name in seen:
            continue
        own = [r for r in regions if r[5] == 0]
        seen[name] = {
            "name": name,
            "line": regions[0][0],
            "regions": len(own),
            "regions_hit": sum(1 for r in own if r[4] > 0),
            "executed": any(r[4] > 0 for r in regions),
        }
    funcs = sorted(seen.values(), key=lambda f: f["line"])
    return {
        "functions": len(funcs),
        "functions_hit": sum(1 for f in funcs if f["executed"]),
        "regions": sum(f["regions"] for f in funcs),
        "regions_hit": sum(f["regions_hit"] for f in funcs),
    }, funcs


SHOW = re.compile(r"^\s*(\d+)\|([^|]*)\|")


def count_value(text: str) -> int:
    """llvm-cov abbreviates large counts (`14.9k`); only zero/nonzero matters."""
    text = text.strip()
    if not text:
        return 0
    mult = 1
    if text[-1] in "kM":
        mult = 1000 if text[-1] == "k" else 1_000_000
        text = text[:-1]
    return int(float(text) * mult)


def show_lines(show: Path, start: int = 0, stop: int | None = None) -> tuple[int, int]:
    hit = total = 0
    for line in show.read_text(encoding="utf-8", errors="replace").splitlines():
        m = SHOW.match(line)
        if not m:
            continue
        n = int(m.group(1))
        if n < start or (stop is not None and n > stop):
            continue
        count = m.group(2).strip()
        if not count:
            continue
        total += 1
        if count_value(count) > 0:
            hit += 1
    return hit, total


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--c", required=True, type=Path)
    ap.add_argument("--export", required=True, type=Path)
    ap.add_argument("--show", required=True, type=Path)
    ap.add_argument("--report", type=Path)
    ap.add_argument("--exit-code", type=int)
    ap.add_argument("--json", action="store_true", help="print one JSON object")
    args = ap.parse_args()

    section = section_line(args.c)
    defs = definitions(args.c)
    export = json.loads(args.export.read_text(encoding="utf-8"))
    whole = whole_file(export, args.c)
    gen, funcs = generated(export, args.c, section)
    file_lines = show_lines(args.show)
    gen_lines = show_lines(args.show, section)

    source_lines = args.c.read_text(encoding="utf-8").splitlines()
    has_line = sum(1 for l in source_lines if l.startswith("#line"))
    c_lines = len(source_lines)

    result = {
        "c_file": str(args.c),
        "c_lines": c_lines,
        "has_line_directives": has_line,
        "generated_marker_line": section,
        "program_exit": args.exit_code,
        "whole": {
            **whole,
            "lines_from_show": file_lines[1],
            "lines_hit_from_show": file_lines[0],
        },
        "generated": {
            **gen,
            "lines": gen_lines[1],
            "lines_hit": gen_lines[0],
        },
        "executed": [
            {"name": f["name"], "wiz": decode(f["name"]), "line": f["line"]}
            for f in funcs
            if f["executed"]
        ],
    }

    if args.json:
        print(json.dumps(result, indent=1))
        return 0

    w = result["whole"]
    g = result["generated"]
    print(f"generated C: {args.c} ({c_lines} lines; {has_line} #line directives)")
    if args.exit_code is not None:
        print(f"program exit: {args.exit_code}")
    print()
    print("whole file (runtime + generated; llvm-cov summary):")
    print(
        f"  regions {w['regions_hit']}/{w['regions']} = {pct(w['regions_hit'], w['regions']):.2f}%"
        f"   lines {w['lines_hit']}/{w['lines']} = {pct(w['lines_hit'], w['lines']):.2f}%"
        f"   functions {w['functions_hit']}/{w['functions']} = {pct(w['functions_hit'], w['functions']):.2f}%"
    )
    print(f"  (llvm-cov show: {file_lines[0]}/{file_lines[1]} executable lines hit)")
    print()
    print(f"generated section (line {section} on: the Wiz declarations, not the runtime):")
    print(
        f"  regions {g['regions_hit']}/{g['regions']} = {pct(g['regions_hit'], g['regions']):.2f}%"
        f"   lines {g['lines_hit']}/{g['lines']} = {pct(g['lines_hit'], g['lines']):.2f}%"
        f"   functions {g['functions_hit']}/{g['functions']} = {pct(g['functions_hit'], g['functions']):.2f}%"
    )
    print()
    print("executed generated functions (demangled Wiz name):")
    for f in result["executed"]:
        print(f"  line {f['line']:5d}  {f['wiz']}")
    print()
    print("NOTE: no #line directives point at .wiz source, so this is generated-C")
    print("coverage. A Wiz line/region number needs a compiler change (see the note).")
    if args.report and args.report.exists():
        print()
        print(f"raw report: {args.report}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
