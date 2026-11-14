#!/usr/bin/env python3
"""Run `wiz lint` in CI: changed `lib/**/*.wiz` and `selfhost/*.wiz` files, compared with
a checked-in baseline of the warnings that are already known.

  scripts/lint-baseline.py check [--wiz BIN] [--baseline FILE] [FILES…]
                                     lint the files (default: all linted files) and fail
                                     (exit 1) on an elaboration error or on a warning
                                     that is not in the baseline (`--deny` semantics,
                                     minus the known warnings). Prints GitHub error
                                     annotations for the new ones.
  scripts/lint-baseline.py update [--wiz BIN] [--baseline FILE] [FILES…]
                                     write the baseline of the files (default: all), so
                                     a warning that is there today counts as known
  scripts/lint-baseline.py changed [--base REV]
                                     the linted files that differ from REV (a pull
                                     request's base, or a push's `before`); all of them
                                     when REV is empty, all zeros, or not a commit
  scripts/lint-baseline.py files    the linted files, one per line

The baseline (`.github/lint-baseline.tsv`) is one warning per line:
`COUNT<TAB>FILE<TAB>RULE<TAB>MESSAGE`. Positions are not part of it, so moving a line does
not create a warning; a count may go down without a refresh (it is reported as stale, not
as a failure). Messages are escaped (`\\`, `\\t`, `\\n`) so a line stays one line.

`selfhost/*.wiz` are concatenated into one program (`Wiz/Selfhost.lean`), so a fragment
usually does not elaborate on its own: it is skipped with a notice, and the `selfhost`
shards (which compile the concatenation) remain its gate. A fragment that does parse is
linted like a library file.

The linter is advisory in CI (`.github/workflows/lint.yml`): it is not part of `CI result`
and does not block a merge. Refresh the baseline with
`python3 scripts/lint-baseline.py update`, from the checkout with the `.lake` build.
"""
import json
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BASELINE = ROOT / ".github" / "lint-baseline.tsv"
DEFAULT_WIZ = ROOT / ".lake" / "build" / "bin" / "wiz"


def lint_file(path):
    """Is `path` (relative to the repository root) one of the files ward runs on?"""
    p = str(path).replace(os.sep, "/")
    if p.startswith("lib/") and p.endswith(".wiz"):
        return True
    if p.startswith("selfhost/") and p.endswith(".wiz"):
        return "/" not in p[len("selfhost/"):]
    return False


def all_files():
    files = [p.relative_to(ROOT).as_posix() for p in (ROOT / "lib").rglob("*.wiz")]
    files += [p.relative_to(ROOT).as_posix() for p in (ROOT / "selfhost").glob("*.wiz")]
    return sorted(files)


def escape(s):
    return s.replace("\\", "\\\\").replace("\t", "\\t").replace("\n", "\\n")


def unescape(s):
    out, i = [], 0
    while i < len(s):
        if s[i] == "\\" and i + 1 < len(s):
            c = s[i + 1]
            out.append({"t": "\t", "n": "\n", "\\": "\\"}.get(c, "\\" + c))
            i += 2
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def read_baseline(path):
    counts = Counter()
    if not path.exists():
        return counts
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t", 3)
        if len(parts) != 4:
            sys.exit(f"{path}: not COUNT<TAB>FILE<TAB>RULE<TAB>MESSAGE: {line!r}")
        count, file, rule, message = parts
        counts[(file, rule, unescape(message))] += int(count)
    return counts


def write_baseline(path, counts):
    lines = [
        "# ward (wiz lint) baseline: the warnings that are known today, so CI fails only",
        "# on new ones. COUNT<TAB>FILE<TAB>RULE<TAB>MESSAGE; positions are left out, so",
        "# moving a line does not make a warning new.",
        "# Refresh: python3 scripts/lint-baseline.py update",
    ]
    for (file, rule, message), count in sorted(counts.items()):
        lines.append(f"{count}\t{file}\t{rule}\t{escape(message)}")
    path.write_text("\n".join(lines) + "\n")


def run_lint(wiz, file):
    """(warnings, errors) of `file`; exits on a linter that does not answer in JSON."""
    proc = subprocess.run([str(wiz), "lint", "--json", "--deny", file],
                          cwd=ROOT, capture_output=True, text=True)
    try:
        doc = json.loads(proc.stdout)
    except json.JSONDecodeError:
        sys.exit(f"wiz lint {file}: no JSON document (exit {proc.returncode}):\n"
                 f"{proc.stdout}{proc.stderr}")
    if not isinstance(doc, dict) or "diagnostics" not in doc:
        sys.exit(f"wiz lint {file}: unexpected JSON: {proc.stdout}")
    warnings = [d for d in doc["diagnostics"] if d.get("severity") == "warning"]
    errors = [d for d in doc["diagnostics"] if d.get("severity") == "error"]
    return warnings, errors


def warning_key(file, d):
    """The baseline key of a warning. `style.line-length` says how long the line is,
    which changes when the line is edited: only the count of long lines per file
    matters, so that key drops the length (`--max-line` is fixed for the job)."""
    message = d["message"]
    if d["rule"] == "style.line-length":
        message = "line is longer than --max-line"
    return (file, d["rule"], message)


def fragment(file):
    """`selfhost/*.wiz` are concatenated into one program (`Wiz/Selfhost.lean`): they have
    no imports of their own and refer to names the earlier fragments declare, so most do
    not elaborate one file at a time. A fragment that does parse is linted; one that does
    not is skipped (its errors are the concatenation's, not a file's)."""
    return file.startswith("selfhost/")


def collect(wiz, files):
    counts = Counter()
    first = {}
    errors = []
    skipped = []
    for file in files:
        warnings, errs = run_lint(wiz, file)
        if errs and fragment(file):
            skipped.append((file, len(errs)))
            continue
        for d in warnings:
            key = warning_key(file, d)
            counts[key] += 1
            first.setdefault(key, d)
        errors += [(file, d) for d in errs]
    return counts, first, errors, skipped


def annotation(file, d):
    def esc(s):
        return str(s).replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    return (f"::error file={file},line={d.get('line', 1)},col={d.get('column', 1)},"
            f"title=ward::{esc(d.get('rule', 'lint'))}: {esc(d.get('message', ''))}")


def selected(args):
    files = [str(f).replace(os.sep, "/") for f in args]
    for f in files:
        if not lint_file(f):
            sys.exit(f"{f}: not a linted file (lib/**/*.wiz or selfhost/*.wiz)")
    return sorted(dict.fromkeys(files)) or all_files()


def changed(base):
    zero = not base or set(base) == {"0"}
    if zero:
        return all_files()
    known = subprocess.run(["git", "cat-file", "-e", f"{base}^{{commit}}"],
                           cwd=ROOT, capture_output=True).returncode == 0
    if not known:
        print(f"lint-baseline: {base} is not a commit here: linting every file",
              file=sys.stderr)
        return all_files()
    out = subprocess.run(["git", "diff", "--name-only", "--diff-filter=ACMR", base, "HEAD"],
                         cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return sorted(f for f in out.splitlines() if lint_file(f) and (ROOT / f).is_file())


def take(args, name, default):
    if name in args:
        i = args.index(name)
        if i + 1 >= len(args):
            sys.exit(f"{name} needs a value")
        value = args[i + 1]
        del args[i:i + 2]
        return value
    return default


def main(argv):
    if not argv:
        sys.exit(__doc__)
    cmd, args = argv[0], list(argv[1:])
    wiz = take(args, "--wiz", str(DEFAULT_WIZ))
    baseline = Path(take(args, "--baseline", str(DEFAULT_BASELINE)))
    base = take(args, "--base", "")

    if cmd == "files":
        print("\n".join(all_files()))
        return 0
    if cmd == "changed":
        files = changed(base)
        if files:
            print("\n".join(files))
        return 0
    if cmd not in ("check", "update"):
        sys.exit(__doc__)
    files = selected(args)
    if not files:
        print("lint-baseline: no files")
        return 0
    if cmd == "update":
        counts, _, errors, skipped = collect(wiz, files)
        for file, n in skipped:
            print(f"lint-baseline: {file}: skipped ({n} elaboration error(s): a selfhost "
                  f"fragment, not a module)", file=sys.stderr)
        if errors:
            for file, d in errors:
                print(annotation(file, d), file=sys.stderr)
            print(f"lint-baseline: {len(errors)} elaboration error(s): not writing a "
                  f"baseline", file=sys.stderr)
            return 1
        # a partial update (explicit files) keeps the other files' known warnings
        checked = set(files)
        merged = Counter({k: n for k, n in read_baseline(baseline).items()
                          if k[0] not in checked})
        merged.update(counts)
        write_baseline(baseline, merged)
        print(f"lint-baseline: {sum(counts.values())} warning(s) in {len(counts)} "
              f"entries from {len(files)} file(s) -> {os.path.relpath(baseline, ROOT)}")
        return 0

    known = read_baseline(baseline)
    counts, first, errors, skipped = collect(wiz, files)
    for file, n in skipped:
        print(f"::notice file={file},title=ward::not linted: a selfhost fragment, not a "
              f"module ({n} elaboration error(s) when concatenation is missing)")
    new = []
    for key, count in sorted(counts.items()):
        have = known[key]
        if count > have:
            new.append((key, count - have))
    checked = set(files)
    stale = [k for k, n in known.items()
             if k[0] in checked and n > counts.get(k, 0)]
    for file, d in errors:
        print(annotation(file, d))
    for key, n in new:
        file, rule, _ = key
        d = first[key]
        print(annotation(file, d))
        print(f"new warning: {file}: {d['message']} [{rule}]"
              + (f" (x{n})" if n > 1 else ""))
    if stale:
        print(f"lint-baseline: {len(stale)} baseline entry/entries no longer occur; "
              f"refresh with scripts/lint-baseline.py update", file=sys.stderr)
    total = sum(counts.values())
    print(f"lint-baseline: {total} warning(s) in {len(files)} file(s), {len(new)} new, "
          f"{len(errors)} error(s), {len(skipped)} selfhost fragment(s) skipped")
    return 1 if new or errors else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
