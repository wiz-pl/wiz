#!/usr/bin/env bash
# The STC metatheory check (the `stc` job of .github/workflows/ci.yml).
#
# STC (`STC.lean` and `STC/`, the F0 specification) is a separate Lake library and is
# deliberately **not** a default target: `lake build`, `lake test` and the Nix build do
# not typecheck it, and `STC/` is not in flake.nix's `unwrapped` fileset (putting it
# there would rebuild the compiler derivation on every STC edit). This script, run by
# the non-default `stc` job, is the only thing that checks it. Three properties:
#
#   1. it compiles: `lake build STC STC.Prototype.Totality`. The prototype is outside
#      `STC.lean`'s import closure, so it is named here explicitly.
#   2. no orphan: every `.lean` under `STC/` (and `STC.lean` itself) has an `.olean`
#      afterwards. A file the library does not import would otherwise rot untested.
#   3. it is honest: no `sorry`, no `admit`, no `axiom` declaration. The F0 obligation
#      statements are `def`s in `Prop`, not axioms, and a hole in a proof is a failed
#      proof (wiz-notes/stc-coverage.md).
#
# Usage:
#   scripts/check-stc.sh            the check above (what CI runs)
#   scripts/check-stc.sh self-check the two deliberate breaks from
#                                   wiz-notes/stc-coverage.md, each of which must make
#                                   the check fail:
#                                     * `theorem stc_ci_probe : False := by trivial`
#                                       appended to `STC/F0/Sanity.lean`;
#                                     * a `| probe` constructor added to `Tm` in
#                                       `STC/F0/Syntax.lean` (the `ren`/`sub` equations
#                                       and the rule matches are the only mechanical
#                                       guard a `Tm` change has).
#                                   Not part of CI: each break is a rebuild, and CI is
#                                   the critical path. Run it after changing this
#                                   script, the job's commands or `lakefile.lean`. It
#                                   refuses a dirty `STC/` and restores both files even
#                                   if it is interrupted.
set -uo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$ROOT" || exit 2

# Lake's default `buildDir`: `.lake/build/lib/lean/<Module/Path>.olean`.
OLEAN_DIR=${STC_OLEAN_DIR:-.lake/build/lib/lean}

error() {
  echo "::error title=STC::$*"
}

# Whether the build log has a Lean error in FILE (the compiler prints
# `<file>:<line>:<col>: error: …`).
has_error_in() { # LOG FILE
  grep -q "$2" "$1" && grep -q 'error' "$1"
}

check() {
  local bad=0 f olean

  echo "== lake build STC STC.Prototype.Totality"
  if ! lake build STC STC.Prototype.Totality; then
    error "lake build STC STC.Prototype.Totality failed"
    return 1
  fi

  echo "== every STC module produced an .olean"
  while IFS= read -r f; do
    olean="$OLEAN_DIR/${f%.lean}.olean"
    if [ ! -f "$olean" ]; then
      error "no olean for $f (looked for $olean); is the module imported, or is a target missing?"
      bad=1
    fi
  done < <(find STC -name '*.lean' | sort; printf 'STC.lean\n')
  [ "$bad" -eq 0 ] && echo "ok: every STC source has an olean"

  echo "== no sorry/admit, no axiom declaration"
  # `axiom` is matched only as a declaration: `SigWF`'s constructor `| axiom` (indented,
  # after a `|`) and the prose that names the word are fine.
  if grep -RnE --include='*.lean' '\b(sorry|admit)\b' STC STC.lean; then
    error "sorry/admit in STC: a hole is a failed proof, not a pass"
    bad=1
  fi
  if grep -RnE --include='*.lean' \
      '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+)*axiom([[:space:]]|$)' \
      STC STC.lean; then
    error "axiom declaration in STC: the F0 metatheory is checked with no project axioms"
    bad=1
  fi
  [ "$bad" -eq 0 ] && echo "ok: no sorry, admit or axiom declaration"

  if [ "$bad" -ne 0 ]; then
    return 1
  fi
  echo "check-stc: ok"
}

# The acceptance test: prove that the check can fail. Each break must make the build fail
# *for that reason*, not merely make some build fail.
self_check() {
  local sanity=STC/F0/Sanity.lean syntax=STC/F0/Syntax.lean
  local backup out rc bad=0

  # In a heavy --rsync copy there is no .git (heavy excludes it): the sources are the
  # node's scratch copy, so there is nothing to protect and the check is skipped.
  if git rev-parse --is-inside-work-tree >/dev/null 2>&1 &&
     ! git diff --quiet -- STC STC.lean; then
    echo "self-check: STC/ or STC.lean has uncommitted changes; refusing to edit it" >&2
    return 2
  fi
  backup=$(mktemp -d "${TMPDIR:-/tmp}/stc-self-check.XXXXXX") || return 2
  out=$(mktemp "${TMPDIR:-/tmp}/stc-self-check-log.XXXXXX") || return 2
  cp "$sanity" "$backup/Sanity.lean" && cp "$syntax" "$backup/Syntax.lean" || return 2
  # Always put the sources back, including on Ctrl-C or a killed build.
  # shellcheck disable=SC2064
  trap "cp '$backup/Sanity.lean' '$sanity'; cp '$backup/Syntax.lean' '$syntax'; rm -rf '$backup' '$out'" EXIT INT TERM

  echo "== self-check 1: a false theorem must fail the build"
  printf '\ntheorem stc_ci_probe : False := by trivial\n' >> "$sanity"
  lake build STC > "$out" 2>&1
  rc=$?
  cp "$backup/Sanity.lean" "$sanity"
  if [ "$rc" -eq 0 ]; then
    error "self-check: the false theorem stc_ci_probe compiled; check-stc cannot fail"
    bad=1
  elif ! has_error_in "$out" 'Sanity\.lean'; then
    error "self-check: the build failed without an error in Sanity.lean; not the probe"
    tail -20 "$out"
    bad=1
  else
    echo "ok: stc_ci_probe failed the build"
  fi

  echo "== self-check 2: a new Tm constructor must fail the build"
  # Insert `| probe` at the end of `inductive Tm` (before its `deriving` clause; see
  # STC/F0/Syntax.lean), so the recursive definitions that match on `Tm` must change.
  python3 - "$syntax" <<'PY'
import sys

path = sys.argv[1]
lines = open(path, encoding="utf-8").read().splitlines(keepends=True)
try:
    i = next(i for i, line in enumerate(lines) if line.startswith("inductive Tm where"))
except StopIteration:
    sys.exit("self-check: cannot find `inductive Tm where` in " + path)
# Doc comments (single- and multi-line) may sit between constructors, so scan to the
# `deriving` clause, or to the next top-level declaration when there is none.
j = None
for k in range(i + 1, len(lines)):
    stripped = lines[k].strip()
    if stripped.startswith("deriving"):
        j = k
        break
    if stripped and not lines[k].startswith(("  ", "\t")):
        break
if j is None:
    constructors = [k for k in range(i + 1, len(lines)) if lines[k].startswith("  | ")]
    if not constructors:
        sys.exit("self-check: no constructors after `inductive Tm where` in " + path)
    j = constructors[-1] + 1
lines.insert(j, "  | probe\n")
open(path, "w", encoding="utf-8").write("".join(lines))
PY
  if [ $? -ne 0 ]; then
    error "self-check: could not add the probe constructor to $syntax"
    bad=1
  else
    lake build STC > "$out" 2>&1
    rc=$?
    cp "$backup/Syntax.lean" "$syntax"
    if [ "$rc" -eq 0 ]; then
      error "self-check: a new Tm constructor compiled; the theorems are not guarded"
      bad=1
    elif ! has_error_in "$out" 'missing cases' || ! grep -q 'probe' "$out"; then
      error "self-check: the build failed without a missing-cases error for Tm.probe"
      tail -20 "$out"
      bad=1
    else
      echo "ok: the new Tm constructor failed the build (missing cases)"
    fi
  fi

  if [ "$bad" -ne 0 ]; then
    return 1
  fi
  echo "self-check: ok (both breaks fail the build)"
}

case "${1:-check}" in
  check) check ;;
  self-check) self_check ;;
  *) echo "usage: $0 [check|self-check]" >&2; exit 2 ;;
esac
