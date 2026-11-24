#!/usr/bin/env bash
# touched-derivations.sh BASE [HEAD] [--select-only] [--json] [--no-build]
#
# Which derivations CI would build differently because of this diff -- chosen by
# `drvPath`, checked by a build.
#
# The night's reds had two shapes, and this script catches both (ci-reds-2026-11-23-night):
#
#   * the derivation changed but was never built (9105c0544: an unquoted heredoc
#     erased every `${…}` in a buildPhase; 244f4515b: the build ran a flag that only
#     exists on another branch) -- evaluation passes, so the selector names it and the
#     build is what fails;
#   * the `lib.*With` call CI writes does not evaluate at all (a33011326, 98f86f457:
#     an attribute that `packages` does not export; 48005c211: a fileset that names a
#     file the branch does not have) -- `.#X` never evaluates that path, this does, and
#     an eval failure is itself the finding, in seconds.
#
# How it works
#   1. `.github/ci-shaped.nix` is one attribute per derivation CI evaluates or builds:
#      every `packages.${system}` derivation, plus each `lib.*With` call exactly as
#      ci.yml writes it.  A new `lib.` call in ci.yml needs a row there
#      (`scripts/ci.py check-ci-shaped`).
#   2. Both commits are evaluated as committed trees in throwaway worktrees, so an
#      uncommitted tree cannot hide or invent a change.
#   3. An attribute is selected when its drvPath differs, it is new at HEAD, or it
#      fails to evaluate at HEAD (that failure is the finding, not a reason to stop).
#   4. Each selected attribute is built once, through `/workspace/wiz-tools/heavy`,
#      smallest closure first -- never on the controller -- and `heavy` writes the
#      `heavy:nix-build:<attr>` record for this sha that `.githooks/pre-push` reads.
#
# Usage
#   scripts/touched-derivations.sh HEAD~1 [--select-only]     # what does this commit touch?
#   scripts/touched-derivations.sh origin/integration/train13  # what would a merge add?
#   scripts/touched-derivations.sh BASE HEAD --select-only --json
#
# Builds only run from a CLEAN worktree whose HEAD is `HEAD` (a build of another tree
# is not a build of that sha); otherwise they are refused with `--select-only`'s hint.
#
# Exit status: 0 nothing to build and no eval failure; 1 something changed or failed
# (the summary says which); 2 a usage or checkout error.
set -u

usage() {
  cat <<'EOF'
touched-derivations.sh BASE [HEAD] [--select-only] [--json]

Which derivations CI would build differently because of this diff: chosen by
`drvPath` (an eval failure at HEAD is itself the finding), then built one per
`heavy` job, smallest closure first, from a clean worktree at HEAD.

  scripts/touched-derivations.sh HEAD~1 [--select-only]
  scripts/touched-derivations.sh origin/integration/train13 --select-only --json

0 nothing changed and no eval failure; 1 something changed or failed; 2 a usage
or checkout error.  The expression set is .github/ci-shaped.nix; a new `lib.` call
in ci.yml needs a row there (scripts/ci.py check-ci-shaped).
EOF
}

base=""
head="HEAD"
select_only=0
json=0
for a in "$@"; do
  case "$a" in
    --select-only|--no-build) select_only=1 ;;
    --json) json=1 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "touched-derivations: unknown option $a" >&2; exit 2 ;;
    *)
      if [ -z "$base" ]; then base=$a
      elif [ "$head" = HEAD ]; then head=$a
      else echo "touched-derivations: unexpected argument $a" >&2; exit 2
      fi ;;
  esac
done
if [ -z "$base" ]; then
  echo "usage: $0 BASE [HEAD] [--select-only] [--json]" >&2
  echo "  e.g. $0 origin/integration/train13   (from a clean worktree at HEAD)" >&2
  exit 2
fi

root=$(git rev-parse --show-toplevel 2>/dev/null) || {
  echo "touched-derivations: not inside a git checkout" >&2; exit 2; }
shaped="$root/.github/ci-shaped.nix"
[ -f "$shaped" ] || { echo "touched-derivations: no $shaped" >&2; exit 2; }
command -v nix >/dev/null 2>&1 || { echo "touched-derivations: no nix" >&2; exit 2; }
command -v python3 >/dev/null 2>&1 || { echo "touched-derivations: no python3" >&2; exit 2; }

resolve() {  # REV -> full sha, or empty
  git -C "$root" rev-parse --verify --quiet "$1^{commit}" 2>/dev/null
}
base_sha=$(resolve "$base")
head_sha=$(resolve "$head")
[ -n "$base_sha" ] || { echo "touched-derivations: $base is not a commit (fetch it first)" >&2; exit 2; }
[ -n "$head_sha" ] || { echo "touched-derivations: $head is not a commit (fetch it first)" >&2; exit 2; }
if [ "$base_sha" = "$head_sha" ]; then
  echo "touched-derivations: $base and $head are the same commit ($base_sha); nothing to compare"
  exit 0
fi

system=$(nix eval --impure --raw --expr builtins.currentSystem) || {
  echo "touched-derivations: cannot ask nix for the system" >&2; exit 2; }

# A throwaway worktree per side: the *committed* tree, not whatever is checked out.
scratch=$(mktemp -d "${TMPDIR:-/tmp}/touched-derivations.XXXXXX") || exit 2
cleanup() {
  for d in "$scratch/base" "$scratch/head"; do
    [ -d "$d" ] && git -C "$root" worktree remove --force "$d" >/dev/null 2>&1
  done
  rm -rf "$scratch"
}
trap cleanup EXIT INT TERM
for side in base head; do
  sha=$base_sha; [ "$side" = head ] && sha=$head_sha
  if ! git -C "$root" worktree add --detach --quiet "$scratch/$side" "$sha" 2>"$scratch/$side.err"; then
    echo "touched-derivations: cannot create a worktree at $sha:" >&2
    cat "$scratch/$side.err" >&2
    exit 2
  fi
done

# The expression set of a checkout: the current worktree's ci-shaped.nix (which may
# itself be new on this branch) evaluated against that checkout's flake.
expr_for() {  # TREE
  printf 'import "%s" { flake = builtins.getFlake "%s"; system = "%s"; }' "$shaped" "$1" "$system"
}

# `--apply` keeps the Nix code out of the shell's quoting: one function string per
# question.  tryEval turns one broken attribute into `{"error": true}` instead of
# aborting the whole evaluation -- an eval failure is a finding, not a crash.
APPLY_NAMES='set: builtins.attrNames set'
APPLY_DRVS='set: builtins.mapAttrs (n: v: let r = builtins.tryEval (v.drvPath); in if r.success then { drv = r.value; } else { error = true; }) set'

eval_json() {  # TREE APPLY -> JSON on stdout
  nix eval --impure --json --expr "$(expr_for "$1")" --apply "$2"
}

fail=0
count() { if [ -z "$1" ]; then echo 0; else printf '%s\n' "$1" | wc -l | tr -d ' '; fi; }
for side in base head; do
  if ! names=$(eval_json "$scratch/$side" "$APPLY_NAMES" 2>"$scratch/$side.names.err"); then
    echo "touched-derivations: the expression set does not evaluate at the $side" \
      "($( [ "$side" = base ] && echo "$base_sha" || echo "$head_sha")):" >&2
    sed -n '1,12p' "$scratch/$side.names.err" >&2
    echo "touched-derivations: that is the finding: ci-shaped.nix itself is broken there" >&2
    exit 1
  fi
  printf '%s\n' "$names" > "$scratch/$side.names.json"
  if ! eval_json "$scratch/$side" "$APPLY_DRVS" > "$scratch/$side.json" 2>"$scratch/$side.err"; then
    echo "touched-derivations: cannot evaluate $side ($( [ "$side" = base ] && echo "$base_sha" || echo "$head_sha")):" >&2
    sed -n '1,12p' "$scratch/$side.err" >&2
    exit 1
  fi
done

# The comparison, and the per-attribute error text for anything that failed at HEAD
# (the message is the finding, so it is not hidden behind `error: true`).
compare=$(python3 - "$scratch/base.json" "$scratch/head.json" <<'PY'
import json, sys
base = json.load(open(sys.argv[1], encoding="utf-8"))
head = json.load(open(sys.argv[2], encoding="utf-8"))
rows = []
for name in sorted(set(base) | set(head)):
    b = base.get(name)
    h = head.get(name)
    bdrv = (b or {}).get("drv")
    hdrv = (h or {}).get("drv")
    if h is None:
        state, detail = "gone", "not in the expression set at HEAD"
    elif h.get("error"):
        state, detail = "eval-failure", "does not evaluate at HEAD"
    elif b is None:
        state, detail = "new", "new at HEAD"
    elif b.get("error"):
        state, detail = "now-evaluates", "failed to evaluate at BASE"
    elif bdrv != hdrv:
        state, detail = "changed", "drvPath differs"
    else:
        state, detail = "same", ""
    if state in ("gone", "same", "now-evaluates"):
        continue
    rows.append((name, state, bdrv or "-", hdrv or "-", detail))
for name, state, bdrv, hdrv, detail in rows:
    print("\t".join([name, state, bdrv, hdrv, detail]))
PY
) || { echo "touched-derivations: the comparison failed" >&2; exit 2; }

selected=$(printf '%s\n' "$compare" | awk -F'\t' 'NF && $2 != "gone" { print $1 }')
eval_failures=$(printf '%s\n' "$compare" | awk -F'\t' '$2 == "eval-failure" { print $1 }')

if [ "$json" = 1 ]; then
  python3 - "$scratch/base.json" "$scratch/head.json" "$base_sha" "$head_sha" <<'PY'
import json, sys
base = json.load(open(sys.argv[1], encoding="utf-8"))
head = json.load(open(sys.argv[2], encoding="utf-8"))
out = {"base": sys.argv[3], "head": sys.argv[4], "attributes": {}}
for name in sorted(set(base) | set(head)):
    out["attributes"][name] = {
        "base": (base.get(name) or {}).get("drv"),
        "head": (head.get(name) or {}).get("drv"),
        "base_error": bool((base.get(name) or {}).get("error")),
        "head_error": bool((head.get(name) or {}).get("error")),
    }
print(json.dumps(out, indent=2, sort_keys=True))
PY
  exit 0
fi

if [ -z "$compare" ]; then
  echo "touched-derivations: ${base_sha:0:7}..${head_sha:0:7} changes no derivation in ci-shaped.nix"
  exit 0
fi

echo "touched-derivations: ${base_sha:0:7}..${head_sha:0:7}"
printf '%s\n' "$compare" | while IFS=$'\t' read -r name state bdrv hdrv detail; do
  printf '  %-34s %-12s %s\n' "$name" "$state" "$detail"
done

if [ -n "$eval_failures" ]; then
  echo
  echo "touched-derivations: evaluating these at HEAD fails; the message is the finding:"
  for name in $eval_failures; do
    echo "--- $name"
    nix eval --impure --raw --expr "( $(expr_for "$scratch/head") ).\"$name\".drvPath" 2>&1 |
      grep -v '^\s*$' | sed -n '1,8p' | sed 's/^/    /'
  done
  fail=1
fi

buildable=$(printf '%s\n' "$selected" | grep -vxF -f <(printf '%s\n' "$eval_failures") || true)
if [ -z "$buildable" ]; then
  echo
  echo "touched-derivations: nothing left to build ($(count "$eval_failures") eval failure(s))"
  exit "$fail"
fi

if [ "$select_only" = 1 ]; then
  echo
  echo "touched-derivations: to build (selection only, --select-only):"
  printf '%s\n' "$buildable" | sed 's/^/  /'
  echo "touched-derivations: run this from a clean worktree at ${head_sha:0:7} without" \
    "--select-only to build them through heavy"
  exit "$fail"
fi

# A build of another tree is not a build of this sha (the `heavy` record would be
# dirty, and the push guard would rightly refuse it).
worktree_head=$(resolve HEAD)
if [ "$worktree_head" != "$head_sha" ]; then
  echo "touched-derivations: this worktree is at ${worktree_head:0:7}, not ${head_sha:0:7};" \
    "check HEAD out (or drop HEAD) to build, or use --select-only" >&2
  exit 2
fi
if [ -n "$(git -C "$root" status --porcelain | head -n 1)" ]; then
  echo "touched-derivations: this worktree has uncommitted changes; a build of it is not" \
    "a build of ${head_sha:0:7} (heavy records it as dirty). Commit or stash-free them, or" \
    "use --select-only" >&2
  exit 2
fi

heavy=/workspace/wiz-tools/heavy
[ -x "$heavy" ] || { echo "touched-derivations: no $heavy" >&2; exit 2; }

# Smallest closure first, so a cheap failure surfaces before an expensive build.  The
# closure size is the number of derivations `nix derivation show --recursive` reports:
# an evaluation, not a build.
sized=""
for name in $buildable; do
  drv=$(printf '%s\n' "$compare" | awk -F'\t' -v n="$name" '$1 == n { print $4 }')
  size=$(nix derivation show --recursive "$drv" 2>/dev/null |
    python3 -c 'import json,sys; print(len(json.load(sys.stdin)))' 2>/dev/null || echo 999999)
  sized="$sized$size\t$name\n"
done
ordered=$(printf '%b' "$sized" | sort -n -k1,1 | awk -F'\t' 'NF { print $2 }')

echo
echo "touched-derivations: building $(count "$ordered") derivation(s)" \
  "through heavy (smallest closure first); each one writes its own ledger record"
built=0
for name in $ordered; do
  echo "--- building $name"
  if HEAVY_LEDGER_NAME="heavy:nix-build:$name" "$heavy" --sshfs -- \
       nix build --impure --no-link --print-out-paths \
       --expr "( $(expr_for "$root") ).\"$name\""; then
    built=$((built + 1))
  else
    echo "touched-derivations: $name FAILED to build: the diff changes a derivation CI" \
      "would build, and the build is what broke" >&2
    fail=1
  fi
done

echo
echo "touched-derivations: $(count "$buildable") selected," \
  "$built built, $(count "$eval_failures") eval failure(s)," \
  "$([ "$fail" = 0 ] && echo 'nothing left for CI to break on these' || echo 'see above')"
exit "$fail"
