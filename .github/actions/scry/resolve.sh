#!/usr/bin/env bash
# Resolve the scry executable, its source tree and the rule pack.
#
# Writes GITHUB_ENV (for later steps) and GITHUB_OUTPUT (for the action's `if:` and
# cache key). It never builds anything: build.sh does that only when `needs-build` is
# true and no cached binary exists.
#
# Inputs arrive as INPUT_* environment variables from action.yml.
set -euo pipefail

say() { printf 'scry: %s\n' "$*"; }
die() { printf 'scry: error: %s\n' "$*" >&2; exit 1; }

workdir="${INPUT_WORKING_DIRECTORY:-.}"
[ -d "$workdir" ] || die "working-directory does not exist: $workdir"

repo_root=$(git -C "$workdir" rev-parse --show-toplevel 2>/dev/null) \
  || die "not a git checkout (needed for --diff): $workdir"

abs() { # abs PATH RELATIVE-TO
  case "$1" in
    /*) printf '%s' "$1" ;;
    *) (cd "$2" && printf '%s/%s' "$PWD" "$1") ;;
  esac
}

needs_build=false
scry_bin=""

# 1. An explicit path wins; 2. scry on PATH; 3. build from source into the cache.
if [ -n "${INPUT_SCRY_PATH:-}" ]; then
  scry_bin=$(abs "$INPUT_SCRY_PATH" "$workdir")
  [ -f "$scry_bin" ] || die "scry-path does not exist: $INPUT_SCRY_PATH"
  [ -x "$scry_bin" ] || die "scry-path is not executable: $INPUT_SCRY_PATH"
elif command -v scry >/dev/null 2>&1; then
  scry_bin=$(command -v scry)
else
  needs_build=true
  scry_bin="${HOME}/.cache/scry/bin/scry"
fi

# The source tree supplies the default rule pack (and the build, when needed). A
# consuming repository normally has no scry source, so clone the wiz repository at the
# requested revision; that is also what makes the action usable in one line.
version="${INPUT_SCRY_VERSION:-master}"
scry_source="${INPUT_SCRY_SOURCE:-}"
if [ -z "$scry_source" ] && [ -f "$repo_root/scry/grail.wiz" ]; then
  scry_source="$repo_root"
fi
if [ -z "$scry_source" ] && [ "$needs_build" = true ]; then
  scry_source="${RUNNER_TEMP:-/tmp}/scry-source"
  marker="$scry_source/.scry-action-version"
  if [ -f "$marker" ] && [ "$(cat "$marker")" != "$version" ]; then
    rm -rf "$scry_source"
  fi
  if [ ! -f "$scry_source/scry/grail.wiz" ]; then
    repo="${INPUT_SCRY_REPO:-wiz-pl/wiz}"
    say "cloning https://github.com/${repo}.git at ${version}"
    mkdir -p "$scry_source"
    git -C "$scry_source" init -q
    git -C "$scry_source" remote add origin "https://github.com/${repo}.git" 2>/dev/null \
      || git -C "$scry_source" remote set-url origin "https://github.com/${repo}.git"
    git -C "$scry_source" fetch -q --depth 1 origin "$version" \
      || die "cannot fetch ${repo}@${version} (pin scry-version to a branch, tag or commit)"
    git -C "$scry_source" checkout -q FETCH_HEAD
    printf '%s\n' "$version" > "$marker"
  fi
fi
if [ -n "$scry_source" ]; then
  scry_source=$(abs "$scry_source" "$repo_root")
  [ -f "$scry_source/scry/grail.wiz" ] \
    || die "scry-source is not a wiz checkout (no scry/grail.wiz): $scry_source"
fi

# Rules: explicit input, else the source tree's default pack. With a prebuilt binary
# and no source, leave it empty and let scry's own lookup try; scan.sh reports a clear
# error with the `rules:` hint if that fails.
rules="${INPUT_RULES:-}"
if [ -n "$rules" ]; then
  rules=$(abs "$rules" "$repo_root")
  [ -f "$rules" ] || die "rules file does not exist: $INPUT_RULES"
elif [ -n "$scry_source" ] && [ -f "$scry_source/lib/Scry/rules/default.scry" ]; then
  rules="$scry_source/lib/Scry/rules/default.scry"
fi

# A content key, not HEAD: a pull request's synthetic merge commit changes on every
# push, and the build cache should survive that. Only the files that build scry count.
source_key=no-source
if [ -n "$scry_source" ]; then
  source_key=$(
    cd "$scry_source"
    python3 - <<'PY'
import hashlib
import os

h = hashlib.sha256()
for root in ("scry", "lib/Scry", "c", "runtime"):
    for dirpath, _, names in os.walk(root):
        for name in sorted(names):
            if name.endswith((".wiz", ".c", ".h", ".json")):
                path = os.path.join(dirpath, name)
                h.update(path.encode())
                h.update(b"\0")
                with open(path, "rb") as fh:
                    h.update(fh.read())
for name in ("grail.wiz", "flake.nix", "flake.lock"):
    if os.path.exists(name):
        h.update(name.encode())
        with open(name, "rb") as fh:
            h.update(fh.read())
print(h.hexdigest()[:16])
PY
  )
fi

if [ "$needs_build" = true ]; then
  say "executable: ${scry_bin} (to build or restore from cache)"
else
  say "executable: ${scry_bin}"
fi
say "source: ${scry_source:-none}"
say "rules: ${rules:-scry default lookup}"

{
  echo "SCRY_BIN=${scry_bin}"
  echo "SCRY_SOURCE_DIR=${scry_source}"
  echo "SCRY_RULES=${rules}"
  echo "SCRY_NEEDS_BUILD=${needs_build}"
} >> "${GITHUB_ENV:?GITHUB_ENV is required}"

{
  echo "executable=${scry_bin}"
  echo "needs-build=${needs_build}"
  echo "source-key=${source_key}"
} >> "${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}"
