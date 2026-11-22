#!/bin/sh
# The Lake seed: cache keys, the cold producer's save, and the seeded build.
#
# Trust direction — seeds come from **cold trusted builds**; PRs consume them and
# may add their own untrusted seed; nothing a PR writes is ever read by a trusted
# job.
#
#   producer   The `lake_seed` job runs on a push to master only. It restores no
#              cache (the workflow asserts the checkout has no `.lake`), runs a cold
#              `nix develop --command lake build wiz grail tests`, and saves the
#              resulting `.lake` under both the trusted and the untrusted key. A
#              seed harvested from a warm tree is only as good as whatever produced
#              the warmth, so cold is the point.
#   consumer   A pull request restores the untrusted namespace first (its own
#              previous run, or the producer's copy) and the trusted one second, and
#              builds flake.nix's `withLakeCache` from it. A pull request writes
#              nothing: `withLakeCache` installs only `bin/` (the oleans never enter
#              the store), so a Nix build has no `.lake` to save, and the design
#              deliberately does not add a `.lake` store output. A PR's later runs
#              restore the trusted seed again and recompile only its own modules.
#   guard      Every seed carries a `toolchain` stamp (lean-toolchain's text);
#              `withLakeCache` refuses a seed whose stamp differs, and the cache key
#              names the toolchain (`flake.lock` and the `lean-toolchain` stamp), the
#              architecture and the `lean`/`runtime` subset hashes, so a seed from
#              another toolchain is never offered under an exact key or a prefix.
#
#   scripts/lake-cache.sh key
#       four `name=value` lines for $GITHUB_OUTPUT:
#         pr-key=<base>-pr-<sources>              pr-prefix=<base>-pr-
#         trusted-key=<base>-trusted-<sources>    trusted-prefix=<base>-trusted-
#       <base> = lake-<os>-<arch>-<toolchain>; <toolchain> hashes flake.lock and
#       lean-toolchain (nixpkgs' Lean pin and the compiler the stamp names); <sources>
#       hashes the `lean` and `runtime` subset hashes (scripts/repo-subsets.py). Both
#       namespaces use this one function, so a PR can fall back from its own seed to
#       the trusted one without ever being offered a different toolchain. flake.nix is
#       not in the key: it names the derivation, not the oleans' inputs — Lake
#       content-keys every module, so a changed fileset or flag recompiles what changed.
#
#   scripts/lake-cache.sh save [DIR]
#       copy the checkout's `.lake` (a dev-shell `lake build wiz grail tests`) and
#       the toolchain stamp into DIR (default `.lake-seed`). A cold build's `.lake`
#       is the only producer: it drops `.lake/build/bin`, which the seeded build
#       relinks.
#
#   scripts/lake-cache.sh choose DIR...
#       print the first DIR with a `.lake` and a matching stamp; with none, make and
#       print `.lake-seed-cold` (an empty seed: the cold build, never a failure).
#
#   scripts/lake-cache.sh init DIR
#       make an empty seed in DIR (for a run with no cache to restore).
#
#   scripts/lake-cache.sh build SEED ATTR...
#       build `lib.<system>.withLakeCache SEED` and print `attr=<store path>` for
#       each attr (`unwrapped`, `wiz`, `tests`, `wiz-web`, ...). The flake output
#       cannot be a function, so this evaluates the `lib` output with
#       `nix build --impure --expr`.
#
# `LAKE_CACHE_NIX_ARGS` adds flags to `build`'s `nix build` (the wasm job passes
# `--max-jobs 1`: the playground engine's peak memory does not allow two).
#
# Called from `.github/workflows/ci.yml` only; the release path never runs it.
# Exit status: 0 ok, 2 usage or a seed that cannot be used, otherwise nix's status.
set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

usage() {
  sed -n '2,/^set -eu$/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'
}

hash_file() { sha256sum "$1" | cut -d' ' -f1; }

system() {
  if [ -n "${NIX_SYSTEM:-}" ]; then
    printf '%s\n' "$NIX_SYSTEM"
  else
    nix eval --impure --raw --expr builtins.currentSystem
  fi
}

empty_seed() { # DIR
  rm -rf "$1/.lake"
  mkdir -p "$1/.lake"
  cp lean-toolchain "$1/toolchain"
}

case ${1:-} in
  key)
    # the architecture is part of the key: a .lake is not reusable across it (the
    # Actions cache is shared, and an aarch64 runner must never restore an x64 seed)
    base="lake-$(uname -s)-$(uname -m)-$( { printf 'lake-cache-v1\n'
                                              hash_file flake.lock
                                              hash_file lean-toolchain; } | sha256sum | cut -d' ' -f1)"
    sources=$( { python3 scripts/repo-subsets.py --print lean
                 python3 scripts/repo-subsets.py --print runtime; } | sha256sum | cut -d' ' -f1)
    printf 'pr-key=%s-pr-%s\n' "$base" "$sources"
    printf 'pr-prefix=%s-pr-\n' "$base"
    printf 'trusted-key=%s-trusted-%s\n' "$base" "$sources"
    printf 'trusted-prefix=%s-trusted-\n' "$base"
    ;;
  save)
    [ $# -le 2 ] || { usage >&2; exit 2; }
    dir=${2:-.lake-seed}
    [ -d .lake/build/lib ] || {
      echo "lake-cache: the checkout has no .lake/build/lib; run" >&2
      echo "  nix develop --command lake build wiz grail tests" >&2
      echo "first (save does not harvest a Nix build: its output is only bin/)" >&2
      exit 2
    }
    rm -rf "$dir"
    mkdir -p "$dir"
    cp -a .lake "$dir/.lake"
    # the seeded build relinks the binaries; leaving them out keeps the entry small
    rm -rf "$dir/.lake/build/bin"
    cp lean-toolchain "$dir/toolchain"
    chmod -R u+w "$dir"
    printf 'lake-cache: seed in %s (%s)\n' "$dir" "$(du -sh "$dir/.lake" | cut -f1)"
    ;;
  choose)
    for dir in "$@"; do
      if [ -d "$dir/.lake" ] && [ -f "$dir/toolchain" ] \
         && cmp -s "$dir/toolchain" lean-toolchain; then
        printf '%s\n' "$dir"
        exit 0
      fi
    done
    dir=.lake-seed-cold
    empty_seed "$dir"
    printf 'lake-cache: no usable seed restored; %s is empty (cold build)\n' "$dir" >&2
    printf '%s\n' "$dir"
    ;;
  init)
    [ $# -eq 2 ] || { usage >&2; exit 2; }
    empty_seed "$2"
    printf 'lake-cache: empty seed in %s (a cold run)\n' "$2"
    ;;
  build)
    [ $# -ge 3 ] || { usage >&2; exit 2; }
    seed=$1
    shift
    [ -d "$seed/.lake" ] || {
      echo "lake-cache: $seed/.lake is missing; run 'scripts/lake-cache.sh init $seed'" >&2
      exit 2
    }
    seed=$(cd "$seed" && pwd)
    # A seed from another lean-toolchain is not a failure for CI: discard it and
    # build cold (the flake would refuse it, and a cache restore falling back under
    # a broader restore-key must not fail the job).
    if [ ! -f "$seed/toolchain" ] || ! cmp -s "$seed/toolchain" "$root/lean-toolchain"; then
      echo "lake-cache: $seed has no matching toolchain stamp; discarding it (cold build)" >&2
      empty_seed "$seed"
    fi
    sys=$(system)
    for attr in "$@"; do
      # LAKE_CACHE_NIX_ARGS: extra `nix build` flags (e.g. `--max-jobs 1`, for the
      # memory-hungry wasm derivations)
      out=$(nix build -L ${LAKE_CACHE_NIX_ARGS:-} --impure --no-link --print-out-paths --expr "
        let f = builtins.getFlake \"$root\";
            s = f.lib.\"$sys\".withLakeCache
                  (builtins.path { path = \"$seed\"; name = \"lake-cache\"; });
        in s.$attr")
      printf '%s=%s\n' "$attr" "$out"
    done
    ;;
  -h|--help)
    usage
    ;;
  *)
    usage >&2
    exit 2
    ;;
esac
