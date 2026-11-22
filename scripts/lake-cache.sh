#!/bin/sh
# The PR-only Lake seed: cache key, cached package set, and the seed round trip.
#
# `.github/workflows/ci.yml`'s `build` job restores a previous run's `.lake` from
# the GitHub Actions cache and then builds flake.nix's `withLakeCache` package set
# instead of the pure one. Lake keys an olean on its inputs' content hashes, so a
# seeded build recompiles exactly the modules the branch changed (and links the
# rest), instead of every compiler and test module.
#
#   scripts/lake-cache.sh key
#       `key=<key>` and `prefix=<prefix>` lines for $GITHUB_OUTPUT.
#       key    = lake-<os>-<arch>-<toolchain>-<sources>
#       prefix = lake-<os>-<arch>-<toolchain>-
#       <toolchain> hashes flake.lock and flake.nix (nixpkgs' Lean, the flags, the
#       fileset); <sources> hashes the `lean` and `runtime` subset hashes
#       (scripts/repo-subsets.py). The exact key is never reused for a seed from a
#       different toolchain or compiler sources; `restore-keys` may fall back to a
#       seed from the same *toolchain* only, which is the previous run's cache and
#       still safe: Lake recompiles every module whose inputs changed.
#
#   scripts/lake-cache.sh init DIR
#       create an empty seed (DIR/.lake and DIR/toolchain) for a cold run, whose
#       build then seeds the next run. A miss is a cold build, never a failure.
#
#   scripts/lake-cache.sh build SEED ATTR...
#       build `lib.<system>.withLakeCache SEED` and print `attr=<store path>` for
#       each attr (the cached package set: `unwrapped`, `wiz`, `tests`, `wiz-web`,
#       ...). The flake output cannot be a function, so this evaluates the `lib`
#       output with `nix build --impure --expr`.
#
#   scripts/lake-cache.sh save OUT DIR
#       copy OUT/lake/.lake and OUT/toolchain into DIR: the next run's seed.
#
# The seed is a `.lake` from another build: `withLakeCache` refuses one whose
# toolchain stamp differs from lean-toolchain's content, and CI only restores one
# under a key that names the same toolchain. Nothing here pushes the seed to a
# binary cache; the store paths the jobs use are the ordinary `wiz`/`tests`.
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
  sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'
}

hash_file() { sha256sum "$1" | cut -d' ' -f1; }

system() {
  if [ -n "${NIX_SYSTEM:-}" ]; then
    printf '%s\n' "$NIX_SYSTEM"
  else
    nix eval --impure --raw --expr builtins.currentSystem
  fi
}

case ${1:-} in
  key)
    # the architecture is part of the key: a .lake is not reusable across it (the
    # Actions cache is shared, and an aarch64 runner must never restore an x64 seed)
    os=$(uname -s)-$(uname -m)
    toolchain=$( { printf 'lake-cache-v1\n'
                   hash_file flake.lock
                   hash_file flake.nix; } | sha256sum | cut -d' ' -f1)
    sources=$( { python3 scripts/repo-subsets.py --print lean
                 python3 scripts/repo-subsets.py --print runtime; } | sha256sum | cut -d' ' -f1)
    printf 'key=lake-%s-%s-%s\n' "$os" "$toolchain" "$sources"
    printf 'prefix=lake-%s-%s-\n' "$os" "$toolchain"
    ;;
  init)
    [ $# -eq 2 ] || { usage >&2; exit 2; }
    dir=$2
    mkdir -p "$dir/.lake"
    cp lean-toolchain "$dir/toolchain"
    printf 'lake-cache: empty seed in %s (a cold run)\n' "$dir"
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
      rm -rf "$seed/.lake"
      mkdir -p "$seed/.lake"
      cp "$root/lean-toolchain" "$seed/toolchain"
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
  save)
    [ $# -eq 3 ] || { usage >&2; exit 2; }
    out=$2
    dir=$3
    [ -d "$out/lake/.lake" ] || {
      echo "lake-cache: $out/lake/.lake is missing (was it a withLakeCache output?)" >&2
      exit 2
    }
    mkdir -p "$dir"
    rm -rf "$dir/.lake"
    cp -a "$out/lake/.lake" "$dir/.lake"
    cp "$out/toolchain" "$dir/toolchain"
    # the store copies are read-only; the next run's Actions-cache tar and the
    # build's own `cp -a` do not care, but a human inspection is easier this way
    chmod -R u+w "$dir"
    printf 'lake-cache: seed in %s (%s)\n' "$dir" "$(du -sh "$dir/.lake" | cut -f1)"
    ;;
  -h|--help)
    usage
    ;;
  *)
    usage >&2
    exit 2
    ;;
esac
