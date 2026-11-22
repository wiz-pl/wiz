#!/bin/sh
# The Lake seed: cache keys, the trusted producer, and the seeded build.
#
# Trust direction — seeds come from **cold trusted builds**; PRs consume them and
# may add their own untrusted seed; nothing a PR writes is ever read by a trusted
# job.
#
#   producer   A push to master's `lake_seed` job builds flake.nix's
#              `withLakeCache empty-lake`: a cold compile *inside* the derivation, so
#              the sandbox — not an assertion about cache restores — enforces it. Its
#              `unwrapped.lake` output is the seed; the job saves it under both the
#              trusted and the untrusted key. It publishes no store path, and its
#              `bin` is byte-identical to the pure build's (measured).
#   consumer   A pull request restores the untrusted namespace first (its own
#              previous run, or the producer's copy) and the trusted one second, and
#              builds `withLakeCache <seed>` from it; with no usable restore it builds
#              `withLakeCache empty-lake`, the same cold build, never a failure.
#   guard      Every seed's `lake` output carries a `toolchain` stamp
#              (lean-toolchain's text); `withLakeCache` refuses a seed whose stamp
#              differs, and the cache key names flake.lock and the stamp, the
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
#   scripts/lake-cache.sh empty
#       build and print `lib.<system>.empty-lake`: a store path with an empty
#       `.lake/build` and the toolchain stamp. It is the producer's seed and the
#       consumer's fallback, so the function's argument is never nullable.
#
#   scripts/lake-cache.sh save OUT [DIR]
#       copy OUT/.lake and OUT/toolchain (OUT is a `withLakeCache` `lake` output) into
#       DIR (default `.lake-seed`): the path an Actions cache entry carries.
#
#   scripts/lake-cache.sh choose DIR...
#       print the first DIR with a `.lake` and a matching stamp; with none, print
#       `empty` (the same cold build the producer runs).
#
#   scripts/lake-cache.sh build SEED ATTR...
#       build `lib.<system>.withLakeCache SEED` and print `attr=<store path>` for each
#       attr (`wiz`, `tests`, `unwrapped`, `unwrapped.lake`, `wiz-web`, ...). The flake
#       output cannot be a function, so this evaluates the `lib` output with
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

empty_seed() {
  nix build -L --impure --no-link --print-out-paths --expr "
    (builtins.getFlake \"$root\").lib.\"$(system)\".\"empty-lake\""
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
  empty)
    empty_seed
    ;;
  save)
    [ $# -le 3 ] || { usage >&2; exit 2; }
    out=$2
    dir=${3:-.lake-seed}
    [ -d "$out/.lake" ] || {
      echo "lake-cache: $out/.lake is missing (is OUT a withLakeCache \`lake\` output?)" >&2
      exit 2
    }
    rm -rf "$dir"
    mkdir -p "$dir"
    cp -a "$out/.lake" "$dir/.lake"
    cp "$out/toolchain" "$dir/toolchain"
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
    printf 'lake-cache: no usable seed restored; using empty-lake (cold build)\n' >&2
    empty_seed
    ;;
  build)
    [ $# -ge 3 ] || { usage >&2; exit 2; }
    seed=$1
    shift
    [ -d "$seed/.lake" ] || {
      echo "lake-cache: $seed/.lake is missing (see 'scripts/lake-cache.sh empty')" >&2
      exit 2
    }
    # A seed from another lean-toolchain is not a failure for CI: build cold instead
    # (the flake would refuse it, and a restore-key fallback must not fail the job).
    if [ ! -f "$seed/toolchain" ] || ! cmp -s "$seed/toolchain" "$root/lean-toolchain"; then
      printf 'lake-cache: %s has no matching toolchain stamp; building from empty-lake\n' "$seed" >&2
      seed=$(empty_seed)
    fi
    sys=$(system)
    # a store path is passed as itself (`builtins.storePath`), a restored Actions-cache
    # directory is copied in (`builtins.path`, keyed by its contents)
    case $seed in
      /nix/store/*) seed_expr="builtins.storePath \"$seed\"" ;;
      *) seed_expr="builtins.path { path = \"$seed\"; name = \"lake-cache\"; }" ;;
    esac
    for attr in "$@"; do
      # LAKE_CACHE_NIX_ARGS: extra `nix build` flags (e.g. `--max-jobs 1`, for the
      # memory-hungry wasm derivations)
      out=$(nix build -L ${LAKE_CACHE_NIX_ARGS:-} --impure --no-link --print-out-paths --expr "
        let f = builtins.getFlake \"$root\";
            s = f.lib.\"$sys\".withLakeCache ($seed_expr);
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
