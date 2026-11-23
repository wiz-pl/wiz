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
#              `unwrapped.lake` output is the seed; the job publishes that store path
#              (`.#lake-seed`) to the trusted Cachix. Its `bin` is **expected** to be
#              byte-identical to the pure build's; the seed measurement's `cmp` is the
#              evidence and has not yet run (see `wiz-notes/fixpoint-research.md`), so
#              this is a design expectation, not a measured fact.
#   consumer   A pull request restores its own untrusted seed first (a previous run)
#              and otherwise names its base commit's `.#lake-seed` derivation and
#              **substitutes** it from the trusted Cachix (`trusted` below); it builds
#              `withLakeCache <seed>` from that store path. The trusted seed is never a
#              tarball in an Actions cache. With no substitutable output it builds
#              `withLakeCache empty-lake`, the same cold build, never a failure.
#   guard      Every seed's `lake` output carries a `toolchain` stamp
#              (lean-toolchain's text); `withLakeCache` refuses a seed whose stamp
#              differs, and the cache key names flake.lock and the stamp, the
#              architecture and the `lean`/`runtime` subset hashes, so a seed from
#              another toolchain is never offered under an exact key or a prefix.
#
#   scripts/lake-cache.sh key
#       two `name=value` lines for $GITHUB_OUTPUT, the pull request's own untrusted
#       entry:
#         pr-key=<base>-pr-<sources>              pr-prefix=<base>-pr-
#       <base> = lake-<os>-<arch>-<toolchain>; <toolchain> hashes flake.lock and
#       lean-toolchain (nixpkgs' Lean pin and the compiler the stamp names); <sources>
#       hashes the `lean` and `runtime` subset hashes (scripts/repo-subsets.py). The
#       trusted seed is not keyed here: it is a store path named by the base commit's
#       flake and substituted from Cachix (`trusted`), so it cannot be a stale entry
#       from another toolchain. flake.nix is
#       not in the key: it names the derivation, not the oleans' inputs — Lake
#       content-keys every module, so a changed fileset or flag recompiles what changed.
#
#   scripts/lake-cache.sh empty
#       build and print `lib.<system>.empty-lake`: a store path with an empty
#       `.lake/build` and the toolchain stamp. It is the producer's seed and the
#       consumer's fallback, so the function's argument is never nullable.
#
#   scripts/lake-cache.sh trusted BASE
#       evaluate the `packages.<system>.lake-seed` output of the flake at BASE (a
#       checkout of the pull request's base commit), check it against the trusted
#       Cachix and substitute it; print the store path, or `empty` when the base
#       predates the output or the cache does not hold it. It never builds the seed:
#       a cold compile is the consumer's `empty-lake` fallback.
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
    ;;
  empty)
    empty_seed
    ;;
  trusted)
    # BASE is a checkout of the pull request's base commit (master). The seed is the
    # base flake's `.#lake-seed` output — the same derivation master's `lake_seed` job
    # built — so a store path that is present in the trusted cache is the cold seed,
    # not a tarball this or any other job wrote. `nix path-info --store` is a read:
    # when it misses, the printer is `empty`, never a local build of the seed.
    [ $# -eq 2 ] || { usage >&2; exit 2; }
    base=$2
    [ -f "$base/flake.nix" ] || {
      echo "lake-cache: $base has no flake.nix" >&2
      exit 2
    }
    out=$(nix eval --raw "path:$base#packages.$(system).lake-seed.outPath" 2>/dev/null) || {
      printf 'lake-cache: no lake-seed output at %s; using empty-lake\n' "$base" >&2
      echo empty
      exit 0
    }
    cache=${CACHIX_NAME:+https://$CACHIX_NAME.cachix.org}
    # `nix path-info --store` is a read of the binary cache; `nix copy --from` is a
    # substitution, never a build. Do not use `nix build`/`nix-store --realise` on the
    # output path here: with the derivation instantiated, Nix may build it (the cold
    # seed) and then the seeded build — exactly the duplicate compile this branch
    # exists to avoid. A failed check or copy is the `empty-lake` fallback.
    if [ -n "$cache" ] && nix path-info --store "$cache" "$out" >/dev/null 2>&1 \
       && nix copy --from "$cache" "$out" >/dev/null 2>&1; then
      printf '%s\n' "$out"
    else
      printf 'lake-cache: trusted seed %s is not substitutable; using empty-lake\n' "$out" >&2
      echo empty
    fi
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
    # `build <seed> <attr>…`: shift the subcommand first. Without this, `$1` is
    # still `build`, so the seed check reads `build/.lake` and every seeded build
    # falls back to "missing" (the first fast-ci run's failure).
    shift
    [ $# -ge 2 ] || { usage >&2; exit 2; }
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
      *)
        # `builtins.path` requires an absolute path; `choose` prints the relative
        # `.subset-cache/lean` a restore created.
        seed=$(cd "$seed" && pwd)
        seed_expr="builtins.path { path = \"$seed\"; name = \"lake-cache\"; }"
        ;;
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
