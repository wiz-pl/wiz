#!/bin/sh
# Publish the aarch64-linux Wiz packages to the public Cachix cache.
#
#   scripts/publish-arm-cache.sh [OUT] [OPTIONS]
#
# Builds `.#wiz` and `.#tests` for aarch64-linux through the aarch64 builder in
# nix.buildMachines, copies the results to that builder, runs
# `cachix push badlydrawnwizards ...` there (the token is that machine's, never
# this checkout's), and verifies that a clean Nix store can substitute the paths
# again. A store path that already exists locally is not rebuilt.
#
# OUT is an optional file that receives the published store paths, one per
# line; without it the paths go to standard output. Progress goes to standard
# error, so `scripts/publish-arm-cache.sh paths.txt >/dev/null` is quiet.
#
# Prerequisites (docs/building.md, "Publishing aarch64 builds"):
#   * an aarch64-linux builder in the Nix configuration (`nix config show builders`);
#   * `ssh millionants` without a password, with `nix` and `cachix` on PATH;
#   * a token for the cache in `~/.config/cachix/cachix.dhall` on that machine;
#   * the cache's public key in this machine's `trusted-public-keys`.
#
# Examples:
#   scripts/publish-arm-cache.sh                # build, push, verify
#   scripts/publish-arm-cache.sh paths.txt      # also write the paths to a file
#   scripts/publish-arm-cache.sh --check        # report; no build, no push
#   scripts/publish-arm-cache.sh --dry-run      # print the commands
#   scripts/publish-arm-cache.sh --flake /src/wiz --target wiz
set -eu

prog=${0##*/}
flake=.
targets=
system=aarch64-linux
cache=badlydrawnwizards
cache_url=
builder=millionants
mode=run
dry=0
verify=1
out=
explicit=
ssh_ok=0

usage() {
  cat <<EOF
Usage: $prog [OUT] [OPTIONS]

Build .#wiz and .#tests for aarch64-linux, push them to Cachix from the builder,
and check that a clean store substitutes them.

  OUT                 write the store paths to OUT (default: stdout)
  --flake REF         flake reference (default: .)
  --target NAME       package to publish, repeatable (default: wiz tests)
  --system SYSTEM     system to build for (default: aarch64-linux)
  --cache NAME        Cachix cache (default: badlydrawnwizards)
  --cache-url URL     cache URL (default: https://NAME.cachix.org)
  --builder HOST      the aarch64 builder and Cachix-token host (default: millionants)
  --check             report local/builder/cache state; do not build or push
  --dry-run           print the commands instead of running them
  --no-verify         skip the clean-HOME substitution check
  --path PATH         check/publish an existing store path instead of a flake target
  -h, --help          show this help

--target may be repeated; it replaces the default. With --path, no flake is
evaluated and the paths are not built.
EOF
}

die() { printf '%s: %s\n' "$prog" "$*" >&2; exit 1; }
log() { printf '%s: %s\n' "$prog" "$*" >&2; }

# Print a command for --dry-run (no argument needs quoting: attribute names and
# store paths have no whitespace).
run() {
  if [ "$dry" = 1 ]; then
    printf '+ %s\n' "$*" >&2
  else
    "$@"
  fi
}

while [ $# -gt 0 ]; do
  case $1 in
    --flake) [ $# -ge 2 ] || die '--flake needs a value'; flake=$2; shift 2 ;;
    --flake=*) flake=${1#*=}; shift ;;
    --target) [ $# -ge 2 ] || die '--target needs a value'; targets="$targets $2"; shift 2 ;;
    --target=*) targets="$targets ${1#*=}"; shift ;;
    --system) [ $# -ge 2 ] || die '--system needs a value'; system=$2; shift 2 ;;
    --system=*) system=${1#*=}; shift ;;
    --cache) [ $# -ge 2 ] || die '--cache needs a value'; cache=$2; shift 2 ;;
    --cache=*) cache=${1#*=}; shift ;;
    --cache-url) [ $# -ge 2 ] || die '--cache-url needs a value'; cache_url=$2; shift 2 ;;
    --cache-url=*) cache_url=${1#*=}; shift ;;
    --builder) [ $# -ge 2 ] || die '--builder needs a value'; builder=$2; shift 2 ;;
    --builder=*) builder=${1#*=}; shift ;;
    --check) mode=check; shift ;;
    --dry-run) dry=1; shift ;;
    --no-verify) verify=0; shift ;;
    --path) [ $# -ge 2 ] || die '--path needs a value'; explicit="$explicit $2"; shift 2 ;;
    --path=*) explicit="$explicit ${1#*=}"; shift ;;
    -h|--help) usage; exit 0 ;;
    -*) die "unknown option '$1' (try --help)" ;;
    *)
      [ -z "$out" ] || die "only one OUT may be given (already '$out')"
      out=$1
      shift
      ;;
  esac
done

command -v nix >/dev/null 2>&1 || die 'nix is not installed'

cache=${cache%/}
[ -n "$cache_url" ] || cache_url="https://$cache.cachix.org"
cache_url=${cache_url%/}

tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-arm-cache.XXXXXX")
# A throwaway Nix store is read-only after registration; make it writable again
# so the temporary directory can always be removed.
cleanup() { chmod -R u+w "$tmp" 2>/dev/null || true; rm -rf "$tmp"; }
trap cleanup EXIT HUP INT TERM

# The builder is needed to push: the token lives there. A check also reports its
# store, but can continue (with a warning) when SSH is not available.
if [ "$mode" = run ] && [ "$dry" = 0 ]; then
  ssh -o BatchMode=yes -o ConnectTimeout=10 "$builder" true 2>/dev/null \
    || die "cannot ssh to $builder (the aarch64 builder and Cachix-token host)"
  ssh_ok=1
elif [ "$mode" = check ]; then
  if ssh -o BatchMode=yes -o ConnectTimeout=10 "$builder" true 2>/dev/null; then
    ssh_ok=1
  else
    log "warning: cannot ssh to $builder; the builder column is unknown"
  fi
fi

is_local() { nix path-info "$1" >/dev/null 2>&1; }
is_remote() {
  [ "$ssh_ok" = 1 ] || return 1
  ssh -o BatchMode=yes -o ConnectTimeout=10 "$builder" nix path-info "$1" </dev/null >/dev/null 2>&1
}
is_cached() { nix path-info --store "$cache_url" "$1" >/dev/null 2>&1; }

# items: one "TARGET<TAB>PATH" line per package, in command-line order.
: > "$tmp/items"

if [ -n "$explicit" ]; then
  n=0
  for p in $explicit; do
    case $p in
      /nix/store/*) ;;
      *) die "--path needs an absolute /nix/store path, not '$p'" ;;
    esac
    n=$((n + 1))
    printf 'path%d\t%s\n' "$n" "$p" >> "$tmp/items"
  done
else
  [ -n "$targets" ] || targets='wiz tests'
  for t in $targets; do
    errf=$tmp/eval.err
    if p=$(nix eval --raw "$flake#$t.outPath" --system "$system" 2>"$errf"); then
      :
    else
      msg=$(tr '\n' ' ' < "$errf")
      hint=
      if [ "$t" = tests ]; then
        hint=' (a tree without packages.tests needs --target wiz)'
      fi
      die "cannot evaluate $flake#$t for $system$hint${msg:+: $msg}"
    fi
    case $p in
      /nix/store/*) ;;
      *) die "evaluating $flake#$t gave '$p', not a store path" ;;
    esac
    printf '%s\t%s\n' "$t" "$p" >> "$tmp/items"
  done
fi

report_paths() {
  [ -n "$out" ] || return 0
  if [ "$out" = - ]; then
    return 0
  fi
  cut -f2 "$tmp/items" > "$out"
  log "wrote the store paths to $out"
}

if [ "$mode" = check ]; then
  printf '%-16s %-6s %-8s %-6s %s\n' TARGET LOCAL BUILDER CACHE PATH
  missing=0
  exec 3< "$tmp/items"
  while IFS="$(printf '\t')" read -r t p <&3; do
    if is_local "$p"; then local_s=yes; else local_s=no; fi
    if [ "$ssh_ok" = 1 ]; then
      if is_remote "$p"; then remote_s=yes; else remote_s=no; fi
    else
      remote_s=unknown
    fi
    if is_cached "$p"; then cache_s=yes; else cache_s=no; missing=1; fi
    printf '%-16s %-6s %-8s %-6s %s\n' "$t" "$local_s" "$remote_s" "$cache_s" "$p"
  done
  report_paths
  if [ "$missing" != 0 ]; then
    log "not every path is in $cache_url"
    exit 1
  fi
  log "every path is in $cache_url"
  exit 0
fi

# Build only what is not already in the local store (a path on the builder or
# in the cache still has to be present locally to check its identity).
exec 3< "$tmp/items"
while IFS="$(printf '\t')" read -r t p <&3; do
  if is_local "$p"; then
    log "already built: $p"
    continue
  fi
  if [ -n "$explicit" ]; then
    if [ "$dry" = 0 ]; then
      die "$p is not in the local store (--path only publishes existing paths)"
    fi
    log "not in the local store yet: $p (dry run: the copy and push below need it)"
    continue
  fi
  log "building $flake#$t for $system via the Nix builders"
  if [ "$dry" = 1 ]; then
    run nix build --system "$system" --no-link --print-out-paths "$flake#$t"
    continue
  fi
  got=$(nix build --system "$system" --no-link --print-out-paths "$flake#$t") \
    || die "nix build failed for $flake#$t"
  [ "$got" = "$p" ] || die "nix build returned $got, expected $p (did the flake change?)"
  is_local "$p" || die "nix build succeeded but $p is not in the local store"
done

# The token is on the builder, so the paths have to be in its store; a remote
# build already leaves them there.
exec 3< "$tmp/items"
while IFS="$(printf '\t')" read -r t p <&3; do
  if [ "$dry" = 0 ] && is_remote "$p"; then
    log "builder $builder already has $p"
    continue
  fi
  run nix copy --to "ssh-ng://$builder" "$p"
done

# Push from the builder: cachix reads ~/.config/cachix/cachix.dhall there. Do not
# read that file, copy it, or print it.
set -- "$builder" cachix push "$cache"
exec 3< "$tmp/items"
while IFS="$(printf '\t')" read -r t p <&3; do
  set -- "$@" "$p"
done
log "pushing to $cache from $builder (the token stays on $builder)"
run ssh "$@" </dev/null

# The manifest is useful even if verification fails below.
report_paths

if [ "$dry" = 1 ]; then
  log 'dry run: not checking the cache or substituting into a clean store'
  cut -f2 "$tmp/items"
  exit 0
fi

# Every path must have a narinfo in the cache. Querying the binary cache does
# not download the contents.
missing=0
exec 3< "$tmp/items"
while IFS="$(printf '\t')" read -r t p <&3; do
  if is_cached "$p"; then
    log "cache has $p"
  else
    log "MISSING from $cache_url: $p"
    missing=1
  fi
done
[ "$missing" = 0 ] || die "the cache does not have every path after the push"

if [ "$verify" = 0 ]; then
  log 'skipping the clean-HOME substitution check (--no-verify)'
  cut -f2 "$tmp/items"
  exit 0
fi

# A throwaway store with a clean HOME: no user Nix configuration, no local
# build results and no builders, so the only way to realise the packages is to
# substitute them (and their closures) from the cache. A missing path fails
# here instead of being rebuilt for aarch64 on this x86_64 machine.
vhome=$tmp/home
vstore=$tmp/verify-store
mkdir -p "$vhome"
substituters=$(nix config show substituters 2>/dev/null || true)
case " $substituters " in
  *" $cache_url "*) ;;
  *) substituters="$substituters $cache_url" ;;
esac
keys=$(nix config show trusted-public-keys 2>/dev/null || true)
case " $keys " in
  *"$cache.cachix.org-"*) ;;
  *) die "$cache.cachix.org is not in trusted-public-keys; run 'cachix use $cache' first" ;;
esac

clean_env() {
  env -i HOME="$vhome" PATH="$PATH" TMPDIR="$tmp" \
    XDG_CACHE_HOME="$vhome/.cache" XDG_CONFIG_HOME="$vhome/.config" "$@"
}

if [ -n "$explicit" ]; then
  exec 3< "$tmp/items"
  while IFS="$(printf '\t')" read -r t p <&3; do
    log "substituting $p into a throwaway store with a clean HOME"
    # `--realise` of a non-derivation path fetches the whole closure from the
    # substituters and never builds; dependencies may come from cache.nixos.org
    # just as they would for a real build.
    got=$(clean_env nix-store --realise --store "$vstore" \
      --option substituters "$substituters" \
      --option trusted-public-keys "$keys" "$p") \
      || die "could not substitute $p (and its closure) from the configured substituters"
    [ "$got" = "$p" ] || die "realising $p returned '$got'"
    clean_env nix path-info --store "$vstore" "$p" >/dev/null \
      || die "$p is not in the throwaway store after the substitution"
  done
else
  exec 3< "$tmp/items"
  while IFS="$(printf '\t')" read -r t p <&3; do
    log "building $flake#$t in a throwaway store with a clean HOME"
    got=$(clean_env nix build --store "$vstore" --system "$system" \
      --no-link --print-out-paths \
      --option substituters "$substituters" \
      --option trusted-public-keys "$keys" \
      --option builders '' --option max-jobs 0 "$flake#$t") \
      || die "clean-HOME build of $flake#$t failed (is it in $cache_url?)"
    [ "$got" = "$p" ] || die "clean-HOME build returned $got, expected $p"
    log "substituted $p from $cache_url"
  done
fi

cut -f2 "$tmp/items"
