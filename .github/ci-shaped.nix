# ci-shaped.nix: one attribute per derivation CI actually evaluates or builds, so
# that a changed `drvPath` is a changed derivation (`scripts/touched-derivations.sh`).
#
# The point is the *shape*, not the packages.  CI does not evaluate `.#selfhost-compiler`;
# it evaluates `(lib.selfhostWith { wiz = …; tests = …; }).compiler`, and
# `lib.towerWith (builtins.storePath …)`.  Those go through `flake.lib`, which a
# `.#X` evaluation never touches: a `lib.*With` call that reads an attribute `packages`
# does not export fails to evaluate here, in seconds, which is what the night's
# `flake.nix:1484`/`:1504` breaks needed (`.#selfhost-compiler` was fine).
#
# Inputs are the *pure* packages, not seeded store paths: `drvPath` is what this file
# is for, and a pure derivation evaluates with nothing built or substituted.
#
# Evaluation only.  The selector evaluates it three ways:
#   names:    nix eval --impure --json --expr 'builtins.attrNames (import …)' --apply …
#   drvPaths: … --apply 'set: builtins.mapAttrs (n: v: v.drvPath) set'
#   build:    nix build --impure --expr '(import …)."ATTR"' --no-link
# `scripts/ci.py check-ci-shaped` keeps the `lib-*` rows in step with the `lib.` calls
# in .github/workflows/ci.yml, so a new call site cannot go unselected.
{ flake, system ? builtins.currentSystem, ... }:
let
  pkgs = flake.packages.${system};
  lib = flake.lib.${system};

  # The derivations of a package set, without nixpkgs: `builtins` has no filterAttrs,
  # and the flake's own nixpkgs is not an output.  `packages` also holds functions
  # (`selfhostProgramWith`), which have no drvPath.
  derivations = attrs:
    builtins.listToAttrs (builtins.concatMap
      (n:
        let v = attrs.${n}; in
        if (v.type or "") == "derivation" then [{ name = "pkg-${n}"; value = v; }] else [ ])
      (builtins.attrNames attrs));

  # The one place CI writes the two `lib.*With` calls (ci.yml lines ~594 and ~846).
  seeded = { wiz = pkgs.wiz; tests = pkgs.tests; };
in
  derivations pkgs // {
    # `nix build (…lib."$sys".selfhostWith { wiz = …; tests = …; }).compiler`
    "lib-selfhostWith-compiler" = (lib.selfhostWith seeded).compiler;
    "lib-selfhostWith-checker" = (lib.selfhostWith seeded).checker;
    # `nix build (…lib."$sys".towerWith (builtins.storePath <wiz>))`
    "lib-towerWith-wiz" = lib.towerWith pkgs.wiz;
    # `nix build --expr (…lib."$sys".webWith (builtins.storePath <wiz>)).<attr>` - the four
    # web packages the `wasm` job builds with the seeded compiler (ci.yml, the
    # pull_request branch of "nix build (wiz-web, …)"). Without these rows the
    # touched-derivations selector never inspects them, so a change that would rebuild a
    # web package could be skipped.
    "lib-webWith-wiz-web" = (lib.webWith pkgs.wiz).wiz-web;
    "lib-webWith-wiz-playground" = (lib.webWith pkgs.wiz).wiz-playground;
    "lib-webWith-wiz-playground-ui" = (lib.webWith pkgs.wiz).wiz-playground-ui;
    "lib-webWith-wiz-source-ui" = (lib.webWith pkgs.wiz).wiz-source-ui;
    # scripts/lake-cache.sh: the trusted Lake seed, `(lib.withLakeCache empty-lake).unwrapped.lake`
    "lib-withLakeCache-lake-seed" = (lib.withLakeCache lib.empty-lake).unwrapped.lake;
  }
