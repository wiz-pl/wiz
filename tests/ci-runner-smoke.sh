#!/usr/bin/env bash
# Local smoke test for the optional NixOS CI-runner module (docs/ci-runner.md).
#
# It builds the runner wrapper, exercises its environment/credential check,
# and evaluates the NixOS module: the unit must load the token as a systemd
# credential, restart after its one ephemeral job, run the listener as the
# unprivileged user, and refuse a token that would be copied into the store.
#
#   tests/ci-runner-smoke.sh
#
# Nothing here contacts GitHub or needs a real token.

set -euo pipefail

root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
export SMOKE_ROOT=$root

pass() { printf 'ci-runner-smoke: %s\n' "$*"; }
fail() {
  printf 'ci-runner-smoke: %s\n' "$*" >&2
  exit 1
}

runner=$(nix build --no-link --print-out-paths .#wiz-ci-runner | tail -n 1)
github_runner=$(nix build --no-link --print-out-paths 'nixpkgs#github-runner' | tail -n 1)
[[ -x $runner/bin/wiz-ci-runner ]] || fail "the wiz-ci-runner package did not build"
[[ -x $github_runner/bin/config.sh ]] || fail "the github-runner package did not build"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/credentials" "$tmp/empty" "$tmp/state" "$tmp/work"
printf '%s\n' 'github_pat_smoke' >"$tmp/credentials/token"

common_env=(
  WIZ_CI_RUNNER_URL=https://github.com/wiz-pl/wiz
  WIZ_CI_RUNNER_NAME=wiz-heavy-smoke
  WIZ_CI_RUNNER_LABELS=wiz-heavy
  WIZ_CI_RUNNER_TOKEN_TYPE=auto
  WIZ_CI_RUNNER_API_URL=https://api.github.com
  WIZ_CI_RUNNER_SCOPE=repo:wiz-pl/wiz
  WIZ_CI_RUNNER_STATE_DIR="$tmp/state"
  WIZ_CI_RUNNER_WORK_DIR="$tmp/work"
  WIZ_CI_RUNNER_USER=nobody
  WIZ_CI_RUNNER_GROUP=nogroup
  WIZ_CI_RUNNER_GITHUB_RUNNER="$github_runner"
)

env "${common_env[@]}" CREDENTIALS_DIRECTORY="$tmp/credentials" \
  "$runner/bin/wiz-ci-runner" check
pass "the runner environment and credential check"

if env "${common_env[@]}" CREDENTIALS_DIRECTORY="$tmp/empty" \
  "$runner/bin/wiz-ci-runner" check >/dev/null 2>&1; then
  fail "an empty credential directory was accepted"
fi
pass "a missing credential is rejected"

# Evaluate the module itself.  `assertions` are a plain list, so a false one is
# checked without instantiating a full NixOS system.
expr=$(cat <<'EOF'
let
  flake = builtins.getFlake (builtins.getEnv "SMOKE_ROOT");
  nixpkgs = flake.inputs.nixpkgs;
  system = builtins.currentSystem;
  eval = withModule: extra: nixpkgs.lib.nixosSystem {
    inherit system;
    modules = (if withModule then [ flake.nixosModules.ci-runner ] else [ ]) ++ [ extra ];
  };
  baseline = eval false { };
  good = eval true {
    services.wiz-ci-runner = {
      enable = true;
      tokenFile = "/run/secrets/wiz-ci-runner-token";
      warm.enable = false;
    };
  };
  unit = good.config.systemd.services.wiz-ci-runner;
  user = good.config.users.users.wizci;
  storeToken = toString (nixpkgs.legacyPackages.${system}.writeText "token" "x");
  bad = eval true {
    services.wiz-ci-runner = {
      enable = true;
      tokenFile = storeToken;
      warm.enable = false;
    };
  };
  credential = eval true {
    services.wiz-ci-runner = {
      enable = true;
      tokenCredential = "wiz-ci-runner-token";
      warm.enable = false;
    };
  };
  # A minimal NixOS configuration has a couple of unrelated false assertions
  # (no filesystems, no boot loader).  Compare the number of false assertions:
  # the module adds none, and the store-token configuration adds exactly its
  # own tokenFile assertion.
  falseCount = assertions: builtins.length (builtins.filter (a: !a.assertion) assertions);
  baselineFalse = falseCount baseline.config.assertions;
  allOk = falseCount good.config.assertions == baselineFalse;
  badOk = falseCount bad.config.assertions == baselineFalse + 1;
in
if !allOk then throw "the enabled module failed its own assertions"
else if unit.serviceConfig.LoadCredential != [ "token:/run/secrets/wiz-ci-runner-token" ] then throw "LoadCredential is not the token file"
else if credential.config.systemd.services.wiz-ci-runner.serviceConfig.LoadCredential != [ "token:wiz-ci-runner-token" ] then throw "tokenCredential is not a systemd credential"
else if unit.serviceConfig.User != "root" then throw "registration does not start as root"
else if unit.serviceConfig.Restart != "always" then throw "the ephemeral runner does not restart"
else if !user.isSystemUser then throw "the runner user is not a system user"
else if !badOk then throw "a token in the Nix store was accepted"
else "ok"
EOF
)

result=$(nix eval --impure --raw --expr "$expr")
[[ $result == ok ]] || fail "module evaluation: $result"
pass "the module's unit, credential, and store-token assertions"

pass "all checks passed"
