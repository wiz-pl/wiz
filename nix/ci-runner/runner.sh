#!/usr/bin/env bash
# The Wiz ephemeral CI runner.
#
# `run` starts as root so that it can read the registration token from the
# systemd credential directory, registers an ephemeral runner, and then drops
# to the unprivileged runner user before the listener (and therefore any job)
# starts.  The credential is never visible to that user.
#
# `cleanup` runs as root from ExecStopPost: it removes a stale registration
# through the GitHub API (when the token is a personal access token), then
# wipes the runner and work directories so the next job starts empty.

set -euo pipefail

log() {
  printf 'wiz-ci-runner: %s\n' "$*" >&2
}

die() {
  log "$*"
  exit 1
}

usage() {
  cat <<'EOF'
usage: wiz-ci-runner run|cleanup|check

The settings are read from the environment set by services.wiz-ci-runner:
  WIZ_CI_RUNNER_URL, WIZ_CI_RUNNER_NAME, WIZ_CI_RUNNER_LABELS,
  WIZ_CI_RUNNER_TOKEN_TYPE, WIZ_CI_RUNNER_API_URL, WIZ_CI_RUNNER_SCOPE,
  WIZ_CI_RUNNER_STATE_DIR, WIZ_CI_RUNNER_WORK_DIR, WIZ_CI_RUNNER_USER,
  WIZ_CI_RUNNER_GROUP, WIZ_CI_RUNNER_GITHUB_RUNNER
and the token from $CREDENTIALS_DIRECTORY/token.
EOF
}

need() {
  local name=$1
  [[ -n ${!name:-} ]] || die "$name is not set"
}

need_absolute() {
  local name=$1 value=${!1:-}
  [[ $value == /* && $value != / ]] || die "$name must be an absolute directory (not /): $value"
}

load_token() {
  local directory=${CREDENTIALS_DIRECTORY:-}
  [[ -n $directory ]] ||
    die "CREDENTIALS_DIRECTORY is not set; run this through systemd with LoadCredential=token:..."
  [[ -r $directory/token ]] || die "the token credential is not readable"
  tr -d '\r\n' <"$directory/token"
}

is_access_token() {
  [[ $1 =~ ^gh[pousr]_ ]] || [[ $1 =~ ^github_pat_ ]]
}

api_base() {
  printf '%s' "${WIZ_CI_RUNNER_API_URL%/}"
}

# The scope is "repo:owner/name" or "org:owner"; the module derives it from
# the URL and lets GitHub Enterprise hosts set it explicitly.
runner_endpoint() {
  local scope=${WIZ_CI_RUNNER_SCOPE:-}
  local kind=${scope%%:*} name=${scope#*:}
  [[ -n $kind && -n $name && $kind != "$scope" ]] ||
    die "WIZ_CI_RUNNER_SCOPE must be repo:owner/name or org:owner"
  case $kind in
    repo) printf '/repos/%s/actions/runners' "$name" ;;
    org) printf '/orgs/%s/actions/runners' "$name" ;;
    *) die "WIZ_CI_RUNNER_SCOPE must be repo:owner/name or org:owner: $scope" ;;
  esac
}

api() {
  local token=$1
  shift
  curl --fail --silent --show-error --location \
    --retry 3 --retry-delay 2 --max-time 30 \
    -H "Authorization: Bearer $token" \
    -H "Accept: application/vnd.github+json" \
    -H "X-GitHub-Api-Version: 2022-11-28" \
    "$@"
}

# A personal access token is exchanged for a fresh, one-use registration token
# here, so no registration token has to be rotated on the host.
registration_token() {
  local token=$1
  local type=${WIZ_CI_RUNNER_TOKEN_TYPE:-auto}

  if [[ $type == auto ]]; then
    if is_access_token "$token"; then
      type=access
    else
      type=registration
    fi
  fi

  case $type in
    registration)
      printf '%s' "$token"
      ;;
    access)
      if ! is_access_token "$token"; then
        die "WIZ_CI_RUNNER_TOKEN_TYPE=access but the token does not look like a GitHub access token"
      fi
      api "$token" -X POST "$(api_base)$(runner_endpoint)/registration-token" | jq -er '.token'
      ;;
    *)
      die "WIZ_CI_RUNNER_TOKEN_TYPE must be auto, access, or registration: $type"
      ;;
  esac
}

check_env() {
  local name
  for name in \
    WIZ_CI_RUNNER_URL \
    WIZ_CI_RUNNER_NAME \
    WIZ_CI_RUNNER_LABELS \
    WIZ_CI_RUNNER_TOKEN_TYPE \
    WIZ_CI_RUNNER_API_URL \
    WIZ_CI_RUNNER_SCOPE \
    WIZ_CI_RUNNER_STATE_DIR \
    WIZ_CI_RUNNER_WORK_DIR \
    WIZ_CI_RUNNER_USER \
    WIZ_CI_RUNNER_GROUP \
    WIZ_CI_RUNNER_GITHUB_RUNNER
  do
    need "$name"
  done

  need_absolute WIZ_CI_RUNNER_STATE_DIR
  need_absolute WIZ_CI_RUNNER_WORK_DIR
  [[ -x $WIZ_CI_RUNNER_GITHUB_RUNNER/bin/config.sh ]] ||
    die "$WIZ_CI_RUNNER_GITHUB_RUNNER does not contain the GitHub Actions runner"
  runner_endpoint >/dev/null
}

check() {
  check_env
  local token type
  token=$(load_token)
  [[ -n $token ]] || die "the token credential is empty"

  type=${WIZ_CI_RUNNER_TOKEN_TYPE:-auto}
  if [[ $type == auto ]]; then
    if is_access_token "$token"; then type=access; else type=registration; fi
  fi
  case $type in
    access | registration) ;;
    *) die "WIZ_CI_RUNNER_TOKEN_TYPE must be auto, access, or registration: $type" ;;
  esac

  log "configuration is valid: url=$WIZ_CI_RUNNER_URL name=$WIZ_CI_RUNNER_NAME labels=$WIZ_CI_RUNNER_LABELS token=$type"
}

prepare_dirs() {
  install -d -m 0700 -o "$WIZ_CI_RUNNER_USER" -g "$WIZ_CI_RUNNER_GROUP" "$WIZ_CI_RUNNER_STATE_DIR"
  install -d -m 0700 -o "$WIZ_CI_RUNNER_USER" -g "$WIZ_CI_RUNNER_GROUP" "$WIZ_CI_RUNNER_WORK_DIR"
  find "$WIZ_CI_RUNNER_STATE_DIR" -mindepth 1 -maxdepth 1 -exec rm -rf -- {} +
  find "$WIZ_CI_RUNNER_WORK_DIR" -mindepth 1 -maxdepth 1 -exec rm -rf -- {} +
}

run() {
  [[ $EUID -eq 0 ]] || die "run must start as root (it registers the runner, then drops privileges)"
  check_env

  local token registration
  token=$(load_token)
  [[ -n $token ]] || die "the token credential is empty"
  registration=$(registration_token "$token")

  prepare_dirs

  local -a args=(
    --unattended
    --disableupdate
    --replace
    --ephemeral
    --url "$WIZ_CI_RUNNER_URL"
    --token "$registration"
    --work "$WIZ_CI_RUNNER_WORK_DIR"
    --labels "$WIZ_CI_RUNNER_LABELS"
  )
  [[ -n ${WIZ_CI_RUNNER_NAME:-} ]] && args+=(--name "$WIZ_CI_RUNNER_NAME")

  log "registering ephemeral runner ${WIZ_CI_RUNNER_NAME} for $WIZ_CI_RUNNER_URL"
  (
    export HOME=$WIZ_CI_RUNNER_WORK_DIR
    export RUNNER_ROOT=$WIZ_CI_RUNNER_STATE_DIR
    export RUNNER_ALLOW_RUNASROOT=1
    cd "$WIZ_CI_RUNNER_STATE_DIR"
    "$WIZ_CI_RUNNER_GITHUB_RUNNER/bin/config.sh" "${args[@]}"
  )

  chown -R "$WIZ_CI_RUNNER_USER:$WIZ_CI_RUNNER_GROUP" \
    "$WIZ_CI_RUNNER_STATE_DIR" "$WIZ_CI_RUNNER_WORK_DIR"

  # The listener, and every job it runs, must not inherit the PAT or the
  # credential-directory path.  It runs as the unprivileged user, for whom the
  # systemd credential directory is unreadable.
  unset token registration
  log "running one job as $WIZ_CI_RUNNER_USER"
  exec setpriv \
    --reuid="$WIZ_CI_RUNNER_USER" \
    --regid="$WIZ_CI_RUNNER_GROUP" \
    --init-groups \
    env -u CREDENTIALS_DIRECTORY -u RUNNER_ALLOW_RUNASROOT \
    HOME="$WIZ_CI_RUNNER_WORK_DIR" \
    RUNNER_ROOT="$WIZ_CI_RUNNER_STATE_DIR" \
    "$WIZ_CI_RUNNER_GITHUB_RUNNER/bin/run.sh"
}

clean_dir() {
  local directory=$1
  [[ $directory == /var/lib/wiz-ci-runner/* ]] ||
    die "refusing to clean a directory outside /var/lib/wiz-ci-runner: $directory"
  [[ -d $directory ]] || return 0
  find "$directory" -mindepth 1 -maxdepth 1 -exec rm -rf -- {} +
}

cleanup() {
  # An ephemeral runner unregisters itself after its one job.  If the service
  # was stopped first, or the listener died before it could do that, remove
  # the registration by name.  A registration token cannot list runners, so
  # this needs a PAT; a failure is not fatal (the runner is already gone, or
  # an administrator must remove it by hand).
  if [[ ${WIZ_CI_RUNNER_SKIP_CLEANUP:-0} != 1 ]]; then
    local token=
    if token=$(load_token 2>/dev/null) && [[ -n $token ]] && is_access_token "$token"; then
      local ids id
      ids=$(
        api "$token" "$(api_base)$(runner_endpoint)?per_page=100" 2>/dev/null |
          jq -r --arg name "${WIZ_CI_RUNNER_NAME:-}" \
            '.runners[]? | select(.name == $name) | .id' 2>/dev/null || true
      )
      for id in $ids; do
        log "deregistering runner $id ($WIZ_CI_RUNNER_NAME)"
        api "$token" -X DELETE "$(api_base)$(runner_endpoint)/$id" >/dev/null 2>&1 ||
          log "runner $id was already gone"
      done
    fi
  fi

  [[ -n ${WIZ_CI_RUNNER_STATE_DIR:-} ]] && clean_dir "$WIZ_CI_RUNNER_STATE_DIR"
  [[ -n ${WIZ_CI_RUNNER_WORK_DIR:-} ]] && clean_dir "$WIZ_CI_RUNNER_WORK_DIR"
  return 0
}

case ${1:-} in
  run) run ;;
  cleanup) cleanup ;;
  check) check ;;
  -h | --help | help) usage ;;
  *)
    usage >&2
    exit 2
    ;;
esac
