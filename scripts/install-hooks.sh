#!/bin/sh
# Install the checkout's git hooks: `pre-commit` runs the fast tier on the staged files,
# `pre-push` runs the full tier. Both call scripts/pre-commit.sh from the work tree, so
# a later edit to that script (or to the tiers) needs no reinstall.
#
#   scripts/install-hooks.sh           install both, if no hook is there
#   scripts/install-hooks.sh --force   replace an existing hook (it is not backed up:
#                                      copy it away first if it does something you keep)
#
# A hook that is already byte-for-byte the one this script writes is left alone, so
# running it twice is safe. Any other existing hook is an error without --force: the
# script never silently replaces someone's hook. `core.hooksPath` is respected (the
# hook goes where git will look for it). Exit status: 0 installed/kept, 1 refused,
# 2 usage error, 3 not a git checkout.
set -u

force=0
while [ $# -gt 0 ]; do
  case $1 in
    --force) force=1; shift ;;
    -h|--help) sed -n '2,15p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "install-hooks: unknown argument $1" >&2; exit 2 ;;
  esac
done

root=$(git rev-parse --show-toplevel 2>/dev/null) || {
  echo "install-hooks: not inside a git checkout" >&2
  exit 3
}
hooks=$(git rev-parse --git-path hooks 2>/dev/null) || {
  echo "install-hooks: cannot find the hooks directory" >&2
  exit 3
}
case $hooks in
  /*) ;;
  *) hooks=$PWD/$hooks ;;
esac
mkdir -p "$hooks" || exit 1

pre_commit_body() {
  cat <<EOF
#!/bin/sh
# Installed by $root/scripts/install-hooks.sh; remove this file to stop it.
# The fast tier on the staged files. Exit 3 means "nothing could run": allow the commit.
root=\$(git rev-parse --show-toplevel 2>/dev/null) || exit 0
"\$root/scripts/pre-commit.sh" --fast --staged
code=\$?
if [ "\$code" -eq 3 ]; then
  echo "pre-commit: skipped (no tool available)" >&2
  exit 0
fi
exit "\$code"
EOF
}

pre_push_body() {
  cat <<EOF
#!/bin/sh
# Installed by $root/scripts/install-hooks.sh; remove this file to stop it.
# The full tier: the fast checks plus the ledger, the reproducibility corpus and the
# formatter's tests. Exit 3 means "nothing could run": allow the push.
root=\$(git rev-parse --show-toplevel 2>/dev/null) || exit 0
"\$root/scripts/pre-commit.sh" --full
code=\$?
if [ "\$code" -eq 3 ]; then
  echo "pre-push: skipped (no tool available)" >&2
  exit 0
fi
exit "\$code"
EOF
}

install_one() { # NAME BODY-FUNCTION
  _ih_name=$1
  _ih_body=$2
  _ih_path=$hooks/$_ih_name
  _ih_new=$work/$_ih_name
  "$_ih_body" >"$_ih_new"
  if [ -f "$_ih_path" ] && cmp -s "$_ih_new" "$_ih_path"; then
    echo "install-hooks: $_ih_name is already up to date"
    rm -f "$_ih_new"
    return 0
  fi
  if [ -e "$_ih_path" ] && [ "$force" -ne 1 ]; then
    echo "install-hooks: $_ih_name exists and is not this script's hook;" \
      "not replacing it without --force" >&2
    rm -f "$_ih_new"
    return 1
  fi
  if ! mv "$_ih_new" "$_ih_path"; then
    rm -f "$_ih_new"
    return 1
  fi
  chmod +x "$_ih_path"
  echo "install-hooks: installed $_ih_name"
  return 0
}

work=$(mktemp -d "${TMPDIR:-/tmp}/wiz-install-hooks.XXXXXX") || exit 1
trap 'rm -rf "$work"' EXIT INT TERM

status=0
install_one pre-commit pre_commit_body || status=1
install_one pre-push pre_push_body || status=1
exit "$status"
