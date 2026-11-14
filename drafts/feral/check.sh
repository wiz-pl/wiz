#!/bin/sh
# Check the Feral drafts from the worktree root (after `lake build`):
#   sh drafts/feral/check.sh
# * the runtime stand-ins and every hand-lowered program check;
# * every surface program (lib/Feral.wiz lowers it) checks;
# * every program of rejected/surface is rejected by the front end, and every hand-written
#   lowering in rejected/ by the kernel (a type error, or a private constructor).
# The test group `feral` (lake test -- '=feral') checks more: results against the
# hand-lowered programs, error classes and lines, and the kernel's verdict on the
# `#unchecked` lowering of each rejected program.
set -e
WIZ=${WIZ:-./.lake/build/bin/wiz}
for f in drafts/feral/lib/FeralCore.wiz drafts/feral/lowered/*.wiz drafts/feral/surface/*.wiz; do
  echo "== $f"
  "$WIZ" check -I drafts/feral/lib "$f"
done
for f in drafts/feral/rejected/surface/*.wiz; do
  echo "== $f (must be rejected by the front end)"
  if out=$("$WIZ" check -I drafts/feral/lib "$f" 2>&1); then
    echo "accepted, but it must be rejected: $f"; exit 1
  fi
  want=$(sed -n 's/^-- expect: \(.*\) at .*/\1/p' "$f")
  case "$out" in
    *"generated source"*) echo "the front end missed it:"; echo "$out"; exit 1 ;;
    *"$want"*) echo "rejected: $(echo "$out" | head -1)" ;;
    *) echo "rejected for another reason:"; echo "$out"; exit 1 ;;
  esac
done
for f in drafts/feral/rejected/*.wiz; do
  echo "== $f (must be rejected)"
  if out=$("$WIZ" check -I drafts/feral/lib "$f" 2>&1); then
    echo "accepted, but Rust rejects it: $f"; exit 1
  fi
  case "$out" in
    *"type mismatch"*|*"is private to module Region"*|*"quantity"*) echo "rejected: $(echo "$out" | head -1)" ;;
    *) echo "rejected for another reason:"; echo "$out"; exit 1 ;;
  esac
done
