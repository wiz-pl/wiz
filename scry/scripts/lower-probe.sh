#!/usr/bin/env bash
# lower-probe.sh SCRY FILE: run `scry taint FILE --progress`, stop it right after the
# lower stage, print the store/lower elapsed times and VmHWM at that moment.
scry=$1; f=$2
tmp=$(mktemp -d)
mkfifo "$tmp/err"
"$scry" taint "$f" --json --allow-errors --progress --timeout 0 2>"$tmp/err" >/dev/null &
pid=$!
store=""; lower=""
while IFS= read -r line; do
  case "$line" in
    *"[stage] store "*) store=$(sed -n 's/.*elapsed=\([0-9]*\)ms.*/\1/p' <<<"$line") ;;
    *"[stage] lower "*) lower=$(sed -n 's/.*elapsed=\([0-9]*\)ms.*/\1/p' <<<"$line")
       hwm=$(awk '/VmHWM/{print $2}' /proc/$pid/status)
       info=$(sed 's/.*elapsed=[0-9]*ms //' <<<"$line")
       kill $pid; break ;;
  esac
done <"$tmp/err"
wait $pid 2>/dev/null
rm -rf "$tmp"
echo "$(basename "$f") $(stat -c %s "$f")B store_ms=$store lower_ms=$((lower - store)) hwm_kb=$hwm [$info]"
