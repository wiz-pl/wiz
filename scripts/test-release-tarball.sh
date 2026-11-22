#!/bin/sh
# Is the binary release tarball (scripts/release-tarball.sh) reproducible?
#
#   scripts/test-release-tarball.sh [options] [REV]
#
# It runs release-tarball.sh twice for one commit, in two independent roots, with a
# deliberately different environment each time:
#
#   PWD                 the two roots (also a different absolute path length)
#   HOME, TMPDIR        separate directories (no shared cache or temp file)
#   umask               022 vs 077
#   LC_ALL              C vs C.UTF-8
#   TZ                  UTC vs Asia/Tokyo
#   SOURCE_DATE_EPOCH   1111111111 vs 1700000000 (the tarball must derive its own
#                       epoch from the commit: see release-tarball.sh)
#
# and then:
#
#   * cmp's the two tarballs and their .sha256 files;
#   * writes a per-member manifest (path, type, mode, size, mtime, uid/gid, sha256)
#     for each tarball and compares them, so a mismatch names the FIRST differing
#     member and the field that differs;
#   * checks the archive's canonical metadata (sorted, uid/gid 0, one epoch, one
#     mode per kind, no `..` or absolute names);
#   * optionally scans every member for an absolute build path ($HOME, $TMPDIR, the
#     two roots) and (with --strict) for /nix/store.
#
# The default mode is the cheap one: the build outputs are supplied with --bindir
# (and --cc/--web) and copied unchanged, so only the archive layer is compared. That
# is the check a pull request runs. --full builds wiz, grail and tower from REV in
# each root instead, which is what a tag/nightly wants; --build-cc adds the bundled C
# toolchain (GMP/GC, minutes) to that.
#
# A difference exits 1 and leaves the two manifests in the printed work directory
# (--keep keeps the whole tree, including both tarballs). Usage and input errors
# exit 2.
#
#   scripts/test-release-tarball.sh                       # archive layer, HEAD
#   scripts/test-release-tarball.sh --full v0.1.0         # two full builds
#   scripts/test-release-tarball.sh --bindir out/bin --cc cc-bundle --web web-out
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
# A `heavy` job can inherit a PATH without cc (AGENTS.md); grail's default compiler is
# `cc`, so put a gcc wrapper first when there is one but it is not on PATH.
if ! command -v cc >/dev/null 2>&1; then
  for c in /nix/store/*-gcc-wrapper-*/bin/cc; do
    [ -x "$c" ] && { PATH=$(dirname "$c"):$PATH; export PATH; break; }
  done
fi

usage() {
  sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'
  exit 2
}

full=no
build_cc=no
keep=no
leak_scan=yes
strict=no
bindir=
ccdir=
webdir=
revarg=HEAD
jobs=$( (nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2) )
downloads=

while [ $# -gt 0 ]; do
  case $1 in
    --full) full=yes ;;
    --build-cc) build_cc=yes ;;
    --keep) keep=yes ;;
    --no-leak-scan) leak_scan=no ;;
    --strict) strict=yes ;;
    --bindir) shift; bindir=${1:?--bindir needs a directory} ;;
    --cc) shift; ccdir=${1:?--cc needs a directory} ;;
    --web) shift; webdir=${1:?--web needs a directory} ;;
    --downloads) shift; downloads=${1:?--downloads needs a directory} ;;
    --jobs) shift; jobs=${1:?--jobs needs a number} ;;
    --rev) shift; revarg=${1:?--rev needs a commit} ;;
    -h|--help) usage ;;
    -*) echo "test-release-tarball: unknown option $1" >&2; usage ;;
    *) revarg=$1 ;;
  esac
  shift
done

start_seconds=$(date +%s)
fail() {
  echo "release-tarball test: $*" >&2
  work_kept=yes
  [ -z "${work:-}" ] || echo "work directory: $work" >&2
  exit 1
}
die() { echo "test-release-tarball: $*" >&2; exit 2; }
abs() { case $1 in /*) echo "$1" ;; *) echo "$(cd "$1" && pwd)" ;; esac; }

# --- the commit ----------------------------------------------------------------------
# WIZ_RELEASE_SRC is the checkout that has the commit (a `heavy --rsync` copy has no
# .git); it defaults to the repository this script is in.
src=${WIZ_RELEASE_SRC:-}
[ -n "$src" ] || src=$(git -C "$root" rev-parse --show-toplevel 2>/dev/null) || \
  die "not a git checkout: run this beside a commit, or set WIZ_RELEASE_SRC"
rev=$(git -C "$src" rev-parse --verify "$revarg^{commit}" 2>/dev/null) || \
  die "$revarg is not a commit"
epoch=$(git -C "$src" log -1 --format=%ct "$rev")
arch=${WIZ_RELEASE_ARCH:-$(uname -m)}
name=wiz-$arch-linux

if [ "$build_cc" = yes ] && [ "$full" = no ]; then
  die "--build-cc needs --full (it builds the bundle in each root)"
fi
[ -n "$ccdir" ] && ccdir=$(abs "$ccdir")
[ -n "$webdir" ] && webdir=$(abs "$webdir")
if [ "$full" = no ]; then
  [ -n "$bindir" ] || bindir=$root/.lake/build/bin
  bindir=$(abs "$bindir")
  [ -x "$bindir/wiz" ] || die "$bindir has no wiz (build it, or pass --full)"
  [ -x "$bindir/grail" ] || die "$bindir has no grail (build it, or pass --full)"
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/wiz-release-repro.XXXXXX")
work_kept=no
cleanup() { [ "$keep" = yes ] || [ "$work_kept" = yes ] || rm -rf "$work"; }
trap cleanup EXIT INT TERM
if [ "$keep" = yes ]; then
  echo "work directory: $work"
fi

# --- two roots at one commit ---------------------------------------------------------
extract() { # DIR
  mkdir -p "$1"
  git -C "$src" archive --format=tar "$rev" | tar -xf - -C "$1"
}
extract "$work/a/repo"
extract "$work/b/repo"

# --- the two environments ------------------------------------------------------------
umask_a=022; umask_b=077
lc_a=C; lc_b=C.UTF-8
tz_a=UTC; tz_b=Asia/Tokyo
epoch_a=1111111111; epoch_b=1700000000

for side in a b; do
  mkdir -p "$work/$side/home" "$work/$side/tmp" "$work/$side/out"
done

# Lean's toolchain lives under HOME for an elan install. HOME must vary (it is one of
# the inputs under test) but the compiler must not: pin ELAN_HOME when it is set, or
# keep the real ~/.elan reachable through the per-side HOME.
real_home=${HOME:-}
if [ -n "${ELAN_HOME:-}" ]; then
  elan_home=$ELAN_HOME
elif [ -n "$real_home" ] && [ -d "$real_home/.elan" ]; then
  elan_home=$real_home/.elan
else
  elan_home=
fi

# The build command for --full. RELEASE_BUILD_CMD overrides it (the caller may know
# how to reach its toolchain); it runs with cwd = the root and the side's environment.
build_full() { # SIDE
  side=$1
  # The default build: wiz and grail with lake, then tower. build-tower-wiz.sh builds
  # in a temp dir, so it does not read the root's grail.local.wiz; pass the checkout's
  # machine settings as flags (the release job does the same). A caller whose toolchain
  # is different sets RELEASE_BUILD_CMD.
  cat > "$work/$side/build.sh" <<'EOS'
set -eu
export C_INCLUDE_PATH="$(lean --print-prefix)/include/clang:/usr/include/x86_64-linux-gnu:/usr/include"
export LEAN_NUM_THREADS="${WIZ_RELEASE_JOBS:-4}"
t0=$(date +%s)
lake build wiz grail
echo "build seconds: $(( $(date +%s) - t0 ))"
# Lean's include path is for lake's C link; grail's tower link uses the C compiler's
# own headers, and a Nix gcc wrapper finds them only with a clean C_INCLUDE_PATH
unset C_INCLUDE_PATH
flags=
if [ -f grail.local.wiz ]; then
  flags=$(awk -F'"' '/Settings.set "(cflags|ldflags|gc-cflags|gc-ldflags|llc)"/ { printf " --%s \"%s\"", $2, $4 }' grail.local.wiz)
fi
eval "scripts/build-tower-wiz.sh .lake/build/bin/tower .lake/build/bin/grail $flags"
# the step's cgroup peak: the number heavy-local prints for a --rsync job
cg=$(sed -n 's/^0:://p' /proc/self/cgroup)
if [ -n "$cg" ] && [ -r "/sys/fs/cgroup$cg/memory.peak" ]; then
  echo "build cgroup peak: $(cat "/sys/fs/cgroup$cg/memory.peak") bytes"
fi
EOS
  (
    cd "$work/$side/repo"
    # the checkout's toolchain settings (GMP/GC/llc paths) for `grail build`; a
    # release in CI has none and takes them from the bundled C toolchain
    [ -f "$root/grail.local.wiz" ] && cp "$root/grail.local.wiz" .
    umask "$(eval echo \$umask_$side)"
    if [ -n "${RELEASE_BUILD_CMD:-}" ]; then
      set -- sh -c "$RELEASE_BUILD_CMD"
    else
      set -- sh "$work/$side/build.sh"
    fi
    env HOME="$work/$side/home" TMPDIR="$work/$side/tmp" \
      LC_ALL="$(eval echo \$lc_$side)" TZ="$(eval echo \$tz_$side)" \
      ${elan_home:+ELAN_HOME="$elan_home"} WIZ_RELEASE_JOBS="$jobs" \
      SOURCE_DATE_EPOCH="$(eval echo \$epoch_$side)" \
      "$@"
  )
}

tarball() { # SIDE
  side=$1
  (
    cd "$work/$side/repo"
    umask "$(eval echo \$umask_$side)"
    if [ "$full" = yes ]; then
      b=$work/$side/repo/.lake/build/bin
    else
      b=$bindir
    fi
    cc=${ccdir:-}
    web=${webdir:-}
    if [ "$build_cc" = yes ]; then cc=$work/$side/repo/cc-bundle; fi
    if [ "$full" = yes ] && [ "$build_cc" = yes ]; then
      ( cd "$work/$side/repo"
        [ -z "$downloads" ] || ln -sfn "$downloads" bundle-downloads
        umask "$(eval echo \$umask_$side)"
        env HOME="$work/$side/home" TMPDIR="$work/$side/tmp" \
          LC_ALL="$(eval echo \$lc_$side)" TZ="$(eval echo \$tz_$side)" \
          sh scripts/bundle-cc.sh cc-bundle bundle-downloads ) || return
    fi
    env HOME="$work/$side/home" TMPDIR="$work/$side/tmp" \
      LC_ALL="$(eval echo \$lc_$side)" TZ="$(eval echo \$tz_$side)" \
      ${elan_home:+ELAN_HOME="$elan_home"} \
      SOURCE_DATE_EPOCH="$(eval echo \$epoch_$side)" \
      sh "$here/release-tarball.sh" "$work/$side/out/$name.tar.gz" \
        "$b" "$rev" "$cc" "$web" "$src"
  )
}

if [ "$full" = yes ]; then
  for side in a b; do
    echo "release-tarball test: building in root $side ($work/$side/repo)" >&2
    build_full "$side" || fail "the build in root $side failed"
  done
fi
for side in a b; do
  echo "release-tarball test: tarball in root $side" >&2
  tarball "$side" || fail "release-tarball.sh failed in root $side"
done

a=$work/a/out/$name.tar.gz
b=$work/b/out/$name.tar.gz
[ -f "$a" ] || fail "root a wrote no $a"
[ -f "$b" ] || fail "root b wrote no $b"

# --- per-member manifests ------------------------------------------------------------
if ! python3 - "$a" "$b" "$work/a/manifest.tsv" "$work/b/manifest.tsv" "$epoch" <<'PY'
import hashlib, sys, tarfile

tarballs = sys.argv[1:3]
out = sys.argv[3:5]
epoch = int(sys.argv[5])
side = ["a", "b"]
members = []
for path in tarballs:
    tf = tarfile.open(path, "r:gz")
    rows = []
    for m in tf.getmembers():
        if m.isfile():
            data = tf.extractfile(m).read()
            digest = hashlib.sha256(data).hexdigest()
            kind = "f"
        elif m.isdir():
            digest, kind = "-", "d"
        else:
            digest, kind = "-", "l" if m.issym() else "?"
        rows.append(dict(path=m.name, kind=kind, mode=f"{m.mode:04o}", size=m.size,
                         mtime=m.mtime, uid=m.uid, gid=m.gid,
                         uname=m.uname, gname=m.gname, sha256=digest))
    members.append(rows)

for rows, path in zip(members, out):
    with open(path, "w", encoding="utf-8") as f:
        f.write("path\tkind\tmode\tsize\tmtime\tuid\tgid\tuname\tgname\tsha256\n")
        for r in rows:
            f.write("\t".join(str(r[k]) for k in
                              ("path", "kind", "mode", "size", "mtime", "uid", "gid",
                               "uname", "gname", "sha256")) + "\n")

# canonical metadata
for s, rows in zip(side, members):
    names = [r["path"] for r in rows]
    assert names, f"root {s}: the tarball is empty"
    assert names == sorted(names), f"root {s}: members are not sorted"
    top = names[0].split("/")[0]
    assert all(n == top or n.startswith(top + "/") for n in names), \
        f"root {s}: a member is outside the top directory"
    assert all(not n.startswith("/") and ".." not in n.split("/") for n in names), \
        f"root {s}: an absolute or .. path"
    for r in rows:
        assert r["mtime"] == epoch, \
            f"root {s}: {r['path']}: mtime {r['mtime']} is not the commit time {epoch}"
        assert r["uid"] == 0 and r["gid"] == 0 and r["uname"] == "" and r["gname"] == "", \
            f"root {s}: {r['path']}: not owned by 0:0"
        if r["kind"] == "d":
            assert r["mode"] == "0755", f"root {s}: {r['path']}: directory mode {r['mode']}"
        else:
            assert r["mode"] in ("0644", "0755"), \
                f"root {s}: {r['path']}: mode {r['mode']} is not canonical"
print(f"ok: {len(members[0])} members, canonical metadata (epoch {epoch}, 0:0, one mode per kind)")

if members[0] == members[1]:
    print("ok: the two per-member manifests are equal")
    sys.exit(0)

# name the first differing member, and what differs
A, B = members
n = min(len(A), len(B))
i = 0
while i < n and A[i] == B[i]:
    i += 1
if i == n and len(A) == len(B):
    print("first differing member: none (the manifests are equal)", file=sys.stderr)
elif i == n:
    longer, rows = ("a", A) if len(A) > len(B) else ("b", B)
    extra = rows[i:]
    print(f"first differing member: {extra[0]['path']} "
          f"(only in {longer}; {len(extra)} extra member(s))", file=sys.stderr)
else:
    ra, rb = A[i], B[i]
    if ra["path"] != rb["path"]:
        print(f"first differing member: {ra['path']} (a) vs {rb['path']} (b)",
              file=sys.stderr)
        onlya = {r["path"] for r in A} - {r["path"] for r in B}
        onlyb = {r["path"] for r in B} - {r["path"] for r in A}
        if onlya:
            print(f"  only in a: {sorted(onlya)[:5]}", file=sys.stderr)
        if onlyb:
            print(f"  only in b: {sorted(onlyb)[:5]}", file=sys.stderr)
    else:
        fields = [k for k in ra if ra[k] != rb[k]]
        print(f"first differing member: {ra['path']}: "
              + ", ".join(f"{k} {ra[k]!r} != {rb[k]!r}" for k in fields),
              file=sys.stderr)
sys.exit(1)
PY
then
  fail "the per-member manifests differ (see $work/a/manifest.tsv and $work/b/manifest.tsv)"
fi

# --- the archive itself --------------------------------------------------------------
if cmp -s "$a" "$b"; then
  h=$(sha256sum "$a" | cut -d' ' -f1)
  echo "ok: two builds in different roots and environments are byte-identical (sha256 $h)"
else
  # The manifest comparison above named the first differing member.
  fail "the tarballs differ"
fi

if cmp -s "$a.sha256" "$b.sha256"; then
  echo "ok: the .sha256 files are identical"
else
  fail "the .sha256 files differ"
fi
# and the .sha256 really is the tarball's digest, with the expected basename
want=$(sha256sum "$a" | cut -d' ' -f1)
got=$(cut -d' ' -f1 "$a.sha256")
[ "$want" = "$got" ] || fail "$a.sha256 does not name the tarball's digest"
grep -q "  $name.tar.gz\$" "$a.sha256" || fail "$a.sha256 does not name $name.tar.gz"

# --- absolute paths in the members ---------------------------------------------------
# Every member is scanned as bytes (so an ELF's strings are covered), and the text
# members are also scanned for the caller's $HOME and for the tool input directories
# --cc/--web/--bindir. sysroot/usr/include/*.h is text: GMP's gmp.h records __GMP_CC,
# which used to be the absolute $out/bin/cc and so leaked the bundle directory into a
# header the release promises is path-free.
if [ "$leak_scan" = yes ]; then
  python3 - "$a" "$work/a/repo" "$work/b/repo" "$work/a/home" "$work/b/home" \
    "$work/a/tmp" "$work/b/tmp" "$strict" "$ccdir" "$webdir" "$bindir" \
    "$real_home" <<'PY'
import re, sys, tarfile

path = sys.argv[1]
patterns = [p for p in sys.argv[2:8] if p]
strict = sys.argv[8] == "yes"
ccdir, webdir, bindir, home = sys.argv[9], sys.argv[10], sys.argv[11], sys.argv[12]
tools = [p for p in (ccdir, webdir, bindir) if p]
text_suffixes = (".h", ".hpp", ".c", ".inc", ".lean", ".wiz", ".txt", ".md", ".json",
                 ".mjs", ".js", ".css", ".html", ".py", ".sh", ".toml", ".lock")
text_names = {"LICENSE", "NOTICE", "REVISION", "TOOLCHAIN", "VERSIONS",
              "COPYING.RUNTIME"}
tf = tarfile.open(path, "r:gz")
hits = 0


def hit(message):
    global hits
    print(f"release-tarball test: {message}", file=sys.stderr)
    hits += 1


for m in tf.getmembers():
    if not m.isfile():
        continue
    data = tf.extractfile(m).read()
    for p in patterns + tools:
        if p.encode() in data:
            hit(f"{m.name} contains the build path {p}")
    base = m.name.rsplit("/", 1)[-1]
    is_text = m.name.lower().endswith(text_suffixes) or base in text_names
    if home and is_text and home.encode() in data:
        hit(f"{m.name} is text and contains $HOME ({home})")
    if m.name.endswith("/sysroot/usr/include/gmp.h"):
        mm = re.search(rb'^#define\s+__GMP_CC\s+"([^"]*)"', data, re.M)
        if mm and mm.group(1).startswith(b"/"):
            hit(f"{m.name}: __GMP_CC is the absolute path "
                f"{mm.group(1).decode(errors='replace')} (it must be \"cc\")")
    if strict and b"/nix/store" in data:
        hit(f"{m.name} contains a /nix/store path")
if hits:
    sys.exit(1)
print("ok: no member contains a build root, tool input or /tmp path"
      + (", text $HOME" if home else "")
      + (", or /nix/store" if strict else ""))
PY
fi

# --- does an ELF's RUNPATH/RPATH name the builder? ----------------------------------
# wiz and grail are linked by Lean with a RUNPATH to the toolchain lib directory (a
# path under the builder's HOME) and, on a Nix machine, /nix/store. This is a
# diagnostic, not a failure: the two-build comparison above is the oracle, and a
# RUNPATH is normalised only if it actually differs between two roots.
if [ "$leak_scan" = yes ] && command -v readelf >/dev/null 2>&1; then
  python3 - "$a" "$name" "$real_home" "$work" "$strict" <<'PY'
import os, subprocess, sys, tarfile

path, name, home, work, strict = sys.argv[1:6]
strict = strict == "yes"
targets = {
    f"{name}/share/wiz/.lake/build/bin/wiz",
    f"{name}/share/wiz/.lake/build/bin/grail",
    f"{name}/bin/tower",
}
tf = tarfile.open(path, "r:gz")
tmp = os.path.join(work, "elf-check")
os.makedirs(tmp, exist_ok=True)
bad = []
seen = 0
for m in tf.getmembers():
    if m.name not in targets or not m.isfile():
        continue
    data = tf.extractfile(m).read()
    if not data.startswith(b"\x7fELF"):
        continue
    seen += 1
    f = os.path.join(tmp, os.path.basename(m.name))
    with open(f, "wb") as out:
        out.write(data)
    out = subprocess.run(["readelf", "-d", f], capture_output=True, text=True)
    for line in out.stdout.splitlines():
        if "RUNPATH" not in line and "RPATH" not in line:
            continue
        value = line.split("[", 1)[-1].rstrip("]")
        for entry in value.split(":"):
            if not entry.startswith("/"):
                continue  # $ORIGIN/... is relative to the install, and is fine
            hit = [p for p in (home, work) if p and
                   (entry == p or entry.startswith(p.rstrip("/") + "/"))]
            if hit or (strict and entry.startswith("/nix/store")):
                bad.append((m.name, entry))
if bad:
    for member, entry in bad:
        print(f"release-tarball test: warning: {member}: RUNPATH names the builder: "
              f"{entry}", file=sys.stderr)
    print("release-tarball test: warning: the RUNPATH is a builder path, but the "
          "two same-image builds above are the oracle; it is not normalised",
          file=sys.stderr)
else:
    print(f"ok: {seen} ELF command(s) have no RUNPATH naming the builder")
PY
fi

echo "release-tarball test: total $(( $(date +%s) - start_seconds )) s"
echo "release-tarball test: ok"
