#!/bin/sh
# The source tarball (scripts/source-tarball.py) is deterministic, its manifest matches
# the tarball, and a different SOURCE_DATE_EPOCH changes only the metadata.
#
#   scripts/test-source-tarball.sh
#
# No toolchain and no build: it runs the script a few times on this checkout (git mode)
# and on a small synthetic tree (tree mode, the Nix path). A few seconds.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT INT TERM

fail() { echo "source-tarball test: $*" >&2; exit 1; }
sha() { sha256sum "$1" | cut -d' ' -f1; }

# --- two builds, different directory, cache-free environment, umask and locale --------
(
  cd "$root"
  umask 022
  SOURCE_DATE_EPOCH=1700000000 TZ=UTC LANG=C PYTHONHASHSEED=1 \
    python3 scripts/source-tarball.py --out "$tmp/a" --mode git >/dev/null
)
mkdir -p "$tmp/home"
(
  cd "$tmp"
  umask 077
  HOME="$tmp/home" TZ=Asia/Tokyo LANG=en_US.UTF-8 SOURCE_DATE_EPOCH=1700000000 \
    PYTHONHASHSEED=2 PYTHONPYCACHEPREFIX="$tmp/pycache" \
    python3 "$here/source-tarball.py" --root "$root" --out "$tmp/b" --mode git >/dev/null
)
a=$(ls "$tmp/a"/*.tar.gz)
b=$(ls "$tmp/b"/*.tar.gz)
cmp "$a" "$b" || fail "two builds in different directories differ"
cmp "$a.manifest.json" "$b.manifest.json" || fail "the manifests differ"
cmp "$a.sha256" "$b.sha256" || fail "the .sha256 files differ"
h=$(sha "$a")
echo "ok: two builds are identical (sha256 $h)"

# --- a different SOURCE_DATE_EPOCH: only the metadata changes --------------------------
(
  cd "$tmp"
  SOURCE_DATE_EPOCH=1234567890 \
    python3 "$here/source-tarball.py" --root "$root" --out "$tmp/c" --mode git >/dev/null
)
c=$(ls "$tmp/c"/*.tar.gz)
cmp -s "$a" "$c" && fail "a different SOURCE_DATE_EPOCH did not change the tarball"
python3 - "$a.manifest.json" "$c.manifest.json" <<'PY'
import json, sys
a, c = (json.load(open(p)) for p in sys.argv[1:])
assert a["tree"] == c["tree"], "the tree digest changed with the epoch"
assert a["files"] == c["files"], "the file content hashes changed with the epoch"
for k in ("schema", "name", "revision"):
    assert a[k] == c[k], f"{k} changed with the epoch"
assert a["sourceDateEpoch"] != c["sourceDateEpoch"]
assert a["tarball"] != c["tarball"]
PY
echo "ok: SOURCE_DATE_EPOCH changes the tarball digest, not the tree digest"

# --- the manifest matches the tarball, and the archive is canonical -------------------
python3 - "$a" <<'PY'
import hashlib, json, sys, tarfile
path = sys.argv[1]
raw = open(path + ".manifest.json", "rb").read()
m = json.loads(raw)
assert raw == json.dumps(m, sort_keys=True, separators=(",", ":")).encode(), \
    "the manifest is not canonical JSON"
tf = tarfile.open(path, "r:gz")
members = tf.getmembers()
assert [x.name for x in members] == sorted(x.name for x in members), "entries are not sorted"
assert all(x.uid == 0 and x.gid == 0 and x.uname == "" and x.gname == "" for x in members)
assert all(x.mtime == m["sourceDateEpoch"] for x in members), "an mtime is not the epoch"
prefix = m["name"] + "/"
files = {x["path"]: x for x in m["files"]}
assert members[0].name == m["name"], "the first entry is not the top directory"
seen = set()
for x in members:
    if x.isdir():
        assert x.mode == 0o755, f"{x.name}: directory mode {oct(x.mode)}"
        continue
    rel = x.name[len(prefix):]
    f = files[rel]
    assert x.mode == int(f["mode"], 8), f"{rel}: mode"
    data = tf.extractfile(x).read()
    assert len(data) == f["size"], f"{rel}: size"
    assert hashlib.sha256(data).hexdigest() == f["sha256"], f"{rel}: sha256"
    seen.add(rel)
assert seen == set(files), f"manifest and tarball differ: {seen ^ set(files)}"
assert m["tree"]["files"] == len(files)
assert m["tree"]["bytes"] == sum(f["size"] for f in m["files"])
assert hashlib.sha256(open(path, "rb").read()).hexdigest() == m["tarball"]["sha256"]
PY
echo "ok: the manifest lists every file, with its size, mode and SHA-256"

# --- what the tarball contains, and what it must not ---------------------------------
prefix=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["name"])' \
  "$a.manifest.json")
tar -tzf "$a" > "$tmp/names"
for p in LICENSE COPYING.RUNTIME README.md CHANGELOG.md docs/index.md docs/building.md \
         lib/Prelude.wiz runtime/wiz_rt.h runtime/WizRuntime.lean lakefile.lean \
         lake-manifest.json lean-toolchain Wiz.lean Wiz/Version.lean selfhost/rt.c \
         scripts/source-tarball.py; do
  grep -qx "$prefix/$p" "$tmp/names" || fail "the tarball has no $p"
done
python3 - "$tmp/names" "$prefix" <<'PY'
import sys
names = [line.strip().removeprefix(sys.argv[2] + "/") for line in open(sys.argv[1])]
bad_dirs = {".git", ".lake", ".grail", ".wiz-cache", "__pycache__", "node_modules",
            "dist", "drafts", "cc-bundle"}
bad_suffixes = (".olean", ".ilean", ".o", ".a", ".so", ".pyc", ".class")
for name in names:
    parts = name.split("/")
    for part in parts[:-1]:
        assert part not in bad_dirs, f"the tarball contains {name}"
    assert "web/out" not in name, f"the tarball contains {name}"
    assert not name.endswith(bad_suffixes), f"the tarball contains the build output {name}"
PY
echo "ok: the required files are in, and .git, caches, drafts and build outputs are out"

# --- tree mode: the Nix path, on a tree that has cache and build junk ----------------
mkdir -p "$tmp/tree/Wiz" "$tmp/tree/lib" "$tmp/tree/.git/objects" \
  "$tmp/tree/.lake/build" "$tmp/tree/.grail" "$tmp/tree/drafts" \
  "$tmp/tree/__pycache__" "$tmp/tree/web/out" "$tmp/tree/dist" "$tmp/tree/node_modules/x"
printf 'licence\n' > "$tmp/tree/LICENSE"
printf 'the version\n' > "$tmp/tree/Wiz/Version.lean"
printf 'module A\n' > "$tmp/tree/lib/A.wiz"
for junk in .git/config .lake/build/x.o .grail/y drafts/z.wiz __pycache__/q.pyc \
            web/out/w.js dist/d.tar.gz node_modules/x/index.js scratch.olean \
            grail.local.wiz wiz-toolchain.local Tests/Groups.lean; do
  mkdir -p "$tmp/tree/$(dirname "$junk")"
  printf 'junk\n' > "$tmp/tree/$junk"
done
python3 "$here/source-tarball.py" --root "$tmp/tree" --out "$tmp/t" --mode tree \
  --epoch 0 >/dev/null
python3 - "$tmp/t"/*.tar.gz <<'PY' > "$tmp/tree-names"
import sys, tarfile
for m in tarfile.open(sys.argv[1]).getmembers():
    if m.isfile():
        print(m.name.split("/", 1)[1])
PY
sort -o "$tmp/tree-names" "$tmp/tree-names"
printf '%s\n' LICENSE Wiz/Version.lean lib/A.wiz | sort > "$tmp/tree-want"
cmp "$tmp/tree-names" "$tmp/tree-want" || fail "tree mode included or lost a file"
echo "ok: tree mode includes source files only"

# --- git mode ignores an untracked file (a scratch file cannot leak in) --------------
mkdir -p "$tmp/repo/sub"
(
  cd "$tmp/repo"
  git init -q
  git config user.email t@example.invalid
  git config user.name test
  printf 'a\n' > tracked.wiz
  printf 'b\n' > sub/b.wiz
  printf 'junk\n' > untracked.txt
  git add tracked.wiz sub/b.wiz
  git commit -qm fixture
)
python3 "$here/source-tarball.py" --root "$tmp/repo" --out "$tmp/g" --mode git \
  --epoch 0 >/dev/null
if tar -tzf "$tmp/g"/*.tar.gz | grep -q 'untracked.txt'; then
  fail "git mode included an untracked file"
fi
echo "ok: git mode includes tracked files only"

echo "source-tarball test: ok"
