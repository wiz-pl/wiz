# Stage 26: tower, a toolchain manager

tower is to Wiz what elan is to Lean (and rustup to Rust). It installs Wiz toolchains
(`wiz`, `grail`, the standard library, the editor plugins) by channel or version, and
puts **shims** named `wiz` and `grail` on `PATH`. A shim runs the toolchain the current
directory asks for. The editor plugin starts `wiz lsp` from `PATH`, and grail runs the
`wiz` it finds there, so both get the project's toolchain without any setup of their own.

## 26a: specs, project files, overrides

A **spec** names a toolchain:

| spec | means |
|---|---|
| `nightly` | the commit of the tag `nightly` (the newest commit of `nightly-ref`, default `master`, whose CI passed, 26g); without that tag, the tip of `nightly-ref` |
| `stable` | the highest `vX.Y.Z` tag |
| `v0.2.0`, `my-branch`, a commit | that tag, branch or commit |
| `REF@COMMIT` | that commit (`master@6f29a0a…`); the ref is a label |
| a linked name | a toolchain made by `tower toolchain link` |

A project names its toolchain in a file **`wiz-toolchain`** at its root (one line, a
spec; lines starting with `#` or `--` are comments), the same way `lean-toolchain` works
for Lean. It's a separate file rather than a field of `grail.wiz`: tower then never has
to evaluate Wiz, and directories that have no grail package can use one too.

Which toolchain runs (`tower show` says which, and why):

1. `wiz +SPEC …`: a first argument starting with `+` (as with rustup);
2. else, walking up from the current directory, an **override** for that directory
   (`tower override set SPEC [DIR]`, kept in the settings), a `wiz-toolchain.local`
   file in it, or a `wiz-toolchain` file in it, in that order. The first directory
   with any of them wins;
3. else the **default** (`tower default SPEC`).

**Local overrides: `wiz-toolchain.local`.** A file `wiz-toolchain.local` next to
`wiz-toolchain` is your own override for that project. It is not committed, so add it
to the project's `.gitignore`:

```
wiz-toolchain.local
```

It has the same format (the first line that isn't blank or a comment) and takes
everything `wiz-toolchain` does (`nightly`, `master@<sha>`, `v0.2.0`, a linked name),
plus a **path to a toolchain**: a line starting with `/`, `./`, `../` or `~/` (or `.`,
`..`). A relative path is resolved against the directory that holds the file. A bare
`a/b` is a branch name, not a path; write `./a/b`. The directory is either a toolchain
(`bin/wiz`, `bin/grail`, e.g. an unpacked release tarball or a Nix `result`) or a
built checkout (`.lake/build/bin/wiz`, `lib/`), exactly what `tower toolchain link`
takes. On first use tower links it under its absolute path as the name (the same code
as `toolchain link`, with the `tower set cflags …` flags), so `tower toolchain list`
shows it as `/path  [link /path]` (relinked if that link is removed). To try a
compiler you are working on in one project:

```sh
echo ../wiz > wiz-toolchain.local   # a checkout after `lake build wiz grail`
tower show
# /home/me/src/wiz
#   from /home/me/proj/wiz-toolchain.local (local override: wiz-toolchain names nightly)
#   /home/me/.tower/toolchains/--home--me--src--wiz
```

The shims, `tower which` and `tower show` all honour it. A path that does not exist
or holds no toolchain is an error naming the file
(`…/wiz-toolchain.local: /home/me/src/wiz is not a toolchain: …`), not a silent fall back to
`wiz-toolchain`. An absolute path also works as a spec elsewhere (`wiz +/path/to/tc …`).

## 26b: sources

Installing first resolves the spec to a commit with `git ls-remote` on the `git`
setting, then realises it from one of three sources:

* **nix**: `nix build FLAKE/COMMIT#wiz`, the package from the flake (`packages.wiz`),
  which comes from the Cachix cache `badlydrawnwizards` when your Nix user is trusted
  (tower passes the substituter, as in docs/building.md). The store path is linked as
  `toolchains/NAME/nix`, which is a GC root. `bin` and `share` point into it.
* **release**: `RELEASES/TAG/wiz-ARCH-linux.tar.gz` from GitHub Releases (26d) for a
  tag (and `stable`); for anything else, a commit, `REF@COMMIT` (`master@<sha>`), a
  branch or `nightly`, the snapshot of its commit, `RELEASES/snapshot-<sha>/…` (26g).
  It is checked against its `.sha256`, which a snapshot must have. A commit without a
  snapshot is an error that lists the retained snapshots and the other sources.
* **source**: `git clone`, then `lake build wiz grail` (this needs elan), then the build
  is copied into the layout below and the clone is removed.

`--source auto` (the default, the `source` setting) tries nix when `nix` runs, then the
release, then the source, and moves on to the next when one fails.
`tower update` re-resolves channels and branches and reinstalls the ones that moved,
using the source and flags they were installed with.

## 26c: layout, wrappers and shims

```
~/.tower/
  settings                 `tower settings`, `tower set KEY VALUE`
  bin/wiz, bin/grail       the shims; bin/tower (`tower self install`)
  toolchains/NAME/
    bin/wiz, bin/grail       run these: the binary with the toolchain's flags
    share/wiz/lib/           the standard library
    share/wiz/.lake/build/bin/{wiz,grail}   the binaries (grail finds lib/ from here)
    share/wiz/editors/       the editor plugins, when the source has them
    share/wiz/TOOLCHAIN      a marker: editors find the toolchain a library file belongs to
    tower.info               spec, source, ref, commit, flags
```

This is the layout of the Nix package (`$out/share/wiz` looks like a checkout), so a Nix
toolchain is just links into the store. A toolchain is built in
`toolchains/.tmp-…` and renamed into place, so a shim never sees half of one.

**Flags, not environment variables** (stage 23a). The wrappers `bin/wiz` and
`bin/grail` of a release, source or linked toolchain are generated `sh` scripts. They
`exec` the binary with the C toolchain as flags (`--cc`, `--cflags`, `--ldflags`,
`--libs`, `--llc`, `--gc-cflags`, `--gc-ldflags`: the `tower set cflags …` settings,
overridden by `tower toolchain install … --cflags …`), and `wiz` also gets
`-I share/wiz/lib`. This is the same thing the Nix package's `makeWrapper` does. With no
flags set, `wiz build` uses `cc` and the system's GMP.

**The shims** are generated `sh` scripts too:

```sh
case "$1" in
  +*) tc=$('/home/me/.tower/bin/tower' --home '/home/me/.tower' resolve "$1") || exit; shift ;;
  *) tc=$('/home/me/.tower/bin/tower' --home '/home/me/.tower' resolve) || exit ;;
esac
exec "$tc/bin/wiz" "$@"
```

`tower resolve` prints the toolchain's directory, installing it first if needed
(`tower set auto-install false` turns that off). It writes its notes to stderr, so a
first `wiz lsp` still works. Because the shim `exec`s, the process that keeps running is
the toolchain's own `wiz`, which is what the language server's stdio, signals and exit
codes need. The shims are scripts rather than tower itself under another name (elan
uses one binary for everything) because a Lean program can't see its `argv[0]` and
can't `exec`. A script costs one `sh` and one quick tower run per call.

**Why tower was first written in Lean** (it was ported to Wiz in 26e, and the Lean
version was removed in 26h). Wiz programs could read their arguments (`IO.args`,
21k), but they couldn't start or `exec` processes, read environment variables, list,
rename or link files, or set file modes. tower needs all of these, and grail is written
in Lean for the same reason. tower was then its own small library (`Tower/`, which didn't
import Wiz) and its own Lake executable, so its Nix package built in seconds.

Commands:

```
tower toolchain install SPEC… [--source auto|nix|release|source] [--force] [--cflags …]
tower toolchain uninstall NAME… / toolchain list
tower toolchain link NAME DIR      a checkout (DIR/.lake/build/bin) or a toolchain dir
tower default [SPEC]               (installs it)
tower override set SPEC [DIR] / override unset [DIR] / override list
tower show / which wiz / run SPEC -- CMD…   (run: SPEC's bin/ first on PATH)
tower update [NAME…]
tower set KEY VALUE / settings     source flake git releases nightly-ref auto-install cc cflags …
tower self shims / self install    [--self PATH: the tower the shims call]
```

`tower toolchain link dev ~/src/wiz` points the toolchain `dev` at a checkout's
`lake build`. Put `dev` in a project's `wiz-toolchain`, or run `wiz +dev …`, to try a
compiler you are working on.

## 26d: installing tower, release tarballs

**With Nix**: the package (`packages.tower`) contains tower and the `wiz` and `grail`
shims, which call that same tower; installing it puts all three on `PATH`:
`nix profile install github:wiz-pl/wiz#tower` (or `home.packages` /
`environment.systemPackages`), then `tower default nightly`. Nix installs only tower and
the shims: the toolchains are installed by tower into `~/.tower` (with `tower set source
release` they come from the release tarballs and never from Nix). The package adds git,
tar and curl to tower's `PATH`; `nix` and `lake` are yours. `tower self shims` is still
there for shims in `~/.tower/bin` (they then call the tower given with `--self`).

**With the install script** (no Nix):
`curl -sSfL https://raw.githubusercontent.com/wiz-pl/wiz/master/scripts/tower-init.sh | sh`
(or `| sh -s -- v0.2.0` for a tag). It downloads the tarball, runs `tower self install`
and then `tower default nightly`.

**From a release tarball**: unpack `wiz-x86_64-linux.tar.gz`. Its `bin/` already works
on its own (`bin/wiz`, `bin/grail` and `bin/tower`). Then run
`wiz-x86_64-linux/bin/tower self install`, which copies tower to `~/.tower/bin` and
writes the shims, followed by `tower default stable` (or `nightly`).

`.github/workflows/release.yml` builds the tarball (`scripts/release-tarball.sh`) outside
Nix with elan's Lean. The binaries then depend only on glibc (2.27 or later) and the C
runtime, as Lean's own releases do, and the job checks that no `/nix/store` path is
linked in. It runs on:

* tags `vX.Y.Z`: a GitHub release with the tarball and its `.sha256`;
* pushes to `master`: the snapshot of the commit; the tag `nightly` moves to it once
  CI has passed on it (26g);
* pull requests that touch the packaging: the tarball is built and tested, but nothing
  is uploaded.

The job also builds and runs `examples/io.wiz` and a small grail package with the
unpacked tarball in plain Ubuntu 20.04 and 24.04 containers (no compiler, no GMP), runs
the programs built there in Ubuntu 18.04, and installs the tarball through tower from a
local release directory. The tarball brings
its own C compiler, GMP and Boehm collector (26f), so `wiz build` and grail need nothing
installed.

**Editors.** wiz.nvim starts `wiz lsp` with the root directory as its working
directory, so the shim picks that project's `wiz-toolchain`. `share/wiz/editors/nvim`
(release and source toolchains) is the plugin that matches the toolchain:
`vim.opt.rtp:append(vim.fn.trim(vim.fn.system 'tower which wiz'):gsub('/bin/wiz$', '') .. '/share/wiz/editors/nvim')`.
`wiz-toolchain` is one of the plugin's root markers.

**Tests** (`lake test -- '=tower'`, all offline). The upstream is a local bare repository
holding a tiny Lake project whose `wiz` and `grail` print their arguments, with a tag
`v1` and a moving `main`. The cases:

* resolution order, settings and version ordering;
* a source install with flags baked into the wrappers, then shims with a
  `wiz-toolchain` file, `+nightly` installing on first use, an override beating the
  file, `run`, `update` moving `nightly` but not `v1`, `uninstall`, and `auto-install
  false`;
* `wiz-toolchain.local`: a spec beating `wiz-toolchain` (and `show` saying so), an
  absolute path to a toolchain directory and a relative path to a checkout run by the
  shims (with the flags), listed as a link, and the errors for a missing path and a
  directory without a toolchain (from `show` and from a shim);
* a release install from a tarball made by `scripts/release-tarball.sh` (which works on
  its own), a refused checksum, no release for a branch, and `link` plus `default` of an
  unpacked tarball;
* snapshots (26g): full and short pinned commits, a bare commit with `auto`, a `keep/`
  tag as a spec, a snapshot without its checksum refused, `nightly` following its tag
  while the branch is ahead (and `update` leaving it alone), and the error for a commit
  with no snapshot;
* a Nix install from a local flake whose package is a plain directory (no nixpkgs),
  linked as a GC root and unlinked by `uninstall` (skipped when there is no `nix`).

The shims in the tests are written by `tower self shims`, so they call the Wiz tower
under test.

## 26e: tower in Wiz

`tower/` is tower again, in Wiz: a grail package (`tower/grail.wiz`) whose executable
`tower` (`cd tower && grail build`: `.grail/bin/tower`) has the same commands, messages,
settings file, `tower.info` and layout as the Lean reference implementation it replaced,
module for module (`Tower/Basic.wiz`, `Install.wiz`, `Cli.wiz`). It uses `lib/Sys.wiz`
(9h, 9k) for processes,
the environment and files (`FS.realPath`, `IO.appPath`, and `SpawnOptions` for a child's
working directory and for `lake build` without the Lean variables), and `lib/Text.wiz`
(9j) for text; no C of its own. `grail test` in `tower/` checks the pure
functions (`tests/pure.wiz` against `tests/pure.expected`).

**Tests.** The cases of `Tests/Tower.lean` run tower as a process, through its command
line only: group `tower` against `tower/`, which the group's first case builds with grail
in `.lake/build/tower-wiz` (about 10 s from clean; later cases find it up to date) and
whose `grail test` it runs. The Wiz tower follows 26g too: release snapshots of commits
(short shas through the `snapshot-*` tags, the `.sha256` required), `nightly` as the
commit of the tag `nightly`, `keep/` tags as specs, release in the `auto` candidates, and
the same error for a commit without a snapshot.

The flake (`packages.tower`) and the release tarball build `tower/` with grail (stage
26h). The Lean reference implementation (`Tower/`) and the test driver's `--tower` mode
were removed in 26h: the `tower` group now tests only the Wiz tower.

## 26f: the C toolchain in the release tarball

Like Lean's releases, a release tarball ships the C toolchain its programs are built
with, in `share/wiz/cc/` (`scripts/bundle-cc.sh`, run by the release job). On a machine
with no `gcc`, GMP or Boehm GC, `tower default nightly` and then `wiz build`, `wiz run`
and `grail build` work.

```
share/wiz/cc/
  bin/cc          clang --sysroot=../sysroot -pthread (links also get libm, as needed)
  bin/llc         for --llvm: the same clang on the textual IR (-x ir), with llc's arguments
  bin/clang, bin/ld.lld, lib/*.so*, lib/clang/N/   from the Lean toolchain (`lean --print-prefix`)
  sysroot/        glibc 2.27 + Linux 4.15 headers and link libraries (Ubuntu 18.04's
                  libc6, libc6-dev, linux-libc-dev), static GMP 6.3.0 (--enable-fat)
                  and Boehm GC 8.2.8, built by the script
  LICENSES/, VERSIONS
```

What Lean ships, for comparison (lean-4.35.0-linux): clang, ld.lld, libLLVM and
libclang-cpp, compiler-rt, a link-only glibc 2.26 and static `libgmp.a`/`libuv.a`, but no
libc headers (Lean's C needs only `lean.h`) and no `llc`. Wiz's runtime and `import_c`
need libc headers, so the bundle has a whole sysroot, with headers and libraries of the
same glibc. The clang is Lean's own, so its LLVM follows `lean-toolchain`. The options
weighed (zig cc, tcc) are in wiz-notes/toolchain-cc.md.

**Downloads.** `scripts/bundle-cc.sources` lists the five outside files (three Ubuntu
.debs, GMP and the Boehm GC) with their sha256 and URLs. Each file is tried from each
URL in turn, with retries, and is kept only if its hash matches. The .debs are tried
on four Ubuntu mirrors (archive.ubuntu.com, mirrors.kernel.org, Princeton, RWTH
Aachen), GMP on ftp.gnu.org, ftpmirror.gnu.org and gmplib.org, and the GC on GitHub and
hboehm.info. The last place tried for every file is this repository's release
`bundle-inputs`. On master pushes the release job copies the downloads there (`gh
release upload` of any file missing). The job also caches the downloads, keyed by the
sources file's hash, so rebuilding the bundle after a change to `bundle-cc.sh` needs no
outside server. A master run once failed because archive.ubuntu.com was unreachable,
which is why there are mirrors.

**Licences in the tarball.** `share/wiz/` has `LICENSE` (GPL-3.0), `COPYING.RUNTIME`
and `NOTICE` (`scripts/release-licenses/NOTICE`). The NOTICE lists what is linked into
wiz, grail and tower: the Lean runtime (Apache-2.0), mimalloc and libuv (MIT), libc++
(Apache-2.0 with LLVM exception), static GMP (LGPL-3.0+) and glibc. It also lists what
the bundled C toolchain contains, and says that the programs it builds link GMP
statically, with the LGPL's relinking terms. `share/wiz/LICENSES/` has the texts: Lean's
`LICENSE` and its third-party `LICENSES` file (LLVM, glibc, GMP), plus libuv's and
mimalloc's. The bundle's own texts are in `share/wiz/cc/LICENSES/`.

**Defaults, not settings.** `wiz` and grail look for `cc/bin/cc` beside their own binary
(`Toolchain.withBundled`: `<dir>/.lake/build/bin/wiz` next to `<dir>/cc`, as they find
`<dir>/lib`). When it is there, the defaults are `cc` and `llc` from the bundle and
`gc-ldflags -lgc -lpthread`; GMP is found by plain `-lgmp`. Flags, `grail.local.wiz`,
a package's settings and tower's wrapper flags (`tower set cc …`) still replace each
field, so `--cc emcc --gmp mini-gmp.c …` (WebAssembly) or `--cc gcc` (the system's
compiler and shared GMP) work as before. A checkout and the Nix package (whose wrapper
passes every flag) have no bundle and keep their defaults.

**What needs which glibc.** The toolchain's own binaries (`wiz`, `grail`, `tower`) need
glibc 2.27 or later, as before. The bundled compiler needs glibc **2.30** or later
(Ubuntu 20.04, Debian 11, RHEL 9 and newer): Lean's `libLLVM` and `libclang-cpp`
reference `GLIBC_2.29`/`GLIBC_2.30` symbols, so Lean's own `leanc` has the same
requirement. On an older system `wiz check` works and `wiz build` needs `--cc gcc` (and
`libgmp-dev`). Programs it builds need glibc 2.27 or later (libc, libpthread, and libm
and ld.so when they use them) and nothing else: GMP and the GC are linked statically.
The release job checks this by running programs built on Ubuntu 20.04 in Ubuntu 18.04. The runtime keeps to glibc 2.27: a spawn in a directory uses
`posix_spawn_file_actions_addchdir_np` (glibc 2.29) when the headers have it, else fork,
chdir and exec with the same errors (`-DWIZ_NO_SPAWN_CHDIR` forces that path; the `sys`
tests run both). That has
licence consequences for programs you distribute, explained in docs/building.md
("What `wiz build` links").

The tarball grows from 72.5 MB to about 131 MB (the bundle is 165 MB unpacked, 59 MB
compressed; libLLVM and libclang-cpp are most of it).

## 26g: release snapshots for every master commit

A project that pins a commit (`master@<sha>` in `wiz-toolchain`) can be installed
without Nix: every master push publishes the tarball of that commit.

**Snapshots.** For each push to master, `.github/workflows/release.yml` builds and tests
the tarball as before. Then `scripts/release-snapshots.sh publish` creates the
pre-release `snapshot-<full sha>` (its tag points at the commit) with
`wiz-x86_64-linux.tar.gz` and its `.sha256`. `gh release create` makes a draft, uploads
the files and then publishes it, so the tag appears only once the files are complete.
There is one release per commit rather than one release that holds every commit's files,
because then tower needs neither the GitHub API nor a token: `git ls-remote` lists the
`refs/tags/snapshot-*` that exist (this also expands a short sha and gives a clear
error), and a full sha names its URL,
`releases/download/snapshot-<sha>/wiz-x86_64-linux.tar.gz`. GitHub sets no limit on the
number of releases or on their total size (only on each file, 2 GiB, and on the files of
one release, 1000), so pruning (below) keeps the size in check. Pull requests that touch
the packaging still build and test the tarball, and they also run
`scripts/test-release-snapshots.sh`, but they publish nothing.

**nightly is a tag.** It moves only to a commit whose CI passed: master can break even
though every merged PR was green (two PRs green alone, in semantic conflict). A snapshot
of a red commit may exist, since pins name commits explicitly, but `nightly` (what
users get by default) never points at one. `.github/workflows/nightly.yml` runs when
the CI workflow completes successfully on a master push (`workflow_run`). It waits up to
an hour for that commit's `snapshot-<sha>` tag, because release.yml runs alongside CI,
and stops at once if no release.yml run of the commit is still going (one that failed,
or was cancelled by a newer push). Then it moves the tag, and only forwards: a commit
that is not ahead of the tag (an older run) leaves it. A ref update is atomic, so tower, which resolves `nightly` through
`git ls-remote` to the tag's commit and downloads that snapshot, can't hit a missing
file. Before, the assets were replaced in place, and downloads returned 404 while they
uploaded. The tag lags the branch by at least one CI run. **A channel is the same
commit whatever the source**: `nightly` resolves to the tag's commit for a Nix, release
or source install alike, and `stable` to its `vX.Y.Z` tag's commit. Before, only
release installs followed the tag, so with `nix` on `PATH` (`--source auto` tries Nix
first) `tower default nightly` built the tip of master, which Cachix may not have yet,
and fell back to a local build of wiz. CI has built the Nix package of the commit behind the
tag (`nix build .#wiz`, pushed to Cachix when the secret is set), so it is usually a
download. Only when there is no tag `nightly` (a fork, a fresh repository) does
`nightly` fall back to the tip of the branch `nightly-ref`. Every install records the
tag's commit, and `tower update` compares against the tag, not against the branch. The release `nightly` (`releases/download/nightly/…`, for people and
older towers) then gets the snapshot's files: each file is uploaded under a temporary name,
the old one is deleted and the new one renamed, so it is missing for one API call
instead of for a whole upload. `scripts/tower-init.sh` uses the snapshot of the tag
when `git` is there, and checks the `.sha256`.

**Retention.** After each publish, pruning keeps the newest 20 snapshots
(`SNAPSHOT_KEEP`; about 2.7 GB at 135 MB a tarball, see 26f), plus every snapshot whose
commit a `v*` tag, a `keep/…` tag or `nightly` points at. The others are deleted
together with their tags. **To keep a pinnable toolchain, push a keep/ tag**:
`git tag keep/icestick <sha> && git push origin keep/icestick`. Its snapshot then
outlives the window, and `tower toolchain install keep/icestick` works too, because a
`keep/` tag is a spec for its commit's snapshot.

**Older commits.** Running the workflow by hand (`workflow_dispatch`) with the input
`commit` set to a full master sha builds that commit and publishes its snapshot (nightly
does not move): `gh workflow run release.yml -R wiz-pl/wiz -f
commit=<sha>`, or "Run workflow" on the Actions page. The commit's tarball is laid out
by the workflow's current `scripts/release-tarball.sh`, not by the commit's own copy. A
dispatched snapshot is new, so it survives the next 20 pushes; push a `keep/` tag to
keep it for good.

**A commit with no snapshot** (never published, pruned, or not on master) fails with
`no release snapshot of commit <sha>`. The error lists what is retained (nightly and
the `keep/`/`v*` snapshots, with their commits, and how many recent ones there are) and
the alternatives: `--source source` (builds with elan), `--source nix`, or dispatching
the workflow for that commit. With `--source auto` tower falls through to the next
source.

## 26h: shipping the Wiz tower

The Wiz tower is feature-complete for the command line, and the flake package and the
release tarball ship it (`scripts/build-tower-wiz.sh`). It was compared command by command
against the Lean reference implementation and against a local upstream and release
directory; their stdout, stderr, exit codes and written files agreed (apart from the home
path, and the OS error text for a path that does not exist). `--version` was
`tower 0.1.0-dev` in both, and `tower settings` byte-identical. The Lean implementation
(`Tower/`) and the test driver's `--tower` mode were then removed; `tower/` is the only
implementation.

| feature | `tower/` |
|---|---|
| `toolchain install/uninstall/list/link`, aliases `install`, `uninstall`, `list`, `link` | ✓ |
| `install` flags `--source`, `--force`, `--cflags …`, several specs, per-spec status | ✓ |
| `default`, `override set/unset/list`, `show`, `which`, `resolve`, `run`, `update` | ✓ |
| `set KEY VALUE`, `settings`, `--home`, `--self`, `--self-arg`, `--version`, `--help` | ✓ |
| settings file: `default`, `source`, `flake`, `git`, `releases`, `nightly-ref`, `auto-install`, seven flag keys, `override` | ✓ |
| `wiz-toolchain` (`#`/`--` comments), `wiz-toolchain.local` (spec or path), overrides walking up | ✓ |
| sources `auto`/`nix`/`release`/`source`; channels as tags (`nightly`, `stable`), `REF@COMMIT`, `keep/`; release snapshots and their `.sha256` | ✓ |
| layout `toolchains/NAME/{bin,share/wiz,tower.info}`, wrappers with flags, atomic install, linked toolchains | ✓ |
| shims (including `+SPEC`), `self shims`, `self install`, `resolve` installing on first use | ✓ |
| error messages and exit codes (1: command failure, 2: usage, child status for `run`) | ✓ |
| `grail test` pure checks, and the `tower` test group (CLI cases) | ✓ |

Shipping it means no Lean at build time: `scripts/build-tower-wiz.sh` copies `tower/` to
a scratch directory and runs `grail build tower` there. `packages.tower` passes the Nix
C compiler and GMP's flags (not the Boehm collector: tower's generated C does not use
it); the release workflow passes the bundled C toolchain (`cc-bundle/bin/cc`) when there
is one, which links GMP statically and keeps the tarball's glibc 2.27 promise, and the
system `cc` otherwise. A test case covers `self install` for the Wiz tower: the copy and
the shims call the copy, and it still runs tower.

The Wiz tower's `--version` is a literal that must be kept in step with
`Wiz/Version.lean` (the file says so); a build-time substitution would remove that
duplicated constant.

