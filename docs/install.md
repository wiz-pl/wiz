# Installing Wiz

Wiz runs on **x86_64 Linux** (glibc 2.27 or later). A toolchain is `wiz` (the checker,
compiler and language server), `grail` (the build tool), the standard library, the
editor plugin and, in a release, a C compiler with GMP and the Boehm collector, so
`wiz build` needs nothing else from the system.

There are three ways to get one:

* **tower**, the toolchain manager (like elan or rustup), from a release tarball. You
  don't need Nix or Lean for this, and it is the way to go if you just want to write Wiz.
* **Nix**: `nix run` the flake, or install tower from it.
* **From source**: a checkout and `lake build` ([building.md](building.md)).

Once you have one: [your first project](#a-first-project-with-grail),
[editor setup](#editors), then [the language tour](tour.md).

## tower

### Install it

```sh
curl -sSfL https://raw.githubusercontent.com/badly-drawn-wizards/wiz/master/scripts/tower-init.sh | sh
export PATH="$HOME/.tower/bin:$PATH"      # put this in your shell's profile
```

The script needs `curl`, `tar` and `git`. It downloads the release tarball of the
`nightly` channel and checks its `.sha256`, then copies `tower` to `~/.tower/bin`, writes
the **shims** `wiz` and `grail` next to it, and makes `nightly` your default toolchain.
For a release instead, `| sh -s -- v0.1.0`.

You can do the same by hand:

```sh
curl -sSfLO https://github.com/badly-drawn-wizards/wiz/releases/download/nightly/wiz-x86_64-linux.tar.gz
tar -xzf wiz-x86_64-linux.tar.gz
wiz-x86_64-linux/bin/tower self install   # tower and the shims in ~/.tower/bin
tower default nightly
```

The unpacked `wiz-x86_64-linux/bin/` works by itself too, without tower.

**With Nix**, tower and the shims come as one package:

```sh
nix profile install github:badly-drawn-wizards/wiz#tower
tower set source release                  # see "Where toolchains come from" below
tower default nightly
```

Check what you have:

```sh
tower show            # the toolchain for this directory, and why
tower toolchain list  # what is installed
tower which wiz       # the real binary behind the shim
```

### Toolchains: channels and pins

A **spec** names a toolchain:

| spec | is |
|---|---|
| `nightly` | the newest master commit whose CI passed (the tag `nightly`) |
| `stable` | the highest release tag `vX.Y.Z` (once there is one) |
| `v0.1.0` | that release |
| `master@<sha>` | that master commit: a **pinned snapshot** |
| `keep/<name>` | a commit someone kept on purpose (below) |

`nightly` moves: `tower update` installs its new commit when there is one. A pin never
moves, so a project that has to build the same way next month should pin. Every push to
master publishes a release tarball of that commit (a *snapshot*). The newest 20 are
kept, plus those of every `v*`, `keep/…` and `nightly` tag, so a pin to an arbitrary
old commit eventually stops being installable from a release. To keep one, push a tag
`keep/<name>` at it (see [stages/26-tower.md](stages/26-tower.md), 26g).

**Per project**, a file named `wiz-toolchain` at the project's root holds one spec:

```sh
echo 'master@6ec079f7f40b83119f0368ae8965678b7afe0eac' > wiz-toolchain
wiz check Main.wiz        # installs that toolchain the first time, then uses it
tower show                # master@6ec0…  from /path/to/project/wiz-toolchain
```

The shims look for the file walking up from the current directory, so `wiz`, `grail`
and the editor's language server all use the project's toolchain. Which toolchain runs,
first match wins:

1. a `+SPEC` first argument: `wiz +v0.1.0 check Main.wiz`;
2. walking up from the current directory, an override (`tower override set SPEC [DIR]`)
   or a `wiz-toolchain` file;
3. the default (`tower default SPEC`).

### Where toolchains come from

`tower set source auto|nix|release|source` picks where a toolchain is installed from:
**release** downloads the tarball (and verifies its checksum), **nix** builds the flake
at that commit, **source** clones and runs `lake build` (it needs elan). The default,
`auto`, tries nix when `nix` is on `PATH`, then the release, then the source.

With Nix on your `PATH` that means `auto` asks Nix first. Nix builds a channel at the tip
of its branch (`nightly` is then master's newest commit, not the tag), and unless your
Nix user is trusted and the cache `badlydrawnwizards` is configured (below), that build
runs on your machine and takes a while. If you just want the binaries, run
`tower set source release` once.

### No system compiler needed

A release toolchain ships its own C toolchain in `share/wiz/cc/`: Lean's clang and
`ld.lld`, a glibc 2.27 sysroot, and static GMP and Boehm GC. `wiz build`, `wiz run` and
`grail build` use it by default, so you don't need `gcc`, `libgmp-dev` or anything else
installed. Programs you build need only glibc 2.27 or later to run. To use another
compiler, pass the flags (`wiz build --cc gcc …`) or set them for every toolchain
(`tower set cc gcc`).

## Nix

```sh
nix run github:badly-drawn-wizards/wiz -- check hello.wiz      # wiz
nix run github:badly-drawn-wizards/wiz#grail -- build          # grail
nix run github:badly-drawn-wizards/wiz#nvim-wiz -- hello.wiz   # Neovim with wiz.nvim
```

Pin a revision the usual way (`github:badly-drawn-wizards/wiz/v0.1.0`, or a commit). The
packages are `wiz` (the default, with `grail`), `tower`, `wiz-nvim` (the plugin as a
Neovim plugin derivation) and `nvim-wiz` (a Neovim with only the plugin, to try it).
Nix's packages pass the C compiler, GMP and the collector from nixpkgs as flags, so
they have no bundled compiler and need none.

**The binary cache.** CI pushes every build to the Cachix cache `badlydrawnwizards`.
Without it, Nix builds Wiz from source. As a trusted Nix user, `cachix use
badlydrawnwizards`. Otherwise, add it to `/etc/nix/nix.conf` (or your NixOS
configuration), because an untrusted user's `--option extra-substituters` is ignored:

```
extra-substituters = https://badlydrawnwizards.cachix.org
extra-trusted-public-keys = badlydrawnwizards.cachix.org-1:TxG+RHY8RMC/AXc0LJbYtYm9LW/XRjfQwgz+EEaAjBI=
```

## A first project with grail

A single file needs no project:

```sh
mkdir hello && cd hello
cat > Main.wiz <<'EOF'
import IO
def main : IO Unit := IO.println "hello from Wiz"
EOF
wiz check Main.wiz        # type check (no output: no errors)
wiz run Main.wiz          # hello from Wiz
wiz build Main.wiz -o hello && ./hello
```

A **grail package** is a directory with a `grail.wiz`, which is itself a Wiz program:
`package` lists the targets. Start one with `grail new`:

```sh
grail new hello                    # executable + test (the default template)
grail new shapes --template lib    # a library and its tests
grail new blinky --template hdl    # an HDL design, Verilog generator and board constraints
cd hello
grail build                        # build the library and the executable
grail run hello                    # hello from hello
grail test                         # build and run the golden test
```

`grail new hello` writes this tree (the other templates are documented in
[stages/23-grail.md](stages/23-grail.md)):

```
hello/
  grail.wiz        Package.new "hello"
                     |> Package.lib "hello-lib" "src"
                     |> Package.exe "hello" "src/Main.wiz"
                     |> Package.tests "tests" "tests"
  src/Main.wiz     import Std; def main : IO Unit := IO.println "hello from hello"
  tests/hello.wiz  a `-- test: run` golden test, with hello.expected
  README.md
  .gitignore       .grail/
```

The generated `grail.wiz` names the targets: `Package.lib "hello-lib" "src"` checks
every module under `src/`, `Package.exe "hello" "src/Main.wiz"` compiles `main` to
`.grail/bin/hello`, and `Package.tests "tests" "tests"` runs each `tests/*.wiz` against
its `.expected`. An optional `wiz-toolchain` file pins the toolchain of the project.

`grail build` again runs nothing: every job is keyed by its inputs. `grail targets`
lists the targets, and `grail config` prints the C toolchain grail uses. Packages can
depend on other packages in git repositories (`Package.dep`, with a lock file) and run
commands as build steps; see [stages/23-grail.md](stages/23-grail.md). Add `.grail/` to
your `.gitignore` (the templates do).

## Editors

### Neovim: wiz.nvim

wiz.nvim (Neovim 0.10 or later) starts the language server for `*.wiz` files and gives
you diagnostics, hover, go to definition, completion and code actions. It also has
Lean-style unicode input (`\lam` gives `λ`, `\r` gives `→`) and an **infoview**, a split
that follows the cursor and shows the goals of a tactic proof and the expected type of
the term there. Its full documentation is
[editors/nvim/README.md](../editors/nvim/README.md).

Every toolchain carries the plugin that matches it, in `share/wiz/editors/nvim`. With
tower, put this in your `init.lua`:

```lua
local tc = vim.fn.trim(vim.fn.system 'tower which wiz'):gsub('/bin/wiz$', '')
vim.opt.rtp:append(tc .. '/share/wiz/editors/nvim')
require('wiz').setup {}
```

With a plugin manager, point it at the repository's `editors/nvim` (lazy.nvim:
`vim.opt.rtp:append(plugin.dir .. '/editors/nvim')` in `config`; packer:
`rtp = 'editors/nvim'`); with Nix, add `packages.<system>.wiz-nvim` to your Neovim's
plugins. To try it without touching your configuration:
`nix run github:badly-drawn-wizards/wiz#nvim-wiz -- hello.wiz`.

**Which server runs.** The plugin finds the project root (the nearest `grail.wiz`,
`wiz-toolchain`, `lakefile.toml` or `.git`) and starts the server there, through the
shims, so the server is the project's toolchain:

* in a grail package it runs `grail lsp`, which knows the package's module roots
  (`import Greet` from `src/`) and its dependencies;
* elsewhere it runs `wiz lsp`;
* in a file of an installed toolchain's standard library (where go to definition into
  `Prelude` takes you) it runs *that toolchain's* `wiz lsp`, one server per toolchain, so
  the library is checked by the version it belongs to.

`:WizInfoviewToggle` (or `<LocalLeader>i`) opens and closes the infoview,
`:WizLspRestart` restarts the server, and `:WizAbbrev λ` tells you how to type `λ`.

### The infoview outside Neovim

The server can serve infoviews that run beside any editor. Start it with
`wiz lsp --infoview SOCK` (a Unix socket) or `wiz lsp --ws PORT` (a WebSocket on
127.0.0.1), and connect one of the two clients, which are Wiz programs in the
repository and are not in the release tarball:

* **in a terminal**: `infoview/build.sh`, then `wiz-infoview SOCK` in a split next to
  the editor (or `wiz-infoview --file F.wiz --at LINE:COL` on its own);
* **in a browser**: `web/build.sh` (needs Emscripten; `nix develop` has it), then
  `web/bridge.sh`, which starts `wiz lsp --ws` and serves the page; open the address it
  prints. The page edits its own documents, and when your editor's server runs with
  `--ws` it also follows that editor's cursor.

Details: [stages/11-tooling.md](stages/11-tooling.md), 11l–11o.

### Other editors

`wiz lsp` is a standard language server on stdin/stdout. Any LSP client can use it: run
`wiz lsp` (or `grail lsp` in a grail package) with the project root as the working
directory. The infoview is extra protocol (`wiz/interactiveGoals` and friends,
`wiz-notes/infoview-protocol.md`), so other clients get diagnostics, hover and the rest,
but not the infoview, unless they run one of the clients above.

## Troubleshooting

**`version 'GLIBC_2.xx' not found`.** `wiz`, `grail` and `tower` need glibc 2.27 or
later (Ubuntu 18.04, Debian 10, RHEL 8). The bundled C compiler needs glibc **2.30**
(Ubuntu 20.04, Debian 11, RHEL 9): on an older system `wiz check` works, but `wiz build`
needs the system compiler: `--cc gcc` and `libgmp-dev` installed. `ldd --version` tells
you what you have.

**The wrong toolchain runs.** Run `tower show` in that directory: it prints the
toolchain and why (a `+SPEC`, an override, which `wiz-toolchain` file, or the default).
`tower override list` shows the overrides. A `wiz-toolchain` file in a parent directory
counts. The editor's server runs in the project root, which may not be the directory of
the file you opened: the root is the nearest `grail.wiz`, `wiz-toolchain`,
`lakefile.toml` or `.git`.

**`no toolchain here`.** There is no `wiz-toolchain` file, override or default:
`tower default nightly`.

**`no release snapshot of commit …`.** A pinned commit's snapshot was never published
or has been pruned. The message lists what is kept. Pin a `nightly`, `v*` or `keep/`
commit, or install from another source: `tower toolchain install SPEC --source source`
(builds with elan) or `--source nix`.

**Go to definition into the library opens a file, and the editor checks it with the
wrong version.** wiz.nvim recognises a toolchain by its layout: the marker file
`share/wiz/TOOLCHAIN` (older toolchains have `share/wiz/REVISION` instead),
`share/wiz/lib/Prelude.wiz` and `share/wiz/.lake/build/bin/wiz`. A library file under a
directory that has these gets that toolchain's own server. If yours lacks the marker
(a hand-copied or very old toolchain), reinstall it with
`tower toolchain install SPEC --force`. To serve such files like any other, set
`lsp = { toolchains = false }`.

**`wiz build` cannot find `gmp.h`.** You are not using a release toolchain (a checkout,
or the Nix package's unwrapped binary) and have no GMP headers. Use a release toolchain,
the Nix package (whose wrapper passes them) or pass `--cflags`/`--ldflags` where GMP
lives.

**Something else.** Bugs and questions: the repository's issues,
<https://github.com/badly-drawn-wizards/wiz/issues>. For a soundness bug (a proof of
`False`), see [Status.md](Status.md), "How to report a soundness bug".
