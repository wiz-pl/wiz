# Stability

What stays the same between Wiz releases, starting with 0.1.0.

Wiz is young and most of it is still changing. The promises below are deliberately few.
They cover what lets a project keep working while everything else changes. Versions
follow [Semantic Versioning](https://semver.org/) in its 0.x form:

* a **patch release** (0.1.0 → 0.1.1) fixes bugs and keeps every promise on this page;
* a **minor release** (0.1 → 0.2) may break anything, promises included. Every break is
  listed in [CHANGELOG.md](../CHANGELOG.md) under that release.

A promise holds for all of 0.1.z: a project that works with 0.1.0 works with any later
0.1.z in the ways listed here. A bug fix can change behaviour that contradicted the
documentation. Snapshots, `nightly` and `master` promise nothing.

## What is promised

### 1. The `wiz-toolchain` file and tower's specs

A project names its toolchain in a file `wiz-toolchain` at its root (or in a parent
directory). The toolchain is the file's first line that is not blank and is not a comment
(`#` or `--`). That line is a **spec**, in one of these forms:

| spec | means |
|---|---|
| `v0.1.0` (any `vX.Y.Z` tag) | that release |
| `stable` | the highest `vX.Y.Z` tag |
| `nightly` | the commit of the tag `nightly` (the newest master commit whose CI passed) |
| a branch or tag name | its commit, resolved when installed |
| a commit (7+ hex digits) | that commit |
| `REF@COMMIT` (e.g. `master@1a2b3c4`) | the commit; `REF` is documentation |
| a name given to `tower toolchain link` | that local toolchain |

Both the file format and these specs keep their meaning in every 0.1.z. tower 0.1.z
resolves them the same way and installs `vX.Y.Z` from that tag's release (below). We
also intend to keep them in 0.2 and later: they are what lets an old project keep its
old toolchain while the rest of Wiz changes. That is an intention, not a promise.

The tower commands that read and write them (`tower default`, `tower override`, `tower
show`, `tower which`, `tower run`, `tower toolchain install|list|uninstall|link`) keep
their names and arguments in 0.1.z. Their output text may change.

### 2. Release tags and their URLs

For every release tag `vX.Y.Z`:

* the tag exists in https://github.com/wiz-pl/wiz and is never moved or deleted;
* its GitHub release has the toolchain tarball and its checksum, at
  `https://github.com/wiz-pl/wiz/releases/download/vX.Y.Z/wiz-x86_64-linux.tar.gz`
  and `…/wiz-x86_64-linux.tar.gz.sha256`. These are the URLs tower installs from. The
  release is never deleted, and its assets are never replaced by different builds;
* the install script is at
  `https://raw.githubusercontent.com/wiz-pl/wiz/vX.Y.Z/scripts/tower-init.sh`;
* the tarball unpacks to one directory `wiz-x86_64-linux/` with the commands
  `bin/wiz`, `bin/grail` and `bin/tower`. The rest of the layout (`share/wiz/…`) is
  for the tools and may change.

The Nix flake reference `github:wiz-pl/wiz/vX.Y.Z` builds the same release. Its package
names (`wiz`, `tower`, `nvim-wiz`) are kept in 0.1.z.

Snapshots (`snapshot-<sha>`), `nightly` and `bundle-inputs` are not releases. Snapshots
are pruned, and `nightly` moves.

### 3. grail's core `Package` API

A `grail.wiz` that builds its package from these functions of `lib/Grail.wiz` keeps
building, with the same targets, with any 0.1.z:

```wiz
import Grail
def package : Package := Package.new "hello"
  |> Package.lib "greet" "src"          -- a library: the modules under src/
  |> Package.exe "app" "App.wiz"        -- an executable from a file with `main`
  |> Package.tests "tests" "tests"      -- tests: each file under tests/
  |> Package.check "spec" "Spec.wiz"    -- a file that must check
  |> Package.dep "util" "https://example.org/util.git" "<rev>"   -- a git dependency
```

The promise covers `Package.new`, `Package.lib`, `Package.exe`, `Package.tests`,
`Package.check` and `Package.dep`, with these argument orders and meanings. It does not
cover:

* the constructors and fields of `Package`, `Target`, `Command` and the other types;
* command targets (`Package.command`, `Package.phony`, `Command.*`), `Package.set`,
  `Package.selfhost`;
* the format of `grail.lock`. A change in 0.1.z would come with an automatic migration;
* grail's command line and its output. The commands `grail build`, `grail run TARGET`
  and `grail test` are documented and are not expected to change, but they are not
  promised.

### 4. The `wiz` command line, within 0.1.z

These commands keep their names, arguments and exit statuses (0 on success, non-zero on
failure) in every 0.1.z:

| command | does |
|---|---|
| `wiz --version` | prints `wiz VERSION`, and for a release `(COMMIT)` |
| `wiz parse FILE` | parses `FILE` and prints its syntax tree |
| `wiz check FILE` | elaborates and checks `FILE` and the modules it imports |
| `wiz build FILE -o OUT [--llvm]` | compiles `main` to an executable |
| `wiz build FILE -o OUT --lib [--llvm]` | compiles the exported functions to an object file and `OUT.h` |
| `wiz build FILE -o OUT --no-main [--llvm]` | links the exported functions without a `main` |
| `wiz run FILE [--llvm]` | builds and runs `main` |
| `wiz lsp` | a language server on stdin/stdout |

The same holds for the toolchain flags, which may go before or after the command:
`-I DIR`, `--cache DIR`, `--cache-ro DIR`, `--no-cache`, `--cc X`, `--cflags "…"`, `--ldflags "…"`,
`--libs "…"`, `--gmp "…"`, `--llc X`, `--gc-cflags "…"` and `--gc-ldflags "…"`.

Not covered:

* **Experimental flags**: `--regularity`, `--predicative-prop`, `--eager-proofs`,
  `--inert`, `--unbox-structs`, `--strict-privacy`, `--pp-all`, every `--trust-*` flag,
  and any flag the usage text marks experimental. These may change or go away in a patch
  release.
* What the commands print: error messages, the syntax tree, warnings. Do not parse them.
* Which programs check. That is the language (below).
* `wiz lsp --infoview SOCK`, `--ws`, `--no-stdio`, and the protocol behind them.

## What is not promised

Anything not listed above may change in a 0.1.z release. In particular:

* **The language.** Syntax, elaboration, type classes, tactics, macros and which
  programs check. Queued work (brands, mandatory sorts, glued equations, linear case)
  changes what checks.
* **The core theory and soundness.** Nothing about Wiz as a whole is proved (see
  [Status.md](Status.md)). There is no promise of consistency. What we do promise is to
  treat a closed proof of `False` with default flags as a bug: we will fix it in a
  0.1.z release when the fix is known, and record it in Status.md either way. A fix may
  reject programs that used to check. To report one, see Status.md, "How to report a
  soundness bug".
* **The standard library** (`lib/`). Module names are kept where possible; definitions,
  names and instances may change.
* **The LSP and infoview protocol**, including the custom methods and the sockets. The
  supported clients (wiz.nvim, the terminal and browser infoviews) ship with each
  toolchain, so they always match it.
* **The C FFI ABI**: object layouts, `export` and `--lib` headers, runtime symbols.
  Rebuild C code against the toolchain that builds the Wiz side.
* **The elaboration cache** (`~/.cache/wiz`). It is keyed by the binary, so toolchains
  never share entries; it may be deleted at any time.
* **The self-hosted toolchain** (`selfhost/*.wiz`), the HDL and separation-logic
  libraries, Feral, and everything documented as experimental in the stage docs.
* **Platforms**: x86_64 Linux only, glibc 2.27 or later (2.30 or later for `wiz build`
  with the bundled C compiler). Other platforms work from source, without a promise.

## Changing this page

Adding a promise is fine in any release. Weakening or removing one is a breaking change:
it waits for the next minor release, and CHANGELOG.md lists it.
