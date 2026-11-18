# Stage 23: grail, a build tool

## 23b: modules by path

`import A.B` reads `A/B.wiz` under the first **module root** that has it; `lib/` is a
root, so `import Prelude` is `lib/Prelude.wiz` as before. The frontend stays pure: the
caller reads every module a file can reach up front, by scanning its import lines
(`Wiz/Module.lean`).

**One name, one declaration.** Two different declarations of one name can't both be
visible in a file: importing a module that declares a name the file already has (from
another module, or declared in the file itself) is an error at that `import`,
`'b' is declared by both module M.A and module M.B`, whichever order the imports come
in, and the module is not brought in. Wiz has no namespaces (`Nat.repr` is one global
name), and the kernel identifies constants by name, so letting the later declaration win
would keep everything checked against the earlier one: a theorem about M.A's `b` would
then be about M.B's (it proved `Empty`; the regression is the case "two modules declaring
one name: …" of the group `modules`).
One module reached by several paths (a diamond) is the same declaration and fine: a
module is imported once per file. Two modules with identical declarations still clash,
as in Lean; put the definition in one module that the others import. A private
function, axiom or foreign function (`private def helper`) is not a global name: its
kernel name is `_private.M.A._0.helper` (as in Lean), which `helper` resolves to in M.A
only, so two modules' private `helper`s never clash, and the file importing them may
declare a `helper` of its own. Messages show `helper`. So do private *types*
(`private inductive`, `private structure`, `private class`, `private coinductive`, a
`mutual` block of inductives): the command is elaborated with the type's name rewritten
to its kernel name (`T` and `T.f` wherever they occur in it), so its constructors,
fields, recursors, description and instances' names are all under it, and in the module
`T`, `T.mk`, `.mk`, patterns, `p.x`, `deriving` and `instance : C T` find them. A derived
`Repr` shows `T.c`. The kernel's `addDecl` refuses a name that is already declared, behind all
of this.

## 23c: a key per module, atomic writes

A module's key is computed from text alone, before anything is elaborated:

    key(M) = hash(salt, toolchain, name and text of M, M's C headers, key(N) for each import N)

and a module is elaborated **in isolation**, from the empty state plus its own imports,
so what it elaborates to depends only on its key. An importer's chain of command keys
mixes in `key(M)` at the `import`. Editing a module now invalidates it and what imports
it, not the whole library, and a module imported by many files is cached once. A module
that uses a name it doesn't import is an error, with the cache or without (`--no-cache`
keeps the effects in memory for the run), and in `runFrontend`, which the tests and the
language server use: it checks each module once in isolation (errors are reported at
the `import`) and then elaborates it into the importer's state, unless that state is
still the initial one and the isolated result serves as it is. So the editor rejects
what `wiz check` rejects. Cache files are
written to a temporary name and renamed, so concurrent runs never see half a file.

## 23d: grail v0

A package is a directory with a `grail.wiz`, written in Wiz against `lib/Grail.wiz`:

```wiz
import Grail
def package : Package := Package.new "wiz"
  |> Package.lib "std" "lib"                    -- check every module under lib/
  |> Package.check "app" "app.wiz"              -- check one file
  |> Package.exe "io" "examples/io.wiz"         -- compile `main`: .grail/bin/io
```

```sh
lake build grail
.lake/build/bin/grail build          # every target; `grail build std` for one
.lake/build/bin/grail targets        # list them; `grail config` prints the toolchain
```

grail evaluates `Package.render package` (an S-expression) in the interpreter and
builds a graph of **jobs**: `check` per file, and `ir → c → obj → link` per executable.
A job's key is computed from its inputs before it runs (a check from the file's key, an
object from the C text and the compiler flags), its output goes to
`.grail/build/<key>/` through a temporary directory and a rename, and a job whose
directory exists doesn't run: **a second build runs no jobs**, an edit reruns the checks
of the files that import what changed, and an edit that leaves the C alone stops there.
The key also covers the grail binary itself, so a new elaborator rebuilds everything.

There are no environment variables: the C compiler and its flags come from flags
(`--cc`, `--cflags`, `--ldflags`, `--llc`, `-I DIR`, `--cache DIR`, `--cache-ro DIR`, `--no-cache`) or from
an uncommitted `grail.local.wiz` with this machine's paths (`nix develop` writes it from
`flake.nix`):

```wiz
import Grail
def settings : Settings := Settings.empty
  |> Settings.set "cflags" "-I/nix/store/…-gmp-…-dev/include"
  |> Settings.set "ldflags" "-L/nix/store/…-gmp-…/lib -Wl,-rpath,/nix/store/…-gmp-…/lib"
```

For local co-development, the same file can override a registry dependency with a
checkout: `|> Package.override "ddr3" "../wiz-ddr3"` (23m, lock v3).

## 23a: the toolchain as flags

`wiz` reads no environment variables: the toolchain record (`Wiz/Toolchain.lean`: C
compiler and flags, `llc`, the collector's flags, the cache, module roots) comes from
`--cc`, `--cflags`, `--ldflags`, `--libs`, `--llc`, `--cache DIR`/`--cache-ro DIR`/`--no-cache` and
`-I DIR` (which replaces `$WIZ_PATH`), and is passed explicitly to everything that
compiles. Its compiler fields are its `id`, which enters grail's keys.

## 23e: the self-hosted toolchain as targets

`Package.selfhost NAME ROLE` builds the self-hosted programs from `selfhost/*.wiz`
(`Wiz/Selfhost.lean` concatenates their sources — the parser tables are the checked-in
`selfhost/Tables.wiz` — for grail and the tests alike): `checker`, `compiler`, and
`bootstrap`, the fixpoint check of
`scripts/fixpoint.sh` as jobs (generate the source, build stage 1, `self1.c`, stage 2,
`self2.c`, compare). `grail build bootstrap` runs it (minutes); run again, it runs
nothing unless a source, `rt.c`, the toolchain or grail changed. `grail build` alone
leaves it out.

## 23f: a test runner

`Package.tests NAME DIR` makes every `.wiz` file under `DIR` a test, with its expected
output beside it in `.expected` (not the files of a nested package: a subdirectory with
its own `grail.wiz` is left out). The first line gives the kind: `-- test: check` (the
default: the messages, as `wiz check` prints them) or `-- test: run` (what `main` prints,
compiled through C). `-- test: skip REASON` marks an example that the package-wide run
cannot check (it needs `--trust-native`, or it takes minutes): it is reported as skipped,
needs no `.expected`, and is not a pass. A `check` or `run` line may end in
`timeout SECS` (`-- test: run timeout 900`) for a test that needs more than
`--test-timeout` gives every test: the larger limit applies to its job and to its
program. A pass is a job like any other, keyed by the file (and its
imports), the kind, the toolchain and the expected output, so `grail test` again runs
nothing; `grail test FILTER` runs the tests whose path contains it, and
`grail test --update` writes the actual output. `grail test --rerun` runs the tests again
even when a pass is recorded (a flaky test, a program that reads something outside its
key): the old record is dropped, a pass is recorded again and a failure leaves none, so the
next plain `grail test` reports what this run saw. Only the tests' own jobs run again;
their programs' checks, objects and links are reused when up to date. Every example is a test
(`examples/*.expected`). The Lean tests stay in `lake test`.

## 23g: parallel jobs

The jobs form an explicit graph (`Grail/Graph.lean`): `obj F` depends on `build F`
(which checks `F` and writes its IR and C in one job: as `check F`, `ir F` and `c F`
it elaborated the same source three times), …, `link E` on `obj F`, a check on the
checks of the package modules it imports, a `run` test on its executable, the bootstrap
steps on each other. A file that is already checked as a package module keeps its
`check F` job and its C comes from `ir F`. A node's key is computed when its
dependencies are done (an object's key hashes the C its `c` node wrote); a node whose
output exists is up to date, the rest are jobs in a ready queue. `grail build -j N`
(default: the cores, at most 4) runs up to `N` jobs at a time, each as a separate process
(`grail --grail-job …` with the toolchain as flags, or the C compiler) with a time limit
(23k; `--timeout SECS`, default 1800; tests `--test-timeout SECS`, default 300, or the larger `timeout SECS` of a
test's `-- test:` line (23f), so a test that hangs fails instead of hanging the run). A failed job is reported and the jobs that depend
on it are skipped; the others still run. Each job's output is buffered and printed in the
graph's order, so `-j 1` and `-j 8` print the same report, and a second build still runs
no jobs.

`--region-cache` (11c) is part of the toolchain record (`Toolchain.regionCache`, or the
`region-cache` setting of `grail.wiz`), so `grail config` shows it and every job gets it
through `Toolchain.toFlags`. A job then serves its imported modules' cached effects from
the `.wizr` regions in the same cache layers as the `.wizc` entries: the write cache is
searched first, then the `--cache-ro` caches (which are never written), and a missing,
truncated or mistagged region falls back to the text entries. Since job keys are unchanged,
a warm region build and a text build produce the same outputs.

## 23h: git dependencies and a lock file

`Package.dep NAME URL REV` depends on the package at a git URL (a path, `file://`,
`https://`) and revision (tag, branch or commit). `grail update` resolves each
dependency, and theirs (from their own `grail.wiz`), to a commit, clones it to
`.grail/packages/NAME`, and writes `grail.lock`, which is committed:

```
(lock
  (dep greet "https://example.org/greet.git" v1 88bef64fe0c79f190976221e57f65d6b17a1866c 89d8a320ea2473de))
```

(name, URL, revision, commit, and a hash of the checked-out files). Builds use the lock
only: each dependency is checked out at its locked commit (fetched if missing), files
that don't match the hash are refused, and a `REV` changed in `grail.wiz` stays at the
locked commit, with a note, until `grail update`. The roots of a dependency's `lib`
targets become module roots, so `import Greet.Hello` finds
`.grail/packages/greet/src/Greet/Hello.wiz`; module keys already hash module texts.
Two different commits of one dependency name are refused (no version resolution yet).

## 23i: command targets

A **command** runs a program with declared inputs and outputs, as a job of the build
graph like any other: it waits for what makes its inputs, runs under `-j N` and the time
limit, and is up to date when its key's directory exists.

```wiz
import Grail
def package : Package := Package.new "uart"
  |> Package.exe "icestick" "app/icestick.wiz"
  -- a program of the package as the tool; its output is a directory
  |> Package.command (Command.new "gen" (Tool.exe "icestick") |> Command.arg "gen" |> Command.outDir "build/gen")
  -- a program from PATH; `build/gen/proto.v` is gen's output, so this waits for gen
  |> Package.command (Command.new "synth" (Tool.path "yosys")
       |> Command.arg "-q" |> Command.arg "-p" |> Command.arg "synth_ice40 -top proto"
       |> Command.arg "-o" |> Command.output "build/proto.json" |> Command.input "build/gen/proto.v")
  -- always runs when named; never by a bare `grail build`
  |> Package.phony (Command.new "flash" (Tool.path "iceprog") |> Command.input "build/proto.bin")
```

* **The tool**: `Tool.path NAME` is looked up on `PATH` (a name with a `/` is a path in
  the package) and run by that path; `Tool.exe NAME` is an `exe` target of the package,
  built first and run from the store.
* **Arguments** are data, never a shell command line: `Command.arg "text"`,
  `Command.input PATH` and `Command.output PATH` (an argument that is a declared input or
  output), `Command.argIn "--json=" PATH` / `Command.argOut` (a prefix and a path, one
  argument), `Command.parts [Part.text …, Part.output …]` for anything else. Use
  `Tool.path "sh"` when you want a shell.
* **Declared without being an argument**: `Command.needs PATH` (input),
  `Command.makes PATH` (output file), `Command.makesDir PATH` (output directory),
  `Command.outDir PATH` (an output directory that is also an argument),
  `Command.stdout PATH` (the command's stdout is this output file).
* **Edges** come from paths: an input that another command declares as an output (or
  that lies under its output directory) depends on that command. Any other input is a
  source file or directory and must exist ("the input X does not exist, and no target
  makes it"). Two commands declaring one output, or outputs inside one another, are
  refused before anything runs.
* **Outputs** are written into the job's own directory: an output argument renders as
  `.grail/tmp/<job>/out/<path>` (absolute; parents are made, an output directory is made
  empty). When the command succeeds, every declared output must exist and nothing else
  may have been made there (both are errors, naming the files); the directory is renamed
  into the store, `.grail/build/<key>/`, and the outputs are **installed** at their paths
  in the package (copied when different; mode 755 if the command made the file executable,
  644 otherwise; an output directory is replaced as a
  whole). So a failed or killed command leaves `build/` as it was, going back to an
  earlier input reinstalls the earlier outputs without running anything, and a deleted
  or hand-edited output is put back by the next build (it is grail's).
* **Installed files** are listed in `.grail/installed` with the hash grail wrote. A build
  removes those that no command declares any more ("removed build/old.bin (installed by
  an earlier build; …)") unless they were changed since ("kept …: changed since grail
  installed it"); `grail clean` does the same for all of them, and removes `.grail/build`
  (the store), `bin`, `tmp` and `log`.
* **Working directory**: the package directory, inputs as written; `Command.inOutDir`
  runs it in its output directory instead (inputs then render as absolute paths).
* **Environment**: grail's own, plus `Command.env K V` (set, and in the key).
* **Log**: stdout and stderr are kept in the store (`log.txt`). Success prints
  `[command NAME]` (a phony command also prints its output); failure prints how it ended
  (`exit code 3`, `killed by signal 9 (SIGKILL: …)`, `timed out after …`), the last 20
  lines of its output, and keeps the whole log in `.grail/log/NAME.txt`.
* **Phony**: `Package.phony` commands have no outputs, are never recorded, always run
  when named, and are not built by `grail build` alone; `Command.manual` keeps an ordinary
  command out of a bare `grail build` too.
* One name per target: two targets with the same name are refused (before, `grail build
  NAME` built both).

**The key** is the command's description (tool reference, argument parts with their
paths as written, inputs, outputs, environment, working directory), the **identity** of
each tool, and for each input the key of the command that made it or the hash of its
contents (a directory: every file under it, by path and contents). A tool's identity:
for `Tool.path`, its real path (symlinks followed) and the hash of that file; for
`Tool.exe`, its link's key (its C, the compiler and flags, its `link_c` files: a change
that leaves the C alone reruns nothing). `Command.uses (Tool.path "abc")` adds the
identity of a program the command runs by itself. Since the identity is part of the key, a
tool must be found even when nothing needs to run ("yosys: not found on PATH" fails the
command and what depends on it, not the rest of the build).

**What grail cannot see.** Nothing is sandboxed and declared inputs cannot be checked
for completeness: a command that reads a file it didn't declare (a header beside an
input, a configuration file in `$HOME`, a data file of the tool) is not rerun when that
file changes, and one that writes outside its output directory does so unseen. A tool's
identity is one file: under Nix that file's real path is a store path, which names the
tool's whole closure, but elsewhere an upgrade of the tool's shared libraries or data
files (yosys's `share/`) or of programs it finds on `PATH` changes nothing (declare them
with `Command.needs` or `Command.uses`). Environment variables other than those set with
`Command.env` are inherited and not in the key. This is make's and ninja's contract, not
Nix's; what grail adds is that what *is* declared is handled exactly.

## 23j: `grail run`

`grail run TARGET [-- ARGS…]` builds what TARGET needs and runs it with ARGS appended,
in the package directory, with grail's own stdin, stdout and stderr, and exits with its
exit code (128+N if it died of signal N). For an `exe`, that is the program; for a
command, its tool, inputs and the commands that make them. A command run this way is not
recorded: its outputs are written at their paths in the package directly, and its
stdout is not redirected. The build's report goes to stderr. The program stays in
grail's process group, so Ctrl-C reaches it.

```sh
grail run icestick -- test /dev/ttyUSB1 3000
```

## 23k: job processes don't outlive grail

Each job's process (a `--grail-job`, the C compiler, a command) runs under a
**supervisor**, `grail --grail-exec MS [--cwd DIR] [--env K=V]… -- CMD ARGS…`
(`Grail/Exec.lean`; the test driver answers `--grail-exec` too). grail starts it in a new
session, with a pipe as its stdin that it never writes; the supervisor starts the job in
a process group of its own and waits for it. When the time limit passes it kills the
group (`timed out after N s`); when its stdin ends, grail has died, by whatever signal,
`SIGKILL` included, and it kills the group and exits. Before, jobs ran under `timeout`,
which puts the job in a process group of its own, so killing grail (`timeout 60 grail
build`, or `SIGKILL`) left them running. (The supervisor ends with `_exit`, from
`c/proc.c`: Lean's own exit waits for the thread blocked on stdin.)

A failed job now always says how it ended. A job that was killed (here: a check job over
its memory cap) used to be reported with an empty message; now it is `killed by signal 9
(SIGKILL: out of memory, or killed by hand?), and printed nothing`, or the end of what it
printed. Tests: groups `grail-commands` and `grail-hygiene` (grail itself, as
`tests --grail …`, killed with `SIGKILL` and `SIGTERM` while a job's grandchild sleeps).

## 23l: `grail lsp`

`wiz lsp` finds modules under the toolchain's library, `./lib` and its `-I` directories,
so in a grail package (`Package.lib "lib" "src"`) an editor reported `import
Icestick.Gates` as an unknown module. `grail lsp [OPTIONS…]` reads `grail.wiz` (and
`grail.local.wiz`) and runs `wiz lsp OPTIONS…` in the package directory with the
package's module roots as `-I` directories, in the order a `grail build` check uses
them: the package directory, the roots of its `lib` targets, its dependencies' roots
(from `grail.lock`, checked out as for a build), then the toolchain's own `-I`. The
toolchain flags are the ones a build would use (the build files' settings, then the
command line). stdin, stdout and stderr are the server's, and grail exits with its exit
code. The `wiz` is `--wiz PATH`, else the one beside `grail`, else `wiz` on `PATH`.

A `grail.wiz` that doesn't evaluate is reported on stderr, and the server starts anyway
with the package directory as its only extra root, so that the build file itself can be
edited with diagnostics.

**Editors.** wiz.nvim (editors/nvim) starts `grail lsp -C ROOT` when the project root has
a `grail.wiz` (`lsp.grail = { enable = true, cmd = { 'grail', 'lsp' } }`), and `lsp.cmd`
otherwise; without `grail` on `PATH` it warns once and starts `wiz lsp`. Its
`lsp/wiz.lua` (for `vim.lsp.enable 'wiz'`) does the same. Another client needs the same
rule: run `grail lsp` in the directory of the nearest `grail.wiz` (or with `-C` it), else
`wiz lsp`. A VS Code extension would decide it per workspace folder (and restart the
server when `grail.wiz` changes); Emacs' eglot or lsp-mode with a server-command
function on the project root; Helix with `language-server.wiz.command = "grail"`,
`args = ["lsp"]` per project (`.helix/languages.toml`), since Helix starts it in the
workspace root.

The server reads the package's modules when it starts, as before: an edit to a module
is seen by the files that import it after a restart (`:WizLspRestart`), and so is an
edit to `grail.wiz`.

## 23m: a package registry

A **registry** gives packages global names and versions. It is three layers, each a file
with one writer:

| layer | file | written by | read at |
|---|---|---|---|
| manifest | `grail.wiz` in the package | the author | `grail update`, every build (targets, roots) |
| index | `index/NAME.sexpr` in a git repository | the publisher, by pull request | `grail update` only |
| lock | `grail.lock` in the consumer | `grail update` | every build, fetch, lsp, doc |

Builds read the lock only: with `grail.lock` and the archives cached, a build needs
neither the index nor the network. That split is what makes a **static index** enough:
there is no server, API or token, just a git repository of text files (a directory or a
`file://` URL is an index too, which is how the tests and air-gapped mirrors use it).

```wiz
import Grail
def package : Package := Package.new "greet"
  |> Package.version "1.2.0"                  -- this release's version
  |> Package.toolchain ">=0.1 <0.3"           -- the Wiz it was tested with (a range)
  |> Package.require "std" "^0.1"             -- a registry dependency
  |> Package.require "text" "~1.0.3"
  |> Package.lib "greet" "src"
```

`Package.version` and `Package.toolchain` are optional (empty means "unversioned" and
"any toolchain"), so an existing `grail.wiz` decodes unchanged.

**`require` and `dep` stay two combinators.** `Package.dep NAME URL REV` names a source
(a git URL and a revision), and `grail update` pins it to a commit. `Package.require
NAME REQ` names a registry package and a *version range*, resolved through the index.
The split keeps the security and compatibility stories separate: a git dependency is a
source you chose, a registry dependency is a constraint the index resolves. They can be
mixed in one package; the lock records both.

### The index

One S-expression file per package, `index/NAME.sexpr` (the parser is the one grail
already uses for `grail.lock`):

```lisp
(index
  (package "greet"
    (summary "Hello, in Wiz")
    (repo "https://github.com/example/greet")
    (version "1.2.0"
      (source "https://github.com/example/greet/releases/download/v1.2.0/greet-1.2.0.tar.gz")
      (sha256 "8a3349def55974e5cbc2eb530a2fc4fff48b292e7b81c6b6563da515f9cdc064")
      (size 1042)
      (tree "…")
      (commands "…")
      (toolchain ">=0.1.0 <0.3.0")
      (deps (dep "std" "^0.1") (dep "text" "~1.0")))
    (yanked "1.2.1" "wrong tarball; use 1.2.2")))
```

* `source` is the immutable archive (an `https`, `file://` or plain path URL);
  `sha256` is the SHA-256 of its bytes. `size` is the archive's byte length (R19), `tree`
  the SHA-256 of its unpacked file tree (R20) and `commands` a digest of the package's
  declared `Package.command` set (R36); `grail publish` writes all three and a lock v3
  records them. Older entries have none of them.
* `deps` is **authoritative for resolution**; it
  must agree with the published manifest, so a lock records the whole graph and a build
  never re-reads dependency manifests to resolve.
* `yanked` stops new resolutions from choosing a version; a lock that already pins it
  keeps working, because `grail fetch` never reads the index.
* Names are global and lowercase (`[a-z][a-z0-9-]{0,63}`); `name@version` is immutable.
  A corrected release gets a new version. Namespaces are deferred, but the reader already
  accepts the scoped layout: `index/@org/name.sexpr` is the package `@org/name` (the
  file name is the resolver key; one duplicate per registry is an error).
* A `source` that is a relative path is resolved against the index root, so a local
  mirror or a checked-out index is self-contained (the test fixture relies on it); a
  published index uses `https://` URLs. Unknown fields in an index entry are ignored, so
  a newer publisher can add `(license …)`, `(size …)` or `(mirror_urls …)` without
  breaking older grails; the **lock** decoder stays strict (a lock is a local trust
  anchor, so an unknown entry is an error).

**The archive is deterministic.** The publisher makes it from the release tag with

```sh
git archive --format=tar --prefix=greet-1.2.0/ COMMIT | gzip -n > greet-1.2.0.tar.gz
```

`gzip -n` drops the filename and timestamp and `git archive` stamps every entry with the
commit's time, so the bytes are a function of the commit and the hash can be re-derived
by anyone. The layout is fixed: one top directory `NAME-VERSION/` containing
`grail.wiz`; `fetch` strips that component.

### Configuring the index

The index is a URL (a git repository), or, for tests and local review, a directory of
`*.sexpr` files or one file holding several packages. (A bare git repository path is
cloned like a URL; an ordinary directory is read in place, so uncommitted edits are
visible.) The URL is chosen by, in order:

1. `--index URL` on the command line;
2. `Package.set "index" "URL"` in `grail.wiz` (or in the machine's
   `grail.local.wiz`, which wins, as for toolchain settings).

The intended deployment is `https://github.com/wiz-pl/grail-index`, but any git URL is
an index, including an organisation's private one. A URL index is cloned once into
`<cache>/grail/index`; `grail update` fetches and resets it, and `--offline` reads the
cached clone (and refuses if there is none, or if it is a clone of another URL). The
lock records the index URL and commit that produced it, so an audit can name the exact
index state.

### Resolution

Requirements: `1.2.3` (exact), `^1.2.3` (`>=1.2.3 <2.0.0`; `^0.2.3` is `<0.3.0`; a
one-component `^0` is `<1.0.0` and `^0.0` is `<0.1.0`), `~1.2.3` (`>=1.2.3 <1.3.0`;
`~1` is `<2.0.0`), `>=1.2 <2`, `>`, `<=`, `<`, and `*`.
The resolver is flat and greedy: it picks the **highest** version of each name that
satisfies *every* requirement on it (one version per name; Wiz has one global name
space), adds that version's index `deps`, and repeats until the *selection* is stable.
Each round rebuilds the requirement map from the roots plus the dependencies of the
**current** selection, so when a version is replaced the requirements that only it
introduced are retracted (otherwise a constraint from an abandoned version could linger
and make a satisfiable graph fail). A conflict names both requesters; there is no
backtracking. A version whose `toolchain` range does not admit the running toolchain is
filtered out (so `>=0.1.0` admits the `0.1.0-dev` nightly), which is a compatibility
signal, not a security boundary. Prereleases only match a requirement that names one.

`grail index resolve` prints the same choice without writing the lock;
`grail index show NAME` prints a package's versions.

### The lock (v3) and the commands

`grail update` resolves the manifest's `require`s (and git `dep`s) and writes
`grail.lock`, which is committed. Version 1 (23h) held git dependencies; version 2 added
the index and registry packages; version 3 adds a schema header, the resolving toolchain,
the index/integrity fields, flat sorted entries and machine-local overrides:

```lisp
(lock
  (version 3)
  (toolchain 0.1.0-dev abcdef0)          -- Wiz.version and the release commit, when known
  (index "https://github.com/wiz-pl/grail-index" "885c4c903032ba188e1c819906ecad6c1912ab2f")
  (dep legacy "https://example.org/legacy.git" v2 "<commit>" "<content>")
  (pkg std 0.1.1 "https://…/std-0.1.1.tar.gz" "<sha256>"
    (size 1042) (tree "<sha256>") (commands "<sha256>")
    (deps "text ^1"))
  (pkg text 1.2.0 "https://…/text-1.2.0.tar.gz" "<sha256>"
    (deps))
  (override ddr3 "../wiz-ddr3" "<tree sha256>"))
```

* **Compatibility.** A file without `(version …)` parses as v1 (only `dep` entries) or
  v2 (with `index`/`pkg`) by inspection, so old locks keep working unchanged; a v1/v2
  lock that is rendered back stays header-less. A `(version N)` newer than 3 is refused
  with a clear message rather than partly understood: a lock is a local trust anchor.
  `grail update` writes v3, which is the upgrade path; nothing rewrites a lock during a
  build.
* **Deterministic text.** Entries are one per line, sorted by name (git deps, packages
  and overrides separately); package dependencies are a flat, sorted
  `(deps "NAME REQ" …)` list rather than nested nodes (v2's nested
  `(deps (dep "NAME" "REQ"))` is still read), so a resolution that changes nothing
  writes nothing and a change is a one-line diff (R15).
* **What v3 records.** `(toolchain VERSION [COMMIT])` is the grail that solved the lock
  (R14); a build notes when the running one differs. `(size N)` is the archive's length
  (R19), `(tree SHA256)` the hash of the unpacked tree (sorted paths and file hashes,
  R20), checked after every unpack so a hand-edited file in `.grail/packages/NAME` is
  refused, and `(commands SHA256)` a digest of the declared `Package.command` set (R36),
  so a release that silently gains a build-time command is visible in the lock.
* **Overrides.** `Package.override NAME PATH` in the uncommitted `grail.local.wiz` takes
  `NAME` from `PATH` instead of the index/git (R37). `grail update` records it in the
  `(override NAME PATH HASH)` section and leaves the package out of `pkg`/`dep`; a plain
  build uses the path and prints `using override NAME from PATH`; `--locked` refuses a
  lock that records one (it is machine-local, so it cannot be reproducible). An edited
  override no longer matches the locked tree and is refused until `grail update`.
* **Signatures.** A signed index adds an `(index-signature …)` entry after `(index …)`
  (key, fingerprint, sequence, digest, expiry); an existing lock without one parses as
  before, and `--require-signature` makes it an error on the next update.
* `grail update [--locked] [--offline]`: resolve and rewrite the lock. `--locked` is a
  **check, not a resolution**: it reads the existing lock, verifies that every
  requirement is pinned and satisfied, and never reads the index or touches the network,
  so publishing a new version upstream cannot make CI fail (`grail index resolve` is the
  view of what a fresh update would choose). `--offline` uses the cached index and
  existing git clones. With no dependencies at all it succeeds and does nothing.
* `grail fetch [--locked] [--offline]`: materialise the lock without building. A missing
  lock is created unless `--locked`; `--locked` never writes and fails when a
  requirement is not pinned or is pinned to a version that does not satisfy it, or when
  the lock records an override.
  `--offline` downloads nothing: the index, archives and git clones must be cached,
  otherwise it is an error. With no dependencies it succeeds and does nothing.
  `fetch --locked --offline` is the hermetic CI prelude (checked archives, no network).
* **Pinning the index.** A URL index is `--index URL`, `Package.set "index" "URL"`, or
  `--index URL#COMMIT` / `Package.set "index-commit" "COMMIT"` for a binding pin; the
  lock records the URL and commit that produced it either way. Without a pin the commit
  is audit metadata; with one, `update` resolves from that commit and `checkLocked`
  refuses a lock from another one. A URL index must **fast-forward** from the lock's
  commit: if the index's history was rewritten or force-pushed, `update` fails with
  `the index history was rewritten (locked at A, now at B)` unless `--allow-rewind` is
  passed (TUF's rollback protection at git's own DAG cost).
* `grail build/test/run/lsp/doc` read the lock only, and `--offline` makes a missing
  archive or git clone an error instead of a download. A missing lock with require/dep
  lines says `no grail.lock: run grail update`.
* The lock holds the **transitive closure** (each `pkg` has its deps), so a build knows
  the graph offline. `checkLocked` also refuses a lock whose `pkg` dependency is absent
  or not satisfied, before anything is fetched.
* Fetching a registry package (`Grail/Registry.lean`) is: if
  `.grail/packages/NAME/.grail-pkg` already equals the archive hash, done; otherwise
  find `<cache>/grail/downloads/SHA256`, verify it (re-download if corrupt), download
  and verify the hash **before** unpacking, unpack once into the shared store
  `<cache>/grail/packages/SHA256` (a temporary directory with
  `tar -xzf --strip-components=1 --no-same-owner`, the lock's `(tree …)` checked before
  the stamp, then a rename), and link `.grail/packages/NAME` to it. A second fetch is a
  few stat calls; a second project reuses the unpacked tree (23n). `--vendor DIR` adds a
  first lookup by hash in a vendored directory, which
  `grail fetch --locked --offline` can use with no cache.

### Publishing

Publishing is a **reviewed pull request to the index repository**: the author tags a
release, uploads the deterministic archive to the release, and opens a PR that adds the
`(version …)` entry. `grail publish ARCHIVE --source URL` does the mechanical part: it
reads the manifest, checks the name, version, toolchain and requirement syntax, checks
the archive layout (one `NAME-VERSION/` with `grail.wiz`), hashes the archive, and
prints the entry to paste into the index. It does not merge anything; the review (URL
resolves, hash matches the release, deps match the manifest, name untaken) is the gate.

### Trust: fetch is not build

The registry gives **integrity and naming**, not safety. A version's bytes cannot change
without failing every lock's SHA-256 check, the lock pins name+version+source+hash, and
a corrupted cache entry is re-verified on every use. But `grail fetch` downloads files,
and `grail build` evaluates the package's `grail.wiz` (a Wiz program), compiles its C and
runs its commands: fetching a package you do not trust is downloading its author's files,
and building it is running its author's code. There is no sandbox. Git `dep` entries keep
v1's 64-bit content hash (accident detection, not cryptographic); registry entries are
the strong path.

**Signed index state (Stage 1).** An index may publish `index/snapshot.sexpr` — every
`name@version` with its SHA-256 and size, a monotone `(seq)`, an `(updated)` time, the
signing key's fingerprint `(key)` and its `(expires)` date — signed as
`index/snapshot.sexpr.sig` with `ssh-keygen -Y sign -n grail-index`. `grail update
--require-signature --allowed-signers FILE` verifies the signature offline and writes an
`(index-signature …)` entry in `grail.lock` with the key, fingerprint, sequence and
snapshot digest. Later updates re-verify from that pinned key even without the flag, and
refuse a changed key, a lower `(seq)` (rollback; `--allow-rewind` accepts a deliberate
rewind), a same-sequence rewrite, an expired key, or an entry whose hash differs from the
snapshot. `grail index verify INDEX [--locked]` is the standalone offline verifier, and
`grail index check --require-signature` audits a repository. The `allowed_signers` file
is a trust root from outside the index: the copy inside a checkout proves nothing. This
gives authorship for an index state, not freshness: there is no transparency log or
gossip, key rotation needs a re-lock, and a mirror serving an old snapshot is only caught
when the lock records a newer sequence. SHA-256 still gives integrity, not authorship.
The snapshot is additive: an index without one is read exactly as before.

**What is verified.** Short list, so "checked" is not read as "safe":

* **Every archive** is SHA-256-checked against the lock *before* it is unpacked, and
  again whenever the cached file is used; a corrupt cache entry is re-downloaded.
  `grail vendor` files are looked up by that same hash.
* **Every unpacked tree** is checked against the lock's `(tree SHA256)` when the lock
  has one, in the shared store before the stamp/rename; a hand-edited file in
  `.grail/packages/NAME` is refused.
* **The lock's shape** is checked before a build: package versions satisfy the
  requirements, the transitive closure is complete, `sha256`/`tree`/`commands` are
  64 lowercase hex digits, and `--locked` refuses a stale lock, a recorded
  machine-local override, or an unsigned registry lock when `--require-signature` is
  given. `--locked` reads no index, so it checks a signature *entry's shape* only;
  `grail index verify --locked` is the command that re-verifies the signature itself.
* **A signed index** is verified with `ssh-keygen -Y verify` against an
  `allowed_signers` file passed from outside the index (or the key a `grail.lock`
  already pinned); the snapshot must cover every entry of the index with the same
  SHA-256, `(seq)` must not go backwards, the key must not change, the same sequence
  must not be rewritten, and `(expires)` must be in the future.
* **Not verified:** git `dep` entries keep a 64-bit content hash (accident detection,
  not cryptographic); there are no signed git tags, no transparency log, no gossip, no
  download size cap, and no build sandbox — `grail build` runs the package author's
  Wiz/C code. Expiry and sequence are checked at `update`/`index verify`, not on every
  build. A first use needs an external `--allowed-signers` policy; an index without a
  snapshot is accepted unless `--require-signature` or a lock pinned one.

**Cache layout.** `<cache>/grail/downloads/<sha256>` holds the archives
(content-addressed, re-verified on every use); `<cache>/grail/packages/<sha256>/` the
unpacked trees (23n), with `.grail/packages/NAME` linked to one; `<cache>/grail/index`
the clone of a URL index. `.grail/` is not committed; `grail.lock` is; `grail cache
path/list/verify` inspects the store.

**Deferred:** a real `wiz-pl/grail-index` with CI naming rules and the first packages;
signed index tags (the signed-snapshot form is implemented) and key rotation without a
re-lock; per-registry index caches and repeatable `--index` overlays; `grail update -p NAME`
and `--minimal`; a SHA-256 tree hash for git deps (lock v3's `pkg` and override tree
hashes are implemented); private-index credential settings, binary artifacts, and automated
publish (a bot that verifies the artifact before merging). The reader understands the
`index/@org/name.sexpr` layout, but scopes are not enforced in names or manifests yet.

**The index repository.** The layout of a `grail-index` (the static `index/NAME.sexpr`
files, deterministic `packages/NAME-VERSION.tar.gz` archives, `index.wiz` and the
generator), the `grail index check` validation (names, versions, semver ranges, archive
SHA-256s, module-prefix conflicts) and the hosting/signing plan (TUF stages, Sigsum; no
transparency log yet) are in
[index-repository.md](23-grail/index-repository.md).

## 23n: `grail vendor`, a shared store, and `grail cache`

Two projects that pin the same packages used to download and unpack each archive twice:
the download cache was content-addressed, but the unpacked tree lived only in
`.grail/packages/NAME`, per project. This section fixes both halves.

**The shared store.** `<cache>/grail/downloads/<sha256>` is still the content-addressed
archive cache (re-verified on every use). The unpacked tree now lives in
`<cache>/grail/packages/<sha256>/` (with the `.grail-pkg` stamp), and
`.grail/packages/NAME` is a symlink to it; where a symlink cannot be made it is a copy of
the same tree. So one archive is downloaded once and unpacked once, for every project
and every package name of a lock (a lock may mention the same bytes twice), and a warm
project fetch is a stat call. `--cache` picks the store (the default is
`~/.cache/wiz`); `--cache-ro` stays for the elaboration cache only.

**`grail vendor [DIR]`** (default `vendor/`) copies the lock's registry archives into
`DIR` as
`<sha256>.tar.gz` (two packages with the same bytes share one file) and writes
`DIR/index.sexpr`, with one `(archive NAME VERSION SHA256 FILE)` line for each package. It never
rewrites `grail.lock`: the lock's `source` stays the published URL, so the same lock
works on a machine with `vendor/` and on one without it. Missing archives are downloaded
(through the cache) unless `--offline`; `--locked` never resolves or writes the lock (it
is a check, as for `update` and `fetch`), so a CI step can only consume the committed
lock.

**Using a vendor directory.** `--vendor DIR` (or `Package.set "vendor" "DIR"` in
`grail.wiz`, or in `grail.local.wiz`) makes `fetch`, `build`, `test`, `run`, `lsp` and
`doc` look each archive up by SHA-256 in `DIR/index.sexpr` first, then in the cache, and
download only if neither has it. The hash is the identity, so the source URL is never
rewritten and the lock stays byte-identical across machines. The hermetic CI prelude is
`grail vendor` once (and commit `vendor/`), then `grail fetch --locked --offline
--vendor vendor` and `grail build`.

**`grail cache [path|list|verify]`.** `path` prints the downloads, packages and index
locations; `list` prints one line per archive (hash and size) and per unpacked tree (hash
and stamp); `verify` re-hashes every archive and checks every stamp, exits 1 on a corrupt
entry and does not repair it (the next fetch re-downloads a corrupt archive; a wrong
stamp just causes an unpack). It needs no `grail.wiz`, so it works in an empty directory.

Vendoring does not change the lock's meaning: the lock is still the v3 file above
(`source` stays the published URL), and `vendor/index.sexpr` is a separate, local file.
Tests: group `grail-vendor` (five cases: content-addressed vendoring with a stable lock,
an offline `--locked` fetch from the vendor directory through the shared store, one
download and one unpack for two packages with the same archive, the cache commands with
a corrupt entry, and the `vendor --locked`/`--offline` failures).

## 23o: `grail new`

`grail new NAME [--dir DIR]` writes the smallest package that builds, runs and tests:

```
grail.wiz        Package.new "NAME"
                   |> Package.lib "NAME-lib" "src"
                   |> Package.exe "NAME" "src/Main.wiz"
                   |> Package.tests "tests" "tests"
src/Main.wiz     import Std; def main : IO Unit := IO.println "hello from NAME"
tests/hello.wiz  a `-- test: run` golden test, with hello.expected
README.md        how to build, run and test it
.gitignore       .grail/
```

It goes into `DIR` — `./NAME` by default, `DIR/NAME` with `-C DIR` — and an existing
non-empty directory is refused, so `new` never overwrites work. The name must be a
letter followed by letters, digits, `_` or `-` (at most 64 characters); it is the
package's name, its targets' names and the greeting. Inside the new directory
`grail build`, `grail run NAME` and `grail test` work as they do here; the second build
runs nothing.

`grail new` found a link-key bug: a link job's key did not include the name of the
binary it makes, so a test whose program compiles to the same C as an `exe` (the
generated test and `src/Main.wiz` print the same line) was "up to date" from the exe's
link directory and the test ran a binary that was not there. The key now includes the
output's name (and whether it is installed in `.grail/bin`), so two programs with the
same object and link files no longer share a directory.

Tests: `grail-commands`, "new: the generated package builds, runs and tests; a
non-empty directory is refused" (also covers the refusal and the name check).
