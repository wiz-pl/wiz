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
then be about M.B's (it proved `Empty`, `wiz-notes/soundness-probes/is-import-shadowing`).
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

```
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

```
import Grail
def settings : Settings := Settings.empty
  |> Settings.set "cflags" "-I/nix/store/…-gmp-…-dev/include"
  |> Settings.set "ldflags" "-L/nix/store/…-gmp-…/lib -Wl,-rpath,/nix/store/…-gmp-…/lib"
```

## 23a: the toolchain as flags

`wiz` reads no environment variables: the toolchain record (`Wiz/Toolchain.lean`: C
compiler and flags, `llc`, the collector's flags, the cache, module roots) comes from
`--cc`, `--cflags`, `--ldflags`, `--libs`, `--llc`, `--cache DIR`/`--cache-ro DIR`/`--no-cache` and
`-I DIR` (which replaces `$WIZ_PATH`), and is passed explicitly to everything that
compiles. Its compiler fields are its `id`, which enters grail's keys.

## 23e: the self-hosted toolchain as targets

`Package.selfhost NAME ROLE` builds the self-hosted programs from `selfhost/*.wiz`
(`Wiz/Selfhost.lean` generates their sources, parser tables included, for grail and the
tests alike): `checker`, `compiler`, and `bootstrap`, the fixpoint check of
`scripts/fixpoint.sh` as jobs (generate the source, build stage 1, `self1.c`, stage 2,
`self2.c`, compare). `grail build bootstrap` runs it (minutes); run again, it runs
nothing unless a source, `rt.c`, the toolchain or grail changed. `grail build` alone
leaves it out.

## 23f: a test runner

`Package.tests NAME DIR` makes every `.wiz` file under `DIR` a test, with its expected
output beside it in `.expected`. The first line gives the kind: `-- test: check` (the
default: the messages, as `wiz check` prints them) or `-- test: run` (what `main` prints,
compiled through C). A pass is a job like any other, keyed by the file (and its
imports), the kind, the toolchain and the expected output, so `grail test` again runs
nothing; `grail test FILTER` runs the tests whose path contains it, and
`grail test --update` writes the actual output. Every example is a test
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
(23k; `--timeout SECS`, default 1800; tests `--test-timeout SECS`, default 300, so a test that
hangs fails instead of hanging the run). A failed job is reported and the jobs that depend
on it are skipped; the others still run. Each job's output is buffered and printed in the
graph's order, so `-j 1` and `-j 8` print the same report, and a second build still runs
no jobs.

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

```
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
