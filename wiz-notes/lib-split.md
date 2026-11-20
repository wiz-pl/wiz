# Splitting `lib/`: what can move, and what the compiler must learn

Scope: `lib/` at `integration/train7` (`7365f7d1`). The inventory is a scan of the
checked-in `.wiz` files; the extension points are read from `Wiz/`, `selfhost/`,
`Grail/` and `scripts/`. Nothing here is a proposal to change the language: the
question is which library modules could live in another repository, and what the
toolchain would have to expose first.

Two different questions hide in "split", and they have different answers:

* **Source split, one installed stdlib.** The module keeps its name and its
  first-root trust; only its git repository (and release cadence) changes. The
  toolchain release assembles `share/wiz/lib` from several repositories.
* **Package split, independent versions.** The module is fetched per project (as a
  `grail` dependency or registry package) and lives in a later root. Only modules
  that need no `builtin`, no new runtime symbol and no compiler name contract can do
  this today.

Most of `lib/` is clean for the first; a large part is clean for the second. The
hard cases are the four modules the SMT translation recognises by module name
(`Prelude`, `Word`, `Logic`, `Int`), the modules the FFI marshaller recognises by
type name (`IO`, `Std`), the HDL names the elaborator looks up (`Hw`, `HwTy`,
`ShareLet`), and `Prelude` itself, which the self-hosted frontend embeds as a string.

## 1. Dependency-graph inventory

Measured over `lib/**/*.wiz`, counting `import M` edges between modules of `lib`
(doc-comment code blocks are excluded; see "the loader's superset" below). The
numbers are reproducible with `python3 drafts/split/lib_graph.py lib`.

| number | value |
|---|---:|
| modules | 139 |
| import edges | 346 |
| cycles | 0 |
| roots (no imports) | 1 (`Prelude`) |
| total lines | 61,757 |
| modules outside the `lib` root | 82 (`Data/` 5, `Hdl/` 31, `Scry/` 42, `Web/` 4) |

The graph is a DAG with a single source. `Prelude` has no imports; `Text` is the
most imported module (50 importers), then `Prelude` (27), `Word` (22), `Hdl.Core`
(19), `Logic` (17), `Scry.Wil` and `Scry.Rules` (10 each), `IO` and
`Scry.Analysis` (9 each), `WordMap` (8), `Nat` and `Json` (7 each).

### Areas

Lines are source lines; "core deps" is the transitive closure outside the area.

| area | modules | lines | core deps (transitive) |
|---|---:|---:|---|
| Prelude | 1 | 1,578 | — |
| runtime core (`Word`, `Int`, `Logic`, `IO`, `Std`, `Nat`, `Data.Order`, `Data.Result`, `Data.WordBytes`) | 9 | 2,426 | Prelude |
| data / text (`Text`, `Json`, `FingerTree`, `Data.PMap`, `Data.ListLemmas`, `Intern`, `Tagged`, `WordMap`, `WordArray`, `Optic`, `OpticDerive`, `Encoding`, `Args`, `Sha`, `Functor`) | 15 | 4,563 | Prelude, Word, Logic, Data.WordBytes |
| vectors / bit vectors (`Vec`, `BitVec`, `BitVecAdd`, `BitVecShift`) | 4 | 1,441 | Prelude, Word, Nat, Ring, Sat, BitBlast, Data.Order |
| proving (`Ring`, `RingTactic`, `Sat`, `SatTactic`, `BitBlast`, `BvDecide`, `SimpLemmas`, `IntRing`, `IntOrder`, `Rat`, `Hoare`, `HoareTactics`, `HProp`, `HoareExamples`) | 14 | 6,899 | Prelude, Word, Int, Logic, Nat, Text, Data.ListLemmas, Data.Order, Functor |
| deriving (`Deriving`) | 1 | 439 | Prelude, Text |
| concurrency / effects (`Eff`, `EffHeap`, `Conc`, `MVar`, `Task`, `Ref`, `Region`, `Scope`, `Session`, `Handle`, `HeapBorrow`) | 11 | 2,534 | Prelude, IO, Logic, Nat, Text, Sys, Data.ListLemmas, Optic, HoareTactics |
| systems (`Sys`, `Serial`, `Trace`, `Infoview`) | 4 | 2,134 | Prelude, IO, Logic, Json, Tagged, Optic, Sys |
| HDL (`Hdl.*`) | 31 | 12,567 | Prelude, Word, Logic, Nat, Vec, BitVec, Text, Deriving, OpticDerive, Std, Trace |
| Scry (`Scry.*`) | 42 | 21,193 | Prelude, Word, Logic, Nat, Text, Deriving, Json, Functor, WordArray, WordMap |
| Web (`Web.*`) | 4 | 1,417 | Prelude, IO, Logic, Text, Json, Optic, Tagged |
| `Feral` | 1 | 3,212 | Prelude, Text, Logic, Deriving, Optic, OpticDerive, Data.Result (+ `FeralCore` from `drafts/feral/lib`) |
| `Plot` | 1 | 1,017 | the whole Rat/Int/Ring/Json/Text cone (11 modules) |
| `Grail` | 1 | 337 | Prelude |

### The compiler-facing core

"Compiler-facing" means the Lean elaborator or the self-hosted frontend names the
module or one of its declarations, not merely that it is useful. The evidence:

| module | what is hard-coded | where |
|---|---|---|
| `Prelude` | the core types and classes (`Bool`, `Nat`, `List`, `Option`, `String`, `Char`, `Except`, `Add`…`OfNat`, `Monad`/`Monad1`, `Mux`), the metaprogramming types (`Syntax`, `Tactic`, `Deriver`, `Macro`, `CommandMacro`), and the `builtin` keys | `Wiz/Elab/Command.lean:1573`, `2278-2304`, `2750-2751`, `2994`; `Wiz/Elab/Term.lean:3218-3250` |
| `Word` | `UIntN` is recognised for SMT translation and is "opaque outside `lib/Word.wiz`" | `Wiz/Smt/Translate.lean:110-142` |
| `Int` | `Int` for SMT; `builtin int` is trusted even outside the library | `Wiz/Smt/Translate.lean:115,130`; `Wiz/Elab/Command.lean:2298` |
| `Logic` | `Trans`/`Trans.trans` for `calc`; `And`/`Or`/`Not`/`Iff` for SMT | `Wiz/Elab/Term.lean:1230-1288`; `Wiz/Smt/Translate.lean:271-274` |
| `IO` | `IO` for `main`, `do` and FFI results; `UInt64`, `Float64`, `Bytes` are the FFI marshalling vocabulary; the self-hosted build prepends `import IO` | `Wiz/Compiler/Build.lean:59-60`; `Wiz/Elab/Command.lean:1602-1606,1618`; `Wiz/Compiler/Run.lean:648`; `Wiz/Selfhost.lean:158-159` |
| `Std` | `Array`, `Str`, `StrMap` are FFI/marshalling types; the self-hosted build prepends `import Std` | `Wiz/Elab/Command.lean:1606,2655`; `Wiz/Compiler/Run.lean:650`; `Wiz/Selfhost.lean:158-159` |
| `Hdl.Core` | `Hw`, `Hw.eq`, `Hw.mux`, `Hw.share`, `Hw.lit`, `HwTy`, `ShareLet` drive the HDL elaboration (signal types, `match` lowering, auto-share) | `Wiz/Elab/Term.lean:2052-2059,3261,3285,3316,3374-3404` |
| `Deriving` | the witness search for `partial` looks for `Inhabited.default` | `Wiz/Elab/Witness.lean:106-108` |
| `Sat` | `Sat.IsTrue` is the shape of a `native_refl`/sat axiom, with a fallback to `e = true` | `Wiz/Elab/Command.lean:1863`; `Wiz/Elab/Term.lean:3911` |
| `Grail` | `grail` finds the stdlib as `<binary>/.../lib` and reads build files through it | `Grail/Cli.lean:167-174`; `Grail/Build.lean:40` |
| `Text` | the prelude-drift CI check requires the names the embedded prelude promotes (`List.map`, `String.length`, …) to be declared under `lib/` | `scripts/check-prelude-drift.py:27-42` |

The important distinction is **module-name** coupling versus **declaration-name**
coupling:

* Only `Wiz/Smt/Translate.lean:113-116` compares a declaration's home module to a
  literal (`"Prelude"`, `"Word"`, `"Logic"`, `"Int"`). That is the one place where a
  module living outside `lib` silently loses a feature (the SMT translation stops
  recognising its definitions).
* The rest are `g.contains "Name"` / `classes.any (·.name == "Name")` checks. They
  fire whenever the name is in the environment, whatever module declares it. A
  package can provide `Hw`, `ShareLet`, `Trans` or `Inhabited.default`; the
  elaborator will use it as soon as the file imports it. The failure mode is a
  degraded feature (no signal lowering, a `calc` error) rather than a wrong term.
* `Prelude` is special because the self-hosted frontend does not read it: it
  embeds `preludeText` and injects it as the module `Prelude`
  (`selfhost/Frontend.wiz:10639`), and canonicalises `IO`, `Std` and `Sys` to that
  same module (`selfhost/Frontend.wiz:10369-10376`). `scripts/check-prelude-drift.py`
  then requires every name of the embedded copy to be declared under `lib/`.

### A trap in the loader's superset

`Wiz/Module.importsOf` is a line scan: it trims each line and takes `import M`
wherever it appears, *including inside a `/-! … -/` doc comment*
(`Wiz/Module.lean:25-34`). The language's import graph is 346 edges; the loader's
scan yields 348, and the two extra edges are doc-block examples:

* `Data.Order` (doc example) imports `Nat`, while `Nat` really imports
  `Data.Order` — the loader sees a `Data.Order ↔ Nat` cycle that the language does
  not have.
* `Hdl.Core` (doc example) imports `IO`.

This does not break elaboration (imports are commands, and `loadClosure` skips a
module it already has), but it does mean a split library's doc examples can pull
extra modules into every consumer's closure. Worth knowing before a module is moved
behind a package boundary.

## 2. Split proposal (ranked)

"Clean" means: no `builtin`, no new runtime symbol, no compiler module-name check;
the package can be a later root today. "Needs a hook" names the extension point in
§3. Sizes are lines; "in-lib importers" counts modules outside the package that
import one of its modules.

| rank | package | modules | lines | in-lib importers | core deps | compiler names | verdict |
|---:|---|---:|---:|---:|---|---|---|
| 1 | **Plot** | 1 | 1,017 | 0 | Rat/Int/Ring/Json/Text cone | none | clean; the prototype |
| 2 | **Scry** | 42 | 21,193 | 0 | Text, Word, WordMap, WordArray, Json, Logic, Deriving, Functor | none | clean; already a `grail` package (`scry/grail.wiz`); largest win |
| 3 | **Feral** | 1 (+`FeralCore` in `drafts/feral/lib`) | 3,212 | 0 | Text, OpticDerive, Optic, Deriving, Data.Result | none | clean for the host; custom `command`/syntax means the self-hosted frontend cannot check it |
| 4 | **Web** | 4 | 1,417 | 0 | Json, Optic, Tagged, Text, IO | none | clean |
| 5 | **Optics** (`Optic`, `OpticDerive`) | 2 | 500 | 5 | Deriving, Logic, Data.Result, Text | none | clean; `[deriver]` is already a user hook |
| 6 | **Data structures** (`FingerTree`, `Data.PMap`, `Data.ListLemmas`, `Data.Order`, `Data.Result`, `Intern`, `Tagged`, `WordMap`, `WordArray`) | 9 | 2,632 | 15 | Json, Text, Word, Logic, Nat | none | clean; the three natives (`WordMap`, `WordArray`, `Intern`) take their runtime ABI and trust-ledger rows with them |
| 7 | **Proving / algebra** (`Ring`, `RingTactic`, `Sat`, `SatTactic`, `BitBlast`, `BvDecide`, `SimpLemmas`, `IntRing`, `IntOrder`, `Rat`, `Hoare`, `HoareTactics`, `HProp`) | 13 | 6,679 | 5 | Int, Logic, Word, Nat, Text, Data.ListLemmas, Data.Order, Functor | `Sat.IsTrue` (optional) | mostly clean; `Sat` is the one declaration-name hook |
| 8 | **Concurrency / effects** (`Eff`, `EffHeap`, `Conc`, `MVar`, `Task`, `Ref`, `Region`, `Scope`, `Session`, `Handle`, `HeapBorrow`) | 11 | 2,534 | 0 | IO, Sys, Logic, Text, Data.ListLemmas, Optic, HoareTactics | none | clean, but many small modules; `Conc`/`Eff` are one story |
| 9 | **Systems** (`Sys`, `Serial`, `Trace`, `Infoview`) | 4 | 2,134 | 4 | IO, Logic, Json, Tagged, Optic | none | clean; `Serial` carries `link_c "serial.c"`, `Sys` several `foreign_type`s |
| 10 | **HDL above Core** (`Hdl.*` except `Hdl.Core`) | 30 | 8,348 | 0 | Hdl.Core, Vec, BitVec, Std, IO, Optic, Trace | `Hw`/`HwTy`/`ShareLet` (provided by Hdl.Core) | clean as a package *if* it imports `Hdl.Core`; see rank 11 |
| 11 | **Hdl.Core** | 1 | 4,219 | 19 | BitVec, Vec, Trace, Deriving, Logic, Text, Word | `Hw`, `Hw.eq/mux/share/lit`, `HwTy`, `ShareLet` | needs a hook or stays in-tree; the names are the elaborator's HDL API |
| 12 | **Grail** (`lib/Grail.wiz`) | 1 | 337 | 0 | Prelude | `grail` finds it in `lib/` | needs `grail` to ship its own module root |
| 13 | **Text** | 1 | 275 | 50 | Prelude | drift check | keep in-tree for now; every library imports it |
| 14 | **Json** | 1 | 540 | 7 | Text | none | keep with Text for now |
| 15 | **Vec** | 1 | 337 | 2 | Nat, Logic, Data.Order | none | keep; `BitVec` and `Hdl.Bus` are its consumers |
| — | **Prelude** | 1 | 1,578 | 27 | — | everything | **never**; embedded in the self-hosted frontend and the anchor of trust/name resolution |

Ranking notes:

* **Scry is the obvious first real package.** It is already a `grail` package
  (`scry/grail.wiz`), it has no in-library importers, it uses no `builtin`, and
  `lib/Scry` is one-way: `scry/src/Scry/*` imports `lib/Scry/*`, never the reverse.
  Moving `lib/Scry` to `scry/lib/Scry` and changing
  `Package.lib "scrylib" "../lib"` to `Package.lib "scrylib" "lib"` is a pure
  relocation: the package keeps its two roots (`src` for the app, `lib` for the
  analysis library), and the root package gains one `lib` target for the examples.
  The library modules are pure Wiz (no `extern`, `builtin`, `link_c` or `import_c` at
  all); the C lives in the package's own `scry/src/Scry/Native.wiz`, with `link_c`
  paths relative to that file (`scry/src/Scry/Native.wiz:37-41`).
* **Plot is the cheapest whole-package proof**: one module, no importers, no
  natives, and a dependency cone that exercises the Rat → Int → Ring → Json → Text
  path. It is the prototype in §4.
* **Feral already proves a cross-root import inside the repo**: `lib/Feral.wiz`
  imports `FeralCore`, which lives in `drafts/feral/lib` and is declared as a
  separate `Package.lib` in the repository's `grail.wiz`. That is the package story
  working for a 3.2k-line module with a custom grammar and command macros.
* **Hdl.Core is the one large module that is genuinely compiler-facing.** Its 4.2k
  lines are mostly the `Hw` model, so "keep the names, move the file" is not a
  small split. Either keep it in-tree (and move only the 30 protocol/implementation
  modules above it) or add the HDL hook in §3.
* **`Text` and `Vec` are structural, not incidental.** `Text` has 50 importers and
  the drift check pins some of its names under `lib/`; `Vec` is what `BitVec` and
  `Hdl.Bus` are written against. Moving either is a whole-stdlib change, not a
  package.

## 3. Extension points, with evidence

For each: what exists, what is missing, and the smallest generalisation that would
let a library move.

### EP1. A package manifest for `wiz` (exists for `grail`, missing for `wiz`)

*Exists.* `grail` has a real package graph: `Ctx.roots` is
`[std, dir] ++ libRoots ++ searchPath` (`Grail/Build.lean:40`), every `Package.lib`
target contributes a root (`Grail/Build.lean:42-43`), `Package.dep`/`Package.require`
resolve through a lock, and a dependency's `lib` roots become module roots
(`docs/stages/23-grail.md`, 23h/23m). `grail lsp` passes the package roots too.

*Missing.* `wiz check`, `wiz run`, `wiz lsp` and `wiz doc` only take `-I`
(`Wiz/Module.lean:169-172`; `Main.lean:115-122`). They do not read `grail.wiz` or
`grail.lock`, so a split library is usable only if every consumer passes the right
`-I` by hand (or goes through `grail`).

*Smallest generalisation.* Either (a) let `wiz` accept `--package FILE` (or read
`grail.wiz` in the current directory) and use only its roots — the manifest is
already a Wiz program and `grail` already evaluates it; or (b) install split
libraries under `share/wiz/packages/NAME/lib` and have `Module.toolchainLib` return
a list. (b) is the one that also solves EP7.

### EP2. Trust for `builtin` registrations (exists: first root only)

*Exists.* Trust is a predicate over module names: `CommandState.trustedModule`
(`Wiz/Elab/Command.lean:149-152`), filled with `Module.fromFirstRoot` — the
modules of the first root, the toolchain's own `lib/`
(`Wiz/Module.lean:189-195`; `Main.lean:118-122`; `Grail/Elab.lean:54-60`). A
registration outside it is recorded as an assumption and warned about
(`Wiz/Elab/Command.lean:2294-2304`); `#print axioms` lists it. The design is
stage 22f (`docs/stages/22-numbers.md:180-213`).

*Missing.* A second root can never be trusted. `-I`, the package's own directory,
and every `grail` dependency are untrusted by construction. That is the right
default; it becomes a blocker only for a package that needs a `builtin`
(e.g. a new numeric type) or wants the checked-in stdlib's registrations reviewed
for a moved `Int`-like module.

*Smallest generalisation.* A `--trust-root DIR` (or `Package.trust NAME`, recorded in
the lock and passed to jobs as a flag) that extends the trusted prefix. Keep the
default "only the toolchain's library", log every use, and make the flag part of
the cache key (`Cache.moduleKeys` already mixes a module's trust,
`Wiz/Cache.lean:644,664`). A more principled version is per-declaration trust in a
signed manifest, but that is a design, not a small change.

### EP3. The `builtin` key list is closed (exists: 21 keys, one registration each)

*Exists.* `builtin k := n` parses (`Wiz/Parser/Builtin.lean:339`), the elaborator
checks the key against a literal list of 21 keys (`Wiz/Elab/Command.lean:2278-2279`),
checks the declaration's shape (`builtinShapeError`), and allows one registration
per key and one key per constant (`2281-2304`).

*Missing.* A package cannot add a new primitive key, and cannot re-register an
existing one. For the split proposed here that is fine: only `Prelude` and `Int`
register keys today, and both stay. It matters for a package that wants a native
numeric type of its own; today it must use `extern` + `implemented_by` instead.

*Smallest generalisation.* Allow a namespaced key (`pkg.key`) with a declared shape
and require the same trust as EP2; or leave the list closed and document
`extern`/`implemented_by` as the package route (this is what `WordMap`/`WordArray`/
`Intern` already do).

### EP4. `deriving` handlers (exists: a user hook; three sharp edges)

*Exists.* `attribute [deriver C] f` is a general, user-registered hook: the parser
has `command.attrDeriver` (`Wiz/Parser/Builtin.lean:385`), the elaborator stores the
pair (`Wiz/Elab/Command.lean:2989-2999`), and `deriving C` looks it up and runs the
deriver (`1656-1672`), with an error that tells the user how to register one
(`1667`). `lib/Deriving.wiz` is itself a user of this hook (`278,320,367,435`).

*Sharp edges.*
* `BEq` and `Repr` on a proposition are rejected by a literal name test in the
  elaborator (`if isProp && (C == "BEq" || C == "Repr")`,
  `Wiz/Elab/Command.lean:1663`), so a package cannot provide its own rule.
* The self-hosted frontend pre-registers a fixed table of five derivers by name
  (`selfhost/Frontend.wiz:605-615`) because its embedded prelude has no classes; a
  package's new deriver is not in it.
* The `partial` witness search looks for `Inhabited.default` and the class
  `Inhabited` by name (`Wiz/Elab/Witness.lean:106-108`); moving `Deriving` out of
  `lib` does not break it as long as the file imports the package, but moving it out
  of every default import silently removes a witness case.

*Smallest generalisation.* Move the Prop rule into the deriver (a class attribute or
a `deriver` field), and have the self-hosted frontend process
`attribute [deriver C] f` (it already parses the command,
`selfhost/Frontend.wiz:9571`) instead of a fixed table. Neither is needed for a
source split; both are needed for a package that ships new derivers.

### EP5. `syntax`, categories, `command` and macros (exists: a full extension point)

*Exists.* New categories with `declare_syntax_cat` (keyword scopes optional,
`docs/stages/13-language.md`, 13j), new rules in any declared category
(`Wiz/Parser/SyntaxCmd.lean:64,98`), new `command` rules, and command macros:
`attribute [macro command.feral] Fe.macro` (`lib/Feral.wiz:3210-3212`) dispatches
on a node kind and expands one command into several
(`Wiz/Elab/Command.lean:2742-2760`; command macros require `CommandMacro`, which is
in `Prelude`). `local` scoping exists (`13m`). `lib/Feral.wiz:57-132` is the proof:
it declares two dozen categories, a whole expression/statement grammar, and three
`command` rules.

*Missing.* The self-hosted frontend has fixed parser tables and a built-in tactic
grammar (`Wiz/Selfhost.lean:68-98`); it dispatches `syntax`/`declare_syntax_cat`
but does not enforce keyword scopes (`docs/stages/13-language.md:463-466`). A split
library that adds syntax or command macros can be checked by the host, not by the
self-hosted frontend.

*Smallest generalisation.* None for the host. For the self-hosted frontend, load
the tables from modules (the planned A1 workstream) — out of scope for a library
split, but the reason a syntax-heavy package (Feral) must be marked "host only".

### EP6. `extern`, `link_c`, `import_c`, `c_struct` (exists; the ABI is the contract)

*Exists.* `extern` (`Wiz/Parser/Builtin.lean:359`), `link_c` (`356`), `import_c`
(`348`), `c_struct` (`305`), `foreign_type` (`Wiz/Elab/Command.lean:2321`). Paths
are resolved relative to the declaring module, not the main file:
`Module.cSourcesOf`/`cSourceTable` (`Wiz/Module.lean:132-157`), the check-time
header table (`Main.lean:275-315`), and `grail`'s link job
(`Wiz/Compiler/Build.lean:46-99`). This already works from any root: `lib/Feral.wiz`
imports `drafts/feral/lib/FeralCore.wiz`, and `scry/src/Scry/Native.wiz:37-41`
links `../../native/*.c`.

*Missing.* The runtime ABI (`runtime/wiz_rt.h` and `runtime/rt_*.inc`, embedded in
the compiler by `runtime/WizRuntime.lean:42-57`) is not something a package can
extend: a package may call the published `wiz_*` symbols, or bring C with `link_c`.
`#eval` cannot run a `link_c` function (only the interpreter's native model), so a
package that wants both `#eval` and a native fast path needs the `implemented_by`
+ interpreter-model pattern (`docs/stages/29-natives.md`). Allowed: `--libs`,
`--cflags`, `--ldflags` in the toolchain record (`Wiz/Toolchain.lean:20-26`), and
`Package.set "libs"` in `grail.wiz`. In `lib/` only `Serial` carries C
(`lib/serial.c`, `lib/Serial.wiz:27`); every other `extern` is a runtime symbol from
`runtime/rt_*.inc`.

*Smallest generalisation.* None required; document `wiz_rt.h` as the package ABI and
add a `Package.include`/`cflags` convenience if packages grow headers.

### EP7. Toolchain library path: one root, assembled at packaging time

*Exists.* `Module.toolchainLib` guesses `<dir>/lib` from the binary's location and
falls back to `./lib` (`Wiz/Module.lean:159-167`); `grail`'s `findStd` does the same
(`Grail/Cli.lean:167-174`). The Nix package stages `lib/` byte for byte, and
`docs/stages/22-numbers.md:197-208` explains why the first root is special.

*Missing.* Exactly one directory is the stdlib. A source split is invisible unless
the release build copies every split repo's modules into that one `lib/` (a
vendoring step), and then module names and trust are unchanged. A *package* split
needs `roots` to include installed package roots after the stdlib.

*Smallest generalisation.* For the source split, no compiler change: assemble
`share/wiz/lib` in the release (Nix `symlinkJoin`/copy, or the flake inputs) —
this is the cheapest path and the one to take first. For independent packages,
change `toolchainLib` to return a list (stdlib first, then
`share/wiz/packages/*/lib`) or read `share/wiz/stdlib.roots`; keep the first-root
trust rule (EP2) and the shadowing rule (`Module.shadowed`, `Wiz/Module.lean:176-187`).

### EP8. The gates are path-scoped to `lib/`

*Exists.* The trust ledger walks `lib/` and the axiom-free examples only
(`docs/trust-ledger.md`, "Scope"; `scripts/trust-ledger.sh`); `native` test group.
`scripts/check-name-collisions.py` scans `lib/`, `scry/src/` and `selfhost/` by
default. `.github/libdiff-corpus.txt` lists `lib/Scry/*`. `scripts/check-prelude-drift.py`
requires the embedded prelude's names to be declared under `lib/`.

*Missing.* A moved native library leaves the ledger's scope and its trust review
silently stops covering it. The ledger doc already measured what a second root
costs (the `selfhost/` proposal: +578 rows, ~9m30s cold) and says it is a scope
decision. The same decision is needed per split root.

*Smallest generalisation.* A repeatable `--root DIR` in the ledger walker and a
reviewed reason per root; update the collision/libdiff corpus and the drift check's
roots. This is CI work, not compiler work.

### EP9. The self-hosted frontend's pinned module names

*Exists.* `checkerSource`/`compilerSource` prepend `import IO` and `import Std`
(`Wiz/Selfhost.lean:155-166`). The frontend injects its embedded `preludeText` as
`Prelude` (`selfhost/Frontend.wiz:10639`) and canonicalises `IO`, `Std`, `Sys` to
`Prelude` (`10369-10376`). It has a built-in tactic grammar
(`Wiz/Selfhost.lean:68-98`).

*Missing.* The self-hosted frontend cannot consume the real `Prelude`, `IO`, `Std`
or `Sys`; those names are pinned. That is a reason to keep those four in-tree, not
a reason to avoid splitting `Plot`. A library that moves out and is used by the
self-hosted sources would need the frontend to load it (A1).

*Smallest generalisation.* None for the split; keep the selfhost sources on the
in-tree core and treat the selfhost frontend as a second consumer of the compiled
stdlib at packaging time.

### EP10. SMT translation recognises modules by name

*Exists.* `Smt.Translate.fromLib` returns true only for a declaration whose home
module is `Prelude`, `Word`, `Logic` or `Int` (`Wiz/Smt/Translate.lean:109-116`), so
a user's own `UIntN.not` is not read as a bit-vector operation. `UIntN` recognition
is gated on the same test (`121-142`).

*Missing.* Moving one of those four out of `lib` (even under its own name) makes
`fromLib` false and silently disables SMT translation for it. That is the only
**hard** module-name coupling in the compiler.

*Smallest generalisation.* Replace the module test with a declaration marker: e.g.
`attribute [smt.trusted] Nat.add` (a boolean in `Globals`), or a per-root
`trusted` predicate threaded into the translation (it already receives `Globals`).
Until then, keep `Prelude`, `Word`, `Logic` and `Int` in `lib`.

### EP11. One global namespace (a package cannot own a name)

*Exists.* Every top-level declaration is a name in one project-wide scope; a module
that declares a name another imported module declares is refused at the `import`
(`docs/stages/23-grail.md`, 23b: "Wiz has no namespaces (`Nat.repr` is one global
name)"). `scripts/check-name-collisions.py` models the coming namespaces and today's
global scope and is the local guard.

*Missing.* Two independently versioned packages can pick the same name; the failure
shows up in a consumer as a duplicate declaration at an `import`, not at publish
time. There is no package-scoped name.

*Smallest generalisation.* Keep the convention the tree already uses (`Scry.*`,
  `Hdl.*`, `Data.*`) and have the registry reject a package whose declarations
  collide with another selected package; or wait for the planned module namespaces,
  which make a declaration `Module.path.name`. For a source split this is unchanged:
  the names move with the files.

## 4. Prototype

Prototype layout (committed under `drafts/split/plot/`):

```
drafts/split/plot/
  grail.wiz        -- Package.new "plot" |> Package.lib "plot" "lib" |> Package.check "demo" "demo.wiz"
  lib/Plot.wiz     -- the library module, unchanged, in its own root
  demo.wiz         -- imports Plot, builds a frame and evaluates Plot.svg
```

The point is not the file move; it is proving that a 1k-line library with an
11-module dependency cone (Rat → Int/Ring → Prelude/Text/Json) checks from a later
root with no compiler change.

*Result.* The prototype checks and evaluates with the train7 worktree binary
(`.lake/build/bin/wiz`, built from `7365f7d1`):

```sh
# with lib/Plot.wiz moved aside: the module is not in lib, so it is not found
$ wiz check drafts/split/plot/demo.wiz
demo.wiz:1:1: error: unknown module Plot            # rc=1
# with the package root: it checks, and #eval prints the SVG
$ wiz check -I drafts/split/plot/lib drafts/split/plot/demo.wiz
demo.wiz:16:1: info: "<svg xmlns=…>…</svg>"         # rc=0, no errors
```

The same two commands were first run with an older Nix `wiz` whose `lib/` predates
`Plot` — the same "moved out of lib" situation — with the same result. The shadowing
half is the complement (train7 binary, `lib/Plot.wiz` in place, a package copy with
one extra declaration):

```sh
$ wiz check -I <scratch>/plotshadow shadow.wiz
shadow.wiz:3:8: error: unknown identifier 'Plot.extra'              # rc=1
shadow.wiz:1:1: warning: …/Plot.wiz is ignored: module Plot is the toolchain's own
  (…/lib), which a module root cannot replace
```

So the package story works today for a module the stdlib does **not** contain, and
`-I` correctly refuses to replace one it does (`Module.shadowed`,
`Wiz/Module.lean:176-187`). That is the safety property the split relies on: a
consumer cannot swap `Prelude` or `Word` for a different file by passing `-I`.

Two existing precedents already in the tree:

* `lib/Feral.wiz` imports `FeralCore` from `drafts/feral/lib`, declared as a
  `Package.lib` target in `grail.wiz`; the import works because the package root is
  in `Ctx.roots`.
* `scry/grail.wiz` already builds a separate package against `lib/` via
  `Package.lib "scrylib" "../lib"` and its own `src` root; the Scry modules are one
  `git mv` away from being package-owned.

## 5. Staged plan

Each stage is a self-contained change with a verification, and the compiler change
is stated. "Repo split" = the module moves to another repository but is still
assembled into the installed `lib/`; "package split" = fetched as a dependency.

**Stage 0 — prototype and guardrails (no compiler change).**
Commit the Plot package under `drafts/split/plot`, and a small script that prints
the graph numbers in §1. Verify `wiz check -I drafts/split/plot/lib
drafts/split/plot/demo.wiz` (and the shadowing behaviour with `lib/Plot.wiz`
present). This is also the place to decide the layout convention
(`packages/NAME/lib` vs `drafts/split/NAME/lib`).

**Stage 1 — Scry (repo split, no compiler change).**
`git mv lib/Scry scry/lib`, change `Package.lib "scrylib" "../lib"` to
`Package.lib "scrylib" "lib"` in `scry/grail.wiz`, and add
`Package.lib "scry" "scry/lib"` to the root `grail.wiz` so `examples/*scry*.wiz` and
`bench/` still resolve `Scry.*`. Update `.github/libdiff-corpus.txt`,
`docs/libraries.md`, the API-index inputs, and the name-collision scan (already
includes `scry/src`, needs `scry/lib`). Add the new root to the trust ledger walk
(no rows today — `lib/Scry` is pure Wiz — so the gate would pin that it stays that
way). Verify `grail build` in `scry/` and the `library`/`scry` test groups.
Compiler change: none.

**Stage 2 — the clean userland packages (repo split, then package split).**
In dependency order: Optics, then Plot, then Web, then Feral (+ `FeralCore`), then the
data structures, then concurrency/systems, then proving/algebra. (Plot needs `Rat`
from the proving cone and `Json`/`Text`; while those stay in-tree it is fine, but
when the math package moves, Plot becomes a package that depends on it — the order
above avoids a cycle.) For each, add a `grail.wiz` with a `lib` target and the
package's tests. Compiler/CI change per package: add the root to the release
assembly and the ledger walk; no Lean change. After this stage the installed `lib/`
is a union of roots, which is the natural point to add `share/wiz/stdlib.roots` / a
list-returning `toolchainLib` (EP7) and the multi-root ledger (EP8). Only after
EP1/EP2 does the *same* packages become independently versioned registry packages.

**Stage 3 — HDL (needs a hook or a deliberate exception).**
Option A (smallest): keep `Hdl.Core` in-tree and move only the 30 modules above it;
no Lean change, because `Hdl.Core` is imported by them and the elaborator's
`g.contains` checks fire. Option B (full): move `Hdl.Core` too and add an
`attribute [elab.hdl]` registration for `Hw`, `HwTy` and `ShareLet`, replacing the
literal `g.contains "Hw.eq"`/`classes.any (·.name == "ShareLet")` tests
(`Wiz/Elab/Term.lean:2052,3285`). Do A first; B is a separate design once the
package story is proven.

**Stage 4 — proving/algebra (needs the Sat hook generalised).**
Move `Ring`, `Rat`, `Sat`, `BitBlast`, `BvDecide`, the tactics and `SimpLemmas` as
one package (they are one dependency cone). Generalise `Sat.IsTrue` to an attribute
(or keep `Sat` in-tree); decide whether `BitVec`/`Vec` move with it (they are
`Hdl.Core`'s dependencies, so they move in Stage 3's order, not here).

**Stage 5 — the structural modules (last, and probably never for `Text`/`Vec`).**
Move `Text`/`Json` only after the drift check can be pointed at a root set, because
`scripts/check-prelude-drift.py` requires `List.map`/`String.length` and the
`IO`/`Std`/`Bytes` names to be declared under `lib/`. `Vec` moves only with `BitVec`
and after `Hdl.Core`. `Prelude` never moves.

**Never split (or split only as "same repo, different build target"):**

* `Prelude` — embedded in the self-hosted frontend (`selfhost/Frontend.wiz`), the
  `builtin` registrations, the macro/class surface the elaborator names.
* `IO`, `Std` — the FFI marshalling vocabulary (`UInt64`, `Float64`, `Bytes`,
  `Array`, `Str`, `StrMap`), and the selfhost canonicalises their names.
* `Word`, `Int`, `Logic` — the SMT translation recognises them by module name; the
  names themselves also appear in elaborator error messages and `calc`.
* `Grail` (`lib/Grail.wiz`) — until `grail` ships its own module root; moving it
  is a toolchain change, not a library change.
* the self-hosted sources (`selfhost/*.wiz`) — outside `lib/`, and a separate
  trust/CI story (`docs/trust-ledger.md`, "Scope").

## Appendix: every module and its direct imports

`imports` excludes doc-comment examples and self-imports (see "the loader's
superset" in §1).

| module | lines | imports |
|---|---:|---|
| `Args` | 254 | `Text` |
| `BitBlast` | 797 | `Ring`, `Sat`, `Word` |
| `BitVec` | 163 | `Prelude`, `Vec`, `Word` |
| `BitVecAdd` | 368 | `BitVec`, `BitVecShift` |
| `BitVecShift` | 573 | `BitBlast`, `BitVec` |
| `BvDecide` | 306 | `BitBlast`, `SatTactic` |
| `Conc` | 751 | `Data.ListLemmas`, `Eff`, `Text` |
| `Data.ListLemmas` | 539 | `Logic`, `Nat`, `Text` |
| `Data.Order` | 31 | `Logic` |
| `Data.PMap` | 298 | `Nat`, `Word` |
| `Data.Result` | 117 | `Prelude` |
| `Data.WordBytes` | 29 | `IO`, `Word` |
| `Deriving` | 439 | `Prelude`, `Text` |
| `Eff` | 336 | `IO` |
| `EffHeap` | 149 | `Eff`, `HoareTactics` |
| `Encoding` | 206 | `Data.WordBytes`, `Text`, `Word` |
| `Feral` | 3212 | `OpticDerive`, `Text` |
| `FingerTree` | 710 | `Data.ListLemmas` |
| `Functor` | 102 | `Prelude`, `Text` |
| `Grail` | 337 | `Prelude` |
| `HProp` | 409 | `Logic` |
| `Handle` | 140 | `Sys` |
| `Hdl.Apb` | 183 | `Hdl.Bus` |
| `Hdl.Arty` | 82 | `Hdl.Xdc` |
| `Hdl.Axi4` | 514 | `Hdl.Bus` |
| `Hdl.Axi4Law` | 208 | `Hdl.Axi4`, `Hdl.BusLaw` |
| `Hdl.AxiLite` | 121 | `Hdl.Bus` |
| `Hdl.AxiStream` | 415 | `Hdl.Core` |
| `Hdl.AxiStreamLaw` | 154 | `Hdl.AxiStream` |
| `Hdl.Bits` | 199 | `Hdl.Core` |
| `Hdl.Bus` | 550 | `Hdl.Core`, `Vec` |
| `Hdl.BusLaw` | 520 | `Hdl.Bits`, `Hdl.Bus` |
| `Hdl.Cdc` | 54 | `Hdl.Core`, `Hdl.Prim` |
| `Hdl.Core` | 4219 | `BitVec`, `Deriving`, `Logic`, `Trace` |
| `Hdl.Crc` | 131 | `Hdl.Core` |
| `Hdl.Ddr` | 135 | `Hdl.Core` |
| `Hdl.Display` | 579 | `Hdl.Core` |
| `Hdl.Mem` | 402 | `Hdl.Core` |
| `Hdl.Netlist` | 224 | `Hdl.Core` |
| `Hdl.Optic` | 74 | `Hdl.Core`, `OpticDerive` |
| `Hdl.Pipe` | 377 | `Hdl.Core` |
| `Hdl.Prim` | 276 | `Hdl.Core` |
| `Hdl.ProtocolLaw` | 341 | `Hdl.Apb`, `Hdl.AxiLite`, `Hdl.BusLaw`, `Hdl.Wishbone` |
| `Hdl.Signal` | 328 | `Hdl.Core`, `Hdl.Temporal`, `Trace` |
| `Hdl.Sim` | 386 | `Hdl.Core`, `Std` |
| `Hdl.Spi` | 540 | `Hdl.Core` |
| `Hdl.SpiLaw` | 212 | `Hdl.Spi` |
| `Hdl.Temporal` | 342 | `Hdl.Core`, `Hdl.Netlist`, `Trace` |
| `Hdl.Uart` | 293 | `Hdl.Core` |
| `Hdl.Verified` | 260 | `Hdl.Core`, `Text` |
| `Hdl.Wishbone` | 139 | `Hdl.Bus` |
| `Hdl.Xdc` | 127 | `Hdl.Core` |
| `Hdl.Xilinx7` | 182 | `Hdl.Prim` |
| `HeapBorrow` | 113 | `HoareTactics`, `Optic` |
| `Hoare` | 536 | `HProp`, `Nat`, `Text` |
| `HoareExamples` | 220 | `HoareTactics` |
| `HoareTactics` | 1276 | `Hoare` |
| `IO` | 443 | `Prelude` |
| `Infoview` | 766 | `Json`, `Tagged` |
| `Int` | 223 | `Prelude` |
| `IntOrder` | 272 | `IntRing` |
| `IntRing` | 547 | `Int`, `Ring` |
| `Intern` | 85 | `Logic`, `Text`, `Word` |
| `Json` | 540 | `Prelude`, `Text` |
| `Logic` | 518 | `Prelude` |
| `MVar` | 96 | `IO` |
| `Nat` | 369 | `Data.Order`, `Logic` |
| `Optic` | 400 | `Data.Result`, `Logic` |
| `OpticDerive` | 100 | `Deriving`, `Optic` |
| `Plot` | 1017 | `Json`, `Rat`, `Text` |
| `Prelude` | 1578 | — |
| `Rat` | 531 | `IntOrder` |
| `Ref` | 86 | `IO` |
| `Region` | 403 | `Optic` |
| `Ring` | 400 | `Nat` |
| `RingTactic` | 251 | `Rat` |
| `Sat` | 738 | `Logic` |
| `SatTactic` | 531 | `Sat` |
| `Scope` | 141 | `IO`, `MVar`, `Region`, `Session` |
| `Scry.Ai` | 22 | `Scry.AiCfg`, `Scry.AiDomain`, `Scry.AiFixpoint` |
| `Scry.AiCfg` | 278 | `Deriving`, `Logic`, `Prelude`, `Scry.AiDomain`, `Text` |
| `Scry.AiDomain` | 508 | `Deriving`, `Logic`, `Prelude`, `Text` |
| `Scry.AiExamples` | 92 | `Prelude`, `Scry.Ai`, `Scry.AiFixpoint`, `Text` |
| `Scry.AiFixpoint` | 267 | `Deriving`, `Logic`, `Prelude`, `Scry.AiCfg`, `Scry.AiDomain`, `Text` |
| `Scry.Analysis` | 656 | `Scry.Wil`, `Text`, `Word`, `WordMap` |
| `Scry.Bounds` | 516 | `Scry.Engine`, `Scry.Models`, `Scry.PointsTo`, `Scry.RuleTaint`, `Scry.Rules`, `Text` |
| `Scry.Cert` | 1790 | `Nat`, `Prelude`, `Scry.Datalog`, `Scry.Eval`, `Scry.Store`, `Text`, `Word` |
| `Scry.Certify` | 94 | `Scry.Cert`, `Scry.Interproc`, `Scry.RuleTaint`, `Scry.Rules`, `Text` |
| `Scry.ConcurrencyExamples` | 158 | `Scry.Wil`, `Scry.WilExamples` |
| `Scry.Datalog` | 305 | `Prelude`, `Scry.Store`, `Text`, `Word` |
| `Scry.Diff` | 390 | `Text` |
| `Scry.Egraph` | 622 | `Prelude`, `Scry.Store`, `Text`, `Word`, `WordArray` |
| `Scry.EgraphExtract` | 475 | `Prelude`, `Scry.Egraph`, `Scry.EgraphWil`, `Scry.Wil` |
| `Scry.EgraphNative` | 1008 | `Prelude`, `Scry.AiDomain`, `Scry.Store`, `Text`, `Word`, `WordArray`, `WordMap` |
| `Scry.EgraphTaint` | 81 | `Scry.EgraphExtract`, `Scry.Taint` |
| `Scry.EgraphWil` | 495 | `Prelude`, `Scry.Egraph`, `Scry.Wil` |
| `Scry.Engine` | 312 | `Logic`, `Prelude`, `Scry.Analysis`, `Text`, `Word` |
| `Scry.EqPlan` | 440 | `Prelude`, `Scry.Datalog`, `Scry.EgraphNative`, `Scry.Eval`, `Scry.Store`, `Text`, `Word` |
| `Scry.Eval` | 609 | `Prelude`, `Scry.Datalog`, `Scry.Store`, `Text`, `Word`, `WordMap` |
| `Scry.Interproc` | 804 | `Scry.Analysis`, `Scry.Bounds`, `Scry.Lifetime`, `Scry.Models`, `Scry.Nullness`, `Scry.PointsTo`, `Scry.RuleTaint`, `Scry.Rules`, `Text`, `WordMap` |
| `Scry.Lifetime` | 626 | `Scry.Analysis`, `Scry.Engine`, `Scry.Models`, `Scry.PointsTo`, `Scry.Rules` |
| `Scry.Models` | 1245 | `Scry.Rules`, `Text` |
| `Scry.NullExamples` | 106 | `Scry.Wil` |
| `Scry.Nullness` | 530 | `Prelude`, `Scry.AiCfg`, `Scry.AiDomain`, `Scry.AiFixpoint`, `Scry.Analysis`, `Scry.RuleTaint`, `Scry.Wil`, `Text` |
| `Scry.Optics` | 489 | `Functor`, `Logic`, `Scry.Analysis`, `Scry.PointsTo`, `Scry.Wil`, `Text`, `WordMap` |
| `Scry.PointsTo` | 827 | `Scry.Analysis`, `Scry.Wil`, `Text`, `Word`, `WordMap` |
| `Scry.Prover` | 672 | `Prelude`, `Scry.Datalog`, `Scry.Eval`, `Scry.RuleTaint`, `Scry.Store`, `Text`, `Word` |
| `Scry.ProverExamples` | 170 | `Scry.Prover`, `Scry.RuleTaint` |
| `Scry.Race` | 203 | `Scry.Analysis`, `Scry.Wil`, `Text` |
| `Scry.Report` | 602 | `Text` |
| `Scry.RuleExamples` | 337 | `Scry.Interproc`, `Scry.RuleTaint`, `Scry.Rules` |
| `Scry.RuleTaint` | 1054 | `Scry.Analysis`, `Scry.Eval`, `Scry.Models`, `Scry.PointsTo`, `Scry.Rules`, `Text`, `Word`, `WordMap` |
| `Scry.Rules` | 466 | `Text` |
| `Scry.Sarif` | 380 | `Json`, `Scry.Diff`, `Scry.Interproc`, `Scry.Rules`, `Text` |
| `Scry.Store` | 466 | `Prelude`, `Text`, `Word`, `WordArray`, `WordMap` |
| `Scry.Taint` | 323 | `Scry.Analysis`, `Scry.Eval`, `Text`, `Word` |
| `Scry.TaintExamples` | 318 | `Scry.Taint` |
| `Scry.UafExamples` | 148 | `Scry.Interproc`, `Scry.Lifetime`, `Scry.Rules` |
| `Scry.Wil` | 1310 | `Functor`, `Text` |
| `Scry.WilExamples` | 220 | `Scry.Wil` |
| `Scry.Workflow` | 779 | `Json`, `Scry.Rules`, `Scry.Sarif`, `Text` |
| `Serial` | 236 | `Sys` |
| `Session` | 196 | `IO`, `MVar` |
| `Sha` | 202 | `Data.WordBytes`, `Encoding`, `Text`, `Word` |
| `SimpLemmas` | 85 | `Data.ListLemmas`, `Functor`, `Int`, `Nat`, `Text` |
| `Std` | 106 | `IO` |
| `Sys` | 902 | `IO` |
| `Tagged` | 429 | `Json` |
| `Task` | 123 | `Logic`, `Text` |
| `Text` | 275 | `Prelude` |
| `Trace` | 230 | `Logic` |
| `Vec` | 337 | `Nat` |
| `Web.Editor` | 82 | `Web.Loom` |
| `Web.Loom` | 696 | `Json`, `Optic`, `Tagged`, `Text` |
| `Web.Playground` | 335 | `IO`, `Text`, `Web.Loom` |
| `Web.Widget` | 304 | `Json`, `Text`, `Web.Loom` |
| `Word` | 590 | `Prelude` |
| `WordArray` | 276 | `Logic`, `Text`, `Word` |
| `WordMap` | 147 | `Logic`, `Text`, `Word` |
