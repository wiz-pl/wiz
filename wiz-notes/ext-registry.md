# One entry model, fail closed

**Status.** Implementation lane `ext-registry`, 2026-11-23, branch `agent/ext-registry`
based on `integration/train12` `6e5924cd8`. This is item 1 of
`wiz-notes/extensibility.md` §4 and implements the model in `wiz-notes/registry-abi.md`
with that note's names (`Entry`, `Capability`, `ArtifactKind`, `Diagnostic`); the
prototype note had called them `Entry`/`Cap`/`Refusal`.

## 1. What is data now

`Wiz/Ext/Basic.lean` is the record: `Kind`, `Capability`, `ArtifactKind`, `Payload`,
`Entry` and `Diagnostic`. `Wiz/Ext/Resolve.lean` is the one entry table and the one
resolver (plus the backend-only artifact metadata side table the note permits):

```
resolve(table, kind, name, needs, enabledSets, abi)
  1. find name or alias; otherwise <kind>-unknown
  2. the provider set must be enabled (core entries have set ""); otherwise <kind>-not-enabled
  3. the entry's abi must be the consumer's; otherwise unsupported-<kind>
  4. needs ⊆ caps; otherwise <kind>-capability
  5. a payload this toolchain cannot serve; entry-unsupported
  6. the entry
```

* **`--target` is five rows, six spellings.** `backendEntries` declares `c`, `llvm`,
  `wasm`, `bpf`, `js`; `bpf` has the alias `ebpf`. `--target` resolves through
  `resolveBackend`/`resolveBackendFor`, and `Main.lean` no longer has a name list
  (`targets` is deleted) or a `target == "…"` chain. `=backend` is unaffected because its
  cases call `Build.build` directly; the six CLI spellings are unchanged (including
  `ebpf`).
* **Capabilities are the shape rules.** `--lib`/`--no-main` need `library`, `--split`
  needs `split`, `--attest` needs `attest`, `run` needs `run`, `repl` needs `repl`, and
  every build needs `emit`. A shape the entry does not declare is refused by the
  resolver before the driver, so `--target js --lib` and `--target bpf --attest` are
  `target-capability` (exit 2) and no artifact is written. This replaces the per-target
  `if target == … && attest.isSome` arms with data.
* **Artifacts are data, in a side table.** `backendArtifacts` (keyed by `target/NAME`)
  declares the kinds each backend writes (`c`/`llvm`: executable/object/header;
  `wasm`/`js`: module; `bpf`: source/header/probe descriptor). It is a description, not
  an enforcement: the payload still writes them. The generic `Entry` does not grow a
  field every other kind would ignore.
* **Duplicates are refused where the table is built.** `Table.register`/`ofEntries`
  refuse a duplicate `(kind, name)` or alias and name both providers. Core rows are
  registered through the same function, so a malformed core row refuses every resolution
  (no partial table).
* **The cache key includes the selection.** `Toolchain.backend` is the canonical
  resolved entry name, not the argv spelling (`ebpf` and `bpf` are one), and it enters
  `Toolchain.targetTag` (and `id`), which is what `Cache.Key.target`/`moduleKeysAll`
  already carry. `Main.elaborateHitsCore` passes `toolchain := tc.id` into
  `Cache.elaborateCached`, and `Toolchain.id` includes `backend`; the fast (`.wizc`)
  lookup is therefore separated by target as well as the strong key. The pure
  `Cache.moduleKeysAll` still puts the target only in its strong key when the caller
  passes `toolchain := 0` (the existing `=wasm` case pins that the *module* key is one
  module); the driver's fast namespace is what separates the store files. `=ext` pins a
  cold/warm pair and asserts the cross-target miss. (A package `ext-set` would add its
  list to the same tag; no manifest reader populates one yet, so no dead field is
  introduced.)
* **D1 in the selfhost is a registration decision.** `Globals.ders` stores
  `DeriverRef := builtin kind | user name`, not a `String`. `attribute [deriver C] f`
  records `.builtin k` only when no declaration has that name; a declaration called
  `deriveBEq` is `.user "deriveBEq"`. `deriving C` dispatches on the value: a `.user`
  entry is refused with `entry-unsupported` (there is no elaboration-time evaluator),
  never run through the built-in body of the same spelling.

## 2. What is still a Lean branch

* `Main.buildCmd`/`runCmd` and the REPL match the payload's `CoreDriver` (`c`, `llvm`,
  `wasm`, `bpf`, `js`) exhaustively. That is host code by definition: a core backend is
  Lean. There is **no `else` that means C**; an entry whose payload is not a core driver
  is refused with `entry-unsupported`/`unsupported-target` before the match. Adding an
  in-tree driver is a compile error at this match, not a silent fallback.
* `Wiz/Compiler/Build.lean` still takes `llvm`/`wasm` booleans and re-checks the wasm
  shape rules (`--lib`, `--no-main`, `--split`) as defence in depth. The capability
  resolver refuses those before `Build.build`; the duplicate checks are intentionally
  kept.
* `CoreDriver` is a closed enum in `Wiz/Ext/Basic.lean`, not a manifest key. A package
  backend will need a `.process`/`.data` payload and a driver for it (item 5's
  `wiz-ir/1` is the missing program ABI).
* The selfhost target table (`selfhost/Cli.wiz`'s `targetModes`/`targetOk`) is still a
  hand-copied list of the same six names. It is not generated from the Lean table; a
  pinned cross-check would be the next step (registry-abi §6 step 3).
* Main's help text still carries a literal `c|llvm|wasm|bpf|js|ebpf`; it is prose, not a
  resolver. Generating it from `backendSpellings` is a cosmetic follow-up.

## 3. Refusal codes

All are `Wiz.Ext.Diagnostic.code`; the message is data too. The CLI prints
`code: message` for the new refusals; the legacy `--target NAME` unknown/missing
sentences stay message-only because `=selfhost-cli-diff` compares them with the
selfhost's wording.

| code | when | exit |
|---|---|---|
| `unknown-target` | no row or alias for `--target NAME`; the message lists the spellings | 1 |
| `target-not-enabled` | a package row is present but its `set` is not in `enabledSets` | 1 |
| `target-capability` | the invocation needs a capability the row does not declare | 2 |
| `duplicate-target` | two providers for one `(kind, name)` or alias, at `register`/`ofEntries` | 1 |
| `unsupported-target` | the row's `abi` is not `wiz-backend/1` | 1 |
| `entry-unsupported` | the payload is `.unsupported`, or not a core driver this build can run | 1 |
| `invalid-target-name` | empty or path-separated name/alias | registration |
| `invalid-target-abi` | empty `abi` | registration |
| `invalid-target-alias` | a repeated/self alias | registration |
| `invalid-target-override` | `override` on a non-doc-language row | registration |
| `invalid-target-payload` | a package provider attempts a `.core` (host-code) payload | registration |

The same generic pattern is used for another kind (`unknown-deriver`,
`duplicate-tactic`, …); `Kind.key` spells the backend kind `target` so the existing CLI
codes and messages do not move.

## 4. The manifest gap

`grail.wiz` is read by `grail`, not by `wiz`: `Main.lean`'s `--target` parser
(`Main.lean:1410`) runs before any module (and before any manifest), and `Main.lean`
imports no `Grail.Config`. The existing container is `Package.command`/`Target.command`
(`lib/Grail.wiz:63-77`, `Package.command` at `:194`; decoded at `Grail/Config.lean:182`,
executed by `Grail/Graph.lean:214`). It is a **build-graph node**, not a backend entry:
it has no `schema`, `abi`, `caps`, payload, or `--target` name, and `grail build` selects
it by its own target name (its `.exe` targets link C directly,
`Grail/Graph.lean:224`, with no target parameter). `Command.output`/`Command.makesDir`
can declare files, so the container can carry *artifacts* for a build step; what it
cannot carry is a **compiler target**: there is no `--target` name, schema, ABI,
capability or payload, and `grail` never passes a target to `wiz`.

So a manifest-declared `demo` target cannot be made to resolve through
`wiz build --target demo` without a new mechanism: either `wiz` learns to read a
manifest (it deliberately does not) or `grail` gains `Package.backend`/`ext-set`, resolves
the row and passes the selection to the compiler (registry-abi §6 step 8). Adding a
second mechanism in this lane would have been the thing to avoid. The resolver is ready
for the row: `=ext` builds a table with a package `demo` row and pins
`target-not-enabled` without its set, and the row resolves with the set enabled; no
manifest reader exists to produce that row yet. This is the precise gap.

## 5. Tests

* `=ext` (13 cases): six spellings/five rows and their caps/artifacts; unknown; duplicate
  and alias collision; package `target-not-enabled`; capability refusals; ABI and
  unsupported payload; malformed rows; the cache-key cold/warm/cross-target probe; the
  three CLI refusals and the `ebpf` alias.
* `=selfhost` A11: the existing deriving cases plus the D1 case (a declaration called
  `deriveBEq` must be refused with `entry-unsupported`, and no `BEq Hijack` instance may
  be produced).
* `=backend`, `=cli` (if present) are unchanged; `=js`, `=bpf`, `=wasm`, `=llvm` cover the
  target groups' own paths and were run as the wider check.

## 6. Run (2026-11-23)

* `heavy --rsync -- lake build wiz tests`: 652 jobs, exit 0.
* `heavy --sshfs -- lake test -- '=ext' '=backend'
  '=selfhost#175,176,183,184,185,186,187' '=selfhost-cli-diff#9,10,12,13'
  '=wasm#35' '=attest#0'`: **47 passed, 0 failed, 2 skipped**. The two skips are the
  existing, explicitly reasoned `=selfhost-cli-diff` cases 12/13 (host selects LLVM/Wasm,
  the self-hosted backend does not exercise them); they are not new. The D1 case (185)
  passed; A11 cases 175–187 passed.
* `python3 scripts/ci.py check-shards`: ok — 160 groups (1 excluded: stc-bridge), 2813
  cases in exactly one of 20 shards; 14 allow-list entries match.
* `python3 scripts/repo-subsets.py --write` + `--check`: current (6 subsets, 1729 files).
* `python3 scripts/check-docs-style.py`: clean (89 files).
* `python3 scripts/check-names.py` and `check-companion-lists.py`: **pre-existing red**
  on 33 unbaselined declarations in `lib/Web/Loom.wiz` and `web/` (not touched here);
  `check-companion-lists` reports only that legacy-names drift. `=ext` adds no
  legacy-name row (the new Lean modules are not Wiz declarations) and the selfhost
  `DeriverRef` is in `namespace __root__`.
* `=cli` is not a test group on this base: `tests '=cli'` exits 2 with "no test group
  matches =cli". The CLI target coverage is `=selfhost-cli-diff#9,10,12,13` above.
* Not run: the full `=selfhost` group (only A11), the full `=js`/`=bpf`/`=wasm` groups
  (only `=wasm#35`), the full test suite, `grail test`, Nix/CI, and the selfhost target
  table cross-check (registry-abi step 3).
