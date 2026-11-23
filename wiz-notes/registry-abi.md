# One entry registry, fail closed

**Status.** Design lane `registry-abi`, 2026-11-23. Tree `/workspace/wt/registry-abi` at
`3fa0eec95` (`integration/train12`). This is item ① of `wiz-notes/extensibility.md` §4:
one declaration of a Wiz-implemented entry, a stable key, explicit resolution / conflict /
refusal semantics, and `--target` as the first user. The note also fixes the minimal
term/decl ABI a Wiz-side entry sees.

The prototype is `Wiz/Ext/Basic.lean` plus `Tests/Groups/Ext.lean`, with `Main.lean`'s
`targets`/`takeTarget` reading the table (≈ 370 lines including comments and tests, not
the ~100 the brief hoped for; §8 says exactly what is and is not converted). Every
`file:line` below was read in the tree above. §9 is the honesty ledger: what ran, what
did not, and what I could not verify.

---

## 0. Verdict

1. **One record, one key, one resolver; several tables by lifetime.** The registry is not
   one mutable list. `Entry` is `(kind, name, provider, set, schema, abi, caps, payload)`;
   the key is `(kind, name)`; `resolve` is total and returns `Entry` or `Refusal`. A
   driver table (targets, doc languages) and an elaboration table (derivers, tactics,
   macros, lint rules) are two instances of the same record and resolver. This is the
   one point where I refine `targets-ext.md` §0: a target is not an *elaboration* entry,
   but it is an entry of the same model, and one resolver is what makes the refusals
   uniform. The lifetime difference is a property of the table, not of the record.

2. **`--target` is the first user.** The core target table is `[c, llvm, wasm, bpf, js]`
   (`Main.lean:924` today), and `takeTarget` (`:945-966`) is the only resolver the CLI
   has. Converting it first proves the model against an existing, closed list before any
   Wiz payload is involved.

3. **The Wiz-side ABI is a narrow, versioned surface, not the kernel.** A Wiz entry sees
   `Syntax`, `IndView`, `Expr`, the `Tac`/`MacroM` request chain and its own `String`
   inputs. It does **not** see `Wiz.Core.Term`, `Globals`, the environment, arbitrary
   declaration bodies, or the type checker's metavariables. Quotation is ordinary Wiz
   code; hygiene is the `✝` marker discipline; reflection is lossy by design; errors are
   one primary span and one message (plus traces), with the host supplying the code.

4. **A backend is not a Wiz function in v1, and a doc language is not code.** A core
   backend is host code in the table; a package backend is a document/process adapter.
   A Wiz-authored backend needs `wiz-ir/1` (item ⑤), not FeEval. A doc language is the
   existing `wiz.doc.languages/1` data and a host builder; the model makes it an entry,
   not a renderer. Saying "Wiz-implemented entry" for these two would be a promise the
   tree cannot keep.

5. **The FeEval decoupling in `extensibility.md` §4 is correct.** Host-side resolution,
   the target conversion, lint sets and the already-host-run derivers/tactics/macros do
   not need FeEval (SH-2.1). Only a Wiz payload under the **selfhost** needs it, and the
   honest selfhost half is a refusal by name with a reason. §5 verifies the claim and
   states the two caveats (IR for backends, `SH-2.0a` for a testable FeEval).

---

## 1. What the tree has, verified at `3fa0eec95`

### 1.1 `--target` is five string comparisons

| site | what it is |
|---|---|
| `Main.lean:924` | `def targets : List String := ["c", "llvm", "wasm", "bpf", "js"]` |
| `Main.lean:945-966` | `takeTarget`: `targets.contains`, then `--llvm`/`--wasm` aliases and conflict checks |
| `Main.lean:968-1004` | `buildCmd`: `if target == "bpf"`, `else if target == "js"`, `else if target == "wasm" && attest.isSome`, then **the C/LLVM fall-through** `Build.build … (target == "llvm") … (target == "wasm")` |
| `Main.lean:1006-1029` | `runCmd`: `bpf` refused in prose, `wasm`/`js` paths, else `Build.runGlobal` (C or LLVM) |
| `Main.lean:1343` | `takeTarget args` runs before any command dispatch; `Main.lean:426` passes `tc.targetTag` into the cache |
| `Main.lean:1366-1379` | REPL: `wasm`, `js`, `bpf` refused by name, else `replCmd` with `llvm` bool |
| `Wiz/Compiler/Build.lean:267-289` | `build` takes `llvm`/`wasm` booleans and re-refuses `wasm` + `--lib`/`--no-main`/`--split`; the refusals are positional |
| `Wiz/Compiler/IR.lean:43-47` | `inductive Backend` is `c | llvm | wasm` — no `bpf`, no `js`; a fifth ISA needs a compiler change, not a registry entry |
| `selfhost/Cli.wiz:1181-1186` | `targetModes := ["c","llvm","wasm"]`, `targetOk` (c, llvm), `targetKnown` |
| `selfhost/Cli.wiz:1274-1301` | parse: unknown vs unsupported, with messages |

The failure mode is the point: **every site is a `String` comparison**, and the final
`buildCmd`/`runCmd`/REPL branches have an `else` that means C. A sixth name added to
`targets` alone compiles, builds C, runs C and opens the C REPL without an error. The
registry exists to make that a type-level or resolution-level failure instead.

The five names are also not the only list: help text (`Main.lean:22-27,43`), the
selfhost's three, and the docs each carry a copy. `Main.lean:924` was changed in the
prototype to `Wiz.Ext.backendNames`; the help text and selfhost remain.

### 1.2 Four registries, no shared vocabulary

* **Derivers.** `CommandState.derivers : List (Name × Name)` (`Wiz/Elab/Command.lean:145`),
  filled by `attribute [deriver C] f` after unifying `f`'s type with `Deriver`
  (`:3707-3717`), read by `derive` (`:2193-2210`) and run through `Elab.runDeriver`
  (`Wiz/Elab/ProcMacro.lean:165-172`). Lookup is `List.lookup` on a latest-first list, so
  a second registration silently wins.
* **Tactics.** `CommandState.tactics` (`:138`), filled by `attribute [tactic k] f` after
  unifying with `Tactic` (`:3509-3517`), read by `Term.lean:4110-4117`, run by
  `runTac` (`:4120-4598`). Same latest-first list, no duplicate check.
* **Macros.** `CommandState.procMacros` / `cmdMacros` (`:136,145`), filled by
  `attribute [macro k] f` (`:3437-3466`), run by `runProcMacro`/`runCommandMacro`
  (`Wiz/Elab/ProcMacro.lean:152-163`), expanded at `Term.lean:276-287` and
  `Command.lean:3930-4005`.
* **Lints.** `Wiz/Lint.lean:388-390` is a core `Array (Rule R)`; package sets are
  `lint-set`/`lint` declarations checked by `checkSet` (`:598-648`) and
  `loadPackageSets` (`:650-665`), with `Capability` in `Wiz/Lint/Basic.lean:49-102`. This
  is the closest thing to an entry model: metadata, declared capabilities, stable codes,
  duplicate-code refusal, trust/`partial` checks.
* **Doc languages.** `wiz.doc.languages/1` JSON (`Wiz/Doc/Registry.lean:8-20`), merged
  with explicit `override` and a reserved `wiz` name (`:127-146`); `Spec`/`Lang` are
  data (`Wiz/Doc/Highlight.lean:90-118`).

There is no `Wiz/Ext/` on the tree (`ls` fails). There is no shared `Entry`, `Capability`,
`Refusal` or `resolve`; the four lists have four different duplicate/unknown behaviours.
`targets-ext.md:20-24` and `extensibility.md:224-229` both say the lint registry is the
shape to copy; this note copies its *vocabulary* and generalises it.

### 1.3 The cache does not see `--target`

`Toolchain.targetTag (_t : Toolchain)` ignores its argument and hashes only the platform
triple and pointer width (`Wiz/Toolchain.lean:67-72`). `Toolchain.tag` (`:75-80`) hashes
that plus compilers and flags. `Cache.Key.target` is a field (`Wiz/Cache.lean:598`) and
`Cache.moduleKeysAll` puts `s!"target-tag:{targetTag}"` into the strong key
(`:693`), but `Main.lean:426` passes the constant `tc.targetTag`, so every `--target`
shares the slot. Elaboration is target-independent, which is why the module key is still
correct today; the slot must become the entry digest **before** a cached region or a
package target can be trusted (`targets-ext.md` §3). The prototype does not change it;
Step 2 does.

### 1.4 The selfhost cannot run Wiz entries

`selfhost/Frontend.wiz:11053-11063` is the whole `runMacroTac`: `result`, `fail`,
`trace`, `getInductive`, `done`; anything else is refused with "this front-end has no
elaboration-time evaluator". `deriveClassOn` (`:11435-11447`) refuses a user deriver by
name and dispatches the five built-in names through hard-coded bodies. `Globals.view`
(`:11029-11045`) reflects an inductive but gives indices as `.missing` types and no level
parameters; `Globals.deriver`/`addDeriver` (`:815-824`) store only the registered string.

The selfhost's `deriverCmd` (`:10834-10847`) records a **declared** function even though
it cannot run it, and `deriveClassOn` dispatches on the registered **name**
(`deriverKind`, `:10806-10819`). A user declaration named `deriveBEq` therefore gets the
built-in `BEq` body in the selfhost and its own body in the host — the D1 bug from
`extensibility.md` §3.3. This is a registration defect, fixable without FeEval.

---

## 2. The model

### 2.1 One record

The prototype's record is the design; the real module can add fields without changing the
key or the resolver.

```lean
inductive Kind | deriver | tactic | macro | lintSet | lintRule | backend | docLanguage | termElab
inductive Cap  -- emit check link run attest library split repl
               -- decl spans imports globals messages facts
inductive Payload
  | core (key : String)        -- host code, core only
  | wizRule (decl : String)    -- a Wiz declaration run by the interpreter
  | data                        -- a validated document; `Entry.schema` names the format
  | process (command : String) -- a child process with a declared contract
  | unsupported (reason : String) -- this toolchain/platform cannot serve it

structure Entry where
  kind : Kind
  name : String
  aliases : List String := []        -- names share one namespace per kind
  provider : String := "wiz-lang"  -- the core table, or the package
  set : String := ""               -- the enablement set; empty for core/already enabled
  schema : String := ""            -- the document the payload consumes
  abi : String := ""               -- the interface the payload was written against
  caps : List Cap := []
  payload : Payload := .core ""
  override : Bool := false         -- doc languages only; `wiz` is reserved
```

**The key is `(kind, name)`**, spelled `kind/name` in messages and baselines. Per kind:

| kind | name shape | stable key examples | `payload` today | executed by |
|---|---|---|---|---|
| deriver | class name, absolute; no `Derive.` stripping | `deriver/BEq` | `.wizRule "deriveBEq"` | host `runDeriver`; selfhost refuses |
| tactic | syntax kind | `tactic/tactic.exact` | `.wizRule "Tactic.exact"` | host `runTac`; selfhost refuses |
| macro | syntax kind | `macro/term.listLit` | `.wizRule "ListLit.expand"` | host `runProcMacro`; selfhost refuses |
| lint set | set name | `lint-set/scry` | `.data` + `schema "wiz-lint/1"` | host `callRunner`; selfhost no |
| lint rule | `W` code | `lint-rule/W501` | `.wizRule` + metadata | host `callRunner`; selfhost no |
| backend | lowercase target name | `target/bpf`, `target/c` | `.core` or `.process` | driver; selfhost compiled-in or `unsupported` |
| doc language | `[A-Za-z][A-Za-z0-9_+-]*`, case-insensitive match | `doc-language/python` | `.data` + `schema "wiz.doc.languages/1"` | host `wiz doc`; no package renderer |
| term elab (future) | syntax kind | `term-elab/term.τ` | `.wizRule` | host (item ②); selfhost refuses |

The payload is a **reference**, never a function value. That is what lets the same record
describe a core target, a Wiz rule and a manifest entry; it is also why resolution can be
pure and why the selfhost can carry the same table with `.unsupported reason`.

The prototype's `Cap` carries the target and lint groups it exercises. The Wiz kinds add
`Syntax`/`inductive`/`type` for a deriver or macro, `goals`/`expr` for a tactic, and
`term` for the future term elaborator; the enum is closed per kind, and `register`
refuses a capability outside its kind's set (a Step 2/5 check, not in the prototype —
§9).

**Names versus the brief's sketch.** `Capability` is `Cap`; `Diagnostic` is `Refusal` (a
stable code and a message, for argv/manifest paths) plus the existing `Msg` where a span
exists; `ArtifactKind` is backend-specific (`targets-ext.md` §2: `.src`, `.object`,
`.header`, `.module`) and deliberately not a field of the generic record; `Resolve` is
`Table.resolve` (a separate `Wiz/Ext/Resolve.lean` is a fine split when it grows). The
prototype keeps the model and resolver in one ~260-line module so the first user has one
import.

The same declaration in its three current/proposed surfaces:

```text
-- core: one row of the pure list, resolved before any module is read
{ kind := .backend, name := "bpf", schema := "bpf-core/1", abi := "wiz-backend/1",
  caps := [.emit, .check], payload := .core "Wiz.Compiler.Bpf" }

-- Wiz rule: the attribute is sugar for the same record (`payload := .wizRule f`)
attribute [deriver BEq] deriveBEq           -- ~ deriver/BEq, provider this module
attribute [tactic tactic.exact] Tactic.exact -- ~ tactic/tactic.exact

-- package (proposed; not in the tree): the manifest names the same fields
Package.backend "demo" (Backend.process "demo-backend" "c-text/1" [.emit, .run])
```

The first is the prototype; the second is the existing syntax, kept as the ergonomic
front-end; the third is Step 8. None of them is a per-kind branch in `Main.lean`. A new
`ext` command is not needed for this item: the four attribute/lint forms are sugar over
`register`, so the *declaration* is one record without a new grammar. Adding `ext` later
would be a parser convenience, not a second registry.

### 2.2 One resolver, several tables

```
resolve(table, kind, name, needs):
  1. canonicalize name for the kind (case-fold only doc languages; validate the shape)
  2. core := coreTable.find(kind, name); pkg := enabledPackageTables.find(kind, name)
  3. if core is some and pkg is some:
       if pkg.override and kind == docLanguage => pkg       -- the declared exception
       else                                    => duplicate-<kind> (both providers)
     else if core is some => core
     else if pkg is some  => pkg
     else                 => unknown-<kind> (+ choices)
  4. unless entry.set.isEmpty or entry.set is enabled => <kind>-not-enabled
  5. unless entry.abi is readable              => unsupported-<kind>
  6. unless needs ⊆ entry.caps                 => <kind>-capability
  7. unless payload is available here          => entry-unsupported / <kind>-not-installed
  8. return entry
```

Notes on each step:

* **Core names are not shadowable.** A package may not shadow a core name: a package
  entry that also provides one is a `duplicate-<kind>` refusal, except a doc language
  with `override := true` (the existing `wiz.doc.languages/1` rule; `wiz` itself is never
  overridable). An `override` on any other kind is a registration refusal. The exception
  is in the resolver, not a per-kind branch in the driver.
* **Two tables, one record.** The driver table is resolved before any module is read
  (`--target`); the elaboration table is resolved while a module is open. A table has a
  lifetime, not a different entry type. This is the answer to `targets-ext.md` §0.1's
  objection: a target is not `local` and is not dropped by `endModule`, but it is still
  an `Entry` and still resolved by the same function.
* **Enablement is the consumer's.** A package's entry is enabled by `Package.lintSet`,
  `ext-set`, an import (for semantic kinds), or the chosen `--target`; a transitive
  dependency is not auto-enabled, and a package cannot enable another package's entry.
* **No default.** `resolve` returns `Except Refusal Entry`. `buildCmd`, `runCmd` and the
  REPL take the resolved entry (or its payload tag), never a bare `String` with an
  `else` branch. A `String` is only the spelling at the CLI boundary.
* **A list is the prototype's index, not the key.** The table is a `List` so resolution
  order and duplicate detection are obvious; a production table may add a `HashMap`
  index for lint-rule lookup. The key remains `(kind, name)`, and the resolver's result
  must not depend on the index.
* **Nothing runs before 9.** Unknown, duplicate, disabled, wrong ABI, missing capability
  and missing tool are all refusals with no artifact written. That is the fail-closed
  property; it is testable without running a backend.

### 2.3 Refusals are data

The generic pattern is `<kind>-<reason>`; the backend kind uses `target` so existing
messages keep their vocabulary (`targets-ext.md` §2 already chose these codes).

| refusal | when | code | exit |
|---|---|---|---|
| unknown name | no entry in the enabled closure; typo | `unknown-<kind>` | 1 |
| duplicate key | two providers in the enabled closure; both named | `duplicate-<kind>` | 1 (registration error at elaboration if found there) |
| not enabled | provider present, consumer did not enable its set | `<kind>-not-enabled` | 1 |
| unreadable ABI/schema | entry's `abi` major is not what the toolchain reads | `unsupported-<kind>` | 1 |
| missing capability | invocation needs `--lib`/`--split`/`--attest`/`run`/REPL and the entry does not declare it | `<kind>-capability` | 2 |
| missing tool/adapter | a declared binary is absent | `<kind>-not-installed` | 1 |
| wrong platform/selfhost | the entry exists but this toolchain cannot serve it | `entry-unsupported` | 1 |
| payload failed | a Wiz runner threw, a process exited non-zero, a document was rejected | `entry-failed` | 1 |
| budget exhausted | a step/fuel limit | `entry-budget` | 1 |
| invalid declaration | empty name, empty ABI, illegal `override` | `invalid-<kind>-<field>` | registration error |

Two positions matter and must not be conflated (`targets-ext.md` §6): a refusal from a
**manifest** can name the file but not a line:column (the manifest is evaluated to a
`String` and re-parsed as `Sx`, which carries no source info, `Grail/Config.lean:216-226`,
`Wiz/Cache.lean:37-40`); a refusal from **argv** has no span at all and prints stderr +
the code. An elaboration refusal (duplicate deriver/tactic) is an ordinary `Msg` with the
new code in `Wiz/Core/ErrorCode.all`; the `lsp-server` test re-pins the table in
`docs/error-codes.md`.

**Trust is per payload, not per entry.** A Wiz rule is gated by the kernel or the
capability view and must pass the trust/`partial` walk (`Wiz/Lint.lean:587-648`); a
target's runtime helpers are trust-ledger rows, not the entry; a process adapter is
outside the ledger's walk, so its capabilities are **advisory** until there is a sandbox
(`targets-ext.md` §6; `registry-provenance.md` §6.6). The registry is not a sandbox, and
"declared capability" must not be read as "enforced".

### 2.4 Conflicts, per kind

* **Payload/provider rule** — a `.core` payload is legal only for `provider ==
  "wiz-lang"`; a package entry is `.wizRule`, `.data` or `.process` (`.unsupported` is
  allowed anywhere). A package cannot register host code in the compiler process. This
  is the registry-level version of `Module.fromFirstRoot`/`trustedModule`
  (`Wiz/Module.lean:202`, `Wiz/Elab/Command.lean:228,2941`).
* **Duplicate `(kind, name)`** — refused wherever it is detected: at registration for a
  Wiz entry (the attribute command), at table construction for core, at resolution for
  package tables. The message names both providers. No "latest wins" by accident.
* **Lint codes** — `W001–W499` core, `W500–W999` package; a code is unique in the enabled
  closure (`Wiz/Lint.lean:650-665` already does this for sets). A duplicate is the same
  `duplicate-lint-rule` refusal.
* **Doc languages** — case-insensitive names and aliases; a duplicate name in one file is
  an error; an override needs `"override": true`; `wiz` is reserved; an alias that
  belongs to another language is an error (`Wiz/Doc/Registry.lean:127-146`).
* **Tactics/macros/derivers** — the attribute commands register globally; `local` today
  covers `syntax`, `macro_rules`, `[macro]`, `[simp]`, `[hint]`, instances and
  unexpanders (`Wiz/Elab/Command.lean:2390-2413`), not `[tactic]` or `[deriver]`. The
  registry treats a duplicate as a refusal; adding `local` scope for the missing kinds is
  a separate, explicit change in `endModule` (`:1856-1915`), not a silent shadow.
* **Backends** — core names are not shadowable. A package that wants a different `bpf`
  must use a different name; aliases are names too (`target/…`).

### 2.5 Cache and determinism

The target entry digest must enter the strong namespace:

```
entryDigest = sha256("wiz-target-entry-v1", [kind, name, schema, abi, caps, payload])
```

Replace the body of `Toolchain.targetTag` (`Wiz/Toolchain.lean:67-72`) with the digest of
the resolved entry, keeping the field name so `Cache.Key.target`, manifests and region
names inherit it without a format change (`Wiz/Cache.lean:598,693`; `Main.lean:426`).
`targetTag` is pure and currently has no entry argument, so the selected entry has to
reach it: add a `Toolchain.backend : String := "c"` field (set from the resolved entry
right after `takeTarget`, `Main.lean:1343-1347`) and have `targetTag` look up its digest,
or pass the digest explicitly to `elaborateHitsCore`. The field is the smaller change and
keeps the `Toolchain` structure as the one place the cache learns what was selected.
The selfhost injects the same digest as a literal, as it already does for `toolchainId`
(`Wiz/Selfhost.lean:155-181`); it cannot hash its own table cheaply and does not need to.
`isoKey` (`Wiz/Frontend/Frontend.lean:77-100`) gains the digest only when a future entry
declares `affectsElaboration`; no entry does today. A Wiz rule's module source is already
in the module key; the digest is for the *target* selection, not for the rule body.

The **elaboration** table has a second cache constraint. `Cache.Effect`
(`Wiz/Cache.lean:281-299`) carries declarations, messages, builtins, classes, instances,
types, code, infos and docs, but **not** `procMacros`, `tactics`, `cmdMacros` or
`derivers`; `Effect.cacheable` (`:299-305`) excludes every `command.attr*`, so a module
with a registration is not `complete` and its non-cacheable commands are replayed
(`:809-814`). Step 5 must either add a serializable entry list to `Effect` (a `.wizr`
format change, `regionFormat` bump) or keep the four existing lists as the storage and
build the `Entry` view at lookup time. The latter is smaller and does not change the
cache format; it is the recommended first cut.

The entry key is the **interface**, not the implementation: a stable `deriver/BEq` may
name a different declaration after a refactor. A cache keyed on the entry alone would
reuse the old body; the module source hash (and the declaration name in the payload) is
what makes a rename/rebuild a miss. Do not put an entry digest into an elaboration cache
where the payload body matters; the target digest is for target selection, where the
payload is the same host code.

---

## 3. The minimal Wiz-side ABI: `wiz-meta/1`

This is the interface a Wiz-implemented entry sees. It is one version marker over the
existing, already-running meta surface; it does not invent a new evaluator. The ABI has
two profiles: **term/decl** (deriver, tactic, macro, future term elaborator) and
**text** (`wiz-lint/1`). Backend and doc-language entries have no Wiz function in v1
(§4.5–4.6).

### 3.1 Entry points

| kind | Wiz type | input | output | host runner |
|---|---|---|---|---|
| deriver | `Deriver = String → MacroM (List Syntax)` (`lib/Prelude.wiz:901-903`) | type name | commands | `runDeriver` (`Wiz/Elab/ProcMacro.lean:165-172`) |
| macro (term) | `Macro = Syntax → MacroM Syntax` (`:818`) | syntax node | syntax | `runProcMacro` (`:152-155`) |
| command macro | `CommandMacro = Syntax → MacroM (List Syntax)` (`:896-899`) | command | commands | `runCommandMacro` (`:158-163`) |
| tactic | `Tactic = Syntax → TacticM Unit` (`:971`) | tactic syntax | goal effects | `runTac` (`Wiz/Elab/Term.lean:4120`) |
| term elab (future) | `Syntax → TacticM Unit` | term syntax | assigned main goal | item ②; not in this registry yet |
| lint rule | `String → String` over `wiz-lint/1` (`docs/lint-abi.md`) | view text | findings text | `callRunner` (`Wiz/Lint.lean:529-531`) |

`MacroM A = TacticM A = (A → Tac) → Tac` (`lib/Prelude.wiz:646`); the request chain is
the only effect. The entry is a *total function over a stable view*, not a host hook.

**Declaration side.** The entry is a Wiz declaration whose type is unified with the
interface at registration — `Deriver` (`Wiz/Elab/Command.lean:3707-3717`), `Tactic`
(`:3509-3517`), `Macro`/`CommandMacro` (`:3437-3466`), `String → String` for a lint rule
(`Wiz/Lint.lean:598-648`). The registry records the declaration's name, not its body;
the body is compiled and run by the interpreter on first use. There is no
`quoteDecl`/declaration quotation in v1: a declaration is visible only through
`IndView` (inductive shape) and `getType` (one declaration's type as `Syntax`), both of
which are views, not kernel terms.

### 3.2 Quotation

A quotation is ordinary Wiz code in a `def` body, not a separate macro template:

```wiz
def Derive.instBinder (cls : String) (p : ParamView) (rest : Syntax) : Syntax :=
  let x := Syntax.mkIdent (ParamView.name p)
  let t := ParamView.type p
  `(term| {$x : $t} → $rest)
```

`lib/Deriving.wiz:120-142` uses this shape throughout. What the ABI guarantees:

* `$x` is an **antiquotation**: the local `x` is checked against `Syntax` and spliced as
  the value it holds (`Wiz/Elab/Term.lean:3777-3795`, the `antiquotName?` branch).
* A literal identifier in the quote is marked with `✝` (`elabQuote`, `:3784-3792`),
  unless it is dotted or under one of `unscopedParents`
  (`Wiz/Elab/Macro.lean:55-56`: `term.dotIdent`, `term.field`, `level.param`,
  `term.syntheticHole`).
* The quote carries **no source positions**: it builds `SyntaxF.missing/atom/ident/node`
  values only. On the way back, `decodeLocated` gives every generated node the
  invocation's span as *synthetic*, while a value that passed through an antiquotation
  keeps its original ranges (`Wiz/Elab/ProcMacro.lean:39-53,79-104`).
* The host scopes the output once per expansion: `scopeQuoted` appends the expansion's
  scope number to every identifier ending in `✝` (`:106-110`). That is the hygiene
  mechanism; there is no scope object and no alpha-renaming.

Consequence: an entry that wants to introduce a binder should build the identifier with
a `✝` name (the quotation does this for literals; `Syntax.mkIdent "x✝"` is the manual
form) or ask `MacroM.fresh`. A user identifier containing `✝` is not safe; the marker is
a literal separator, and `stripScope` (`Wiz/Core/Pretty.lean:186`) takes everything
before the first `✝`.

### 3.3 Typed reflection

There are two views, and they are not interchangeable.

**Declaration view (`IndView`).** For a deriver or a declaration-shaped entry,
`MacroM.getInductive` returns `Option IndView` (`lib/Prelude.wiz:518-540`):
`name`, `levelParams : List String`, `params`/`indices : List ParamView`, `ctors :
List CtorView`, `isStructure`. `ParamView`/`FieldView` carry a name, a `BinderKind`
(`default | implicit | instImplicit`) and a **type as `Syntax`**; `FieldView` adds
`recursive` and `proof` booleans; `CtorView` adds the constructor's result indices as
`Syntax`. The host builds this from the kernel declaration (`Wiz/Elab/Reflect.lean`),
printing each type with `Term.prettyPrec` and re-parsing it (`termSyntax`, `:67-77`).
The selfhost's `Globals.view` is a second implementation (`selfhost/Frontend.wiz:11029-
11045`) with real drift: indices become `.missing` types, level parameters are empty.

What this view deliberately loses:

* **Quantities** (0/1/ω) are not in `ParamView`/`FieldView`; only the binder kind is.
* A type that does not print back becomes a hole `_` (`Reflect.lean:73-76`); the view is
  a printing, not a kernel term.
* There are no class/instance tables, no definition bodies, no arbitrary declaration
  types (`getType` returns the type of one declaration as syntax, `:134-136,138-142`), no
  local context for a declaration, and no way to ask "is this definition equal to that".
* `FieldView.recursive` is true only when the field's type spine is exactly the `const
  T` (`:120-124`); an alias or a reducible spelling is not recognised.

An entry may splice these types into commands, but the host re-elaborates the result:
nothing the entry says about a type is trusted, and a hole in a copied type will be a
hole in the generated command.

**Term view (`Expr`).** For a tactic or a future term elaborator, `Expr`
(`lib/Prelude.wiz:494-504`) is `var i | const n | sort u | pi x implicit q dom body |
lam x body | app f a | lit n | opaque id`. The host reflects with `reflect`
(`Wiz/Elab/Tactic.lean:145-173`) and reifies with `reify` (`:176-207`):

* variables are de Bruijn indices relative to the goal's context;
* a constant loses its universe levels; `reify` makes fresh level metavariables
  (`:185-189`), so a universe-polymorphic constant is not round-tripped faithfully;
* a `sort` is reflected only if its level is a numeral; otherwise `opaque`;
* `pi`/`lam` carry the binder name; `pi` also carries an implicit flag and the quantity
  as an `Expr` (not a `BinderInfo` or a quantity literal), while `lam` carries only its
  name and body; `mu`/`nu` are shown only in the `(T, us, args)` display-hint form
  (`:155-160`);
* every other kernel form is `opaque id`: an index into a 256-entry handle table, tagged
  with the number of variables in scope (`internHandle`, `:132-141`). Two reflections of
  the same term at the same depth get the same handle while it is still in that table;
  a handle may be passed back to `reify`, lifted by `depth - d` or strengthened, and
  using it outside its binders fails (`:183-203`). A handle is never inspectable.
* Constructor applications are recovered only where the **type** is known:
  `reflectT` follows the types down (`:210-224,370`), so a `con` at a known nominal type
  is its constructor applied to parameters and fields; where the type is not known it
  stays opaque. This is enough for tactics and not enough for a rule that must see inside
  a definition body.

**Requests.** `TacTag` (`Wiz/Elab/Tactic.lean:38-90`) is the closed vocabulary: 45 tags,
append-only. A macro or deriver may ask only `result` (1), `fail` (2), `trace` (3),
`fresh` (4), `getInductive` (21), `getType` (22); anything else is refused by
`runMacroTac` (`Wiz/Elab/ProcMacro.lean:124-146`). A tactic may ask all tags, including
goals, `Expr` reflection, `whnf`/`unfold`/`rewrite`, `simp`/`hint` databases, and the
solver requests. A new request is a **host change**; an entry cannot add one. That is the
central limit of this ABI and the reason item ② (term elaborators) is a host item.

### 3.4 Hygiene, precisely

* The separator is the literal character `✝`. `scopeQuoted` appends a number to every
  identifier whose name ends in `✝`; `stripScope` splits at the first `✝`; local lookup
  matches `x✝` prefixes (`Wiz/Elab/Basic.lean:463`). It is a naming convention, not a
  scope object.
* `MacroM.fresh` allocates a number from `nextScope` (`TacTag.fresh`, `runTac`), and
  `runProcMacro`/`runDeriver` start at `scope + 1` and thread the returned next scope
  back into `CommandState.nextScope`. Two expansions in one module do not share names by
  accident.
* Generated syntax is synthetic at the invocation; only the values the entry passes
  through keep the user's ranges. A diagnostic about generated code therefore points at
  the macro/deriver use, not at a nonexistent line in the expansion.
* There is no capture avoidance for *free* names: an entry that writes a name which is
  shadowed at the use site can capture it. The entry must use dotted global names or a
  fresh local; the host does not rename free identifiers.
* `macro.source` is **generated source text**, not a `Syntax` quote: it is parsed and
  positioned with mark spans (`locateMarked`), but its names are ordinary source names
  and are not scoped by `scopeQuoted`. A command macro that emits text is responsible for
  its own freshness; the `✝` mechanism does not reach it.

### 3.5 Error reporting

`Msg` is `{ info : SourceInfo, severity, text, code := "", anchor := "" }`
(`Wiz/Elab/Command.lean:46-52`). One primary span, one message. The per-kind reality:

* **Tactic.** `Tac.fail msg` becomes an error at the tactic syntax with code
  `tactic-failed` (`Wiz/Elab/Term.lean:4161`); `Tac.trace` becomes an info message at the
  same span; `catch` catches only the message string, not a position. `unknown request`
  is an error at the span, no code (`:4598`).
* **Term macro.** `MacroM.throw` becomes an error at the macro invocation (`expand?`,
  `Wiz/Elab/Term.lean:276-287`), text is the entry's message, **code `""`** today; traces
  are info messages.
* **Deriver.** `elabExpansion` reports the runner's error at the `deriving` command with
  text `"deriving C for T: <msg>"` (`Wiz/Elab/Command.lean:2186-2196`), **code `""`**;
  traces are info messages.
* **Command macro.** This one is richer and is the precedent for a future uniform
  diagnostic: the output may contain `macro.error`/`macro.info`/`macro.source`
  pseudo-commands with a **path** into the input (`Wiz/Elab/ProcMacro.lean:173-184`,
  `lib/Prelude.wiz:2226-2234`), so one command macro can emit several messages at several
  input nodes. `macro.source` is parsed and positioned with the mark spans
  (`locateMarked`, `:206-282`). Codes are still `""`.
* **Lint.** A rule returns text findings; the host supplies the rule's code and severity
  (`Wiz/Lint.lean:529-531,544-560`), and the finding's anchor is the stable baseline key.
  This is the only kind with multiple coded findings today.
* **Backend/process.** stderr and exit status; there is no `Msg` and no span. Today
  `buildCmd` prints the error and exits 1 without a code (`Main.lean:995-1004`); under
  `wiz-meta/1` the driver wraps it as one line with `entry-failed`.

What `wiz-meta/1` **requires** (and today's code does not fully provide) is the
intersection: one primary span, one stable code supplied by the registry
(`entry-failed`), the entry's text as a single line after a `<kind> <name>:` prefix, and
traces as info messages. Multi-error and related spans are deliberately out; C5 in
`extensibility.md` §3.2 is the follow-up. Command macros keep their path-based
pseudo-commands as the one legacy extension until the uniform `diag` node exists.

### 3.6 Purity, termination, budget

A Wiz rule must be total and pure: no `partial`, no trust source (`axiom`, `extern`,
`implemented_by`, an untrusted `builtin`, a native representation), no IO. The lint
registry already enforces this for package sets (`Wiz/Lint.lean:587-648`); a registry
entry of any Wiz kind must be checked the same way before it runs. The interpreter
`run` (`Wiz/Compiler/Run.lean:477`) has **no overall step budget**; the only fuel appears
in local list/readback helpers (`:342,410,629,734`). Until C4's budget lands, a Wiz entry
can hang the driver; therefore a package entry may not be enabled by default, and the
acceptance for any default-on entry includes a budget-exhaustion case (`entry-budget`).

### 3.7 What is deliberately out

| out | why |
|---|---|
| `Wiz.Core.Term`, `Globals`, `Environment`, `Name` resolution internals | the ABI is a view; leaking the kernel makes every kernel change an ABI change |
| arbitrary declaration types/bodies; `getType` is the only type query, `IndView` the only declaration view | a rule that needs the body needs the structured view (item ③), not a raw term |
| the class name and its methods in a deriver; `Deriver` receives only the type name | `lib/Deriving.wiz` hardcodes the five method names; a generic deriver is a later ABI change (`getClass` or a second `String` argument) |
| goals outside the current tactic state; direct metavariable assignment | a tactic is a request chain; anything else breaks the kernel's checked-term discipline |
| adding `Tac` requests | `TacTag` is a host frontier (B2); an untyped backdoor would undermine the capability model |
| IO, filesystem, clock, random, network, process control | a Wiz rule is a pure function over a view; the host supplies the view |
| `partial`, trust sources, `builtin`/native registration | a package may not add trust; the registry is not a sandbox and does not pretend to be |
| backend emission, IR, target-specific code | needs `wiz-ir/1` (item ⑤); FeEval alone does not provide the program |
| doc renderer/tokeniser code | doc languages are data; the builder is host-only by design (`docs-highlighting.md` §4.3) |
| cache keys, toolchain flags, options, module roots | the driver's policy, not the entry's |
| suppressing/re-grading core lint rules or diagnostics | core policy is the consumer's and the toolchain's |
| no `quoteExpr`/`quoteDecl`; the entry builds `Syntax` with a quotation and `Expr` with its constructors | the `Expr` view is the stable term interface; a kernel-term quotation would pin the representation |
| multiple spans, related locations, several errors per term/deriver invocation, quick fixes | v1 has one `Msg`; C5 is the follow-up |
| source positions in generated syntax; scope objects; capture avoidance for free names | the quote is a syntax-building term; positions are the call site |

### 3.8 Versioning and the conformance corpus

`wiz-meta/1` names the `Syntax`/`IndView`/`Expr`/`Tac` shapes, the request tags and the
hygiene/error conventions. `wiz-lint/1` and `wiz.doc.languages/1` stay as they are.
Rules:

* The attribute front-ends insert `abi := "wiz-meta/1"`; a package that must pin another
  range uses the lint-set/manifest form or a future `ext` command. There is no silent
  version negotiation: the resolver refuses an unknown major.
* adding a `TacTag` is append-only and backward compatible for an old entry (it does not
  ask the new tag); removing or renumbering a tag is a major bump;
* changing a constructor of `SyntaxF`/`Expr`/`IndView`, or the meaning of `✝`, is a major
  bump;
* an entry declares the `abi` it was written against; the resolver refuses an unknown
  major (`unsupported-<kind>`); a toolchain may accept a range.

The corpus (C2 in `extensibility.md`) is a dozen small programs per profile — a deriver
that builds an instance, a tactic that closes a goal, a command macro with an error path,
a lint rule with a finding, a `getInductive` consumer — run on the host and, where it can,
on the selfhost. Today the selfhost records "unsupported" for each; the corpus is what
turns "the two implementations agree" from a hope into a test.

---

## 4. Per-kind decisions

### 4.1 Deriver (and the D1 fix)

The host is already generic: `attribute [deriver C] f` stores the **name** `f` after
unifying its type with `Deriver` (`Wiz/Elab/Command.lean:3707-3717`), and `derive` runs
the declaration through `runDeriver` (`:2204-2210`). The registry entry is
`deriver/C` with payload `.wizRule f`, capabilities `[inductive]` (a new capability name
for `getInductive`; the prototype does not need it yet). Duplicate `deriver/C` is a
refusal; a user declaration named `deriveBEq` is simply a different declaration, because
the key is the **class** and the payload is the declaration, not a name heuristic.

Two registration details matter for the stable key. First, `attrDeriver` stores `C` as
the **syntactic** id (`:3709-3711`), the `deriving` clause uses `c.getId?` without
`resolveName` (`:2217-2220`), and only the standalone `deriving instance` command
resolves C and T (`:3722-3727`). A deriver registered inside a namespace can therefore
be stored under a name the clause never looks up. Step 5 must resolve `C` in all three
places before constructing `deriver/C`. Second, `f` must be stored as the resolved
declaration, not `deriverBase f`; the host already does the former, the selfhost the
latter (D1).

One ABI gap is easy to miss: `Deriver` receives only the **type** name
(`String → MacroM (List Syntax)`, `lib/Prelude.wiz:903`), not the class `C` or its method
names. The class is in the registry key, but the function cannot see it; `lib/Deriving.wiz`
hardcodes `"BEq.beq"`, `"Repr.reprPrec"`, etc. A generic deriver for a user class must
either hardcode its class (fine for the author) or the ABI needs a `getClass` request or
a `Deriver := String → String → …` change. That is deliberately out of v1; the registry
can still declare the entry and the driver can pass `C` to a future interface.

The selfhost fix (D1) is part of Step 4: `Globals.addDeriver` must carry whether the
registered value is a built-in (compiled into the frontend) or a user declaration
(`selfhost/Frontend.wiz:815-824`); `deriverCmd` records that flag (`:10834-10847`); and
`deriveClassOn` dispatches built-ins by the flag, never by `deriverKind f`
(`:11435-11447`). A user deriver is then either run (after FeEval) or refused by name with
`entry-unsupported`, not silently replaced by the built-in. The host needs no change.

### 4.2 Tactic and macro

The entry is `tactic/k`/`macro/k`, payload `.wizRule f`, capabilities `[goals, expr]` for
a tactic and `[syntax, inductive, type]` for a macro/deriver. The attribute commands
remain the ergonomic front-end; they construct an `Entry` and call `register`, so there is
one table. Duplicate keys refuse (no latest-wins). `local` for `[tactic]`/`[deriver]` is a
separate `endModule` change, not a registry feature.

The tactic ABI is the hardest: `Expr` reflection is lossy (§3.3), the goal state is a
request chain, and `assignLate`/`nativeDecide` are trusted escape hatches that a package
entry must not get. The registry's capability list should therefore start with `goals`
and `expr` and grow one request family at a time; a package tactic that needs `smt` or
`nativeDecide` asks for a capability that is not in the package set.

### 4.3 Lint

`lint-set/NAME` is the set entry (payload `.data`, schema `wiz-lint/1`, plus the rules);
`lint-rule/CODE` is the rule entry (payload `.wizRule runner` plus metadata). The existing
`checkSet` (`Wiz/Lint.lean:598-648`) already implements most of the semantics: ABI
`wiz-lint/1`, stable capabilities, code block, duplicate code, trust/`partial` checks,
compile. The registry wraps it and reuses the same refusal codes; `loadPackageSets`
(`:650-665`) is the duplicate-across-sets check. The view stays text (`docs/lint-abi.md`);
a term-shaped view is item ③, not this item.

### 4.4 Doc language

`doc-language/NAME`, payload `.data`, schema `wiz.doc.languages/1`, capabilities none (the host
builds the page). The existing merge rules (case-insensitive name/alias, duplicate name in
one file, `override`, reserved `wiz`, unknown fields refused, fixed eight classes) become
the kind's conflict/validation semantics (`Wiz/Doc/Registry.lean:8-20,127-146`). A
package may not ship a renderer or tokeniser; that is the existing policy and stays.

### 4.5 Backend

`target/NAME`, payload `.core` for the five in-tree targets, `.process` for a future
out-of-tree adapter, `.unsupported reason` for the selfhost entries it cannot serve.
Capabilities are the operations: `emit`, `check`, `link`, `run`, `attest`, `library`
(`--lib`/`--no-main`), `split`, `repl`. The per-entry table is
`Wiz/Ext/Basic.lean:backendEntries` in the prototype; the real module should keep the
pure-list + `ofEntries` shape, because a pure `Except` table is testable and cannot panic
at startup. A `.process` adapter has a `schema` document (`c-text/1`, `bpf-core/1`) and a
command; its capabilities are advisory until a sandbox exists (`targets-ext.md` §6).

Backend-only fields (`artifacts`, `tools`, `runtime`, `phases` in `targets-ext.md` §2)
do not go into the generic `Entry`: they live in a `Wiz/Backend/Entry` extension or a
side table keyed by `target/NAME`. Putting them in the one record would make every
deriver pay for a target's tool list, and would re-open the per-kind branch the model
exists to remove.

A **Wiz backend** is not in this item. The host's IR is a Lean inductive with
`toString` only (`Wiz/Compiler/IR.lean:243,276,292`); there is no parser, JSON or version,
and `inductive Backend` is `c | llvm | wasm` (`:43-47`). A Wiz function cannot consume
the program until `wiz-ir/1` (item ⑤) exists. FeEval would let the function *run*; it
would not give it the program. This is the one place where "the registry need not wait
for FeEval" must not be read as "a Wiz backend is around the corner".

### 4.6 Term elaborator (future)

`term-elab/K` with `Syntax → TacticM Unit`, dispatched in `check` after `expand?` and
before the built-in kinds (item ②). The registry can declare it now, with a capability
`term` and the same `Expr` limits; the dispatcher is the work. Its dispatch order
(`stage`/priority) is kind-specific, like a backend's phases, and stays in a
`Wiz/Ext/TermElab` side record keyed by `term-elab/K`; the generic `Entry` does not grow
a field every kind would ignore. It is listed here so the `Kind` enum does not need a
breaking change later.

---

## 5. FeEval: verified or refuted?

**The claim:** `extensibility.md` §4 says the registry is host-side resolution and must
not wait for `SH-2.1` (FeEval); the selfhost may refuse non-core entries by name until
FeEval lands, which is fail-closed. **Verdict: verified, with two caveats.**

Evidence:

1. **The host already runs Wiz code.** `Wiz/Compiler/Run.lean:477` is a total interpreter
   over erased terms; `runProcMacro`/`runCommandMacro`/`runDeriver` (`Wiz/Elab/ProcMacro.lean:
   152-172`) and `runTac` (`Wiz/Elab/Term.lean:4120`) call it through `apply code`. The
   lint driver calls a package runner the same way (`Wiz/Lint.lean:529-531`). So a
   deriver/tactic/macro/lint entry that runs on the host needs **no new evaluator**.
2. **The target conversion is host code end to end.** The five entries are `.core`
   payloads; `--target` is resolved before a module is read (`Main.lean:1343`); no Wiz
   function is involved. The selfhost's table is a static mirror with `unsupported`
   reasons (`selfhost/Cli.wiz:1181-1186,1274-1301`). Neither needs FeEval.
3. **The selfhost's gap is real but bounded.** `runMacroTac` answers five requests
   (`selfhost/Frontend.wiz:11053-11063`); `deriveClassOn` refuses a user deriver
   (`:11435-11447`); there is no `#eval` that is not `#reduce`. A registry entry can be
   *declared* and *resolved* there; it cannot be *run*. The honest refusal is
   `entry-unsupported: <name> is a Wiz entry; this toolchain has no elaboration-time
   evaluator (SH-2.1)`. That is fail-closed and testable.
4. **A Wiz backend is not FeEval-gated; it is IR-gated.** The program is not reachable
   from Wiz until `wiz-ir/1`; FeEval alone would run a function that has nothing to
   consume. Do not use the registry's FeEval decoupling to schedule a Wiz backend.

Caveats:

* **`SH-2.0a` still matters.** The embedded prelude has no `Syntax.mkVar`/`mkApp`/`mkStr`
  (`extensibility.md` §3.1 B3; `lib/Prelude.wiz:883-893` is the host prelude). FeEval's
  first test would fail for the wrong reason without it. It is not needed for the
  registry, only for FeEval.
* **Running a Wiz entry under the selfhost is a distinct milestone.** The registry's
  selfhost half is a refusal table; parity begins when FeEval can answer the term/decl
  requests. Keep the two acceptance tests separate: "the selfhost refuses by name" now,
  "the selfhost runs the conformance corpus" after FeEval.

So the recommendation to decouple `CORE-3.3` from `SH-2.1` in `roadmap/program-next.md`
stands, provided the caveat is written down: the registry ships host-side; the selfhost
ships the table and the refusal, not execution.

---

## 6. Ordered steps

Each step names the smallest change, the `file:line` integration point, and the
acceptance that would fail if it were skipped.

### Step 1 — the model and resolver (prototype done)

New `Wiz/Ext/Basic.lean`; import it from `Wiz.lean` (after `Wiz.Lint`). The prototype
contains `Kind`, `Cap`, `Payload`, `Entry`, `Refusal`, `Table.register/ofEntries/find?/
resolve/resolveWith`, the five backend entries and `resolveBackend`/`resolveBackendFor`.
No Main change beyond `targets`/`takeTarget`.

Acceptance: `=ext` (6 cases, §8) green; `resolveBackend "bpf2"` refuses
`unknown-target`; `Table.ofEntries` with two `target/demo` entries refuses
`duplicate-target` naming both providers; `resolveBackendFor "js" [.link]` refuses
`target-capability`.

### Step 2 — `--target` is dispatched by the entry, not by a string

Integration points: `Main.lean:924` delete the literal list (already
`Wiz.Ext.backendNames`); `:945-966` `takeTarget` returns the resolved `Entry` or its
payload tag, not `Option String`; `:968-1005` `buildCmd` takes the entry and dispatches on
`entry.payload`/`entry.name` with a final `entry-unsupported` refusal; `:1006-1029`
`runCmd` checks `caps.contains .run`; `:1366-1379` the REPL checks `.repl`;
`Wiz/Compiler/Build.lean:267-289` is called only from the core payload and stops
re-refusing shapes; `Wiz/Toolchain.lean:67-72` gains a `backend` field and hashes the
entry digest; `Wiz/Cache.lean:598,693` inherit it. `selfhost/Cli.wiz:1181-1186` becomes
the same names with `supported`/`reason`.

Acceptance: `=backend` unchanged (23 cases); `=js`, `=bpf`, `=wasm` unchanged;
`--target bpf2` exits 1, writes nothing; `--attest --target bpf` exits 2 and never enters
`Bpf.buildCmd`; `--target js --lib` exits 2 with `target-capability`; a sixth entry with
no payload refuses instead of building C; `targetTag` differs for `c` and `bpf`.

### Step 3 — the selfhost table and the target lie

`selfhost/Cli.wiz:1181-1186,1274-1301`: `targetModes` becomes `[("c", supported),
("llvm", supported), ("wasm", unsupported "…"), ("bpf", unsupported "reads bpf-core/1;
this toolchain emits c-text/1"), ("js", unsupported "…")]`; the `unknown` vs
`unsupported` distinction and the reasons are data; `--target bogus` still exits 1.
Generate the names/reasons from the host table (the `Wiz/Selfhost.lean:155-181` splice
already does this for `toolchainId`) or pin a test that compares the two tables: a
hand-copied list is the fifth-target bug again.
Acceptance: `=selfhost-cli-diff` gains a case that `--target bpf` is `unsupported-target`
with the `bpf-core/1` reason on the selfhost and a real build on the host; `--target c`
still builds.

### Step 4 — the deriver registration flag (D1)

`selfhost/Frontend.wiz:815-824` (`Globals.addDeriver` carries `builtin | user`),
`:10834-10847` (`deriverCmd` records it), `:11435-11447` (`deriveClassOn` dispatches on
it, not on `deriverKind f`). The host's `Command.lean:3707-3717` is already correct.
Acceptance: a `=selfhost` case declares `attribute [deriver BEq] myBEq` with a body that
reports "user"; `deriving BEq` either reports "user" or refuses with `entry-unsupported`,
never the built-in body; the existing A11 cases stay green.

### Step 5 — the elaboration registries become entries

`Wiz/Elab/Command.lean:124-152` (`CommandState` gains a registry or an index; the four
lists stay as storage), `:3437-3466` (macro), `:3509-3517` (tactic), `:3707-3717`
(deriver), `:2193-2210`/`Term.lean:280,4110` (lookup sites), `:1856-1915` (`endModule` for
`local`). Registration constructs an `Entry` and calls `register`; a duplicate is a
`Msg` with `duplicate-deriver`/`duplicate-tactic`/`duplicate-macro` and both providers.
Acceptance: a unit test registers two tactics for one kind and sees the refusal; the
existing `=tactics`, `=deriving`, `=meta` groups are unchanged (they have no duplicate
registration in `lib/`, verified by grep).

### Step 6 — lint sets and doc languages

`Wiz/Lint.lean:598-665` (`checkSet`/`loadPackageSets`) constructs `Entry`s; the refusal
codes are the registry's. `Wiz/Doc/Registry.lean:8-20,127-146` becomes a
`docLanguage` table with the same merge rules. Acceptance: `=wiz-lint` goldens unchanged;
a duplicate code across two sets refuses with `duplicate-lint-rule` (today it refuses with
a bespoke message); `wiz doc --languages` with a duplicate/override/reserved name refuses
with the same codes.

### Step 7 — freeze `wiz-meta/1` and add the corpus

Add the marker to the entry `abi`; add `Tests/fixtures/meta/` with one deriver, one
tactic, one command macro (with an error path) and one lint rule; run them on the host
and record the selfhost's `unsupported` result. The existing A11/A12 cases are the first
rows of the corpus; a shared fixture directory makes them one artifact instead of two
test-group copies. Add the fuel budget before any package
entry is default-on. Acceptance: the corpus passes byte-identically on the host; the
selfhost records the same `entry-unsupported` code for each; a budget-exhaustion case
reports `entry-budget`, not a hang.

### Step 8 — package discovery (the first real external user)

A manifest key (`Package.backend`, `Package.lintSet`; `lib/Grail.wiz:199-223`,
`Grail/Config.lean:84-105`), an `ext-set` enablement list, and a `grail` table that adds
package entries before dispatch. `wiz` alone knows core entries; `grail` reads the
manifest. Acceptance: a `demo` target declared in a manifest resolves and builds without
a `Main.lean` edit; a package provider present but not enabled refuses
`target-not-enabled` with the `grail add` hint; a second `bpf` refuses `duplicate-target`.
This is the step that makes the registry useful to a third party.

---

## 7. Acceptance tests, in selector form

The prototype ships `=ext` (6 cases, pure). The real steps add:

| selector | what it must show | anti-vacuity |
|---|---|---|
| `=ext` | five core targets resolve; caps are data; unknown/duplicate/capability refuse | delete a `backendEntries` line: the resolve case fails |
| `=backend` | the 23 existing cases unchanged | a change in IR/output fails the goldens |
| `=js`, `=bpf`, `=wasm` | the existing target groups unchanged | each group's build/run case |
| `=selfhost-cli-diff` | `--target bpf` is `unsupported-target` (selfhost), unknown stays unknown | the host/selfhost message pair |
| `=selfhost` A11 | the deriver hijack case | `myBEq` must report "user", not the builtin |
| `=wiz-lint` | the package lint goldens unchanged; duplicate code refuses | remove the duplicate check: the case goes green wrongly |
| `=cli` (none; `=args`/`=elab` are the nearest) | a manifest `demo` target builds | delete `Package.backend`: `unknown-target` |
| cache probe | `targetTag c ≠ targetTag bpf` | a constant tag makes them equal |

Negative tests that must fail, not fall through (from `targets-ext.md` §7, kept because
they are this design's teeth):

1. `--target bpf2` → `unknown-target`, exit 1, **nothing written**.
2. `--attest --target bpf` → `target-capability`, exit 2, and `Bpf.buildCmd` is not
   entered.
3. `--target bpf --lib` → `target-capability`, not the bpf facade's prose.
4. a second `bpf` provider → `duplicate-target`, naming both, before any emit.
5. a provider present but not in `(ext-sets …)` → `target-not-enabled`, not
   `unknown-target`.
6. a `transfer` entry with `runtime := .none` → `target-capability` at registration.
7. under the selfhost, `--target bpf` → `unsupported-target` with the `bpf-core/1` reason.

---

## 8. Prototype: what is actually in the tree

* `Wiz/Ext/Basic.lean` (new, 260 lines with comments): the model, `Table`, the five
  `backendEntries`, `resolveBackend`/`resolveBackendFor`, `choicesText`. Pure Lean, no
  imports, no IO.
* `Tests/Groups/Ext.lean` (new, 101 lines): six pure cases (the five targets and their
  caps; unknown refusal; duplicate naming both providers and an alias collision;
  capability refusal before dispatch; an `entry-unsupported` refusal with its reason;
  illegal `override`/empty name/empty ABI). No compiler, no process, no scratch
  directory.
* `Wiz.lean`: one import line.
* `Main.lean:924`: `targets := Wiz.Ext.backendNames`; `:945-966`: `takeTarget` calls
  `Wiz.Ext.resolveBackend` and returns the entry's **canonical** name, so an alias cannot
  reach the string dispatch under a different spelling; the build/run/REPL dispatch is
  still the string code and is Step 2. The prototype therefore does **not** yet pass the
  fail-closed-dispatch acceptance (a sixth entry is accepted by `takeTarget` and would
  fall through to C); the note says so instead of claiming otherwise.
* `.github/test-shards.json`: `"=ext"` added to the shard that already selects `=args`
  and `=library`.

Build/test results are in §9 (the note is committed with the prototype, so the numbers
are the ones from this tree).

### 8.1 Why this is the smallest useful skeleton

The brief's ~100-line target was for a skeleton that fits the whole model. The model and
resolver alone are about 160 lines of Lean including the five entry declarations; the
first-user wiring is 9 lines in `Main.lean`. What is *not* here is the part that makes
the registry load-bearing: `buildCmd`/`runCmd`/REPL dispatch by payload and capability
(≈ 120 lines), the cache digest (≈ 15), the selfhost table (≈ 30), and the deriver flag
(≈ 20). Those are Step 2–4 in §6 with exact anchors; writing them in this note's tree
without running the target/selfhost groups would be a larger, riskier change than the
design justifies. The prototype therefore proves the *model* and the *resolution
semantics* (the part every later kind reuses) and leaves the dispatch conversion as a
precise, testable slice.

---

## 9. Honesty ledger

**Verified by reading in this tree (`3fa0eec95`).** All `file:line` anchors in §1 and §3
were re-read at those lines, not copied from `extensibility.md` (whose tree was
`25c503002` and whose `Main.lean` anchors are four targets, not five). Specific checks:

* `Wiz/Ext/` does not exist; `Wiz/Lint/Basic.lean:49-102` is the only `Capability` enum;
  `Wiz/Lint.lean:388-390,598-665` is the closest registry.
* `Main.lean:924` has five names (`js` landed since `extensibility.md`); `buildCmd`'s
  final `else` is the C/LLVM fall-through; `runCmd` and the REPL have the same shape.
* `Wiz/Compiler/IR.lean:43-47` is `c|llvm|wasm` (no bpf/js) and `toString` (`:243,276,
  292`) is the only printer.
* `Toolchain.targetTag` ignores its argument; `Main.lean:426` passes the constant.
* `selfhost/Cli.wiz:1181-1186` has three target names; `Frontend.wiz:10806-10819` dispatches
  the deriver by name; `:11053-11063` answers five requests.
* `lib/` has no duplicate real `[tactic]`/`[macro]`/`[deriver]` registration (the
  duplicates in `lib/Prelude.wiz` are inside doc comments; `attribute [tactic
  tactic.exact]` appears at `:1009` only as code, `:969` is a documentation example).

**Executed.** `heavy --rsync --timeout 3600 -- lake build wiz tests` (job 5131,
node `win3`) exited 0: 630 jobs, including `Wiz.Ext.Basic`, `Tests.Groups.Ext`, `Main`,
`wiz:exe` and `tests:exe`. The warnings in that log are pre-existing (`Tests/Elab.lean`
unused `textLib`, `Tests/Scaling`'s `String.mk`, `Tests/Groups/Hdl`'s `String.Slice`
deprecations); none is from `Wiz/Ext/Basic.lean` or `Tests/Groups/Ext.lean`. The `=ext`
test run is `heavy --sshfs -- timeout 600 lake test -- '=ext'`; its result is recorded
below when it returns (one heavy job at a time). What I did **not** run: the full suite,
`=backend`, `=js`, `=bpf`, `=wasm`, `=selfhost`, `=selfhost-cli-diff`, `=wiz-lint`,
`grail test`, any measurement. No Lean build was run on the controller; everything goes
through `heavy`.

**Not implemented (the prototype stops here).**

* `buildCmd`/`runCmd`/REPL dispatch and capability checks (Step 2); the prototype only
  resolves `--target NAME`, `--llvm` and `--wasm` (the last two through the table, as
  fixed CLI aliases). Dispatch after resolution is still the string code.
* The entry digest in `Toolchain.targetTag`/`Cache.Key` (Step 2).
* The selfhost target table and the deriver flag (Steps 3–4).
* The elaboration registry conversion (Step 5), lint/doc conversion (Step 6), the ABI
  marker/corpus/fuel (Step 7), manifest discovery (Step 8).
* Per-kind name shapes and doc-language case-folding; the prototype's `nameOk` only
  rejects whitespace/slashes, and the existing doc registry still owns the case-insensitive
  merge (`Wiz/Doc/Registry.lean:127-146`).
* Per-kind capability validation (a `target` claiming `decl` is accepted by the
  prototype's `register`); the real resolver refuses a capability outside its kind's set.
* The `.core`-only-for-`wiz-lang` payload rule; the prototype records the payload but does
  not enforce the trust boundary (it has no package table yet).
* No package adapter, no `ext-set`, no `grail` manifest key.

**Unverified / open.**

* Whether a cached region can be reused across two `--target` values *today* in a way
  that changes an artifact. `targetTag` is constant, but elaboration is target-independent
  and I did not trace a target-specific region; the slot is still the right place for
  the digest, per `targets-ext.md` §3. Marked unverified, not a claim of a live bug.
* Whether `grail`'s manifest evaluation can name a target before its module graph is
  loaded. `wiz`'s parse order is verified; `grail`'s is not read in this lane.
* Whether the selfhost's `--target bpf` message change breaks `=selfhost-cli-diff`; not
  run.
* Whether `IndView`'s printed types are stable enough for a real deriver across
  renamings; the `_` fallback is explicit (`Wiz/Elab/Reflect.lean:73-76`), but I did not
  measure how often a declaration hits it.
* Whether a package tactic can be useful without `smt`/`nativeDecide`; the capability
  list is a proposal, not a measured minimum.

**Drift from the notes I read.** `extensibility.md` says four targets and cites
`Main.lean:870`; this tree has five (`js`) and `targets` at `:924`. `targets-ext.md` says
`d853fde79`; this tree is `3fa0eec95` and `Wiz/Compiler/Bpf`/`js` have moved. The
qualitative claims (closed list, fall-through, no `Wiz/Ext`, selfhost name dispatch) all
still hold; the line numbers are the ones above.

**No private material.** This note and the prototype use only the public tree and
synthetic names (`demo`, `x`, `myBEq`).

---

## 10. Integration map (file:line → change → test)

This is the checklist behind §6; the prototype already covers the first two rows and the
new module/group.

| site | current | change | test |
|---|---|---|---|
| `Wiz/Ext/Basic.lean` (new) | absent | `Entry`/`Table`/`Refusal`, five target entries | `=ext` |
| `Wiz.lean` after `Wiz.Lint` | no import | import the new module | build |
| `Main.lean:924` | literal five names | `Wiz.Ext.backendNames` (done) | help/unknown text |
| `Main.lean:945-966` | `targets.contains` | `resolveBackend` (done) | `=ext`, `=selfhost-cli-diff` |
| `Main.lean:968-1004` | `target ==` branches + C fall-through | entry payload + `caps` + final refusal | `=backend`, `=bpf`, `=js`, `=wasm` |
| `Main.lean:1006-1029` | `target ==` branches | `caps.contains .run` | `=js`, `=wasm`, `=bpf` |
| `Main.lean:1343-1347` | `takeTarget` → string | keep the entry; set `Toolchain.backend` | cache probe |
| `Main.lean:1366-1379` | REPL by name | `caps.contains .repl` | `=selfhost-cli-diff` |
| `Main.lean:426` | constant `tc.targetTag` | entry digest | cache probe |
| `Wiz/Toolchain.lean:67-72` | ignores its argument | `backend` field + digest | `targetTag c ≠ bpf` |
| `Wiz/Cache.lean:598,693` | `Key.target` slot | inherit the digest | cache format test |
| `Wiz/Elab/Command.lean:124-152` | four lists | registry view over the lists (or `Effect` field) | `=tactics`, `=deriving` |
| `:3437-3466` | macro attribute | construct + register `Entry` | duplicate-macro test |
| `:3509-3517` | tactic attribute | construct + register `Entry` | duplicate-tactic test |
| `:3707-3717` | deriver attribute | construct + register `Entry` | duplicate-deriver test |
| `:1856-1915` | `endModule` | `local` entries for the missing kinds | local-scope test |
| `Term.lean:280,4110-4117` | `List.lookup` | resolve `Entry`, not a bare name | `=meta`, `=tactics` |
| `ProcMacro.lean:152-172` | runners | unchanged; carry the entry name for messages | macro/deriver errors |
| `Lint.lean:598-665` | `checkSet`/`loadPackageSets` | wrap as `lint-set`/`lint-rule` entries | `=wiz-lint` |
| `Doc/Registry.lean:8-20,127-146` | JSON merge | `doc-language` entries, same rules | doc goldens |
| `selfhost/Cli.wiz:1181-1186,1274-1301` | three names | five names + `supported`/reason | `=selfhost-cli-diff` |
| `selfhost/Frontend.wiz:815-824,10834-10847,11435-11447` | name dispatch | builtin/user flag | `=selfhost` A11 |
| `ErrorCode.lean:102+`, `docs/error-codes.md` | no entry codes | `entry-*`, `duplicate-*` | `lsp-server` table |
| `.github/test-shards.json` | no `=ext` | add to the library shard (done) | `check-shards.py` |

The rows that are *not* done are deliberately not claimed as passing; §9 lists the
selectors that were not run.

---

## 11. References

* `wiz-notes/extensibility.md` — item ①, blockers B1–B5/C1–C5, the ordered plan.
* `wiz-notes/targets-ext.md` — the target-entry fields, refusals, cache digest and the
  seven negative tests; §0's lifetime argument is refined in §2.2 here.
* `wiz-notes/separate-repos.md` §Shared extension model — X1–X6: data/Wiz rule/host
  adapter, discovery, `(kind, name)`, enablement, the index.
* `wiz-notes/user-extensions.md` — the four shapes and the closed `Tac` frontier.
* `docs/lint-abi.md` — `wiz-lint/1`, the stable view and the finding format.
* `docs/error-codes.md`, `Wiz/Core/ErrorCode.lean` — the code table a new elaboration
  refusal must join.
* `Wiz/Elab/ProcMacro.lean` — the macro/deriver runner, hygiene and located output.
* `Wiz/Elab/Reflect.lean`, `Wiz/Elab/Tactic.lean` — `IndView`/`Expr` and the request
  tags.
* `selfhost/Frontend.wiz` — the selfhost's five-request runner and name-keyed derivers.
