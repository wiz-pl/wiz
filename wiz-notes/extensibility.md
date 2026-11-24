# Extensibility: which interfaces to open, and in what order

**Status.** Research lane `extensibility`, 2026-11-23. Tree
`/workspace/wt/extensibility` at `25c503002` (`integration/train12`). Notes only: no
code, no build, no test run. Every `file:line` below was read in that tree; §6 records
what was verified and how. The two performance figures quoted in §4 are from
`wiz-notes/elab-evaluator-plan.md` and are that note's measurements, not mine.

**Question.** The priority is to make the language further extensible so that features
can be moved to Wiz. This note decides which *interfaces* to open, in what order, and
what each is worth. It is not a catalogue of every extension point — `wiz-notes/user-
extensions.md` is that (at an older tree, `e3bd36ff`) — and it is not a target design:
`wiz-notes/targets-ext.md` owns that, and §3.2 below cites it rather than repeating it.

---

## 0. Verdict

1. **The tree is rich in extension points and poor in extension interfaces.** There are
   nineteen user-facing points (`user-extensions.md` §1), but each is a closed list in a
   different file: the data primitives in `Wiz/Elab/Term.lean`, the requests in
   `Wiz/Elab/Tactic.lean`, the attributes in `Wiz/Parser/Builtin.lean`, the targets in
   `Main.lean`, the lints in `Wiz/Lint.lean`. A *feature* can be written in Wiz only if
   a list already has a slot for its class; adding a class is a host change.

2. **"Move X to Wiz" is three different projects.** *Porting* the core (Lean → Wiz)
   buys self-hosting, not extensibility: a Wiz-core deriver is as closed as a Lean one.
   *Opening* an interface (a registered Wiz function over a stable view) buys
   extensibility. *Packaging* it (a manifest entry, discovery, refusals) buys a third
   party the ability to add it without a compiler change. The brief's list mixes the
   three; only the second and third deserve the word "extensible".

3. **The derivers are already in Wiz, twice.** `lib/Deriving.wiz` has `Inhabited`,
   `Repr`, `BEq`, `DecidableEq` (and `lib/OpticDerive.wiz` has `Lens`); the Lean host
   already runs *any* registered `[deriver]` function through the erased-code
   interpreter (`Wiz/Elab/Command.lean:2204-2210`, `Wiz/Elab/ProcMacro.lean:165-172`).
   The 529-line block in `selfhost/Frontend.wiz:10906-11434` is the *selfhost's* second
   implementation, and the residue that keeps it there is the missing evaluator, not a
   missing Wiz library. Calling that block "hardcoded in Lean" is wrong in both
   directions: it is Wiz source, and the Lean side is generic.

4. **There is a live correctness bug, not only a gap.** The selfhost chooses the deriver
   by the *registered function's name* (`deriverKind`, `selfhost/Frontend.wiz:10806-
   10819`; `deriveClassOn`, `:11435`). A user who declares a deriver named `deriveBEq`
   and registers it gets the frontend's hardcoded `BEq` body, not their own, and the
   host gets their own. The same `deriving` clause then means two different things
   under the two toolchains. This is cheap to fix (§4, item 1) and should not wait for
   FeEval.

5. **Recommended order:** registry → term elaborators + the primitive table →
   structured view → FeEval → serialized IR. The one place this disagrees with
   `roadmap/program-next.md` is explicit: that plan gates `CORE-3.3` (the `ext`
   registry) on `SH-2.1` (FeEval); §4 argues the registry is host-side resolution and
   must not wait for an evaluator. The selfhost half can refuse by name until FeEval
   lands, which is fail-closed and honest.

---

## 1. Three projects called "move it to Wiz"

| project | what changes | what it buys | what it costs | examples in the brief |
|---|---|---|---|---|
| **Port** | the *core* implementation changes language | self-hosting; one fewer Lean line | a re-implementation, two copies to keep in sync, and no new extension point | derivers into `selfhost/Frontend.wiz`, CLI into `selfhost/Cli.wiz`, C backend into `selfhost/Backend.wiz` |
| **Open** | a Wiz value of a fixed interface is registered and run by the toolchain | a library or package can add the feature; the core keeps one dispatch site | an ABI (what the Wiz code may see and ask), a trust policy, and a cache/determinism story | `[tactic]`, `[macro]`, `[deriver]`, lint rules, `[term_elab]` |
| **Package** | a manifest or import lets the tool *find* the entry | a repository outside the tree adds it without patching `Main.lean` | resolution, conflicts, enablement, versioning, refusal codes | `--target`, `Package.lintSet`, `wiz.doc.languages/1` |

**Decision rule.** A port is worth doing only when it is the same work as opening the
interface (FeEval is: the evaluator is what runs the library deriver) or when it removes
a runtime that a Wiz extension needs. A port that only relocates a special case should
wait, however many lines it deletes.

The `Inhabited` deriver is the worked example of all three:

* **port:** done — `deriveInhabitedV` is Wiz source (`selfhost/Frontend.wiz:11210-11223`)
  and the frontend's `deriving` runs it through `runDeriver` (`:11060`).
* **open:** done — `Deriver := String → MacroM (List Syntax)` and
  `attribute [deriver C] f` are in `lib/Prelude.wiz:901-903`; the host runs it.
* **package:** not done — the selfhost still special-cases the name and cannot run a
  deriver that is not compiled into the frontend (§3.1, B3).

---

## 2. Inventory

### 2.1 The table

Line counts are `wc -l` in the worktree unless stated. "Wiz today" means something a
Wiz program can already *be*, not something the selfhost can already *run*.

| feature | Lean today | Wiz today | what a Wiz version needs | what forces it to stay | verdict |
|---|---|---|---|---|---|
| **derivers** (`BEq`, `Repr`, `DecidableEq`, `Compare`) | host: dispatch only, 0 deriver bodies (`Wiz/Elab/Command.lean:2193-2210`) | `lib/Deriving.wiz` 467 (4 derivers); `lib/OpticDerive.wiz` `Lens`; selfhost 529-line re-implementation (`selfhost/Frontend.wiz:10906-11434`; the four bodies are `:11142-11424`) | selfhost: evaluate the registered function; `IndView` with syntax-valued field/param types | no selfhost evaluator (B3); name-keyed dispatch (D1) | host done; selfhost blocked on FeEval |
| **`Inhabited`** | — | `deriveInhabitedV` (`selfhost/Frontend.wiz:11210-11223`); `lib/Deriving.wiz:291` | — | — | done; the template |
| **lints, core** | `Wiz/Lint.lean` 821 (`registry` at `:388`: `W101`, `W102`, `W103`, `W301`, `W302`), `Wiz/Lint/Basic.lean` 143 | — | a structured view of the command (`info`/`kernelTerm`), not the text view | the package ABI is line-oriented text (`docs/lint-abi.md`); core rules read `Term`/`Info` (`linting.md` §2.8) | don't move yet |
| **lints, package** | registry + interpreter call (`Wiz/Lint.lean:529-531`) | `lib/Lint.wiz` 345 — **on `agent/lint-p2` (`bbc42d405`) only, not on train12**; rules are `String → String` over `wiz-lint/1` | fuel (no overall budget in `Run.lean`); a structured option | no `wiz lint` in the selfhost; no interpreter fuel | keep the text view for v1 |
| **tactics** | request handlers: `runTac` (`Wiz/Elab/Term.lean:4120`), 44 tags (`Wiz/Elab/Tactic.lean:38-90`) | 49 `[tactic]` registrations in `lib/` (`lib/HoareTactics.wiz` 14, `lib/SatTactic.wiz` 2, …) | new requests for new primitives; selfhost evaluation | closed `Tac` set (B2); selfhost runs no user tactic (A13) | open the frontier; do not port |
| **macros / command macros** | registration + runner (`Wiz/Elab/ProcMacro.lean`) | 15 `[macro]` registrations; `macro_rules` works in both frontends | selfhost evaluation; positions/codes (C2, C5) | same as tactics | host done; selfhost blocked |
| **backends** | 2 850 lines: C 626, Wasm 1 732, Js 240, LLVM 252 (plus the Bpf tree: 2 775 in `Wiz/Compiler/Bpf/` and 225 in `Bpf.lean`) | `selfhost/Backend.wiz` 4 022: C (`genProgram` `:2590`, `genProgramRC` `:3107`) + LLVM (`genLLVM` `:4003`, closed `main : Nat`) | a serialized IR or a `getProgram` request; a target registry | IR is a Lean inductive with `toString` only (`Wiz/Compiler/IR.lean:243,276,292`); `--target` is a closed list (`Main.lean:870`) | package/adapt first (item 5) |
| **IR passes** | 2 072 lines: `Inline` 395, `Push` 255, `Reuse` 371, `Borrow` 278, `Simp` 214, `RC` 250, `Lower` 309 | — | the same IR ABI | same | same |
| **CLI** | `Main.lean` 1 361; `Grail/*` 5 648 | `selfhost/Cli.wiz` 3 303; `grail.wiz` build files are Wiz data | nothing new | it is a process/filesystem host (shape D); no user extension point is gained | don't move |
| **doc / highlight** | `Wiz/Doc/*` 1 986; `Wiz/Doc/Registry.lean` reads `wiz.doc.languages/1` | `lib/Web/Highlight.wiz` (runtime spans), `Wiz/Doc/Highlight.lean:90` `Spec` (declarative) | nothing; languages are already data (`--languages FILE`) | the builder is host-only by design; a renderer in a package is refused | done; don't move the builder |
| **data primitives** | a name switch: `builtinNames` (`Wiz/Elab/Term.lean:184-186`), the `Unit`/`Empty`/`Qty`/`Size` case (`:3847-3853`), `mkStringLit`'s fixed `Char`/`Char.mk`/`List.cons`/`List.nil` (`:200-208`) | — (kernel has `unit`/`empty`/`qty`/`size` formers) | `[term_elab]` + `builtin unit := …`-style data | the switch itself (B1); `docs/design/README.md:9-18` names it as the reason the policy exists | open (highest value) |
| **attributes** | fixed parser list (`Wiz/Parser/Builtin.lean:342-455`; `[deriver]`, `[macro]`, `[tactic]`, `[simp]`, `[hint]`, …) | — | a general attribute hook | each new attribute is a parser rule + a match arm | open, after the registry |
| **`#` commands** | each is a `commandLeading` entry (`Wiz/Parser/Builtin.lean:342+`) | — | none, probably: `syntax` atoms grow the token table (`Wiz/Parser/Token.lean:6-8`) | unverified whether a `#`-atom lexes; see §3.3 D2 | verify, then document |

### 2.2 What the table says, feature by feature

**Derivers.** The host's `deriving` path is fully generic: `derive` looks up
`CommandState.derivers`, calls `Elab.runDeriver code f T …`, and `runDeriver` applies the
*erased* user function (`Wiz/Elab/ProcMacro.lean:165-172`). `lib/Deriving.wiz` registers
four; `Lens` a fifth. The selfhost re-implements the four in Wiz and dispatches on the
registered name; `Inhabited` is ported onto the `Deriver`/`runMacroTac` runner, but
`runMacroTac` answers only `result`, `fail`, `trace`, `fresh` and `getInductive`
(`selfhost/Frontend.wiz:11053-11063`) and reports "only getInductive is served" for
anything else. So the blocker for a user deriver is item B3 (evaluate the Wiz function),
plus the `IndView` field/param *types* (the selfhost's `Globals.view` has to delaborate
`Tm` to `Syntax`; `wishful/selfhost-deriving.md` item 1 and the "syntax-valued field
types/indices" line). Porting the other four bodies without that is parity debt, not
extensibility.

**Inhabited.** It is the existence proof and the template. It is also the one place where
a derivation *is* a Wiz metaprogram in the selfhost — but written inside the frontend, so
it is compiled, not interpreted. That is the distinction the whole note turns on.

**Lints.** Two different stories. *Package* rules are already the right shape: a pure
`String → String` over a versioned view, checked for trust sources and `partial`, run in
the interpreter (`Wiz/Lint.lean:529-531`, `docs/lint-abi.md`). *Core* rules are Lean
functions over `RuleInput`/`Term`/`Info`; the stable view is deliberately line-oriented
and does not carry a term, so they cannot move to it. `linting.md` §2.8 already decides
the selfhost gets a pinned source-level subset, not the core. The honest next step is not
"port the core lints"; it is a structured view (item 3) that both a Wiz rule and a Lean
rule can read.

**Macros and command macros.** The host's runner is general (`runMacroTac` plus
`encodeSyntax`/`decodeSyntax`, `Wiz/Elab/ProcMacro.lean`), and `macro_rules` works in
both frontends (A12 has 13 `=selfhost-macro` cases). The selfhost registers `[macro]` and
`[tactic]` but does not run their bodies (`selfhost/Frontend.wiz:10755-10770`; the
comment says "which this frontend checks but does not run"), so it is the same B3 gap.
The one *API* gap on the host is diagnostic quality: one span per message, no related
spans, codes are text (C5).

**Tactics.** Every tactic in `lib/` is already Wiz; the Lean residue is the *request
vocabulary* (`Tac`, 44 constructors) and the handlers. A new primitive tactic is a host
change because it needs a request. That is the same frontier as macros and derivers; the
fix is one generic request/response path, not 44 ports.

**Backends and IR passes.** The selfhost proves a Wiz backend is possible — for *its*
`Tm`/`Globals`, not for the host's IR. The host's IR has no serialized form; `IR.lean`
has `toString` (a human string) and nothing else. A Wiz backend therefore cannot consume
the host's program, and an out-of-tree backend cannot either. A backend port without an
IR ABI would be a second compiler, which is what `selfhost/` already is.

**CLI.** `selfhost/Cli.wiz` is the port; it is 3 303 lines and it re-implements the
closed target list with a different answer (`c`, `llvm`; `wasm` refused, `Cli.wiz:1182-
1186`). Moving `Main.lean`/`Grail` further into Wiz buys self-hosting, not extensibility;
`grail.wiz` and `Package.command` are already the extension points. Don't.

**doc / highlight.** This one is already the model to copy: a language is a declarative
`Spec` (`Wiz/Doc/Highlight.lean:90-100`), external entries are JSON with a schema
(`wiz.doc.languages/1`, `Wiz/Doc/Registry.lean:1-20`), and the runtime span assembler is
Wiz (`lib/Web/Highlight.wiz`). No language feature is missing; the builder stays host-
only because a package may not run a renderer in the host.

**The rest of the hardcoded surface.** The deepest item is not on the brief's list:
`Unit`/`Empty`/`Qty`/`Size` and the `Desc`/`μ`/`ν` table are name switches in
`Wiz/Elab/Term.lean:3847-3853` and `:184-186`, and `mkStringLit` hardcodes `Char`/
`Char.mk`/`List.cons`/`List.nil` even though the *string* type is read from
`builtins.lookup "string"` (`:200-208`). `docs/design/README.md:9-18` states the policy
this violates: "a hard-coded name switch … makes every new data primitive a compiler
change". A library can register `builtin nat := …` but cannot add a data primitive or
provide its own literal encoding. This is the item with the widest payoff: it is what
`Float32`, machine numbers, and a DSL's own literals need.

---

## 3. The blockers, classified

### 3.1 Needs a new language feature

**B1. The data-primitive / term-elaborator frontier.** `builtinNames` is a fixed list of
16 names (`Wiz/Elab/Term.lean:184-186`); the ident case turns `Unit`, `True`, `Empty`,
`False`, `Qty`, `Size` into kernel formers (`:3847-3853`); there is no `[term_elab k]`
anywhere in the tree (grep finds no `term_elab`/`TermRule`). Consequence: a new data
primitive, or a DSL that wants its own literal syntax, is a compiler change. This is the
policy document's first interface and the audit's #6 (`audit-kernel.md` §6, whose line
numbers are stale but whose sites I re-verified at the lines above).

**B2. The closed `Tac` request frontier.** `Tac` is 44 constructors
(`Wiz/Elab/Tactic.lean:38-90`; `lib/Prelude.wiz:555-644`), append-only. `MacroM` is
`TacticM`, so a macro sees the vocabulary, but `runMacroTac` rejects a tactic-only
request ("made a request … that only tactics can make", `Wiz/Elab/ProcMacro.lean:143`).
A user cannot add a request; only the host can. `user-extensions.md` §0 calls this "the
single most important limit", and the tree agrees: `getType` (22), `getSimpLemmas` (40),
`ctorNames` (41), `getHints` (43) are all one-off host additions of the same shape.

**B3. No elaboration-time evaluator in the selfhost.** `runMacroTac` is a five-case
interpreter over an already-built `Tac` value (`selfhost/Frontend.wiz:11053-11063`);
`deriveClassOn` says it outright: "the deriver … cannot be run (this frontend has no
elaboration-time evaluator …)" (`:11435-11440`). There is no `#eval` that is not
`#reduce` (`elab-evaluator-plan.md` §2), and `lib/Deriving.wiz`'s own meta API
(`Syntax.mkVar`, `Syntax.mkApp`, `Syntax.mkIdent`, `Syntax.mkStr`, `Syntax.mkNode`;
`lib/Prelude.wiz:883-893`) is absent from the embedded prelude, which has only
`Syntax.getArg`. A cheap prerequisite, before FeEval: put that meta API in the one
prelude (SH-2.0a), or the first test of FeEval fails for the wrong reason.

**B4. No serialized IR.** `Wiz/Compiler/IR.lean` defines the IR and prints it
(`:243`, `:276`, `:292`); there is no parser, no JSON, no version. `separate-repos.md`
§3.4 and `targets-ext.md` §0 already record the consequence: a package backend cannot
consume the program, and the selfhost cannot either.

**B5. No structured view for analysis.** The package lint ABI is line-oriented text
(`docs/lint-abi.md`; capabilities `decl`, `spans`, `imports`, `globals`, `messages`,
`facts`), and the unstable views (`info`, `tactics`, `kernelTerm`, `sourceText`) are
refused for a package set (`Wiz/Lint/Basic.lean:49-101`). That is the right v1, but it
means a core rule like `W101` (unused binder) cannot be expressed as a Wiz rule: it
walks the elaborated term. A second problem is size: a text view of a term is not an
ABI anyone should pin. The related reflection limit is depth, not existence: `Expr`
carries `opaque` handles, and typed reflection recovers a constructor application only
where the type is known (`Wiz/Elab/Tactic.lean:209-224`) — enough for tactics, not for a
rule that must see inside a definition body.

### 3.2 Needs a convention or an API

**C1. One entry model for registries.** `Wiz/Ext/` does not exist (verified: no such
directory). The only registry-shaped ABI is `Wiz/Lint/Basic.lean:49` (`Capability`) plus
`Wiz/Lint.lean:388-390` (the rule array), and `targets-ext.md` §0 already says it is the
right shape to copy. A backend, a lint set, a doc language and a future
`[term_elab]` should all be `(kind, name, schema, abi, payload)` entries resolved by
one function (discovery is by manifest or by import, per kind), with one set of refusal
codes, not four ad-hoc lists.

**C2. A versioned meta ABI and a conformance corpus.** The metaprogram ABI is
`SyntaxF` (a flat constructor encoding, plus two hidden range fields), `IndView`, `Expr`
(with `opaque` handles) and `Tac`. It has no version marker and no test that the host and
the selfhost agree on a *corpus*. The drift is already real: the selfhost accepts a
one-argument function of any type as a deriver (arity only, `selfhost/Frontend.wiz:10843-
10847`), the host unifies its type with `Deriver` (`Wiz/Elab/Command.lean:3707-3713`),
and the dispatch is by name (D1). A `wiz-meta/1` marker and a dozen shared meta programs
would catch this class cheaply.

**C3. A general attribute hook.** `attribute [foo] f` is a fixed parser list
(`Wiz/Parser/Builtin.lean:417-444`). HDL needs `attribute [hdl top]`; a DSL will need
its own. The registry can carry the table; the parser needs one generic rule.

**C4. Interpreter fuel.** `Wiz/Compiler/Run.lean`'s `run` has no overall step budget
(local fuel appears only in list printing, `:342`, `:410`, `:629`, `:734`). The lint
registry rejects `partial` (`Wiz/Lint.lean:633`) but a total function can still
diverge; `linting.md` §2.5 promises a step/fuel budget and lists it as a follow-up. Any
package-supplied code path needs it *before* it is enabled by default.

**C5. Error reporting is one span and one message.** `Msg` carries `info`, `severity`,
`text` and a `code` (`Wiz/Elab/Command.lean:46-52`), and a macro can place an error at
one *input path* with `Syntax.errorAt`/`infoAt`/`sourceAt` (`Wiz/Elab/ProcMacro.lean:174-
183`). The selfhost's `Diag` has the same shape (`selfhost/Cli.wiz:372`: severity, file,
line, column, message, code). There is no related-span list and no way to emit several
errors from one macro invocation, which is exactly what a DSL front end needs
(`wishful/command-proc-macros.md` items 1–2: "borrow errors must point at the use, the
move and the borrow"; "more than one error per block"). Cheap in fields, but only worth
doing with a consumer; fold it into Item 3's info channel rather than making it its own
item.

### 3.3 Cheap, do now

**D1. The deriver name hijack.** The selfhost records `deriverBase f` (the name without
`Derive.`) and later dispatches by that name (`selfhost/Frontend.wiz:10802-10819`,
`:11435`). The fix is a registration-time decision: a name that resolves to a
*declaration* is a user deriver and must not match a built-in; record that flag (or
refuse with a code until FeEval). No new feature, ~10 lines, and it removes a silent
host/selfhost divergence. (The host is already right: it stores the `Name` and runs the
declaration.) `Compare` makes the point sharper: `lib/Compare.wiz:30` declares the
class, but `lib/` registers **no** `Compare` deriver (grep: no `deriveCompare`), so the
frontend's `deriveCompare` body (`selfhost/Frontend.wiz:11320`) is reachable only by a
user declaration that happens to use that name — and then it replaces the user's body.

**D2. `#` commands are probably already extensible.** The parser is scannerless and the
token table grows from `syntax` declarations (`Wiz/Parser/Token.lean:6-8`); an `atom` is
just a trimmed string (`Wiz/Parser/SyntaxCmd.lean:57-60`), and `#check`/`#plot` are
ordinary atoms in the table. So `syntax "#verilog" ident : command` very likely lexes
today. I did not run a probe (no build in this lane); the probe is one `wiz check` on a
five-line file. If it works, HDL's `#verilog` is a *documentation and command-body*
problem, not a parser feature, and the older audit's "a `#` word is not user-declarable"
is stale.

**D3. Document the `syntax … : command` path.** The parser comment is explicit that
`command` is the extensible category and `import` is deliberately not a rule
(`Wiz/Parser/Builtin.lean:290-300`). A one-page "how to add a command" (with the
`macro_rules` expansion rules and the `local` scope) would move several DSLs off the
"needs a compiler change" list with no code.

---

## 4. Ordered plan

Five items. Each states the change, the smallest acceptance test, the risk, and what it
is a foundation for. The order optimises *interfaces that unlock several feature
classes* over one-off ports; §5 records what was rejected and what would reorder it.

### Item 1 — One entry model, fail closed (registry + the deriver fix)

**Change.** Add `Wiz/Ext/Basic.lean` (`Entry`, `Capability`, `ArtifactKind`,
`Diagnostic`) and `Wiz/Ext/Resolve.lean`: one table, one resolver, conflict and
capability refusals *before* anything runs. Convert `--target` first (`Main.lean:870`,
`takeTarget` `:891-912`, `Build.build`'s booleans `Wiz/Compiler/Build.lean:267-268`) so
`targets-ext.md` §7's slice is the proof. In the same PR, fix D1 in the selfhost: a
registered deriver is either a built-in or a user declaration, never a name.

**Smallest acceptance test.** Two halves. (a) `=selfhost`'s A11 cases stay green, plus a
new case where `attribute [deriver BEq] myBEq` with a body that throws "user" is either
refused at registration with a code or reports "user" at `deriving` — not the builtin
instance. (b) A manifest-declared `demo` target resolves and builds without an edit to
`Main.lean`; unknown, not-enabled and undeclared-capability entries each refuse with a
stable code; `=backend` and `=cli` are unchanged. `targets-ext.md` §7 has the exact
slice; do not re-design it here.

**Risk.** The enabled set must enter the cache key or a cached module can use a target
the run did not enable; a per-kind branch can sneak back into `Main.lean` (the fifth-
target bug class, §1 of `targets-ext.md`). Mitigation: one resolver function, and the
refusals are data.

**Foundation.** Yes: every package-facing kind (backend, lint set, doc language,
attribute kind, future term-elaborator pack) is an entry. It is also the cheapest item
and the only one that needs no evaluator. **Recommendation:** decouple `CORE-3.3` from
`SH-2.1` in `roadmap/program-next.md`; the selfhost may refuse non-core entries by name
until FeEval, which is fail-closed.

**Implemented** on `agent/ext-registry`: `Wiz/Ext/Basic.lean` + `Wiz/Ext/Resolve.lean`,
`--target` as five rows/six spellings, the D1 selfhost fix, and the cache-key change.
`wiz-notes/ext-registry.md` records what is data, what is still a Lean branch, the exact
refusal codes and the manifest gap (`Package.command` is a build-graph node, not a
backend entry).

### Item 2 — Term elaborators and the data-primitive table

**Change.** Add `[term_elab k]` (`TermElab := Syntax → TacticM Unit`) dispatched in
`check` after `expand?` and before the built-in kinds, and in `infer` with a fresh meta,
as `user-extensions.md` M1 designs; the handler builds a term with the existing `Expr`
requests. Then make the primitive table data: `builtin unit := Unit`, `builtin char :=
Char`, `builtin list := List` (the string type already has a key), and delete
`builtinNames` for those names. This is B1. Do *not* try to make `unit`/`empty`/`qty`/
`size` themselves library-defined in the same step; the kernel formers stay, the
*spelling* becomes data.

**Smallest acceptance test.** `=elab`: a library declares `syntax "τ" : term` and
`[term_elab term.τ]` a handler that assigns `Nat`; `#check (τ : Nat)` passes and an
unrelated `τ` still fails. `=reject`: an unknown `[term_elab]` kind is refused. A second
case registers `builtin char := MyChar` and a string literal elaborates to
`String.mk (List MyChar)`; the existing `Unit`/`Empty`/`Qty`/`Size` cases in `=elab` are
byte-identical before and after.

**Risk.** Re-entering elaboration from a tactic (nested goals, `assignLate`, error
positions, scopes, LSP info trees); the `local` allow-list and the cache `Effect` field
must be decided. `user-extensions.md` estimates 4–8 agent-days for the dispatch; the
primitive table is another slice. Medium-high risk, but the audit already names
`elabBy` (`Wiz/Elab/Term.lean:4604`) as the machinery.

**Foundation.** Yes, for every DSL: this is the policy's "data-driven term elaborator"
and it is what stops a new data primitive from being a compiler change. It is host-side,
so it needs no FeEval.

### Item 3 — A structured view as a request (analysis)

**Change.** Add one capability-scoped view (a `wiz-lint/2` section or a new
`wiz-info/1`): per declaration, binder facts with the *term head* and its arity, and the
`Info` nodes a rule may read; not a text blob. Wire it through the lint registry as a new
stable-or-`abi`-pinned capability and through a `Tac` request for tactics. This is B5;
`lint-p2`'s commit message already names "the projected `info`/`termView` view" as the
follow-up.

**Smallest acceptance test.** `=wiz-lint`: a W5xx rule reads the structured view and
reports one finding the text view cannot express (e.g. a binder whose type head is a
given constant); its expected message is checked. Then re-express core `W101` as a Wiz
rule over the same view; `=wiz-lint`'s goldens are unchanged and `W101`'s Lean body is
deleted. If the second half is too large for one slice, keep it as the ratchet.

**Risk.** This is the ABI that must not churn: a term-shaped view leaks the kernel's
representation, and a text-shaped view is what we are replacing. Mitigation: version it,
cap it by capability, and keep `opaque` handles for everything the view does not name
(the `Expr` precedent, `Wiz/Elab/Tactic.lean:209-224`). Size and cache cost are real.

**Foundation.** Yes: lints, hints, code actions, widgets and any term-level rule read
this. It is also the input a term elaborator needs when it must inspect an elaborated
value rather than only syntax.

### Item 4 — FeEval core, on a measured acceptance (selfhost)

**Change.** Implement `selfhost/FeEval.wiz` per `elab-evaluator-plan.md` §3: `EvalEnv`,
encoders/decoders over `Syntax`/`String`/`Nat`/`List`/`IndView`/`Expr`, `whnfE` with
stuck-head repair, the request loop, and the `proofStart` budget as fuel. It is gated by
two prerequisites that are cheaper and independent: SH-2.2's kernel literals (the plan
measures ~19 s for a 40-element list literal with unary `Nat`, versus ~0.02 s for the
host's `#reduce`) and the meta API in the one prelude (B3, cheap). Delete the four
hand-written bodies only after the library derivers run.

**Smallest acceptance test.** A `=selfhost` case (or a `=selfhost-libdiff` ratchet move)
where a deriver declared in a *test module*, using only the supported meta API, is
registered and run by the selfhost: `deriving Inhabited` produces the same instance text
as the host. The stretch acceptance is `lib/Deriving.wiz` moving from `diverging` to `ok`
in `Tests/libdiff-baseline.tsv` (its cause row today is `meta-api`: "no elaborator-time
`Syntax` API in the embedded prelude"). A budget-exhaustion case reports the step limit,
not a hang.

**Risk.** Large (a quarter in the plan's own sizing) and performance-sensitive; the
kernel-literal change is a kernel change; R1 in `program-next.md` says the prelude-
unification branch may be refused, which would leave the evaluator running against a
second prelude. Keep the acceptance on a test module first, not on `lib/`.

**Foundation.** Yes, for every Shape-B extension under the selfhost: derivers, macros,
tactics, lint rules, `[term_elab]`. It is the *only* item that makes the moved library
code run in the self-hosted product. **Do not** gate Items 1–3 on it.

### Item 5 — `wiz-ir/1`, the serialized IR

**Change.** Define a versioned document for `Wiz/Compiler/IR.lean` (the types are 339
lines; they already derive `Repr`), emit it from a new `wiz ir`/`--emit-ir` path, and
write `lib/Ir.wiz` (pure Wiz: parse, print, one pass). Then a backend is an entry from
Item 1 whose payload reads the document; a Wiz backend does not need to be linked into
the Lean process. This is B4, and it is what makes a backend a *package* rather than a
Lean module.

**Smallest acceptance test.** A checked-in `Tests/fixtures/ir/one.ir` round-trips through
`lib/Ir.wiz` byte-identically; the Lean emitter produces exactly that file for the same
source (one `=backend` fixture); a `demo` target entry from Item 1 consumes it and
writes its artefact. Then one pass (`Inline` or `Push`) reimplemented in Wiz produces the
same document as the Lean pass on the existing `=backend` corpus.

**Risk.** The IR is internal and moves; `RC`/borrow annotations are the hard part; a text
format's parse cost is a real budget. Version it and refuse an unknown major. Note the
`bpf` target already has the opposite design (`bpf-core/1` input, not the IR); the two
schemas must be siblings, not one schema.

**Foundation.** Yes, for backends and every IR pass; also the second consumer of the
registry, so it tests whether Item 1's entry model really fits a second kind.

### Dependencies, in one line

```
Item 1 (registry) ──┬─> Item 5 (IR) ──> package backends
                    └─> Item 2 (term elab) ──> Item 3 (view)
Item 3 (view) ──> Item 4 (FeEval)   [FeEval must answer the view's request]
Item 2 ──> Item 4                    [same prelude/meta API]
```

Items 1 and 2 are independent and can run in parallel; Item 3 needs Item 2's dispatch
only if the view is exposed to a term elaborator (a lint-only view does not). Item 4
needs Item 3's request settled and Item 2's prelude decision; Item 5 needs Item 1 for
discovery but not for the round-trip test.

### What would reorder this

* **If the selfhost is the product and the host is a bootstrap:** Item 4 first, Items 1–3
  after. Then the evaluator should be built against the *current* ABI and Item 3's view
  becomes a follow-up request.
* **If a package backend is the next real user (eBPF/WebGPU):** Item 5 before Item 2;
  Item 1 unchanged.
* **If R1 fires (the prelude-unification branch is refused):** Item 4 slips; Items 1–3
  are host-side and unaffected. That is the strongest argument for the order above.
* **If a probe shows `syntax "#foo"` already works (D2):** HDL's command gap is a
  documentation task; Item 2 can be scoped to data primitives only.

---

## 5. Alternatives considered and rejected

| alternative | why rejected |
|---|---|
| **Port the four deriver bodies into the frontend (SH-2.3 as written), before FeEval** | It deletes special cases but adds ~400 lines of core Wiz and does not let a user deriver run; the host would still be the only toolchain where `lib/Deriving.wiz` is real. It is parity debt, not extensibility. Do it only if FeEval is refused. |
| **Move the CLI (`Main.lean`/`Grail`) to Wiz** | 7 000 Lean lines, no user extension point gained; `grail.wiz` and `Package.command` are already the package story. Self-hosting goal, not this priority. |
| **Move the doc builder / LSP server to Wiz** | Shape D in `user-extensions.md` §0. The *languages* are already data and the *runtime* is already Wiz; a package may not run a renderer or tokeniser in the host (`docs-highlighting.md`). |
| **Move the core lints to Wiz now** | The stable view is text and the core rules read `Term`/`Info`; `linting.md` §2.8 deliberately pins the selfhost to a source-level subset. Wait for Item 3, then re-express one rule as the acceptance. |
| **A single untyped `Tac.hostRequest (kind) (payload)` as the first step** | It would work, but it makes the request frontier an untyped backdoor and undermines the capability model that the lint registry just established. Item 3's structured view is the same need with a schema and a capability list; do that first, then generalise. |
| **Gate `CORE-3.3` (the registry) on `SH-2.1` (FeEval)** | Resolution, conflicts and refusals are host-side; payload execution is per-kind. A registry that refuses a Wiz-rule entry by name until FeEval is fail-closed and lets every host-side feature ship. See §4, item 1. |
| **Add a `wiz-ir/1` from `#ir`'s human string** | `#ir` prints a pretty term (`IR.toString`), not a parseable document; a format must be designed with a parser and a round-trip test, not scraped from a printer. |

---

## 6. What I verified, and how

**Read in the worktree** (all citations above; the ones with line ranges were re-read at
those lines, not taken from the audit):

* `selfhost/Frontend.wiz`: `deriverKind` `:10806-10819`; `deriverCmd` `:10832-10847`;
  `runMacroTac`/`runDeriver` `:11053-11064`; `deriveInhabitedV` `:11210-11223`;
  `deriveInhabitedR` `:11427-11430`; `deriveClassOn` `:11435-11440`; `tabStep` `:10755-
  10770`; `expandNotes`/`tabStep` use `:11752-11760`. The four bodies span
  `:11142-11424`; the audit's `10906-11434` range is real (529 lines, arithmetic
  checked) but includes the helpers (`deriveShape` at `:10906`, `DBuild`, `eqAlts`, …),
  so it is not "the four derivers".
* `Wiz/Elab/Command.lean`: deriver registry `:138-141`, `mkMetaCode` `:1526`, `derive`
  `:2193-2210`, `attrDeriver` type check `:3707-3713`.
* `Wiz/Elab/ProcMacro.lean`: `runMacroTac` `:124-142` (the tactic-only refusal is `:143`),
  `runDeriver` `:165-172`.
* `Wiz/Elab/Tactic.lean`: `TacTag` `:38-90` (0–43; the audit's "39 constructors 0–38"
  is stale by five tags). `Wiz/Elab/Term.lean`: `runTac` `:4120`; `builtinNames`
  `:184-186`; `mkStringLit` `:200-208`; the `Unit`/`Empty`/`Qty`/`Size` case
  `:3847-3853`; `elabBy` `:4604`.
* `lib/Prelude.wiz`: `Tac` `:555-644`; `TacticM` `:646`; `Deriver` comment `:901`;
  `Syntax.mk*` `:883-893`.
* `Wiz/Lint.lean`: `registry` `:388-390`; `callRunner` `:529-531`; `checkSet` trust/
  `partial` checks `:633`; the package driver `:667-706`. `Wiz/Lint/Basic.lean`:
  `Capability` `:49`, `packageCapability` `:91-102`.
* `Wiz/Compiler/IR.lean`: `toString` `:243`, `:276`, `:292`. `Wiz/Compiler/Build.lean`:
  `build` `:267-268`. `Main.lean`: `targets` `:870`, `takeTarget` `:891-912`, `buildCmd`
  `:914-960`.
* `selfhost/Cli.wiz`: `targetModes`/`targetOk`/`targetKnown` `:1182-1186`; the parse
  `:1277-1282`.
* `Wiz/Doc/Highlight.lean`: `Spec` `:90-100`. `Wiz/Doc/Registry.lean`: the schema and
  checks `:1-20`. `lib/Web/Highlight.wiz`: the runtime assembler (module docstring).
* `Wiz/Parser/Builtin.lean`: `commandLeading` `:342+`; the attribute rules `:417-444`;
  the `command`-is-extensible comment `:290-300`. `Wiz/Parser/Token.lean`: scannerless,
  growing token table `:6-8`. `Wiz/Parser/SyntaxCmd.lean`: `stx.atom` `:57-60`.
* `Wiz/Compiler/Run.lean`: `run` `:477`; the only `fuel` uses are local (`:342`, `:410`,
  `:629`, `:734`).

**Verified by git, not by eye:**

* `lib/Lint.wiz` is **not** on `train12`: `git merge-base --is-ancestor bbc42d405 HEAD`
  is false; `Wiz/Lint.lean` (`b636c984d`) *is* an ancestor. The brief's "`lib/Lint.wiz`
  and `Wiz/Lint*` just landed" is right about `Wiz/Lint*` and premature about
  `lib/Lint.wiz`.
* `Tests/libdiff-baseline.tsv` has `lib/Deriving.wiz<TAB>diverging`, and
  `scripts/libdiff-causes.tsv` gives its cause as `meta-api` ("`Syntax.mkVar`; no
  elaborator-time `Syntax` API in the embedded prelude") — the reason Item 4's first
  test must be a test module, not `lib/`.

**Counted:** `[tactic]` 49, `[macro]` 15, `[simp]` 44, `[deriver]` 5 in `lib/`;
`attribute [hint]` 0 in `lib/` (tests only); backends 2 850 lines + the Bpf tree
(2 775 + 225); IR passes 2 072; `selfhost` 27 770 Wiz lines.

**Not verified (no build in this lane):**

* D2: whether `syntax "#verilog" ident : command` actually lexes. Reading says yes
  (scannerless, atoms from the table); one `wiz check` probe would decide it. I did not
  run a build, and using another worktree's binary would be a stale-kernel probe.
* D1's behaviour as *executed*: the code path is explicit (`deriverKind` on the
  registered name), but I did not run a case. The fix is cheap either way.
* Any performance number. The 19 s / 0.02 s figures are quoted from
  `elab-evaluator-plan.md` §1; this lane measured nothing.

---

## 7. References

* `wiz-notes/user-extensions.md` — the shape taxonomy and per-point audit (older tree).
* `wiz-notes/targets-ext.md` — the target/entry design; §7 is Item 1's first slice.
* `wiz-notes/separate-repos.md` §3 and "Shared extension model" — the canonical entry
  model; §3.2(a) is the backend row.
* `wiz-notes/refine-platform.md` §1 — the cross-plan table.
* `wiz-notes/elab-evaluator-plan.md` — FeEval design and its measurement gate.
* `wiz-notes/linting.md` §2.5–2.8 — the lint ABI, fuel, and the selfhost decision.
* `wiz-notes/wishful/selfhost-deriving.md` — the deriver gaps, item by item.
* `wiz-notes/selfhost-parity.md` A11–A13 — the current parity state.
* `docs/design/README.md` — the Lean-extensibility policy sentence.
* `docs/lint-abi.md` — the stable view, as shipped.
* `docs/stages/30-selfhost-typeclasses.md` §30b — the Inhabited port.

---

## 8. Item 2 as implemented (`agent/ext-term-elab`)

**Status.** Implemented on `agent/ext-term-elab` from `integration/train12` `6e5924cd8`;
this section is the branch's record. §1–§7 describe the research tree (`25c503002`).

### 8.1 `[term_elab k]`: dispatch point and ABI

`TermElab := Syntax → TacticM Unit` is declared in `lib/Prelude.wiz`, next to `Tactic`.
`attribute [term_elab k] f` is a registry entry — `AttrAction.termElab`, payload `.name`
— parsed by the existing generic `command.attr` rule, so no parser rule and no new
`elabCommand` kind. The command refuses a `k` that is not a declared syntax kind
(`unknown-syntax`: ``attribute [term_elab term.nope]: unknown syntax kind 'term.nope'
(declare it with `syntax … : term`)``) and a target whose type is not `TermElab`
(`… is not a term elaborator: …`). A registration prepends `(k, f)` to
`CommandState.termElabs` (latest first), is threaded through `runElab`/`ElabState`, and
adds `f` to the interpreter roots (`mkMetaCode`).

Dispatch:

* `check ctx stx expected`: after `expand?` and before `checkData?`/`checkOther`'s
  built-in kind switch (`Wiz/Elab/Term.lean`). A handler registered for a built-in kind
  therefore wins over it; the note's "before the built-in kinds" is literal.
* `infer ctx stx`: after `expand?`, with a fresh type metavariable (`freshTypeMeta`), so
  an un-ascribed `#check τ` works instead of failing.

`elabTermElab?` makes one goal — a fresh meta of `expected` (`infer`: of the fresh type
meta) — runs `f stx` through `TacticM.run` in the interpreter, and then applies
`elabBy`'s end checks: every goal it leaves must be solved, and an `assign` whose term
still had holes is type-checked once they are solved. The result is the goal's meta.
The handler uses the existing `Tac`/`TacticM` requests (`mainGoal`, `elabInfer`,
`assign`, `newGoal`, `exact`, …) and `Expr` (`Expr.const`, `Expr.mkApp`, …); it must not
re-elaborate its own node (`TacticM.exact g` of the same `τ` recurses, exactly as a
tactic that `evalTactic`s itself does).

### 8.2 `local` and the cache `Effect`

* **`local`: refused, allow-list unchanged.** `Command.lean`'s `command.local` admits
  only no-op attributes; `termElab` is semantic like `[tactic]`/`[deriver]`, so
  `local attribute [term_elab k] f` gets the existing "only a no-op attribute can be
  `local`; 'term_elab' has an effect that outlives its module". No `localTermElabs`
  list exists.
* **Cache `Effect`: no new field.** `attribute` is deliberately absent from
  `Cache.cacheable`, so a module's registration is replayed (re-elaborated) before its
  cacheable declaration effects, as `[tactic]`/`[macro]` are; a cached declaration is
  never replayed under a different term-elaborator table. The registration is in the
  per-command content-hash chain (`Wiz/Query.lean`), and the isolated-module key
  (`Frontend.isoKey`) now includes the starting `termElabs` with `attrDecls`/`optDecls`,
  so a custom initial state cannot reuse a module elaborated under another one. The
  registration is re-run in the replay path, which is what makes that key sound. **If
  `attribute` ever becomes cacheable, `Effect` needs `termElabs` (and a region-format
  bump)**, or the importer's table would be applied to cached declarations. Being
  non-cacheable is what keeps it correct, not "no effect".

### 8.3 The data-primitive spellings

`builtin` now accepts `unit`, `empty`, `qty`, `size`, `char`, `list`
(`command.builtin`/`builtinShapeError`). The elaborator reads them:

* `infer`'s ident case: `Unit`/`Empty`/`Qty`/`Size` are the fallbacks; a registered
  spelling is accepted with or without `.{l}`. The kernel formers
  (`.unit`/`.empty`/`.qty`/`.size`) are untouched.
* `mkStringLit`: `S.mk (L.cons C (C.mk n) … L.nil C)` with `S`/`C`/`L` from
  `builtin string`/`char`/`list` (fallbacks `String`/`Char`/`List`).
* the pretty printer (`Wiz/Core/Pretty.lean`) follows the table, so `#check` shows
  `MyUnit`/`MyQty`/…, not the old spellings.
* `unit`/`empty`/`qty`/`size` need no declaration (`Unit` has none); `char`/`list` must
  name inductive types (a parameterized former, as `List` is, is peeled through its `Π`
  type and `λ` value to the sort and the `μ`) and `list` must have `nil`/`cons`. None is
  an axiom (`assumed`): no unfolding is claimed, unlike `builtin nat.*`.

`builtin char := MyChar` is supported where the definitional-equality layer allows it:
the literal's type is `MyString.mk (List MyChar)` when the `builtin string` type's `mk`
takes `List MyChar`. With the default `String` (`mk : List Char → String`) there is no
coercion between `List MyChar` and `List Char`, so the literal reports it at the
literal: ``string literals: String.mk takes List Char, but `builtin char`/`builtin list`
build a list of MyChar with List; register a `builtin string` whose constructor takes the
same (there is no coercion)``.

The six keys are **not** registered by `lib/Prelude.wiz`: the old spellings stay as the
elaborator's fallbacks, so a library may register its own (`builtin char := MyChar`
would otherwise be "already registered"), and `string` stays one-shot for the native
readback (`Wiz/Compiler/Run.lean`). A package with its own prelude registers its own.
Each key is registered **once per import chain**, like `builtin string`/`nat`: two
modules that both register `char` with different types make the importer reject the
second, fail-closed rather than silently picking one.

### 8.4 What remains hard-coded

* `True`/`False` (level-0 aliases of `Unit`/`Empty`) keep fixed spellings; no keys were
  added for them.
* `builtinNames` (`Term.lean`) is still the fixed `Desc`/`μ`/`ν`/`con`/… list. Those
  are syntax forms with kernel meaning, not data primitives, and are outside this item.
* `builtin nat` and the numeral path, `Qty`/`Size`'s kernel formers, and the `Bool`/
  `Int`/`UInt64`/`Float64` library types are unchanged.
* The self-hosted frontend does not know `[term_elab]`: its `attrStep` is a fixed
  `inline` case plus the host's built-in names, and its `runMacroTac` is the
  five-request loop. A library that registers one is host-only until FeEval (Item 4);
  the selfhost's refusal is fail-closed with the rest of the unknown attributes.
