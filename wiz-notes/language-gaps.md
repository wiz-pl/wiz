# Language gaps: Lean+Wiz extension points after the ext lanes

**Status.** Research lane `research-language-gaps`, 2026-11-23. Tree
`/workspace/wt/research-language-gaps` at `f489cc876`
(`integration/train12`). This note is static reading only: no build, no test run, no
product-code edit. Every `file:line` is at `f489cc876` unless it names a lane branch.
The lane worktrees were read at their current state on 2026-11-23; two are mid-edit and
three are empty (below).

**Canonical copy.** `/workspace/wiz-notes/language-gaps.md`; this branch commits the
same text at `wiz-notes/language-gaps.md`.

**Question.** `wiz-notes/extensibility.md` (`25c503002`) answered *which interfaces to
open, in what order*. Two of its five items are now being written (`agent/ext-registry`,
`agent/ext-term-elab`), and the other three have worktrees but no code. This note
refreshes the inventory at `f489cc876`, states what the in-flight lanes actually buy,
and names the three gaps that remain after Items 1–5.

---

## 0. Verdict

1. **The host has two new, real extension points; neither is a package extension
   point yet.** `--target` is now a resolved entry rather than a string
   (`agent/ext-registry`), and a library can register a Wiz term elaborator and rename
   the data-primitive spellings (`agent/ext-term-elab`). But the registry has no
   manifest reader, and the term elaborator is registered directly in
   `CommandState`, not through `Wiz/Ext`. A package still cannot install either one.

2. **The five "ext" worktrees are not five lanes in flight.** `ext-registry` and
   `ext-term-elab` contain code (both based on `6e5924cd8`, both uncommitted).
   `structured-view`, `ir-abi` and `feeval-core` are at `f489cc876` with clean trees and
   no commits. Items 3–5 are still designs.

3. **The policy scorecard at the host is about 3.5 of 4.** The four interfaces
   `docs/design/README.md` names are: data-driven term elaborators (partial: dispatch
   and spellings, no new primitives), user-extensible `deriving` (done; the host runs
   the registered Wiz function), hygienic macros (done), and `simp only`-style explicit
   lemma sets (done). The registry that would make them package-level is a separate
   shape and is partial: targets only.

4. **The next three gaps are registration, discovery, and ABI**, in that order of
   *value*: (G1) route the elaboration kinds through `Wiz/Ext` with kind-scoped
   capabilities, purity and a step budget; (G2) package discovery and signed
   enablement (the missing reader for Item 1's table); (G3) freeze `wiz-meta/1` and add
   the host/selfhost conformance corpus. G1 is also the first thing to *start*, because
   `agent/ext-term-elab` already exposes the risk (arbitrary package Wiz code in the
   elaborator, no budget, no capability).

5. **The selfhost is host-only for every Shape B/C point until FeEval.** That is not a
   bug in the registry: resolution is host-side and the selfhost's refusal is
   fail-closed. The consequence for the decision is sharper than the earlier note:
   **port** a Shape B body to the selfhost and you buy parity, not extensibility;
   **open** the host interface now and pay a pinned divergence; **package** a data-only
   entry early, but a code entry is host-only until FeEval. If `SH-2.0a`/`SH-2.1` are
   refused (R1 in `roadmap/program-next.md`), that split is the product, not a delay.

---

## 1. What changed since `extensibility.md`

The earlier note was written at `25c503002`. The refresh matters: several statuses in
`user-extensions.md` (`e3bd36ff`) are stale by two trains.

* **`lib/Lint.wiz` is on the tree now.** It is 345 lines and `bbc42d405` is an ancestor
  of `f489cc876`; the earlier note correctly said it was not on its tree. It is a typed
  wrapper over `wiz-lint/1` (`Lint.Command.parse`, `Lint.Finding`), not a rule set, so
  the package-lint *interface* is still `Wiz/Lint.lean` + `docs/lint-abi.md`, and the
  core rules still read `Term`/`Info`.
* **The selfhost's A12 first milestone landed.** `syntax`, `notation`,
  `macro_rules`, `infix` and `declare_syntax_cat` are implemented in
  `selfhost/Frontend.wiz:10737-10818` (`tabStep`), with the host's rule shape, token
  table and hygiene. `docs/stages/21-bootstrap.md` §21ac records the boundary: keyword
  scopes and `local notation`/`local macro_rules` are not tracked, and `[macro]` /
  `[tactic]` bodies still do not run. The old "syntax/macro_rules missing" status is
  stale.
* **`simp` is implemented, not planned.** `lib/Prelude.wiz:1613-1651` has `simp`,
  `simp [..]`, `simp only [..]`, `simp?`; `[simp]` has 47 lines in `lib/`, and
  `Tac.getSimpLemmas` is a request (`Wiz/Elab/Tactic.lean:84`). `docs/stages/06-macros.md`
  §6h is the design. The selfhost has no `simp` tactic.
* **`TacTag` is 45 tags (0–44), not 39/44.** `getOpen := 44` is the newest
  (`Wiz/Elab/Tactic.lean:92`). The closed frontier grew; the ABI did not open.
* **`agent/ext-registry` exists but is not committed.** 15 staged files plus unstaged
  fixes; it adds `Wiz/Ext/{Basic,Resolve}.lean` (242 + 227 lines), converts `--target`
  to five rows/six spellings, puts the backend into `Toolchain.id`/`targetTag`, fixes
  D1 in the selfhost, and adds 13 `=ext` cases. It does **not** add a manifest reader.
* **`agent/ext-term-elab` exists but is not committed.** It adds
  `[term_elab k]` (`TermElab := Syntax → TacticM Unit`), `AttrAction.termElab`, six
  `builtin` spellings (`unit|empty|qty|size|char|list`), the string-literal encoding,
  and 8 `=elab` + 3 `=reject` cases. It does **not** touch the selfhost, and it
  registers in `CommandState.termElabs`, not in `Wiz/Ext`.
* **`docs/design/README.md` is updated on the `ext-term-elab` branch**: the hard-coded
  switch is now `Desc`/`μ`/`ν` + `True`/`False`, with `Unit`/`Empty`/`Qty`/`Size` as
  `builtin` fallbacks. On `f489cc876` the old sentence (which lists all four) is still
  there; the lane's version is the accurate one once it lands.
* **The other three lanes are empty.** `structured-view`, `ir-abi` and `feeval-core`
  have `HEAD = f489cc876`, no commits, no modified files, no `Wiz/Ext`, no
  `selfhost/FeEval.wiz`. Any statement about Items 3–5 below is about the design, not
  about code.

Counts used in the table, measured at `f489cc876`: `lib/Deriving.wiz` 467 lines with 4
`[deriver]` registrations, plus `lib/OpticDerive.wiz`'s `Lens`; 50 `[tactic` lines;
15 `[macro` lines; 47 `[simp` lines; 5 registration pairs for derivers; `TacTag` 45.

---

## 2. The refreshed inventory (the 19 points)

The row numbers are `user-extensions.md` §1's list, refreshed. **Status is about the
*extension point*, not the feature**: `done` means a user can add a new instance of the
class without a host change on that toolchain; `partial` means only some classes, some
payload shapes, or one toolchain; `open` means there is no user point (or the selfhost
has none). `host`/`selfhost` qualify every status because the two toolchains disagree on
almost every row.

`†` = only on `agent/ext-registry` (uncommitted). `‡` = only on
`agent/ext-term-elab` (uncommitted).

| feature | Lean today | Wiz today | extension point | what still forces a host change | status |
|---|---|---|---|---|---|
| 1. `syntax`, `declare_syntax_cat`, `notation`, `infix*` | Full user grammar; parser is extensible | Host: complete; the library's DSLs (Feral, Hoare, Logic, …) use it heavily. Selfhost: A12 first milestone (`selfhost/Frontend.wiz:10796-10818`); keyword scopes and `local notation`/`local macro_rules` not tracked (`docs/stages/21-bootstrap.md` §21ac) | Parser tables + `macro_rules` (data) | A new parser combinator or a new *kind* of expansion; selfhost keyword scopes | done (host) / partial (selfhost) |
| 2. `macro_rules` | Hygienic `macro_rules`, quotations, `$[…]` repetition | Host: complete. Selfhost: real rules, quotations, hygiene; no repetition; `local` rules stay visible | `macro_rules` (data) | Repetition patterns and `local` scoping; the selfhost's table update | done (host) / partial (selfhost) |
| 3. procedural macros `[macro k]` | `[macro]`, `MacroM`, `Syntax`; user code | Host: complete; 15 `[macro]` lines; `MacroM`/`IndView`/`Syntax.mk*`. Selfhost: checks the declaration, does not run the body (`runMacroTac`, `selfhost/Frontend.wiz:11113-11121`) | `[macro k]` + `MacroM` | A new `Tac` request; FeEval for the selfhost | done (host) / open (selfhost) |
| 4. command macros `[macro command.k]` | `macro_rules` for commands / `elab_rules : command`; user code | Host: complete (`CommandMacro`, `Syntax.errorAt/infoAt/sourceAt`). Selfhost: command `macro_rules` work; `[macro]` command bodies do not | `[macro command.k]` + command syntax | A new request or diagnostic shape; FeEval for the selfhost | done (host) / partial (selfhost) |
| 5. tactics `[tactic k]` | `elab_rules`, `TacticM`; the monad *is* the open request set | Host: complete; 50 `[tactic` lines; `TacTag` 45 (0–44) is a closed append-only enum. Selfhost: no user tactic runner (A13) | `[tactic k]` + `TacTag` | Every new primitive request; the selfhost's `STac` set and FeEval | partial (host: open, but closed requests) / open (selfhost) |
| 6. attributes + `set_option` | `register_attribute`/`register_option`; `[simp]` etc.; user code | Host: `register_attribute`/`register_option` for no-op attributes; `AttrAction` has 11 semantic actions (`Wiz/Elab/Registry.lean:40-82`); `‡` `term_elab`. Selfhost: fixed list (`inline` + built-ins), no user registrations | `AttrAction` + the attribute registry | A new semantic action is a host match arm; there is no registered Wiz *handler* for an attribute; the selfhost's fixed list | partial (host) / open (selfhost) |
| 7. `deriving` / `[deriver C]` | `deriving` handlers; user code | Host: complete; `lib/Deriving.wiz` 4 + `Lens`; the host runs the registered Wiz `Deriver` in the interpreter (`Wiz/Elab/Command.lean:2270-2274`). Selfhost: 5 built-ins run; a user deriver is refused; `†` D1 makes the refusal `entry-unsupported` | `[deriver C]` + `Deriver` | `Deriver` gets only the type name, not the class methods; FeEval for the selfhost | done (host) / partial (selfhost) |
| 8. unexpanders `[app_unexpander c]` | `@[app_unexpander]`; user code | Host: complete for applications; 2 registrations (`lib/`); selfhost parses/accepts, no notation printer | Printer hook | None for a new unexpander; the selfhost's printer | done (host) / open (selfhost) |
| 9. `implemented_by`, `inline`, `sealed` | `@[implemented_by]`, `@[inline]`, `sealed` | Host: complete, including native representation. Selfhost: `inline`/`implemented_by`; native rep missing | Trust/native attributes | Selfhost native representation and the trust policy | done (host) / partial (selfhost) |
| 10. `class`/`instance`/`default_instance`/`binop` | Typeclasses, instances, `default_instance`, `binop` | Host: complete. Selfhost: A10 first milestone; no `default_instance`, `binop`, `outParam`; bounded resolution | Class/instance declarations | Selfhost `default_instance`/`binop`/`outParam`/numeric classes; host `binop` is data | done (host) / partial (selfhost) |
| 11. `local` scoping | `local` on notation/macro/instance/attribute | Host: partial (grammar/macro/unexpander/instance; `[tactic]`/`[deriver]`/`‡[term_elab]` are deliberately not `local`). Selfhost: local notation/macro stay visible (A14) | `CommandState.endModule` + cache | A general scoping rule for semantic attributes; the selfhost's `local` handling | partial |
| 12. LSP: hover/definition/completion/actions/inlay | LSP server; plugins in Lean | Host: complete, **no user hook**; selfhost: D8 missing | None for users | A host hook + a Wiz handler; this is Shape D today | open |
| 13. infoview protocol + widgets | Widgets in Lean (`@[widget]`) | Host: complete server, Wiz clients, **no widgets**; selfhost: missing | None for users | A host hook + a Wiz handler | open |
| 14. `wiz doc` | Doc generation is host-side; no user language registry | Host: complete; languages are `wiz.doc.languages/1` data (`Wiz/Doc/Registry.lean`), the builder is host-only. Selfhost: missing | Declarative `Spec`/`Lang` JSON | None for a new language; a package renderer is refused by design | done (host) / open (selfhost) |
| 15. formatter (`PPFormat`, notation printing) | `Format`/`pp` notation; unexpanders | Host: complete for notation, weak for values; selfhost: no notation printer | `PPFormat` + unexpanders | A new pretty-printing feature; the selfhost's printer | partial (host) / open (selfhost) |
| 16. FFI (`extern`, `foreign_type`, `c_struct`, `link_*`, `import_c`, `glue`, `export`) | `@[extern]`/`@[export]`, `implemented_by`, C FFI | Host: complete; selfhost: `import_c`/`glue` missing (C10) | Attributes/commands + trust ledger | A new FFI kind/ABI; the selfhost's C10 | done (host) / partial (selfhost) |
| 17. `builtin`, trust, solvers, natives | Primitive types fixed; `@[implemented_by]`, `extern`, `opaque`; no user new primitives | Host: `builtin nat/string/...`; `‡` `unit`, `empty`, `qty`, `size`, `char`, `list` and the string-literal encoding; trust ledger. Selfhost: no `builtin` command at all | `builtin key := name`; `‡` the data-primitive table | A genuinely new primitive (`Float32`, machine ints) is still kernel + `Term.lean`; `builtinNames` (`Desc`/`μ`/`ν`), `True`/`False`, numerals unchanged; the selfhost's command | partial (host: spelling/literal data, primitive set still closed) / open (selfhost) |
| 18. package/build commands (`grail.wiz`, `tower`) | Lake; build config is Lean code | Host: complete as data (`Package.command`, `Target.command`); no new kinds/subcommands; **no ext manifest reader**. Selfhost: `tower` is Wiz, `grail` is Lean | `Package.command`/`Target.command` | A new build-step kind; the manifest reader (G2); the selfhost's `grail` | partial (host) / open (selfhost) |
| 19. simplifier `[simp]` | `@[simp]`, `simp only`, user lemma sets | Host: complete (`simp`, `simp only`, `simp?`, `[simp]`, `[hint]`; 47 `[simp]` lines; `getSimpLemmas`). Selfhost: no `simp` | `[simp]`/`[hint]` data + `Tac` requests | A new simp feature/congruence; the selfhost's `STac` and FeEval | done (host) / open (selfhost) |

### 2.1 What the table says

* **The host is now open at the two points the policy names first.** Term elaborators
  and `deriving` are real Wiz-function interfaces; macros and `simp` were already.
  A Wiz library can add a term syntax, a deriver, a tactic, a macro, a simp lemma, an
  unexpander, a lint set and a doc language without editing `Wiz/`. The exceptions are
  exactly the ones the next section is about.
* **The selfhost is open at almost none of the Shape B/C points.** It runs Wiz *data*
  (syntax/notation/macro_rules, class/instance, the five derivers) and refuses or
  ignores Wiz *code*. The one exception is `Inhabited`, which is a compiled-in deriver,
  not a user registration.
* **The deepest host residue is still the data primitives and the request set.**
  `builtinNames` (`Wiz/Elab/Term.lean:184-186`) is a fixed 16-name list for
  `Desc`/`μ`/`ν`/`con`/`cocon`/`out`; at base `mkStringLit` names
  `String.mk`/`List.cons`/`List.nil` (the lane makes `char`/`list`/`string` data, but
  not the kernel's primitive set); `True`/`False` keep fixed spellings; the numeral path
  is `builtin nat` one-shot. A `Float32` or a machine integer is still a compiler
  change.
* **`Wiz/Ext.Capability` is a flat enum.** It mixes backend operations (`emit`,
  `link`, `run`, …) with lint views (`decl`, `spans`, …) and has no elaboration
  capabilities. Nothing checks that a capability is meaningful for a kind: a `lintRule`
  entry can declare `emit`, a `backend` can declare `decl`, and a future `termElab`
  entry has no capability to declare at all. That is a G1 shape bug, not a detail.

---

## 3. What the current lanes actually unlock

### 3.1 `agent/ext-registry` (Item 1)

**State.** Based on `6e5924cd8`; 15 staged files plus unstaged fixes; not committed.
`Wiz/Ext/Basic.lean` is the record (`Kind`, `Capability`, `ArtifactKind`, `Payload`,
`Entry`, `Diagnostic`); `Wiz/Ext/Resolve.lean` is the table and one resolver. Lane
anchors in this subsection are from the worktree, not `f489cc876`.

**Unlocks.**

* **Selection is data.** `--target` is five rows and six spellings (`c`, `llvm`,
  `wasm`, `bpf`, `js`, `ebpf` as `bpf`'s alias). `Main.lean` no longer has `targets` or
  a `target == "…"` chain (`takeTarget` returns the resolved `Entry`; `buildCmd` matches
  `CoreDriver` exhaustively, with no `else` that means C). Unknown, duplicate,
  not-enabled, ABI and capability refusals are `Wiz.Ext.Diagnostic` values with stable
  codes; `=ext` pins 13 cases, including a cold/warm/cross-target cache probe.
* **The lane fixes D1.** `Globals.ders` stores `DeriverRef := builtin kind | user name`; a
  declaration named `deriveBEq` is `.user` and `deriving` refuses it with
  `entry-unsupported`, instead of running the built-in `BEq` body. This removes a real
  host/selfhost divergence today.
* **The lane puts the target in the cache.** The canonical backend enters
  `Toolchain.targetTag` and `Toolchain.id`, which `Main.elaborateHitsCore` passes as the
  fast toolchain namespace. A `bpf` build cannot reuse a module cached under `c`.
* **The shape for the next kinds exists.** `Kind` already names `deriver`, `tactic`,
  `macro`, `lintSet`, `lintRule`, `termElab`; `Table.resolve` is generic; the codes are
  `unknown-<kind>`, `<kind>-not-enabled`, `<kind>-capability` and `unsupported-<kind>`.

**Only relocates.**

* **The backend implementation is still closed.** The five core entries are `.core`
  payloads and `CoreDriver` is a Lean enum; adding an in-tree backend is a compile
  error at an exhaustive match, which is correct for host code but is not
  extensibility. A package `.process`/`.data` payload *resolves* and then
  `Entry.coreDriver?` refuses `unsupported-target`; no driver consumes it.
* **There is no manifest reader.** `--target` is parsed before any module or manifest
  (`Main.lean:1364`); `grail.wiz`'s `Package.command` is a build-graph node with no
  schema/ABI/caps/payload/`--target` name. The `=ext` package `demo` row is built in
  memory by the test. "A package backend without patching `Main.lean`" is not achieved;
  the resolver is ready for the row, the discovery is not.
* **It is a second registry, not the one registry.** `Wiz/Lint.lean`'s `Capability` /
  package-set loader and `Wiz/Doc/Registry.lean`'s `wiz.doc.languages/1` are not
  converted; `Wiz/Ext` is used only by `Main.lean` and the tests (`rg 'Wiz\.Ext'`
  outside `Wiz/Ext` finds no elaboration kind). The `Kind` names are vocabulary, not
  wired entries.
* **The selfhost table is still hand-copied.** `selfhost/Cli.wiz:1183-1186` lists the
  six names independently of the Lean table. The host's fifth-target bug class is gone;
  the selfhost's duplicate list is the same bug waiting for the next row. There is no
  generated table and no cross-check test.
* **The refusal is not the `Msg` envelope.** `Diagnostic` is code + message, printed
  by the CLI. The compiler's `Msg` still has one span and one message; `CORE-3.2`
  (multi-span/structured diagnostics) is not satisfied, and the roadmap's R4 says
  `CORE-3.3` should wait for it. This lane proceeds with a local `Diagnostic`, which is
  fine for the CLI but does not give editors or the LSP structured codes.
* **Capabilities are not kind-scoped.** See §2.1; a lint rule can claim `emit`, a
  backend can claim `decl`, and an elaboration entry has no capability vocabulary.

**Verdict.** It buys *selection* data and a real correctness fix. It does not buy a
package backend, an elaboration entry, or structured diagnostics.

### 3.2 `agent/ext-term-elab` (Item 2)

**State.** Based on `6e5924cd8`; modified files unstaged; not committed. `[term_elab]`
is a real `AttrAction` (`Wiz/Elab/Registry.lean:55,77`), `CommandState.termElabs` is
threaded through `runElab*`, and `elabTermElab?` (`Wiz/Elab/Term.lean:4685`) runs the
handler with one goal in `check` (expected type) and `infer` (fresh type meta). Lane
anchors in this subsection are from the worktree, not `f489cc876`.

**Unlocks.**

* **A library can add a term form.** `syntax "τ" : term` +
  `attribute [term_elab term.τ] tauElab` works in an importer; `#check (τ : Nat)` and
  `#check τ` pass. Unknown kinds and non-`TermElab` targets are refused; `local` is
  refused like `[tactic]`/`[deriver]`; the registration is non-cacheable and is
  replayed on a warm cache; `isoKey` includes the starting `termElabs`.
* **The data-primitive *spellings* are data.** `builtin unit|empty|qty|size` rename
  the kernel formers (the old names are fallbacks); `builtin char`/`builtin list` and
  `builtin string` decide the string literal `S.mk (L.cons (C.mk n) … L.nil C)`; the
  pretty printer follows the table. A library with its own `MyChar`/`List`/`String`
  can define its literal encoding; a mismatch is reported at the literal, not left to
  the kernel.
* **The generic attribute path is exercised.** `[term_elab]` needed no new parser rule
  and no new `elabCommand` kind, only an `AttrAction` and a dispatch point. That is the
  model for `[simp]`/`[hint]`-style semantic attributes and for a future
  `register_attribute` handler.
* **It is host-side only, as intended.** The handler runs in the host interpreter
  (`TacticM.run` + the existing `Tac`/`Expr` requests), so it needs no FeEval. The
  Item 1/Item 2 decoupling is validated.

**Only relocates.**

* **It changes spellings, not primitives.** `.unit/.empty/.qty/.size` are the same
  kernel formers; `True`/`False` keep fixed names; `builtinNames`
  (`Desc`/`μ`/`ν`/`con`/`cocon`/`out`) is untouched; `builtin nat` and the numeral path
  are untouched; `Bool`/`Int`/`UInt64`/`Float64` are library types, not new primitives.
  A new data type (e.g. `Float32`) still needs kernel + `Term.lean` + backend work.
* **The request frontier is unchanged.** `TermElab := Syntax → TacticM Unit` inherits
  the 45 `TacTag` requests. A handler cannot add a request; `elabTermElab?`'s only new
  thing is the goal and the `TacticM` loop. The "single most important limit" in
  `user-extensions.md` §0 is still the limit.
* **It bypasses `Wiz/Ext`.** The registration is a direct `CommandState` mutation and
  the `AttributeDecl` is in `Wiz/Elab/Registry.lean`, not an `Entry`. A package can
  register a term elaborator with no `Kind`, `abi`, `set`, `caps` or resolver check.
  The `termElabs` list is latest-first with no duplicate refusal, like `tactics` and
  `derivers`; a package can silently override a core registration.
* **It is not package-safe.** There is no overall step budget in `Run.run`
  (`Wiz/Compiler/Run.lean:477` has local list/readback fuel only), no purity/trust
  check on the registered declaration (the lint registry has one; the attribute path
  does not), and no `elab` capability in `Wiz/Ext.Capability`. A package `[term_elab]`
  can hang the compiler; the lane's note discusses `local` and cache but not this.
* **The selfhost does not know it.** `attrStep` (`selfhost/Frontend.wiz:10906-10922`) has a
  fixed list; `attribute [term_elab …]` gets `unknown attribute`, and `builtin` is an
  unsupported command. `syntax "τ" : term` itself *does* parse (A12), so the failure is
  at the attribute/command, not the grammar. Fail-closed, but a portability cliff.
* **The `char`/`list` swap is all-or-nothing.** `builtin char := MyChar` with the
  default `String` reports that `String.mk` takes `List Char`; there is no coercion.
  A library must also register a matching `builtin string`, which is deliberately
  fail-closed but limits "change one primitive".

**Verdict.** It buys the first host-side term-elaborator interface and a real data
spelling table. It does not buy new primitives, new requests, package registration, or
selfhost support.

### 3.3 The three empty lanes

* **`structured-view` (Item 3).** No code. The design is a capability-scoped
  `wiz-lint/2` (or `wiz-info/1`) section with binder facts, term heads and `Info`
  nodes, plus a `Tac` request; acceptance is a W5xx rule over the view and `W101`
  re-expressed. It would unlock term-level package rules, hints, code actions and a
  term elaborator that inspects a value. The ABI risk is the highest of the five: a
  term-shaped view leaks the kernel, a text-shaped view is what it replaces.
* **`ir-abi` (Item 5).** No code. The design is `wiz-ir/1`, a parser/printer and one
  pass in `lib/Ir.wiz`, with a `demo` target consuming it. It would unlock package
  backends and Wiz IR passes; it is **not** FeEval-gated, it is IR-gated. The risk is
  the IR's internal churn (`RC`/borrow annotations) and the parse cost.
* **`feeval-core` (Item 4).** No code. The design is `selfhost/FeEval.wiz`
  (`EvalEnv`, encoders/decoders, `whnfE`, the request loop, the `proofStart` budget).
  It would unlock every Shape B/C point under the selfhost; it is the only item that
  makes the moved library code run in the self-hosted product. It is also the largest
  (a quarter in the plan's sizing) and depends on `SH-2.0a` (the prelude with the real
  `Tac`/`MacroM`/`Deriver`) and the meta API in the one prelude.

The plan's five items are therefore **two lanes writing code and three designs
waiting**. The refreshed roadmap should not read "Items 1–5 in flight" as five
parallel efforts.

### 3.4 Together: the scorecard, and the bridge that is missing

| policy interface (`docs/design/README.md`) | host before | host after the two lanes | selfhost |
|---|---|---|---|
| data-driven term elaborators | open | **partial**: dispatch + spellings, no new primitives, not an `Entry` | open |
| user-extensible `deriving` | done | **done** (D1 fixed) | partial: 5 built-ins, user deriver refused |
| hygienic macros | done | done | partial: `macro_rules` only, `[macro]` bodies not run |
| `simp only`-style lemma sets | done | done | open |
| one entry model | none | **partial**: targets only, no reader, no elaboration kinds | none |

The missing bridge is the point of G1: the two lanes do not meet. `ext-registry` has a
`Kind.termElab` but no producer; `ext-term-elab` produces a `termElab` but not an
`Entry`. Until they meet, the new interface is a privileged host attribute, not a
package extension point.

| lane | what it unlocks | what it only relocates |
|---|---|---|
| `ext-registry` | target selection as data; D1; target in the cache key; the `Kind`/`Entry` vocabulary | the closed `CoreDriver`; no manifest reader; no elaboration entry; the selfhost list; `Diagnostic` ≠ `Msg`; flat capabilities |
| `ext-term-elab` | `[term_elab k]`; six `builtin` spellings; the string literal; the pretty printer | the primitive set; the 45-tag request set; registration bypasses `Wiz/Ext`; no budget; no selfhost |
| `structured-view`, `ir-abi`, `feeval-core` | nothing yet: designs for Items 3–5 | nothing yet |

---

## 4. The next three gaps after Items 1–5

The estimates are agent-days from reading, not measurements. `S` ≤ 3, `M` 4–10,
`L` 11–25, `XL` > 25. Risk names the failure mode, not a feeling.

### G1. Register the elaboration kinds in `Wiz/Ext`, with kind-scoped capabilities, purity and a budget

**Why this is first.** `agent/ext-term-elab` adds another extension point that lets a
*library* run arbitrary Wiz code in the elaborator (as `[tactic]`/`[macro]`/`[deriver]`
already do). None of them goes through `Wiz/Ext`, none has an `elab` capability, and
`Run.run` has no overall budget. So the new interface cannot be enabled for packages by
default, and a package can silently replace a core registration. This is the gap that
makes the difference between "a host feature" and "a package extension point".

**Change.**

* Make the attribute handlers (`command.attrMacro`, `command.attrTactic`,
  `command.attrDeriver`, and the generic `command.attr`'s `termElab` action) construct
  a `Wiz.Ext.Entry` and go through `Table.register`/`resolve` (registry-abi §6 step 5).
  The `List (Name × Name)` fields can stay as storage; the entry is the front door and
  the duplicate/unknown/capability refusals are data.
* Add kind-scoped capabilities (`elab.term`, `elab.tactic`, `elab.macro`, `elab.deriver`,
  `elab.lint`; or a `Stage` field) and validate `caps` at registration: a `lintRule`
  cannot declare `emit`, a `backend` cannot declare `elab.term`. The current flat
  `Capability` enum is the bug.
* Add a purity/trust preflight for a Wiz entry: no `partial`, no `axiom`/`extern`/
  `implemented_by`, no untrusted `builtin`, no IO (the lint registry already has this
  check at `Wiz/Lint.lean:598-648`; reuse it). Refuse with `entry-unsafe`.
* Add an overall step budget to `Run.run` and report `entry-budget`; a package entry
  may not be default-on until the budget lands. The LSP needs the same budget so a bad
  handler cannot wedge the server.
* Decide the cache rule: registrations stay non-cacheable (as `attribute` is) or join
  `Cache.Effect` with a region bump. Do not leave it implicit; `termElabs` in
  `isoKey` is not enough once `attribute` becomes cacheable.

**Cost.** M/L: 8–14 agent-days. The registration plumbing is M; the budget and the
purity preflight are the rest. **Risk: high.** Every registration path changes, the
existing `=tactics`/`=deriving`/`=macro` groups must stay green, the budget must not
break `lib/Deriving.wiz` or the `smt` path, and a too-eager purity check rejects a
legitimate library helper (e.g. a deriver that calls a trusted `partial` helper). The
cache/`Effect` decision is a one-way door.

**Test.**

* `=ext`: a package `[term_elab term.τ]` registration without the `demo-set` is
  `term-elab-not-enabled`; with the set but without `elab.term` it is
  `term-elab-capability`; the same for `[tactic]`, `[macro]`, `[deriver]`.
* `=elab`: a registered handler whose body is `partial` (or an `axiom`) is refused
  `entry-unsafe` at registration; a handler that loops is refused `entry-budget:
  term-elab <name> exceeded N steps` and the process exits non-zero. No hang.
* `=ext`: a `lintRule` entry declaring `emit` is `invalid-lint-rule-capability`; a
  `backend` declaring `decl` is `invalid-target-capability`; two `[term_elab]` for one
  kind refuse `duplicate-term-elab` and name both providers.
* `=cache`: the budget failure is not cached as a success; a warm run re-runs the
  registration and the failing command.
* `=selfhost`: until FeEval, the same module is a pinned `entry-unsupported` (or
  `unknown-attribute`), not a silent fallback.

**Unlocks.** Default-on package code; `PK-3.5` can sign an entry whose payload is
actually safe to run; the LSP survives a bad handler; the registry becomes the one
place a package registers anything. It does not add a new *request* (that is G3's
request ABI); it makes the existing ones safe.

### G2. Package discovery and signed enablement

**Why this is second.** Item 1's table has no reader. A package cannot install a
backend, a lint set, a deriver or a doc language without patching `Main.lean` or
building the row in a test. `grail.wiz`'s `Package.command` is a build-graph node, not
an entry: no `schema`, `abi`, `caps`, payload or `--target` name. Until this lands,
"package" remains a design and every new `Kind` is core-only.

**Change.**

* Add an `ext`/`ext-set` block to the package manifest (the `Package`/`Target` data in
  `lib/Grail.wiz`, decoded by `Grail/Config.lean`), with `(kind, name, provider, set,
  schema, abi, caps, payload)` rows. `grail` validates the schema/ABI/caps, computes
  the entry digest and signs it (`PK-1.1`'s `entryDigest`/`covers`), and passes the
  resolved entry + enabled sets to `wiz build` (file or argv). **`wiz` does not learn to
  read a manifest**; the boundary stays.
* Add at least one package payload driver: a `.process` backend that reads
  `wiz-ir/1` (after Item 5) or a `.data` lint set / doc language (already a document).
  A `.process` stub is enough for the acceptance; it proves the resolver's per-kind
  payload path.
* Put the enabled set in `Toolchain.tag`/the cache key, not only the canonical
  backend name. A cached module under `c` must not be served to a run with `demo-set`
  enabled.
* `grail add/remove/list` over the manifest; a refusal names the entry and the set.

**Cost.** M: 6–10 agent-days. **Risk: medium.** The `grail` (Lean) / `wiz` (CLI)
boundary is easy to blur; the digest must be stable across `grail` and `wiz`; the cache
key grows; and a second manifest reader is the thing to avoid. The `.process` driver is
a new attack surface, so it needs the G1 budget/caps or it must stay disabled by
default.

**Test.**

* `=ext`/`=grail`: a checked-in `demo` package declares a `.process` backend; `grail
  build` selects the `demo` entry and passes it to `wiz build --target demo`, which
  writes `out`; the proposed `grail remove demo` makes the entry `unknown-target`.
* Without the `demo-set` enabled: `target-not-enabled`; with it enabled: resolves and
  builds. A tampered digest: `entry-tampered` (or `signature-invalid`), before any
  artifact. Two providers for one `(kind, name)`: `duplicate-target`, naming both.
* `wiz build --target demo` with no `grail` invocation still refuses: `wiz` does not
  read the manifest; the test pins that boundary.
* Cache: a cold `c` build, then a `demo` build, then a warm `c` build hits its own
  cache; the enabled set changes the key.
* A package `lintRule`/`docLanguage` row resolves through the same table and its
  refusal codes are the same generic ones.

**Unlocks.** The package leg of "port vs open vs package" for every kind; `PK-3.5`;
the first real external user; a test for the resolver's `.process`/`.data` payloads.
It does not make a package *portable* to the selfhost (G3/FeEval), and it does not
replace G1's budget.

### G3. `wiz-meta/1`: a versioned request ABI and a host/selfhost conformance corpus

**Why this is third.** Every Shape B/C extension still hits the 45-tag `Tac` set; Item
3 adds *one* view request, Item 4 makes the selfhost able to run code, but the ABI has
no version marker and no corpus. D1 was one drift between the host and the selfhost;
there will be more as `[term_elab]`, `[macro]`, `[tactic]` and the lint rules grow. A
new request is still a host enum change, and a package's "works in Wiz" claim cannot be
tested.

**Change.**

* Freeze `Syntax`/`IndView`/`Expr`/`Tac` shapes and tags under `wiz-meta/1`; add the
  marker to every registered entry's `abi`; a package that pins another range is
  refused (`unsupported-<kind>`), no silent negotiation.
* Define the request envelope: name, payload schema, result schema, capabilities; an
  unknown tag refuses `unsupported-request` rather than falling into a host `match`
  default. Adding a tag is append-only; removing/renumbering or changing a `SyntaxF`/
  `Expr`/`IndView` constructor or the `✝` meaning is a major bump.
* Add `Tests/fixtures/meta/` with a dozen small programs per profile: a deriver that
  builds an instance, a tactic that closes a goal, a term elaborator, a command macro
  with an error path, a macro, a lint rule with a finding, a `getInductive` consumer.
  Run them on the host (a new `=meta` group) and, after FeEval, on the selfhost
  (a new `=selfhost-meta` group); compare output and diagnostics byte-for-byte.
* Keep `wiz-lint/1` and `wiz.doc.languages/1` as their own schemas; the meta ABI is for
  the elaboration payloads, not the lint text view or the doc builder.

**Cost.** L: 15–25 agent-days, plus FeEval for the selfhost half. **Risk: high.** ABI
churn (freeze too much and you pin the wrong shape; freeze too little and it is not an
ABI), two frontends, hygiene/positions, cache, and flaky corpus tests. Do not freeze
more than the corpus exercises; the corpus is the contract.

**Test.**

* `=meta`: the corpus runs on the host; each program's expected text/exit is checked;
  a `wiz-meta/2` entry is refused `unsupported-term-elab` (or the generic
  `unsupported-<kind>`); an unknown tag is `unsupported-request`, not a silent
  fallthrough.
* `=selfhost-meta` (after FeEval): the same corpus runs on the selfhost; the same
  instance/goal/error text is produced. Until FeEval, the selfhost's row is a pinned
  `entry-unsupported`, and the test asserts the refusal, not a pass.
* A `✝`/constructor-change probe: the corpus fails, and the ABI check reports a major
  bump. A new request tag appears in the corpus without changing an existing tag.
* A package entry that declares `wiz-meta/1` but uses a request from `wiz-meta/2` is
  refused by the resolver before it runs.

**Unlocks.** A stable target for package code; the selfhost can run the same corpus
after FeEval; new request kinds can be added with a schema and a test rather than a
host `match` arm. It is the "open" leg at the ABI level; it does not itself add the new
requests (Item 3's view is the first).

### 4.1 Close contenders, and why they are not the top three

| gap | value | cost/risk | why not now |
|---|---|---|---|
| multi-span diagnostics (`CORE-3.2`) | Every DSL needs "the use, the move and the borrow" and several errors per command; it is a prerequisite for a good package error story | M / medium (both frontends, `Msg`, LSP, `=diagnostics` 15 cases; `diagnostics-cascade` is already in flight) | It changes *how* errors are reported, not *what* can be extended. Fold its error-path cases into G3's corpus; land `CORE-3.1/3.2` on its own track. |
| generic semantic attributes/commands (`[hdl top]`, `#verilog`) | HDL-2.3 and every DSL; `#verilog` likely already lexes as an atom (`D2`), so the remaining half is a semantic attribute and a command handler | M / medium (a new `AttrAction` per feature is a host arm; a registered Wiz handler is the open version) | It is the first new *kind* after G1/G3; it needs the registration and the schema those two build. It is not more valuable than package discovery or the ABI. |
| selfhost target table generation/cross-check | Removes the hand-copied six-name list (`selfhost/Cli.wiz:1183-1186`); catches the fifth-target bug on both sides | S / low | Cheap and worth doing inside G2, but it is a duplicate-list fix, not a new capability. |
| data-primitive completeness (`True`/`False`, `Desc`/`μ`/`ν`, numerals, `Float32`) | The rest of Item 2's frontier; machine numbers and DSL literals | M/L / medium (kernel + `Term.lean` + backend; `Float32` is a real primitive) | It is a continuation of Item 2, not a new interface. Do the `builtinNames`/`True`/`False` slice when a consumer needs it; `Float32` is a kernel project. |
| `#`-command probe/documentation (`D2`/`D3`) | `syntax "#verilog" ident : command` probably lexes today; a one-page "how to add a command" moves DSLs off the list | S / low | Documentation, not a gap. Run the one `wiz check` probe when a build lane is free. |
| LSP/widget extension points (12/13) | Code actions, hover, widgets | L / high | Shape D by design; the host hook + Wiz handler is a product decision, not the current extension priority. |

---

## 5. The selfhost: host-only until FeEval, and what it means

### 5.1 Host-only until FeEval

These points are **Shape B/C**: the payload is Wiz code run at elaboration time. The
selfhost has no evaluator, so it can register or parse them but not run them. After
FeEval, the blocker becomes the meta API/request runner, not the parser.

| extension point | selfhost today | gate | after FeEval? |
|---|---|---|---|
| `[macro k]` | Declared and checked; body not run (`runMacroTac` answers `result`/`fail`/`trace`/`getInductive`/`done`, `selfhost/Frontend.wiz:11113-11121`) | FeEval + `MacroM` runner | yes |
| command macros `[macro command.k]` | `macro_rules` command macros work; `[macro]` bodies do not | FeEval + runner | yes |
| `[tactic k]` | No user tactic runner; the core `STac` engine only (A13) | FeEval + `Tac` runner | yes |
| `[deriver C]` (user) | 5 built-ins run; a user deriver is refused (`entry-unsupported` after `†`); at base, D1 lets a user declaration's spelling select a built-in body | FeEval | yes |
| `[term_elab k]` (`‡`) | Unknown attribute: `attrStep` has a fixed list (`selfhost/Frontend.wiz:10906-10922`) | FeEval + the attribute table + `TermElab` in the prelude | yes |
| `[simp]` / `simp` | No `simp` tactic; `[simp]` data is not read | FeEval (the tactic is Wiz in `lib/Prelude.wiz`) | yes |
| semantic attributes (`register_attribute` with a Wiz handler) | Fixed list; user registrations are not read | Host registration + FeEval for the handler | yes |
| package lint rules | No `wiz lint` in the selfhost | Host lint driver + FeEval for the runner | yes |
| structured view / term-level rules | No view; `wiz-lint/1` is host-only | Item 3 + FeEval | yes |

### 5.2 Host-only regardless of FeEval

These are Shape D, or they need a different runtime (IR/C), not an evaluator:

* the LSP server and infoview server (`D8`), widgets, hover/definition/completion;
* `wiz doc`'s builder (the *languages* are data; a package renderer is refused by
  design), and the formatter's notation printer;
* `grail` (Lean), the CLI, the release path;
* backend emission beyond C/LLVM (Wasm, BPF, JS, a package backend) — this is
  `wiz-ir/1`/Item 5, not FeEval;
* FFI `import_c`/`glue` (C10), native representation, the runtime allocator ABI;
* `builtin` itself: it is a host *command* and a table, not an evaluator feature. A
  selfhost could port the data command earlier than FeEval if a package only needs the
  spellings, but that is a second implementation of `command.builtin`, not
  extensibility.

### 5.3 Consequences for "port vs open vs package"

**Port.** A port of a Shape B body into the selfhost without FeEval buys parity, not
extensibility: the body is compiled into the frontend, and a user still cannot register
one. The D1 bug is the cautionary example — a name-keyed dispatch made the host and the
selfhost disagree about what `deriving BEq` means. Port a Shape B point only when the
port *is* the evaluator (FeEval) or when it removes a runtime a package needs (IR/C).
Port the data readers (`syntax`, `class`/`instance`, eventually `builtin` spellings)
earlier; they are cheap and they make library files check.

**Open.** Open the host interface now; it is the only place a Wiz extension can run
today. Accept that every open point creates a host/selfhost divergence, and make the
divergence a *pinned refusal* with a code (`entry-unsupported`), not a silent fallback.
The `[term_elab]` and `builtin` cases are the test: the selfhost should say
`entry-unsupported: term-elab term.τ` (or the current `unknown attribute`) and
`unsupported command builtin`, and a `=selfhost` case should pin that. Generate the
selfhost's target/attribute tables from the host's, or pin a cross-check; a hand-copied
list is the fifth-target bug.

**Package.** A package's portability is a property of its payload shape, not its source
language. Split the manifest into tiers:

* `portable-data`: syntax/notation, lint sets (`wiz-lint/1`), doc languages
  (`wiz.doc.languages/1`), target rows, `[simp]` lemma data. The selfhost can read
  these once the readers exist; no FeEval.
* `portable-code`: derivers, macros, tactics, term elaborators, lint runners,
  semantic-attribute handlers. Host-only until FeEval; the selfhost refuses by name.
* `host-only`: LSP/widgets, doc builder, package backend emission (until `wiz-ir/1`).

The manifest should declare the tier (or derive it from the entry `Kind` + payload), and
the resolver should refuse a code entry on a toolchain without FeEval rather than
pretending. Do not advertise a package as "works in Wiz" if it only works in the Lean
host.

**If FeEval is refused (R1).** Then the selfhost is a bootstrap/checker, not the
extension host. The host remains the only place a Wiz extension runs; package execution
is host-only; the docs must say so. The registry and the manifest can still ship
host-side (G1/G2), and `wiz-meta/1` becomes a host-only ABI plus a pinned selfhost
refusal table. That is a deliberate product split, not a failure of Item 1.

**The decision in one line.** *Port* only FeEval/IR-shaped work; *open* the host
interfaces now; *package* the data half early and the code half only after FeEval (or
declare the package host-only). The registry does not change that calculus; it only
makes the host side cheap enough to do first.

---

## 6. What I verified, and what I did not

**Read at `f489cc876`.**

* `wiz-notes/extensibility.md` (all 548 lines), `wiz-notes/registry-abi.md`,
  `wiz-notes/user-extensions.md` §0–§1, `docs/design/README.md`, `docs/lint-abi.md`,
  `docs/stages/11-tooling.md` (the attribute registry), `docs/stages/21-bootstrap.md`
  §21ac, `docs/stages/30-selfhost-typeclasses.md` §30a–30b, `docs/Status.md` (top and
  §8), `roadmap/program-next.md` (the CORE/SH/PK rows and R1/R4).
* `Wiz/Elab/Term.lean` (`builtinNames` `:184-186`, `mkStringLit` `:202-208`, the
  `Unit`/`Empty`/`Qty`/`Size` case `:3856-3862`, `runTac` `:4129`, `elabBy` `:4613`);
  `Wiz/Elab/Tactic.lean` (`TacTag` 0–44); `Wiz/Elab/Command.lean`
  (`procMacros`/`tactics`/`cmdMacros`/`derivers` `:137-146`, `runElabS` `:1525`,
  `mkMetaCode` `:1572`, `deriving` `:2270`, `command.builtin` `:2993`, the attribute
  handlers `:3513`/`:3651`/`:3708`/`:3777`/`:3891`); `Wiz/Elab/ProcMacro.lean`
  (`runMacroTac` `:124-143`,
  `runDeriver` `:166`); `Wiz/Elab/Registry.lean` (`AttrAction` `:40-55`,
  `builtinAttributes` `:64-82`).
* `Wiz/Lint.lean` (`registry` `:388`, `viewOf` `:495`, `callRunner` `:529`,
  `checkSet` `:598`, the package ABI `wiz-lint/1`), `Wiz/Lint/Basic.lean`
  (`Capability` `:49`, `packageCapability` `:91`), `lib/Lint.wiz` (345 lines).
* `Wiz/Doc/Registry.lean` (`wiz.doc.languages/1`), `Wiz/Doc/Highlight.lean` (`Spec`
  `:90`), `Wiz/Compiler/IR.lean` (`toString` only; no JSON/parser), `Wiz/Compiler/Run.lean`
  (`run` `:477`; the only `fuel` is local), `Wiz/Compiler/Build.lean` (`build` `:330`).
* `Main.lean` (`targets` `:943`, `takeTarget` `:964`, `buildCmd` `:987`, `runCmd`
  `:1027`, `mainImpl` `:1302`), `selfhost/Cli.wiz` (`targetModes` `:1183-1186`),
  `selfhost/Frontend.wiz` (`tabStep` `:10796`, `attrStep` `:10906`, `runMacroTac`
  `:11113`, `deriverKind` `:10848`, `deriveClassOn` `:11495`).
* `lib/Deriving.wiz` (467 lines; 4 registrations), `lib/OpticDerive.wiz` (`Lens`),
  `Tests/Groups/Elab.lean` / `Reject.lean` at base, and the lane test files.

**Worktrees read.**

* `ext-registry`: `HEAD 6e5924cd8`, staged + unstaged, 15 staged files; `Wiz/Ext/*`,
  `Main.lean`, `Tests/Groups/Ext.lean`, the selfhost D1 diff, `wiz-notes/ext-registry.md`.
* `ext-term-elab`: `HEAD 6e5924cd8`, unstaged; `Wiz/Elab/{Term,Command,Registry,Basic}.lean`,
  `lib/Prelude.wiz`, `Tests/Groups/{Elab,Reject}.lean`, the `extensibility.md` §8
  appendix, the `docs/design/README.md` update.
* `structured-view`, `ir-abi`, `feeval-core`: `HEAD f489cc876`, clean, no commits, no
  `Wiz/Ext`, no `selfhost/FeEval.wiz`.

**Counted.** `TacTag` 45 (0–44); `[tactic` 50, `[macro` 15, `[simp` 47, `[deriver`
registrations 5 (4 in `lib/Deriving.wiz`, 1 in `lib/OpticDerive.wiz`); `lib/Deriving.wiz`
467; `lib/Lint.wiz` 345; `Wiz/Ext/Basic.lean` 242; `Wiz/Ext/Resolve.lean` 227.

**Not verified (no build, no test run).**

* The lane tests' pass/fail: `=ext` 13 cases, `=elab` 8, `=reject` 3 are counted from
  the files; none was run. The lanes' own notes do not contain a build log.
* `D2` (whether `syntax "#verilog" ident : command` lexes) is still a one-probe
  question; this lane did not run `wiz check`.
* The cost/risk estimates are reading, not measurement.
* The exact file:line anchors will move when the lanes rebase from `6e5924cd8` to
  `f489cc876`; the lane-only anchors are marked with the branch.

---

## 7. References

* `wiz-notes/extensibility.md` — the five items, the 19-point table, B1–B5/C1–C5/D1–D3.
* `wiz-notes/registry-abi.md` — the entry model, `wiz-meta/1`, steps 1–8.
* `wiz-notes/user-extensions.md` — the shape taxonomy and the original 19-point map.
* `wiz-notes/targets-ext.md` — the target/entry design; §7 is Item 1's first slice.
* `wiz-notes/elab-evaluator-plan.md` — FeEval design and its measurement gate.
* `wiz-notes/linting.md` §2.5–2.8 and `docs/lint-abi.md` — the stable view, fuel, the
  selfhost decision, and the `termView`/fuel follow-ups.
* `docs/design/README.md` — the policy sentence (four interfaces).
* `docs/stages/21-bootstrap.md` §21ac — the selfhost's `syntax`/`macro_rules` boundary.
* `docs/stages/30-selfhost-typeclasses.md` §30a–30b — classes and `deriving` parity.
* `roadmap/program-next.md` — CORE-3.3/3.4, PK-3.5, SH-2.0a–2.5, R1/R4.
* `wiz-notes/ext-registry.md` and `wiz-notes/extensibility.md` §8 — the two lanes'
  records (uncommitted).
