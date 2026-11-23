# Code elegance review — 2026-11-23

A read-only smell pass over the train12 integration line and the active lanes, treated as a
proxy for "is this the code we would want to read in March". Nothing in the product tree,
tests, workflows or lanes was modified; this note (and its `INDEX.md` link) is the only
write.

## Scope and method

* **Integration line:** `git diff b5eb50555..28bfc1b6b` on `integration/train12`
  (`/workspace/wt/code-elegance`): the Lake-seed/Cachix rework, `scripts/ci.py`'s subset
  keys, the `ci.yml` job split, the new `flake.nix` artifacts, the selfhost
  plain-goal work, the Web.Loom canonicaliser and the static-playground tests.
* **Lanes, committed code only:** `structured-view` (`7bb588f14`), `ir-abi`
  (`59c64be5b`), `target-registry` (`d42108c9f`), `feeval-core` (`ebad89f4f`).
  `pkg-derivations`' two commits (`4dcde34e5`, `cd6a17005`) are already in train12 and
  were reviewed there. `ext-registry`, `ext-term-elab` and `cache-signed-index` have **no
  commits past the train12 merge** — their worktrees hold dirty/untracked lane work — so
  per the no-scratch rule they were not reviewed. The `Wiz/Ext` code that exists is on
  `agent/registry-abi` (`208cffc49`); it was read only to compare its target table with
  the one on `target-registry` (finding 2).
* **Static checks run:** `check-boundaries`, `check-doc-links`, `check-docs-style`,
  `check-name-collisions`, `repo-subsets.py --check`, `check-prelude-drift` and
  `check-complexity --diff b5eb50555` are clean. **`check-companion-lists.py` fails** at
  HEAD (finding 1). No build, test group, `lake` or `nix` command was run.
* Paths in the location column: `main:` is `/workspace/wt/code-elegance`; `lane:<name>:`
  is that worktree. Line numbers are this tree's.

## Ranked findings

| # | severity | location | smell | concrete suggestion | effort |
|---|---|---|---|---|---|
| 1 | **high** | `main:legacy-names.tsv`, `main:Wiz/LegacyNames.lean` | The integration line is red on a static gate: `check-companion-lists.py` exits 1, and `check-names.py --quiet` reports 33 declarations with no baseline row — 16 `lib/Web/Loom.wiz`, 12 `web/framework/hash_gen.wiz`, 1 `web/playground-ui.wiz`, 4 `web/playground_static_gen.wiz`. The last baseline refresh (`086da8e7a`) predates the web merge, so the first gate `docs_style` runs is stale. | Run `scripts/gen-legacy-names.py` and `--update-digest`, commit both files. A generated baseline has to travel with the declarations it covers; the web merge added the declarations and did not add the rows. | S |
| 2 | **high** | `lane:target-registry:Wiz/Compiler/Target.lean:30-44`, `Wiz/Ext/Basic.lean:101,206-223` (`agent/registry-abi` `208cffc49`) | Two modules each call themselves the one `--target` name table, and they disagree before either lands: `Target.lean`'s mapping table promises `Target.aliases → Entry.aliases`, but Ext's `Entry` has **no `aliases` field**, and `Ext.backendEntries` omits `ebpf` (the host CLI already accepts it). `Target.all` and `Ext.backendEntries` also duplicate the five names. | Land Ext as the only table and make `Target` a view of it (the doc already says to), add `aliases` to `Entry`, and add a test that pins `ebpf` through whichever table is live. Until then, a test comparing `Target.all`'s names to `Ext.backendEntries` catches the divergence. | M |
| 3 | **high** | `main:flake.nix:624-1055`; no workflow reference | Seven new derivations (`wasm-fixtures`, `web-bundle`, `docs-site`, `pages`, `release-unwrapped`, `release-tower`, `release-bin`) are built by **no job**, so their `doCheck`s — the portability test, the static-site checker, the no-store-path scan — are the evidence the docs cite but never execute. `passthru.subset` is read by nothing either; it is prose that duplicates `docs/building.md`'s table. | Add one nightly/master job (`nix build .#wasm-fixtures .#web-bundle .#docs-site .#pages .#release-bin`) so the checks run, or mark them "unexercised" in `docs/building.md`/`docs/release.md`. Make `passthru.subset` a list of subset names a check can compare with `repo-subsets.json`, or delete it. | M |
| 4 | medium | `main:.github/workflows/ci.yml:489-517` vs `:1263-1282`; guards `:576,:871,:1324`; pushes `:580,:595,:875,:1327,:1341` | The 15-line "Trusted Lake seed" step is copied verbatim into `lean` and `wasm`; the empty-token guard appears three times, and the `nix develop .#ci … cachix push` invocation five times with two token/name variants. | One composite action `.github/actions/lake-seed` (fetch base, `git archive`, `lake-cache.sh trusted`, output) and one `.github/actions/cachix-push` (cache name, token, paths, `allow-missing`), the way `.github/actions/setup` already factors the shell. | M |
| 5 | medium | `main:.github/workflows/ci.yml:349,1474` | Both docs caches are keyed on the `docs` subset alone, and that subset is `docs/**`, README/CHANGELOG/AGENTS, `.github/**` — **not `lib/`**. The old key deliberately carried `git rev-parse HEAD:lib` in the key (not the prefix), so a lib-only push refreshed the snapshot. Now the exact key does not move, `cache-hit` is true, and the save step is skipped: every lib change re-elaborates and is never written back. The tests/trust-ledger keys still pin the lib tree, so the sibling paths disagree. | `--suffix "$(git rev-parse HEAD:lib)"` for `docs`; for `docs_examples`, either add the compiler hash to the key again or rely on the checker's internal key knowingly (and drop the outer-save claim in the comment). The `--suffix` flag exists for exactly this. | S |
| 6 | medium | `main:scripts/ci.py:729-790`; `main:.github/workflows/ci.yml:195-205,1674+` | One subset table has four hand-maintained views: the JSON, the `changes` job's six `subset_*` outputs, the job `if:`s, and the `CI result` `want_*` checks. A subset added to `repo-subsets.py` gates nothing and no check fails; `subset-key lean --with` (missing value) raises `StopIteration`/traceback rather than a usage error. The two table loaders also catch the same JSON errors twice with different exception types. | One `load_subsets()`; `next(it, None)` + `raise SystemExit("--with needs a name")`; add a `docs_style` check that the workflow's declared `subset_*` outputs (and the CI-result list) equal the JSON keys. | S-M |
| 7 | medium | `main:scripts/lake-cache.sh:28-36,97-108`; `main:scripts/README.md:32` | `lake-cache.sh key` is dead after `ci.py subset-key` replaced both call sites; its `uname`-based key spelling also differs from the new `platform.system()`/`machine()` one, so it is a trap for the next reader. Its header and the README still advertise it. | Delete the `key` arm and its header block; drop the `lake-cache.sh key` reference from `scripts/README.md`. | S |
| 8 | medium | `main:flake.nix:669,703,766,820` and `:769,823` | Four copies of the store-path scan with two different regexes (`'/nix/store'` vs `-E '/nix/store/[0-9a-z]{32}-'`) and two messages; two copies of the build-root scan. The comments in the two docs jobs claim the same rule the wasm fixture job states differently, so "what counts as a leaked path" depends on which output you read. | One `noStorePaths dir` and one `noBuildRoot dir` helper in the flake's `let`, with the strict regex and one message; call them from every derivation. | S |
| 9 | medium | `main:selfhost/Frontend.wiz:429-433` and `:5223-5228` | The new `Size` builtin is a second copy of the name→term switch: `elab` handles `Unit`/`Size`, `identHead` handles `Unit`/`True`/`False`/`Size`, with near-identical comments. This is exactly the hard-coded switch `docs/design/README.md` says not to grow, and the two copies return different result shapes (`.size` vs `.size (.vsort …)`). | One `builtinTerm? : String → Option (Term × Val)` table consumed by both, the seed of the data-driven term elaborator; a test can then assert both scopes answer the same names. | S-M |
| 10 | medium | `main:selfhost/Cli.wiz:2680-2759` | `lspGoalBlockGo`, `lspGoalStartingGo`, `lspGoalInsideGo` and `lspGoalBeforeGo` are four ~20-line list scans with the same skeleton (skip `term`/`decl`, filter on phase and range, keep the best), and four tie-break rules that are easy to transpose — starting/block prefer the *larger* span on a tie, inside/before the *smaller*. | One `lspGoalScan` parameterised by the phase, a range predicate and a `better` comparator (or a small `GoalRule` record); put the four rules in one comment/table. The `h<n>`-style manual threading is not needed here. | M |
| 11 | medium | `main:Tests/Meta.lean:967-974` | The D3 test's message says "the bridge is not vacuous", but the assertion is `markedTerms == 29`; it also pins `outside == 102`, `preRejected == 283`, `bothAccept == 250`. Any improvement to the marking pass (fewer pre-rejections, a better marker) is then a red test, not a regression. | Keep the invariants (`verdictChanges == 0`, `typeChanges == 0`, `markedInFragment == 0`), assert `markedTerms > 0` for non-vacuity, and print the census (283/250/29) in the summary line; pin the corpus size (635) so the counts stay meaningful. | S |
| 12 | medium | `lane:target-registry:Main.lean:966-1002` | `--target NAME`, `--llvm` and `--wasm` each repeat the same "recurse, match `other`, compare, throw `two targets`" block; a fourth alias would be a fourth copy. | `pick (want) (rest)` doing the recursion/compare once; each arm becomes `checkTarget want; pick want rest`. | S |
| 13 | low | `main:flake.nix:1057-1070,1226,1236`; `main:docs/release.md:68` | `release-tarball` now means the **source** tarball while `release-bin` produces the **binary** release tarball; `docs/release.md` calls the binary "the release tarball" too. Two artifacts, one phrase. | Rename the source output to `source-tarball` (keep `release-tarball` as a deprecated alias one release), and use "release archive" for `release-bin` in prose. | S |
| 14 | low | `lane:ir-abi:lib/Ir.wiz:209-214,231-259` | `Ir.bind` reimplements `Except.bind` (`lib/Functor.wiz:77`) — the comment explains "no `do`", not why bind is duplicated; `namedNatList` and `namedBits` are the same wrapper with a different element parser. | `import Functor` and use `Except.bind`; one `namedList (parse : Sexp → Except String α) (head : String)`. | S |
| 15 | low | `lane:feeval-core:selfhost/FeEval.wiz:50-56,217-221,244-258` | The Tac tag numbers are a **third** copy (host `TacTag`, the prelude's `Tac`, these `feTac*` constants); `feMem`/`feFindPartial` duplicate `String.elem`/`String.lookup`; `feCtorsOf` silently drops a constructor it cannot find, so a prelude rename turns encoders into `none` instead of failing loudly. And 931 lines have no caller and no CI group. | Generate the tag table from `TacTag` the way `targetsSource` does; use `Text`'s helpers; assert the core ctor table resolves completely at startup; land E1 with the first caller (or keep the skeleton in the note). | S-M |
| 16 | low | `main:web/framework/runtime.js:55-130` vs `:133-232` | `applyFast` and `applyMorph` duplicate the whole op dispatch (`text`/`setAttr`/`removeAttr`/`insert`/`remove`/`move`/`default`), though only `replace` and `text` differ; a new op must be added twice or the morph path throws "unknown patch op". | One dispatch table whose `replace`/`text` entries are the only ones the morph path overrides; the rest call the same helpers. | S-M |
| 17 | low | `main:docs/building.md:1002-1003` | "then its own previous untrusted seed" is a third seed choice the code no longer has: `choose .subset-cache/lean <base seed>` is two choices. `scripts/lake-cache.sh`'s header is already correct, so the two documents disagree. | Delete the clause (the PR's own `.subset-cache/lean` then the base commit's store path). | S |
| 18 | low | `main:web/modules-from-store.sh:4,50` | The script still names the old `web_modules` job in its header and its error ("the web_modules job must build and publish them"); the job is `wasm` in the same line. | Rename to `wasm`; the workflow's own comments already use the new name. | S |

### Small nits

* `lane:target-registry:selfhost/Cli.wiz:1197` — `probeRefusal` embeds `docs/selfhost-compiler.md:114`; a line number in an error message drifts. Cite the section heading instead.
* `main:web/check-site.sh:107` — "Every local ES import of a page's scripts resolves" only matches `from "./…"`; a side-effect `import "./x.js"` is silently unchecked. Match `import "…"` and single quotes too (or say "every `from` import").
* `main:.github/workflows/ci.yml:164-183` — the comment pins "the exact keys" with literal `lean12`/`toolchain12` hashes that move on nearly every commit; it already omits `docs12` for exactly that reason. Delete the example block — `subset-key` prints the live key.
* `main:web/framework/hash_test.mjs:25` — `TREE` is a third copy of the tree-hash grammar (`Loom.canonical`/`Wire.ssrHash`, `adopt.js:52`); export `TREE_HASH`/`parseTreeHash` from `adopt.js`. At `:37-39`, "sorts attributes" asserts the `A5:` length-prefix encoding; assert relative order only.
* `main:Tests/Groups/SelfHost.lean:3448` — A19 pins binder names (`szSuc : (x0 : Size) → Size`), so a pretty-printer change fails a case about surface sizes. Pin one line per declaration without the `x0` (the echo stub still cannot produce it).
* `main:Tests/Groups/WizLint.lean:245-246` — the v1-refusal test checks `splitOn "info"`/`splitOn "wiz-lint/2"`, i.e. substrings of a message; assert the refusal class and the full sentence, as the IR test does.
* `main:scripts/lake-cache.sh:158-165` — `choose` treats an empty argument as `/.lake` / `/toolchain`; skip empty entries before the `-d` test.
* `main:lib/Web/Loom.wiz:276-285` — `sortAttrs` is insertion sort (quadratic in an element's attribute count). Bounded and deliberate; do not "fix" it, but say so if the file grows an unbounded aria/`data-*` path.

## Good patterns worth copying

1. **One table, generated into the other language, inside its cache identity.**
   `Wiz/Compiler/Target.lean`'s `all` is the only list of `--target` names;
   `Wiz/Selfhost.targetsSource` (`Wiz/Selfhost.lean:90`) renders it as Wiz definitions
   spliced into `selfhost/Cli.wiz`, and `toolchainId` (`:187`) includes that generated
   text, so changing the table makes the self-hosted cache cold. The driver keeps no
   second list, and the host/selfhost refusal sentences are pinned by
   `=selfhost-cli-diff`. This is the pattern most worth copying: it removes the class of
   bug that finding 2 is, rather than testing around it. **Runner-up:** the same idea in
   `Wiz.Selfhost.wizTables` for the parser tables.
2. **A non-vacuity meta-case.** `Tests/Groups/SelfHost.lean:4570+` runs every `=selfhost`
   case under a compiler/checker that echoes its input and requires each to fail; a new
   case that forgets to invoke the pipeline fails by construction, and the sweep now has
   a per-case 600 s bound and a 45 min aggregate bound (so a hang is reported by name).
   That is how a "the test group is real" claim should be made.
3. **One table with a generated copy and a checker that proves it current.**
   `scripts/repo-subsets.py` owns the subset split, writes `.github/repo-subsets.json`,
   `--check` proves the copy still describes `git ls-files`, and `--self-test` proves
   locality. The one gap is that its consumers (the workflow's outputs) are not checked
   (finding 6) — the pattern is still the right one.
4. **A hash whose identity rules are tested, with a collision witness.**
   `lib/Web/Loom.wiz:236-349` hashes the normalised tree (`t1-<digest>-<length>-<nodes>`),
   `web/framework/adopt.js:52` treats a digest match with a different witness as
   `hash-collision`, and `hash_test.mjs` pins exactly the distinguishing cases: attribute
   order, whitespace, a real change, a key, child order. The fixture is generated by the
   Wiz implementation itself (`web/framework/hash_gen.wiz`), so the test compares two
   implementations rather than a golden the author typed.
5. **A narrow, documented exception to a rule, at the site.** `scripts/scrub-store-paths.py`
   says in its own doc why it is *not* what a Nix package does, that the replacement is
   same-length so offsets stay valid, and "do not call this on an intermediate
   derivation". The flake's `release-bin` repeats the rule at the call site. A reviewer can
   tell an intentional rule-break from an accident.
6. **Aliases instead of copies.** `Wiz/Elab/View.lean` took `hiddenName` and the binder walk
   out of `Wiz/Lint.lean`, and `Wiz/Lint.lean:89,372` aliases them, so `W101`/`W102` and
   `Tac.getBinderFacts` read one traversal. That is the opposite of finding 9.
7. **Refusal as data.** `Wiz/Compiler/Target.lean`'s `unknown`/`unsupported` split, and
   `Wiz/Ext`'s `Refusal { code, message }`, make a driver print a stable sentence instead
   of inventing one; the selfhost parity test pins the two sentences that must agree.
8. **The inline excuse.** `scripts/check-complexity`'s `-- complexity: ok (reason)` carries
   the review next to the line, through moves and reindents, and deletes with the line. A
   small design worth keeping for every "this looks wrong but is bounded" site.

## Do not "fix"

* **The two `h<n>` namespaces in the structured view.** `docs/lint-abi.md:143-148` says a
  `binder-info` handle is meaningful only among its declaration's binder rows and an
  `info` handle only among the command's rows; `h0` appearing in both is the documented
  contract, and `Tests/Groups/WizLint.lean:267-269` exercises it. "Unifying" the counters
  would change the ABI for no reader.
* **`release-bin`'s leaf-only ELF work.** The `patchelf`/`strip`/`scrub` step
  (`flake.nix:996-1049`, `docs/building.md` "Nix artifacts for CI and releases") is the
  one place allowed to break Nix convention. Do not move it into an intermediate
  derivation, and do not make it a "normal" package.
* **`Target.supported`/`reason` as an interim seam.** `Target.lean:47-56` deliberately
  does not carry `set`/`caps`; adding them now would be the second registry the doc warns
  about. Replace the table with `Wiz.Ext` when it lands instead.
* **Wiz's total-function style** (`match Nat.beq n 40` chains, no `do` in `lib/`). It is
  the house style and the code is total by construction; the deep nesting is not the smell
  this pass is looking for.
* **`lake-cache.sh trusted` using `nix path-info`/`nix copy`, never `nix build`.** The
  comment at `scripts/lake-cache.sh:129-135` says why: instantiating the derivation can
  build the cold seed and then the seeded build, the duplicate compile the branch exists
  to avoid. Do not "simplify" it to `nix build`.
* **`adopt.js` replacing the whole container on any hash mismatch.** One decision per
  container, no partial adopt, is the contract (`docs/notes/loom-wire-protocol.md` §4.1);
  the morph path is an optimisation inside a batch, not a second adopt policy.
* **The test bounds** (600 s per selfhost case, 45 min sweep, 512 MB parser bound, step
  budget). They are liveness guards with a named failure, not flaky-test padding.
* **`Loom.collapseSpace` keeping leading/trailing space**, and `verbatimTag`'s
  `pre`/`textarea`/`script`/`style` list. Both are content-model choices the tests pin;
  "normalising harder" would change page identity.

## Suggested next actions (cheapest first)

1. Regenerate `legacy-names.tsv` + `LegacyNames.lean` (finding 1) — the only red static
   gate found.
2. Add the `--suffix "$(git rev-parse HEAD:lib)"` to the docs cache key (finding 5).
3. Delete `lake-cache.sh key` and the README line (finding 7).
4. Add the composite action for the Lake seed and the Cachix push (finding 4).
5. Reconcile `Wiz/Compiler/Target.lean` with `Wiz/Ext.Basic` before either lands
   (finding 2) — a test comparing the two names/aliases is enough until the merge.
