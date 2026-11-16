<!-- Mirror of /workspace/wiz-notes/wishful/TRIAGE.md (the canonical notes directory is outside the repo). -->
# Wishful triage, 2026-11-15

Sweep of all 86 entries in `wishful/` (the README is not counted), against
`origin/master` `627b48f6` in `/workspace/wt/wish-triage` (branch
`agent/wish-triage`). Each entry was read for `status:`, `needed-by:`, `decision:`
and body, then checked against the tree: `git merge-base --is-ancestor` for every
cited commit, `grep` for the symbol or command, the issue list for #252–#322, and
a small `wiz check` probe where the source alone was ambiguous. Probes used the
master build at `bea4396e` (five commits ahead of the branch tip; no relevant
difference) and stayed inside `timeout 60`, no cache, no heavy job. No push.

Every file now has a dated `verified:` line. Statuses were changed only where the
evidence was conclusive; other prose was left alone.

## Counts

| class | files |
|---|---:|
| done (feature exists on master) | **58** |
| unblocked (the gating decision or blocker landed) | **5** |
| still wanted (real, ready to implement) | **12** |
| blocked (named blocker still open) | **10** |
| stale (optimistic code gone / decision changed) | **0** |
| dropped | **1** |
| **total** | **86** |

There is no entry whose optimistic code disappeared: `drafts/feral`, `drafts/hdl`
and `drafts/vec-lib` all still exist, and no cited decision was reversed. The one
process entry (`wishful-status-drift`) is dropped because the drift itself is
gone: all four commits it called unmerged are ancestors of `627b48f6`.

## The table

### Done (58)

| file | evidence on `627b48f6` |
|---|---|
| as-patterns | 13g `term.asPat` (`Parser/Builtin.lean:256`); f3c7019 ancestor. `Vec.last` still limited by the family scheme, as the file says. |
| cast-refl | `axiom castRefl` (`lib/Prelude.wiz:37`), used in `lib/Optic.wiz` and `lib/Vec.wiz`. |
| c-sources | `link_c`/`link_lib`, docs 9f. |
| compiled-closed-constants | 3ef38ad8 (15i) CAFs in C and LLVM. |
| conv-sigma-eta-neutral | 71b7dc70 (#286): neutrals compared before Π/Σ η. |
| copattern-cocon | 9717950; `elabCopatternsCocon` at `Elab/Command.lean:926`. |
| ctor-params-from-expected-type | acd1b34 + 50ff179; elabfix test; selfhost 21j. |
| do-let-omega-scope | eced3c78; `letBindW`/`T`/`P` doSeq rules; elabfix test. |
| do-match-expected-type | eced3c78; elabfix test. |
| elab-bugs-from-hdl | items 2–4 fixed (fc3c454f, eee22ef); item 1 now 1.9 s for 17 fields (was ~13 s). |
| elab-postpone-lambdas | c7a04dd/7992435; elabfix test. |
| elab-rfl-unchecked | 893de491 (`sameSides`); elabfix test. |
| elab-solve-type-before-body | 50ff179; elabfix test. |
| eq-pending-metas | 50ff179; words/builtins tests. |
| error-message-size | eced3c78: `elideLong` (`Pretty.lean:755`), test "a type in a message is bounded". |
| feral-import-deriving | 2f505047; `ElabFix.lean:750`. |
| ffi-callbacks | docs 9g; `export "c"`, `Callback`, `wiz build --lib`. |
| grail-command-targets | b17eac06 (23i–k): `Package.command`, `Command.new`, `grail run`. |
| hdl-circuit-composition | 8f39a932: `Circuit.seq/par/loop/delay`. |
| hdl-named-ports | 8f39a932 + `Netlist.describe`; remaining items are the two files below. |
| hdl-reset-enable | 8f39a932 + f45710df (S4); async reset deferred. |
| hdl-sim-scaling | 6da92af7 (H14 S3): `Netlist.simFast`/`Design.simFast`. |
| implicit-lambda-binders | `fun {n}` binds by name; `fun {ω n} => n` checks. See Ambiguous. |
| import-shadowing | "declared by both" at `Elab/Command.lean:222`; `Tests/Grail.lean:489-502`. |
| io-args | `lib/IO.wiz:212-226`; selfhost natives (21k). |
| let-tuple-patterns | 1d0f7fa (13f). |
| list-literals | f7153472 (13k); probe prints conses; Language test. |
| machine-int-literals | `OfNat (UIntN w)` in `lib/Word.wiz`; wrapping. |
| memoised-codata | b9dda3f4: `lazySet` + `wiz_lazy_set` (`rt_words.inc:73`). |
| mutual-ctor-names | 3f882627; `Tests/Grail.lean:580`, `Groups/Deriving.lean:108`. |
| numerals-in-class-decls | b3b1d1f; elabfix test. |
| numeric-classes-bitvec | Prelude `Add/Sub/Mul/Div/Mod/Neg/OfNat`; `lib/Word.wiz`. |
| phantom-parameters | `phantomTail` (`Elab/Inductive.lean:81`); `lib/Word.wiz` uses it. |
| prelude-functor-applicative | `lib/Functor.wiz` (e59fe70, 13d). |
| prelude-if-bool-ops | `lib/Prelude.wiz:456`; e2f8198 (13c). |
| prelude-int | `lib/Int.wiz` (7e). |
| private-decls | `Globals.privates`/`elabView`; 13b tests; `lib/Region.wiz`. |
| projection-functions | f03690c; elabfix test. |
| quotation-splices | 13t; used by `lib/Deriving.wiz`. |
| region-indices | 30fa72a7 (22j): `'a` tokens; items 1–2 in `lib/Region.wiz`. |
| selfhost-phantom-parameters | a97e0dc2 (21i); `=selfhost` tests. |
| slow-failing-unification | 0c5e580f (#230): failure cache, `Unify.lean:425`. |
| string-append-operator | f7153472: `class Append` (`Prelude.wiz:1332`). |
| structural-rec-column-order | d3bfc851 (#249); FINDINGS B4 shape checks (probe). |
| structure-patterns | bc5462d (13h); language tests. |
| structure-update | b6007ef (13i); language tests. |
| syntax-reserved-keywords | b8859b4 (13j); `feral_kw`. |
| sys-serial-bytes | 7433a878 (9k): `lib/Serial.wiz`, `File.readBytes`, `Fd.*Within`, `Pty`. |
| sys-tower-gaps | 7433a878: `FS.realPath`, `IO.appPath`, `SpawnOptions`, `Clock`. |
| tactic-hygienic-names | 053a6eb; docs 6e. |
| tactic-reflect-constructors | bd61cef; docs 6g. |
| tactic-trace-output | a2e7862; docs 6d. |
| tactic-whnf-unfold | e4a1aba; docs 6f. |
| trailing-instance-args | 9b85684; elabfix test. |
| uintn-range-proof | 5dd80517 (22l): private `mk` with range proof, `toNat_lt`, `cases1`. |
| unify-nonlinear-spine | PR #92; workarounds removed. |
| unknown-dotted-name | 506d4efd (#273/#266); probe reports `'A.g'`. |
| vec-literal | 13s; `#v[…]` in `lib/Vec.wiz`. |

### Unblocked (5)

| file | blocker that landed | what is left |
|---|---|---|
| beq-indexed-families | HD8 deriver mechanism (9717950) | `Derive.noIndices` is the only gap; `deriving BEq` on `Vec A n` still throws. |
| deriving-bitpack | `attribute [deriver BitPack]` (`Hdl/Core.wiz:3789`); 22l range proofs (5dd80517) | inductives with fields (tag + widest constructor) and the general `ofBits (toBits s) = s` law. Enums/bundles already work. |
| final-specs | RD11 named optics; `specGo` in `lib/Feral.wiz:2920-2976` | `final result` (`Feral.wiz:3095`) and specs with outlives bounds. |
| implemented-by | type-level native repr (`implemented_by mk get`, R0b/22d); selfhost command (`Frontend.wiz:5465`) | `Vec A` as an array (`takeAt`/`fillAt` and a multi-operation model). |
| sized-signal-fix | HD1 combinators: `Circuit.seq/par/loop` (8f39a932) | sized `scofix`/`Signal.fix` itself. |

### Still wanted (12)

| file | why it is still real |
|---|---|
| command-proc-macros | Feral has located output and `#lower`, but no cross-block state (`getState`/`setState` absent), no `import` inside `feral`, no Wiz-global queries. |
| constructor-contexts | no `Ctx.fill`/`Ctx.comp`; the lowering still uses closures/zippers. Backend-only, "measure first". |
| copattern-escape | `graft` with `.right => t` still fails "must be a corecursive call"; only pure coit/cocon. |
| elab-head-meta-first-order | the `frame9` flex-flex repro is fixed; the converse first-order mis-solve was not reproducible in a small file. |
| erased-use-in-types | `substP` still fails "variable y … used ω"; `transp` motives are scaled as computation. |
| fixed-params-recursion | `count (acc + 1) xs` still rejected; #267 open. |
| hdl-commands | no `attribute [hdl]`, `#netlist` or `#verilog`; only library functions. |
| hdl-let-names | no `ShareLet.shareNamed`; `let` wires stay `nK`. |
| nat-arith-proofs | `lib/Nat.wiz`/`ListLemmas.wiz` lemmas exist, but no `induction`/`omega`/`simp`; #253 open. |
| prop-connectives | notation is done; native inductive props (D4) still open, #252. |
| spec-clauses | `requires`/`ensures`/`final` done; loop `invariant`, `decreases`, `final result` missing. |
| string-patterns | still "String has none" for literal patterns. |

### Blocked (10)

| file | blocker |
|---|---|
| decreases-loops | no well-founded recursion/`termination_by` (`docs/stages/04-data.md:369`); RD8. |
| hdl-circuit-universe | `List` is not universe-polymorphic (`Prelude.wiz:106`); a `Type 1` `Circuit` cannot enter it. |
| hdl-staging-2ltt | still designing: no L3 stage modality in the elaborator; SD1–SD11 decided, S2 not started. |
| kernel-eval-throughput | P1 glued equations still a plan; #155 closed without merging; no `lazyEq`. |
| linear-case | kernel R9a not started; only Feral's front end rejects E0499/E0502. |
| nat-pow-blowup | fix 95cc9e9d is on unmerged `agent/kernel-eval-batch`; huge-power probes still panic. |
| numeral-sub-blowup | same unmerged 95cc9e9d; `h - 2^(2^34)` still panics. |
| reborrow-recursion | `rewriteRecCalls` is syntactic; `05_bst.wiz` still `partial def insert`. |
| selfhost-deriving | selfhost has `deriving BEq/Repr` (A11) but no elaborator-time evaluator/reflection (A12). |
| unify-computed-equations | unifier part landed (0576d91), but `Eq.trans h e1` still fails; #257 open. |

### Dropped (1)

| file | why |
|---|---|
| wishful-status-drift | the drift it documents is gone: e2f8198, b6007ef, bc5462d and 1d0f7fa are all ancestors of 627b48f6, and `if`, `{ s with … }` and list literals check. The rule ("done means on master") is still worth following, but there is no gap left to track. |

## Top ten: highest-value unblocked / still-wanted

1. **beq-indexed-families** (unblocked) — `Derive.noIndices` is the only gap; it unblocks `BEq`/`DecidableEq` for `Vec`, `BitVec` and every indexed family.
2. **deriving-bitpack, inductives with fields** (unblocked) — Uart's `TxState` and Cpu's `Instr` need tag + widest-constructor packing; enums and bundles already derive.
3. **final-specs, `final result`** (unblocked) — the last missing piece of Feral specs for functions that return a borrow; `final`/`old` already desugar.
4. **implemented-by, `Vec` as an array** (unblocked) — turns the Rust lowering's list model into O(1) access while keeping the kernel model provable.
5. **sized-signal-fix** (unblocked) — HD1's "combinators first" stage landed (`Circuit.seq/par/loop`), so Clash-style `Signal.fix` feedback is next.
6. **spec-clauses, loop `invariant`/`decreases`** (wanted) — the remaining half of the Feral verification story; `requires`/`ensures`/`final` are already in.
7. **fixed-params-recursion** (wanted, #267) — a cheap elaborator fix; idiomatic `count (acc + 1) xs` is still rejected, forcing every tower/icestick helper to reorder arguments.
8. **hdl-commands** (wanted) — `#netlist`/`#verilog`/`attribute [hdl]` would retire the string-built Verilog and PCF paths in the iCEstick demo.
9. **command-proc-macros, items 3–5** (wanted) — cross-block macro state and Wiz-global queries are what keep Feral a one-file DSL.
10. **hdl-let-names** (wanted) — a small `ShareLet.shareNamed` hook makes `let` wires readable in the netlist and Verilog; the rest of H14 S1 is already done.

Next in line: `string-patterns` (unlocks Feral/tower dispatch tables), `constructor-contexts` (in-place lowering), `copattern-escape` (codata trees), `erased-use-in-types` (proof friction).

## Issue cross-check (#252–#322 family)

The tracker currently double-counts the same gaps as both issues and wishful files.
Direct correspondences:

| issue | state | wishful file | now |
|---|---|---|---|
| #252 no inductive propositions | open | prop-connectives (D4 part) | still wanted |
| #253 no arithmetic automation | open | nat-arith-proofs | still wanted |
| #255 no list/Boolean lemmas | open | (none; `lib/ListLemmas.wiz` exists) | probably closable |
| #256 kernel `rfl` over a machine run | open | (none; 68dbd060 landed, but `kernel-eval-throughput` is a different complaint) | probably closable |
| #257 computed equation as `Eq.trans` arg | open | unify-computed-equations | blocked |
| #259 hypothesis before colon not refined | open | (none) | — |
| #260 unannotated motive escapes | open | elab-head-meta-first-order (related) | still wanted |
| #265 `some v = some w` | open | unify-computed-equations (related) | blocked |
| #267 parameters before the colon | open | fixed-params-recursion | still wanted |
| #268 `{ s with }` + `deriving DecidableEq` | open | structure-update (done), beq-indexed-families | update landed; close or narrow |
| #321 no namespaces | open | (none) | — |
| #322 `Eq.substBack` for Prop families | open | erased-use-in-types (related) | still wanted |
| #249/#270 indexed-family recursion | merged | structural-rec-column-order | done |
| #261/#274 `rfl` as a keyword | merged | (elab-rfl-unchecked is a different `rfl` gap) | done |
| #266/#273 unknown qualified name | merged | unknown-dotted-name | done |
| #286 neutrals before Π/Σ η | merged | conv-sigma-eta-neutral | done |

#255, #256 and #268 look closable on this evidence; closing them would remove
three double-counts. Issue #347 (root `grail test`) is not a wishful gap.

## Ambiguous — needs a human

1. **implicit-lambda-binders** — I marked it done because `fun {n}` now binds by name and `fun {ω n} => n` checks. But the file's example (`fun {n} a b => …` using `n` as data) still fails at quantity check, since `{n : Nat}` is quantity 0. Is the desired end state "implicit binders are ω by default" (a language decision), or is `{ω n}` the answer?
2. **nat-pow-blowup / numeral-sub-blowup** — both said `done`, citing 95cc9e9d; that commit is on `agent/kernel-eval-batch`, not master, and the file's own probes still print `INTERNAL PANIC: Nat.pow exponent is too big`. Merge the branch or re-open these as real bugs.
3. **kernel-eval-throughput vs unify-computed-equations** — both need P1 (glued equations, README 4.16); #155 was closed without merging. Is P1 still planned? If not, both entries need a different design.
4. **#268** — `{ s with … }` (b6007ef) and `deriving DecidableEq` (06b90879) both landed. The issue can probably be closed; the wishful files are already done.
5. **elab-head-meta-first-order** — the primary flex-flex repro (`Hw.cat (Hw.lit 1 1) d`) now checks, but the converse first-order mis-solve from the same file could not be reproduced without the icestick tree. Decide whether to keep the entry for that half or close it.
6. **hdl-staging-2ltt** — "designing" since 2026-11-10; SD1–SD11 are decided but S2 has not started. Keep it on the board or archive the entry until S2?
7. **error-message-size** — truncation landed (eced3c78), but the second ask ("print the type as written, not its computed form") did not. I marked it done on the 40 KB-message complaint; say if the un-normalised printing is still wanted.
8. **sys-tower-gaps** — the library delivers equivalents, not the requested names (`Process.runWith` instead of `runIn`, `IO.appPath`, `Clock.monotonic`). The features exist; tower's code may still need a port. Check whether the gap is names or behaviour before closing tower's side.
9. **grail-command-targets** — the API in the entry (`Package.rule`) never landed; the shipped API is `Package.command`/`Command.new` (b17eac06). The entry is done, but its `needed-by` paths are historical.
10. **wishful-status-drift** — dropped, but the underlying convention should be written somewhere permanent: `done (<commit>)` ought to mean the commit is an ancestor of `origin/master`, and the sweep found exactly the failure it predicted (95cc9e9d).

## Status corrections made in this pass

`beq-indexed-families`, `command-proc-macros`, `compiled-closed-constants`,
`conv-sigma-eta-neutral`, `decreases-loops`, `deriving-bitpack`, `do-let-omega-scope`,
`do-match-expected-type`, `elab-bugs-from-hdl` (status line added),
`elab-rfl-unchecked`, `error-message-size`, `feral-import-deriving`, `final-specs`,
`grail-command-targets`, `hdl-circuit-composition`, `hdl-circuit-universe`,
`hdl-sim-scaling`, `implemented-by`, `implicit-lambda-binders`,
`kernel-eval-throughput`, `linear-case`, `list-literals`, `memoised-codata`,
`mutual-ctor-names`, `nat-arith-proofs`, `nat-pow-blowup`, `numeral-sub-blowup`,
`reborrow-recursion`, `region-indices`, `selfhost-deriving`, `sized-signal-fix`,
`slow-failing-unification`, `spec-clauses`, `string-append-operator`,
`structural-rec-column-order`, `syntax-reserved-keywords`, `sys-serial-bytes`,
`sys-tower-gaps`, `tactic-hygienic-names`, `tactic-reflect-constructors`,
`tactic-trace-output`, `tactic-whnf-unfold`, `uintn-range-proof`,
`unify-computed-equations`, `unknown-dotted-name`, `wishful-status-drift`.
