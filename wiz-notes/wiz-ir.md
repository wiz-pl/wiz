# `wiz-ir/1`: the serialized IR

**Status.** Implementation lane `ir-abi`, 2026-11-23, worktree `/workspace/wt/ir-abi`,
branch `agent/ir-abi`, base `integration/train12` `f489cc876`. This is item ⑤ of
`wiz-notes/extensibility.md` §4, not a redesign of that plan. The code is
`Wiz/Compiler/IRDoc.lean` (emitter), `lib/Ir.wiz` (reader, printer, one pass) and
`Tests/Groups/Ir.lean` (the `=ir` group); the fixtures are
`Tests/fixtures/ir/one.ir`, `inline.ir` and `inline.out.ir`. **No build or test run is
in this lane** (the queue was held for train11 green); §5 is the exact ledger of what
was and was not checked. `bpf-core/1` stays a sibling schema: it carries types and this
document deliberately does not (`docs/stages/08-backend/bpf.md`).

## 1. The document

The format is a small S-expression with a version in the first atom. It is deliberately
canonical so that `render (parse text) = text` is a byte-for-byte test:

```
(wiz-ir/1
  (decl "twice" (params 0 1) (borrow 0 0) (dup 0 (vdecl 2 (ap 0 (1)) (vdecl 3 (ap 0 (2)) (ret 3)))))
)
```

* a header line `(wiz-ir/1`, one **declaration** per line prefixed by two spaces, a
  closing `)` line, and one final newline (LF);
* one space between fields, none before a closing `)`, no comments in emitted bytes;
* a reader accepts arbitrary ASCII white space and `;`-to-end-of-line comments, and a
  printer must emit the canonical bytes above.

```
doc      := "(wiz-ir/1\n" decl* ")\n"
decl     := "(decl " STRING " (params " VAR* ") (borrow " BIT* ") " BODY ")"
expr     := "(erased)"
          | "(lit " NAT ")"
          | "(ctor " TAG " (" VAR* "))"
          | "(proj " FIELD " " VAR ")"
          | "(fap " STRING " (" VAR* "))"
          | "(pap " STRING " (" VAR* "))"
          | "(ap " VAR " (" VAR* "))"
          | "(prim " STRING " (" VAR* "))"
          | "(reset " VAR ")"
          | "(reuse " VAR " " TAG " (" VAR* "))"
body     := "(vdecl " VAR " " expr " " body ")"
          | "(case " VAR " " body* ")"
          | "(ret " VAR ")"
          | "(jdecl " JOIN " (" VAR* ") " body " " body ")"
          | "(jmp " JOIN " (" VAR* "))"
          | "(dup " VAR " " body ")"
          | "(drop " VAR " " body ")"
          | "(unreachable)"
```

`STRING` is a quoted string; the escapes are `\"`, `\\`, `\n`, `\t` and `\r` and nothing
else. Names, foreign keys and primitive keys are strings; `VAR`, `JOIN`, `TAG`, `FIELD`
and `NAT` are decimal atoms. `prim` carries `PrimOp.key` (`nat.add`, or a whole `extern:`
key), not a Lean constructor: a package backend owns its primitive table and refuses
what it does not implement.

Schema rules:

1. **Borrow.** `(borrow …)` has exactly one bit per parameter, in parameter order: `1` is
   a borrowed parameter (stage 8e), `0` owned. A reader refuses a length mismatch. The
   emitter pads `Decl.borrow`'s short form to one explicit bit per parameter, so a
   document never depends on the short-form default.
2. **Case order.** `(case x b0 b1 …)` is in tag order: alternative `i` is tag `i`.
3. **Join scoping.** `(jdecl j (p…) body k)` is `join j(params) := body; k`; `body` may
   only use its parameters, and `jmp j (args)` jumps to it. Join ids and variables are
   separate number spaces in the IR and stay separate here.
4. **Order.** Declarations are emitted in the IR array's order (lowering sorts by name
   and appends the primitive code, entry and export wrappers); a reader preserves it.
   Nothing in the document is a hash-order artifact.
5. **No source positions and no types.** It is the backend's input, not the typed core:
   the typed form is `bpf-core/1`, and recovery of source spans is not a promise of v1.

The canonical printer lives in both implementations: `IRDoc.render` (Lean) and
`Ir.render` (Wiz). The Wiz reader is independent (there is no Lean parser) so the
round-trip test is not a printer checked against itself.

## 2. Version refusal

The first form's head must be exactly the atom `wiz-ir/1`. The reader's rule, in
`Ir.docOf`:

* `wiz-ir/1` — accepted;
* `wiz-ir/N` with `N ≠ 1` — refused with
  `ir: unsupported version wiz-ir/N (this reader is wiz-ir/1)`;
* anything else — refused with `ir: not a wiz-ir document`.

There is no minor version in v1. A consumer matches the forms above exhaustively, so
**any** grammar change (a new form, a renamed field, a changed bit width) is a new major,
and v1 is frozen. Unknown forms are refused (`ir: unknown expression form`,
`ir: unknown body form`), not ignored: a backend must never silently build half a program.
`wiz-ir/2` may add optional fields and must say how a v1 reader fails; it may not reuse
the v1 name. The CLI path has the same rule because it uses the same reader.

## 3. The one pass, and why it is Inline

`Ir.inlineIdentity` / `IRDoc.inlineIdentity` eliminate a call of a definition whose
parameters are one variable and whose body is `ret` of that variable:

```
let x := f a; b        f = λp. ret p        ⟹        b[x := a]
```

The substitution renames `x` in expressions, case scrutinees, join arguments and in the
**arguments** of `dup`/`drop` (they are reference-count operations, not binders); it
stops at the real binders `vdecl` and `jdecl`. Declarations are kept, because an exported
identity function is still part of the program.

Why this and not `Inline.lean` or `Push.lean` as written: both compiler passes run
*before* the IR. `Inline.inlineSimp` rewrites `ETerm` (de Bruijn indices, lambdas and
`fix`) inside `compileReachableE` (`Wiz/Compiler/Run.lean:899`), before `lowerProgram`;
`Push.pushCalls` rewrites the checked `Term` before erasure (`Wiz/Compiler/Push.lean`).
A `wiz-ir/1` consumer cannot see either input, so reimplementing them "over the
document" would not be the same pass and would need the ownership information that the
document does not carry. Identity elimination is the slice that is unambiguously
ownership-neutral: the call consumed its argument and the uses now read it directly,
and any `dup`/`drop` already present is substituted too. It is small on purpose; a
faithful IR inline is in §4.

The pass is **not** part of the emitter. `wiz ir` writes the IR that `Build.irProgram`
produced (post-lowering, post-`optimizeProgram`); a package backend runs the pass if it
wants it. On the current corpus the compiler has already inlined its trivial forwarders
(`trivialBody`), so the pass is usually a no-op there — the tests therefore also carry
`inline.ir`, where it fires.

## 4. CLI and what remains

`wiz ir FILE [-o OUT]` writes the document of `main`; `wiz build FILE -o OUT --emit-ir`
is the same output and does not invoke a C compiler or linker. `Main.lean` elaborates as
`wiz check` does and stops before target selection, so the build graph is untouched.
Grail has no `--emit-ir` target yet; a `grail` target would be the natural second
consumer once item ①'s backend entry model is on the tree.

What remains, in dependency order:

1. **RC/borrow annotations in a pass.** The document records `borrow` bits but does not
   carry the derivation of `dup`/`drop`/reuse. A backend can use the bytes as they are;
   an IR pass that rewrites them must either preserve ownership exactly (as the identity
   pass does) or implement the `Borrow`/`RC` analyses over the document. Until then the
   one pass is the only promised equivalence.
2. **A backend consumer through item ①'s registry.** `wiz-ir/1` proves the payload can
   be a file; it does not yet prove a `demo` target can be resolved and write an
   artefact. That is item ①'s second consumer and is not in this lane.
3. **A faithful Inline (and a `Push` equivalent).** Both need the ownership story in 1,
   and a use-count pass over the document. Do not call a text rewrite "the compiler's
   Inline" before that exists.
4. **A streaming reader / bounded parse.** `Ir.parse` is a whole-string recursive
   descent. It has no input cap (unlike `Json.parse`'s `maxInput`); a backend reading an
   untrusted file needs one, and a large program needs the parser to stop copying the
   token list. Measure before choosing either.
5. **Grail target plumbing and a `--check` mode** for a package backend that wants
   `wiz ir --check FILE` (parse and refuse without building). Not in this lane.

## 5. What was verified, and how

**Checked statically** (the lane's allowed checks):

* `git diff --check` — clean.
* `scripts/check-libdiff-corpus.sh --quiet` — `lib/Ir.wiz` added to
  `.github/libdiff-corpus.txt`, the walk is total.
* `scripts/repo-subsets.py --write` then `--check` — the new Lean module, Wiz module,
  test group, fixtures and notes move the `lean`, `wizlib` and `tests` subsets.
* `scripts/gen-legacy-names.py --update-digest` and `scripts/check-names.py --quiet` —
  the baseline was regenerated (it also carries 33 pre-existing `web/`/`Web.Loom` rows
  the base lacked) and the digest is current; `check-name-collisions.py --quiet` is
  clean.
* `.github/test-shards.json` parses; `=ir` is selected by the `library` shard.

**Checked with the installed command, not the worktree build.** `wiz 0.1.0-dev
(aeaa34ef8527c2a72e703959742f7a99d9c03fc9)` (from `PATH`) elaborated `lib/Ir.wiz` against
this worktree's `lib/` with no diagnostics, and `#eval` on the fixtures produced the
expected bytes: `Ir.render (Ir.parse one.ir)` is `one.ir`,
`Ir.render (Ir.inlineIdentity (Ir.parse inline.ir))` is `inline.out.ir`, and `Ir.parse`
on `wiz-ir/2` gives the exact refusal text. `#ir twice` on the same `lib/` printed the
body in `one.ir`. This validates the Wiz half (it is not a `lake` build of the worktree):
it does not compile the test group, and it does not exercise a full program document.

`IRDoc.lean` was also compiled with `lean` against a minimal stub that repeats
`IR.lean`'s `Var`/`Name`/`PrimOp.key`/`Expr`/`Body`/`Decl` signatures (the worktree has
no oleans, and `lake`'s cached oleans are not usable here). Running the emitter on the
`twice` declaration and the pass on `id`/`main` reproduced `one.ir` and `inline.out.ir`
byte for byte. This catches the Lean syntax and the printer's string building; it is not
the real module build, and it does not prove `Build.irProgram` gives that declaration in
a built worktree — that is the first `=ir` case to run.

**Not run** (the reason this note is not an acceptance claim):

* `lake build` of `Wiz/Compiler/IRDoc.lean` and `Tests/Groups/Ir.lean`;
* `lake test -- '=ir'`, `lake test -- =backend`, or any C build;
* `wiz ir` on a real file from this worktree.

So `one.ir` is the expected emitter output for the `twice` declaration that
`=backend` already pins through `#ir` (`dup x0; let x2 := ap x0 x1; let x3 := ap x0 x2;
ret x3`), but the emitter-vs-fixture case has not run. If it disagrees, the first suspect
is the `hoistConsts`/`optimizeProgram` pair in `Build.irProgram` versus the `#ir` path;
the source used by the test has no constants, so the declaration slice should be
identical. Run the four commands above before trusting the fixture.
