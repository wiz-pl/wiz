# Feral drafts: what checks, what doesn't, and why

Branches `agent/rust-drafts`, `agent/rust-regions` (regions). Check everything that
should check, and that the rejected programs fail, with `sh drafts/feral/check.sh` (from
the worktree root, after `lake build`); the libraries' tests are `lake test -- optic`
and `lake test -- regions`.

## The front end (22j, branch agent/feral-surface)

`lib/Feral.wiz` (about 2400 lines of Wiz) implements `feral … end` for the fragment of
LOWERING.md §1a. Test group `feral`: the twelve `surface/` programs lower, check and
evaluate like `lowered/`; the nine `rejected/surface/` programs are rejected by the front
end (error class and line) and by the kernel on their `#unchecked` lowering.

What Feral is and isn't: Feral is Rust's ownership discipline for a small first-order
language, explained by translation — a Feral program *is* the Wiz program `#lower` shows,
and the borrow errors are that program's type errors, reported early and in Rust's terms
by a front-end checker with the same region-carrying types. Since cohesion M4 the
mutable handles (`Uniq`, `Mut`, `MutOpt`) are linear (linear-case stage 2): the kernel
rejects using a `&mut` twice (E0499) and keeping one past its scope, and every error
alternative hands the handles back (D8). Reading a lender while it is lent (E0502) is
still enforced by the *shape* of the lowering — every borrow is a scope that rebinds the
lender's name to a `Lent` token — not by types: the lender is an ω value (a pinned
known gap of `regions`). The surface never mentions handles, scopes, tokens or
handed-back tuples.

Not in the fragment (each is an error "not supported yet", never a silent miscompile):
inline spec clauses on `fn` (use a `spec f requires (P) ensures (Q)` item), loop invariants, `loop`/`break`/`continue`, `impl`/`trait`, closures, struct literals with
fields, assignment to `x.f`/`v[i]`, `while let` directly through a `&mut` (use a cursor),
more than two lenders, `From.from` in `?`, integer types other than `U64`.
Differences from rustc: a `&mut` argument is never implicitly reborrowed at a shorter
region (rejected/surface/outlives_wrong_way; rustc accepts it); a borrow's extent is
NLL only for straight-line code (a borrow taken in a branch or a loop body ends with that
statement or block); a block-local `let` that shadows an outer variable stays visible
after the block when the block is in tail position.

## Checks today

| file | contents | evidence |
|---|---|---|
| `lib/Result.wiz`, `lib/Optic.wiz` | `Error`, `Result` (+ `bind`, `map`, `Monad`, `All`, `Holds`; lib/Result.wiz); `Store` (`comp`, `compP`, `underR`, `extract`, `put`); `Lens`, `PLens`, `ALens`; `Lens.comp`, `PLens.comp`, `Lens.toP`; `zoom`, `zoomP`; `Affine` (`comp`, `over`, `extract`); `TraverseMut` + `List` instance; laws `GetPut`/`PutGet`/`PutPut`/`Lawful` (total and partial), `Lens.Indep`, `Lens.pair` | `lake test -- optic` (4 cases) |
| | **proofs:** structure-field lenses lawful and independent (`rfl`); head of a list (`List.headL`) and **index of a list (`List.atL i`) lawful partial lenses** (all three laws, by induction on the index through generic `Store.underR_*` lemmas); **composition of lawful lenses is lawful** (`Lens.comp_lawful`); `Lens.pair_getPut`; `Store.final` (the `final(r)` desugaring equation) | kernel-checked; a negative test shows an unlawful lens's GetPut is rejected |
| `lib/Region.wiz` | `Region`, `Outlives` (opaque; `refl`/`trans`/`static`); handles `Shr`, `Lent` (structures) and the linear `Uniq`, `Mut`, `MutOpt` (one-constructor inductives used at quantity 1; the region is part of the type and inferred; constructors private to the module, so handles can't be forged); `Result1`, `Borrowed` (the error alternative hands the handles back, D8); borrow scopes `Region.scope`, `Shr.borrow(In)`, `Uniq.borrow(In)`, `Uniq.reborrow(In)`, `Uniq.share(In)`, `Uniq.zoom(In)`, `Uniq.both`; `Uniq.peek`/`write`/`read`/`end`; `Shr.weaken`, `Mut.weaken`; `Mut.ofLens`/`ofPLens`/`ofUniq`/`whole`/`peek`/`set`/`close`/`release`/`comp`/`alongside`/`mapBack`/`finish`, `MutOpt.ofAffine`/`over`/`release`; spec readers `Uniq.get`, `Mut.store`, `Borrowed.All` | `lake test -- regions` (distinct regions, inference, scopes run, outlives, E0515 ×2, E0597, E0499/E0502, forging, swap, list traversal, pick with its bound, lengthening, linearity: E0499 by passing a handle twice and escapes rejected, E0502 under a renamed token pinned as a known gap) |
| `drafts/feral/lib/FeralCore.wiz` | `Flow`; Nat-backed `U64` (checked `add`/`sub`/`mul`, `checkedAdd`, `midpoint`); List-backed `Vec` (`push` on a `Uniq`, `len` on a `Shr`, `index`, `indexMut` as a lawful `PLens` with proof, `getMut` as `MutOpt`) | `check.sh` |
| `drafts/feral/lowered/01_swap.wiz` | `swap` through two `&mut` (`Uniq ρ₁`, `Uniq ρ₂`), `mem.swap`; nested borrow scopes at the call site | `#eval` .ok (2, 1) |
| `…/02_push.wiz` | `push_twice (v : &mut Vec U64)`, `for` loop as structural recursion | 10 elements |
| `…/03_get_mut.wiz` | returned `&'a mut` as `Mut ρ U64 (Vec U64)`, called in a reborrow scope; generated lawfulness; the `ensures … final(v) = old(v).set i final(result)` spec **stated and proved** | `.ok [1,12,3]`, `.err .outOfBounds` |
| `…/04_reverse.wiz` | in-place reversal with `while let` (partial def), `mem.take` | `#ir`: `reuse … ctor` |
| `…/05_bst.wiz` | BST insert: recursive `&mut` (field reborrows in scopes; now `partial`, reborrow-recursion), cursor loop as a `Mut.comp` chain, and as a zipper | three agree |
| `…/06_count.wiz` | `while` + `?` on a user `Result` (`R (Except E T)`) + `Flow.ret` | ok and returned-error cases |
| `…/07_disjoint.wiz` | two disjoint `&mut` field borrows: place aliases (unpack/rebuild in a reborrow scope) and the optic form (`Uniq.zoom`, `Lens.pair`, `Uniq.both`), generated field lenses + laws + independence | both `.ok (12, 4)` |
| `…/08_first_mut.wiz` | `Option (&mut U64)` as `MutOpt` | some / none cases |
| `…/09_bsearch.wiz` | `&'a Vec U64` as `Shr ρ`, `while` with early `return` | found / not found |
| `…/10_regions.wiz` | `'a : 'b` bounds as erased `Outlives` arguments (`longest`, `remember` storing a `&'a` into a `&'b` slot), nested scopes handing out evidence | `.ok 8` |
| `…/11_list.wiz` | a linked list through `&mut`: `incr_all` recursing on reborrows of the tails (`partial`, reborrow-recursion), `push_back` as a cursor | `.ok [2, 3, 7]` |
| `…/12_pick.wiz` | returning one of two `&mut` (`Mut.ofUniq`, `Mut.weaken` with `'a : 'b`, `Mut.mapBack`, `Mut.finish`) | `.ok (10, 2)`, `.ok (1, 10)` |
| `drafts/feral/rejected/*.wiz` | E0515 (return a local's `&` / `&mut`), E0597 (borrow outlives its scope; short reference stored into a long slot), E0499 (two `&mut`), E0502 (lender used while borrowed), missing `'a : 'b` (for `&` and `&mut`), the bound pointing the wrong way at a call, a lengthened borrow; a forged handle (`forge_handle`: the handles' constructors are private to `lib/Region.wiz`, docs/stages/13-language.md, 13b) | each rejected with a type mismatch, the forgery as private (`check.sh`) |

## Doesn't check (wishful), and why

| file / feature | missing | wishful entry |
|---|---|---|
| spec clauses in `drafts/feral/surface/*.wiz` (now comments) | `requires`/`ensures`/`invariant`/`decreases` in the grammar and their lowering | `spec-clauses`, `final-specs`, `decreases-loops` |
| positions inside macro-generated code, state across `feral` blocks, calling Wiz functions from Feral | positions in runtime `Syntax`, a macro environment, `getType` used for interop | `command-proc-macros` (located output by path is done, 22j) |
| `let (u, ra, rb) := r` (L6) | `let` tuple patterns of more than two components (nested binary lets today) | `let-tuple-patterns` |
| E0502 enforced by the type checker (today: by the lowering's shape, `Lent` rebinding; the lender is ω). E0499 and escapes are type errors since cohesion M4 | linear lenders, and a Copy notion to read `*x` out of one (K3) | `linear-case` |
| structural recursion through a field reborrow (05 `insert`, 11 `incr_all` are `partial`) | the termination checker seeing a recursive call on a scope's handle of a pattern variable | `reborrow-recursion` |
| `invariant`, `decreases`, `final result` | loop specs, returned-borrow specs (`requires`/`ensures` are `spec` items since M7) | `spec-clauses` |
| `final(x)`, `old(x)` | desugaring over the backward function | `final-specs` |
| `decreases` on loops | well-founded recursion; loops stay `partial def` (unverifiable) | `decreases-loops` |
| numerals at integer types other than `U64` (the front end writes `U64.lit n`) | numerals at machine-int types | `machine-int-literals` |
| `∃`, `∧`, `¬`, `∈` in laws/specs (`drafts/feral/Optic.wiz` §1, surface 09) | Prop connectives | `prop-connectives` |
| `Lens.pair_putPut` (`drafts/feral/Optic.wiz` §2; `pair_putGet` is in lib/Optic.wiz since `castRefl`) | the unifier comparing an equation with its computed form | `unify-computed-equations` |
| native `Vec` with `takeAt`/`fillAt` (FeralCore uses a List model) | `implemented_by` | `implemented-by` |
| backward functions that reuse cells without inlining (`drafts/feral/Optic.wiz` §7) | constructor contexts | `constructor-contexts` |
| `transp` with a Prop motive using its variable | quantity-0 variables used in types count as ω | `erased-use-in-types` (worked around in `Eq.substProp`, lib/Logic.wiz) |
| `match s with \| .mk h m` on a structure | constructor patterns on structures (tuple patterns work) | `structure-patterns` (low priority) |
| `deriving instance Lenses for S` (`drafts/feral/Optic.wiz` §6) | command macros over reflected structures (agent/deriving has the base) | `command-proc-macros` |
| `RStore` refined backward functions, `FunList` traversal spec (`drafts/feral/Optic.wiz` §4–5) | front-end proof obligations at borrow end; the `Vec` model | `spec-clauses`, `implemented-by` |

## Elaborator issues found (worked around; not wishful features, reported for fixing)

1. **Implicit arguments in a parameter type of an equation-style definition stay
   metavariables.** `def f … (hC : (x : A) → Store.underR k (m x) = C (k x)) : (r : …) → …
   | .ok st, h => … | .err e, h => ()` → "kernel does not accept metavariables (?m1)";
   writing `@Store.underR A B S k (m x)` fixes it (lib/Optic.wiz `underR_pg`/`_pp`).
   The same statement checks as an `axiom` or as a non-matching `def`, so it's the match
   compiler's reverted parameters.
2. **`@f` on the recursive call of an equation-style definition** is "unknown identifier"
   (lowered/05: recursive calls must omit the region argument, which works because it is
   a parameter before the colon).
3. **`.c` constructors inside tuple components** (`.ok (.nil, st)`, `.ok (.true, v)`) get
   no expected type ("no elaborator for syntax kind term.dotIdent"); write `List.nil`,
   `Bool.true`.
4. **Generalised field notation doesn't see through `def`-aliases** (`st.put fin` for
   `st : Store A S` fails; `Store.put st fin` works) — expected, since `Store` is a
   `def`, but it makes the library less pleasant (nominal `structure Store` would fix it
   at the cost of the pair patterns).
5. **Unifier vs computed equations** (see `unify-computed-equations`): every congruence
   in a proof needs all implicit arguments explicit.
6. `match` on a non-variable discriminant doesn't generalise hypotheses that mention it
   (`match List.atL i xs, ih with …`); worked around by stating lemmas over an arbitrary
   `r` and instantiating them (the `Store.underR_*` lemmas). A `match h : e with` form
   would make this direct.

7. **Escapes reported as "rigid mismatch".** When a scope's body returns a handle of the
   scope's region, the error is sometimes "type mismatch … (rigid mismatch)" between two
   metavariables (`Result (?m1 ρ x)` vs `Result (?m5 ρ x ρy hy y)`), not "a variable
   escapes the scope of the hole being solved" (which it does say when the type is
   already concrete). Both are correct rejections; the message should name the escaping
   region. `drafts/feral/rejected/` shows each.
8. **Unannotated scope lambdas** (`fun ρ h v r => …`) check when the expected type is a Π
   with quantity-0 binders: no annotations needed, but the scope's `B` is solved from
   the body, so errors point into it.

## Measurements wanted (not done: no timing claims)

* Allocation/reuse counts (`#run` heap or a future `--stats`) for lowered/04 (expect 0
  allocations in `reverse.loop0`), 05 (closure chain vs zipper), 07 (struct cell reuse).
* The handles are one-field structures, boxed at run time (`#ir`: `proj 0 x1`), so every
  `Uniq`/`Shr`/`Mut` costs a cell and every `Uniq.set` a reuse at best; and the scopes are
  closures (`Uniq.borrow σ s (fun …)`), unless inlined. Wanted: counts before/after this
  change for 01, 02, 07, and either newtype unboxing of one-field structures or inlining
  of the scope combinators.
* Whether the closure form of `get_mut` (03) reuses the vector when compiled; it can't
  natively until `Vec` is native (implemented-by).
