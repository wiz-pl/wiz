# Feral: the surface language and its lowering rules

Plan: `/workspace/wiz-notes/rust-dsl-plan.md`, `borrows-as-optics.md`, `uniqueness.md`.
Decisions RD1–RD16 are the user's (roadmap memory). This file pins down what the front end
emits. The front end exists: `lib/Feral.wiz`, a command macro written in Wiz (RD4;
docs/stages/22-numbers.md, 22j), whose comments cite the rule numbers below.
`lowered/NN_*.wiz` were written by hand following these rules before it existed; the test
group `feral` checks that each `surface/NN_*.wiz` lowers to something that checks and
evaluates like its hand-lowered counterpart (they are not textually equal; `#lower feral …
end` shows what the front end emits). Where writing the front end showed a rule to be
ambiguous or wrong, the rule was changed here and is marked **(changed, 22j)**.

Files:

| path | what | checks? |
|---|---|---|
| `lib/Result.wiz`, `lib/Optic.wiz` | `Result`/`Error` (RD7, lib/Result.wiz), `Store`, `Lens`, `PLens`, `Affine`, `zoom`, `TraverseMut`, laws, proofs | yes, tested (`lake test -- optic`) |
| `lib/Region.wiz` | regions, `Outlives`, the handles `Shr`/`Uniq`/`Mut`/`MutOpt`/`Lent` (structures: the region is part of the type) and the borrow scopes | yes, tested (`lake test -- regions`) |
| `drafts/feral/lib/FeralCore.wiz` | `Flow`, Nat-backed `U64` and List-backed `Vec` stand-ins | yes (stand-ins for agent/natives-ints and agent/vec-lib) |
| `lib/Feral.wiz` | the front end: grammar, a checker whose types carry regions, the lowering | yes, tested (`lake test -- '=feral'`) |
| `drafts/feral/surface/NN_*.wiz` | the programs in Feral, with the `#eval`s of their hand-lowered counterparts | yes (`feral`) |
| `drafts/feral/lowered/NN_*.wiz` | the same programs, hand-lowered | yes, with `#eval`s |
| `drafts/feral/rejected/surface/*.wiz` | the rejected programs in Feral, each with the error class and line it must be reported at (`-- expect:`) | rejected by the front end, and by the kernel on their `#unchecked` lowering (`feral`) |
| `drafts/feral/rejected/*.wiz` | hand-written lowerings of programs Rust rejects (E0499, E0502, E0515 ×2, E0597 ×2, missing bounds for `&` and `&mut`, a bound pointing the wrong way, a lengthened borrow) | each must fail with a type mismatch (`check.sh`) |
| `drafts/feral/Optic.wiz` | the part of the optics library that doesn't check yet | no (wishful) |

## 1. The surface (RD5: closer to Wiz than to Rust; Rust's semantics)

What `lib/Feral.wiz` parses and lowers today is the fragment of §1a. The sketch below is
the wider design; in it, `struct`/`enum`/`fn`, `let`/`let mut`, borrows, `match`, `if`,
`if let`, `while`, `while let`, `for`, `return`, `?` and the library calls of the table
are real, while `requires`/`ensures`/`invariant`/`decreases`, `loop`, `break`/`continue`,
`impl`/`trait`, field and index assignment, closures and tuples of more than two
components are not parsed yet (spec clauses are comments in `surface/`).

```
import Feral
feral
  struct Stats where                       -- like a Wiz structure: one field per line
    hits : U64
    misses : U64
  enum Tree where                          -- like a Wiz inductive; recursion through Box
    | leaf
    | node (key : U64) (left : Box Tree) (right : Box Tree)

  fn get_mut {'a} (v : &'a mut Vec U64) (i : USize) : &'a mut U64   -- Wiz binders; region params in braces
    requires i < v.len                     -- RD13 clauses between the signature and :=
    ensures final(v) = old(v).set i final(result)
  := &mut v[i]

  fn sum_from (s0 : U64) (n : U64) : Result U64 Overflow := {        -- a block: statements separated by ;
    let mut i : U64 := 0;                  -- let / let mut, Wiz's :=
    let mut s := s0;
    while i < n invariant … decreases n - i do {
      s := (s.checked_add i).ok_or Overflow ?;    -- assignment is :=, compound += etc.; postfix ?
      i += 1
    };
    .ok s                                  -- the block's value; `return e` also exists
  }
end
```

| construct | surface | notes |
|---|---|---|
| items | `fn`, `struct … where`, `enum … where`, (later `impl`, `trait`) | inside `feral … end` (one command macro per block) |
| binders | `(x : T)`, `{T : Type}`, `{'a 'b}`, `[Tr T]` | as Wiz; `'a` is a region (lifetime) |
| types | `U64`, `USize`, `Bool`, `Vec T`, `Box T`, `Option T`, `Result T E`, `&'a T`, `&'a mut T`, `A × B` | Wiz-style application, not `Vec<T>`; `'a` may be elided |
| statements | `let x := e`, `let mut x : T := e`, `p := e`, `p += e`, `e;` | places `p`: `x`, `*r`, `p.f`, `p[i]` |
| expressions | `if c then a else b`, `match e with \| .c x => …`, `if let .c x := e then … else …`, `{ … }`, `e ?`, `return e`, `&e`, `&mut e`, `*e`, method calls `v.push x` | `match` is Wiz's (alternatives with `\|`, `.c` constructors) |
| loops | `while c do { }`, `while let p := e do { }`, `loop { }`, `for i in a..b do e`, `break`, `continue`, clauses `invariant`/`decreases` | |
| calls | `f x y` (curried look), saturated from the first `&mut` argument on (RD5) | `f (&mut a) b`; partial application only before the first `&mut` |
| library | `mem.swap`, `mem.replace`, `mem.take`, `Vec.new`, `v.push`, `v.len`, `v.get_mut i`, `x.checked_add y`, `o.ok_or e` | Rust's std names, Wiz's dot style |
| specs | `requires`, `ensures` (with `result`, `old(x)`, `final(x)`), `invariant`, `decreases` | RD13; lowered to quantity-0 Props |

Why Wiz-like: Feral is a teaching device for Rust's *semantics* (moves, borrows,
in-place mutation), read next to its lowering; sharing Wiz's binders, `match` and
constructor syntax keeps the two side by side readable (RD1, RD5).

### 1a. The implemented fragment (22j)

```
import FeralCore                  -- the runtime stand-ins (drafts/feral/lib), until natives-ints and vec-lib replace them
import Feral
feral                             -- `#lower feral … end` also shows the generated Wiz;
  items                           -- `#unchecked feral … end` lowers without the front end's borrow verdict (tests)
end
```
* items: `fn f {'a 'b} {'a : 'b} {T : Type} (x : τ) … : τ := e`, `struct S where f : τ …`,
  `enum E where | c (x : τ) …`;
* types: names, `Vec τ`, `Option τ`, `Result τ ε`, `Box τ`, `τ × τ`, `&'a τ`, `&'a mut τ`
  (the region may be elided: a fresh one per parameter; in a result, the first
  reference parameter's; in a local annotation, inferred), `USize` = `U64`;
* expressions: variables, numerals (at `U64`), `true`/`false`, `()`, pairs, blocks
  `{ s; …; e }`, calls `f a b` (saturated), methods `x.m a` and `(e).m a` of the library
  table (`push`, `len`, `get_mut`, `checked_add`, `ok_or`), `mem.swap`/`take`/`replace`,
  `Vec.new`, constructors `.c a b` and `E.c a b`, a struct without fields by its name,
  `&e`, `&mut e`, `*e`, `v[i]`, `x.f`, `e ?`, `return e`, `+ - * / <` on `U64`,
  `p := e`, `p += e` (places: a variable, `*r`), `if c then a else b`,
  `if let pat := e then a else b`, `match e with | pat => e …`, `while c do e`,
  `while let pat := e do e`, `for i in a..b do e`;
* patterns: `x`, `_`, `.c x _ …`;
* keywords `if then else while for in return mut fn struct enum` are reserved in a file
  that imports `Feral` (wishful: syntax-reserved-keywords).

## 2. Lowering rules

Notation: `⟦e⟧` the lowering; `R A` is `Result A` (lib/Result.wiz).

**L1. Items and generics.** `fn f {'a} {T : Type} [C T] (xs…) : Ret` ↦
`def f {ρ : Region} {T : Type} [C T] (xs…) : R (…)`: region parameters first (implicit,
so quantity 0, RD12), then outlives bounds `'a : 'b` as erased proof arguments
`(0 h : Outlives ρa ρb)` (L22), then type parameters, then instance arguments, then values.
`struct S where f : T` ↦ `structure S where f : ⟦T⟧` (fields at ω, RD2).
`enum E where | c (x : T)` ↦ `inductive E where | c (x : ⟦T⟧)`. Names are unchanged
(no `Rs.` namespace yet: Wiz has no namespaces, so a Feral type can't be called `List`:
04 and 11 say `LList`). A recursive `fn` is a `partial def` (the recursive call is usually
inside a scope's lambda: reborrow-recursion). (01, 04, 05, 07)

**L2. Results and panics (RD7).** Every lowered function returns `R _`, even when it
can't panic (a later optimisation may drop it, R7c). Every panic — overflow,
out-of-bounds, `unwrap` on `none`, division by zero, `panic!` — is `.err (…)` with an
`Error` constructor. A function whose Feral type is `Result T E` returns
`R (Except E T)`: user errors are values, panics are not. (06)

**L3. Arguments.** An owned or `Copy` argument is a plain argument. `&'a T` is
`Shr ρ ⟦T⟧` (the value, shared; read with `.val`). `&'a mut T` is a `Uniq ρ ⟦T⟧` handle,
taken at quantity 1 and **handed back**: the result type is
`Result1 Ret ((1 _ : Uniq ρ₁ T₁) × … × Uniq ρₖ Tₖ)`, whose `ok` and `err` both carry the
handles, in order (D8: an error hands them back too). `*x` is
`let 1 (d, x) := Uniq.peek x` (the value at ω, the handle back), `*x := e` is
`let 1 x := Uniq.write x e`. All handles are types of `lib/Region.wiz` with the region as
a parameter, so their region is part of their type. **(changed, cohesion M4b)** Handles
are linear: using one twice, or not handing it back, is a type error. (01, 02, 07, 09)

**L4. Returned borrows (Aeneas backward functions, RD11).** A function returning
`&'a mut A` borrowed from its `&'a mut S` argument returns
`Borrowed (Mut ρ A S) (Uniq ρ S)`: `ok` hands over a `Mut ρ A S` (linear, around
`Store A S = A × (A → S)`: the borrowed value and the backward function that rebuilds
the lender from the borrow's final value), `err` hands the lender back (D8). The lender is
*not* also handed back on `ok` (it is inside the backward function); `Mut.release m`
(the borrow's last use) or `Mut.close m fin` gives back the `Uniq ρ S`. `*m` is
`let 1 (d, m) := Mut.peek m`, `*m := e` is `let 1 m := Mut.set m e`; `&mut v.p` is
`Mut.ofLens v l`/`Mut.ofPLens v l` for the place's lens. `&mut` arguments in other
regions are handed back beside the borrow, as in L3. A returned borrow that may be one
of several `&mut` arguments (`if c then x else y`) moves all of them into the result:
`Mut.ofUniq x : Mut ρ A (Uniq ρ A)` (the whole argument, its backward function giving
the handle back), and `Mut.alongside m y f` carries the other handle in the backward
function (a linear handle can't be captured by an ordinary closure), so the result is
`Borrowed (Mut ρb A ((1 _ : Uniq ρa A) × Uniq ρb A)) (…)`, and `Mut.finish m` at the
borrow's last use gives the handles back (12). **(changed, cohesion M4b-3c)** An error
exit while a returned borrow is live releases it first and hands back what it held. **(changed, 22j)** The lenders are decided from the
signature alone: the `&mut` parameters of the result's region `'r`, and those of a region
with a bound `'x : 'r`. One lender `&'r mut S` gives `Mut ρ A S` (`Mut.release`), several
give the tuple of handles (`Mut.finish`); returning the single lender itself is
`Mut.whole x`. The other `&mut` parameters are handed back next to the borrow:
`R (Mut … × Uniq …)`. So `pick` *without* its bound has the one lender `y`, and
returning `x` is a missing-evidence error (rejected/surface/lifetime_bound_missing_mut). An argument of a longer region is used at the
result's through `Mut.weaken h` (L22). `Option (&'a mut A)`
returns `R (MutOpt ρ A S)`: `.some m` (a `Mut`) or `.none r` (the lender) (L12). (03, 08)

**L5. Sequencing.** **(changed, 22j: layout)** The front end parenthesises every `match`
it emits and writes `Result.ok`/`Flow.brk` qualified (a `.c` inside a tuple gets no
expected type); a join's scrutinee carries its type, `((…) : Result T)`, and a scope its
type arguments, `@Uniq.borrow S B σ s (fun …)`, so that a region escaping through `B` is
an error at `B`. A call or primitive that may fail is a direct `match`:
`match ⟦e⟧ with | .ok x => ⟦rest⟧ | .err e => .err e` — never `Monad.bind`, never a
closure around an owner (plan §5.1 req. 2). Pure steps are `let`. Each nested match
is laid out with its alternatives on their own lines; a non-final nested match is
parenthesised. (all)

**L6. Mutable locals are SSA.** `let mut x := e` is `let x := e`; each assignment
`x := e` rebinds `x` (`let x := …`), shadowing the old one. After a call that hands back
`&mut` arguments, each is rebound by destructuring the result tuple
(`let (u, v) := r`; three components as `let (u, xy) := r; let (x, y) := xy`, wishful:
let-tuple-patterns), never by projections (`r.2`): a tuple that carries a borrow is a
resource, and projections will be allowed only on unrestricted pairs (the linear-pair
decision of 2026-11-10). (all)

**L7. Joins.** **(changed, 22j: "when the continuation is short" was not a rule.)** An
`if`/`match` in *tail position* (of a function, a loop body, or a joined branch) is
lowered into its branches: each ends with the function's result, the loop's recursive
call, or the join's tuple. Anywhere else it is a *join*: each branch returns
`(value, x₁, …, xₙ)` for the outer variables `xᵢ` it mentions that can change (mutable
locals and handles), and the continuation rebinds them. A join whose branches contain a
`return` or a `?` returns `Flow (value × xs) (Ret × xs)`: `.ret` carries the function's
value out, and the continuation passes it on to the enclosing join, scope or loop until
the function's own result (L3) is built. The same tuple-or-`Flow` protocol is used by
scopes (L20) and loops (L8).

**L8. Loops (RD8).**
* `for i in a..b do body` ↦ a function `f.loopN` structural on the number of iterations
  left, taking the counter and the live mutable variables, returning the variables.
  The increment can't overflow (`i < b`), so it is unchecked (02).
* `while`/`while let` ↦ `partial def f.loopN (params…) (vars…) : R (Unit × vars)`, tail
  recursive; with a `return` or `?` in the body, `R (Flow (Unit × vars) (Ret × vars))`
  **(changed, 22j: `.ret` carries the value and the same variables, not the function's
  `&mut` arguments; the function's result is built where the function returns, after
  every cursor has been released, L16)**. The parameters are the variables in scope that
  the loop mentions: first those it cannot change, then `vars` (mutable locals, handles,
  cursors). The loop function also takes, explicitly and erased, the innermost region
  when it is a local one, and the outlives evidence in scope (L22). `break`/`continue`
  are not implemented (05, 06, 09).
* `decreases m` stays a comment until well-founded recursion exists (decreases-loops);
  then `partial` goes and `termination_by` comes in.

**L9. `?`.** On `Option`/`Result` values, a direct match: `.some x`/`.ok x` continues,
`.none`/`.error e` returns `.ok (.none)`/`.ok (.error (From.from e))` from the function —
`.ok` because a returned error is not a panic. Inside a loop it exits with `Flow.ret`. (06)

**L10. Places and place functions.** A place is a path `x.f.g`, `*r`, `x[i]`, a variant
payload. For each struct field the front end emits a field lens `S.fL : Lens S F` with
its laws (`S.fL_lawful : Lens.Lawful S.fL`, by `rfl`) and the independence of distinct
fields (`Lens.Indep`, by `rfl`) — generated, at quantity 0 (07). A function whose body
is a place expression (after NLL) is a *place function*: its lowering is a (partial)
lens, and the front end emits its lawfulness (03: `get_mut.lawful`, from library lemmas
`List.atL_lawful`, `Vec.indexMut_lawful`). Indexing `v[i]` for writing is
`Vec.indexMut i : PLens (Vec A) A` (in place natively via takeAt/fillAt); for reading it
is `Vec.index v i : R A` (shared).

**L11. Borrows of statically known places are aliases.** **(changed, 22j)** The front end
does this for `let h := &mut s.f` with `s` a `&mut` struct: a reborrow scope of `s` whose
body first peeks the struct and projects *every* field (`let 1 (d, r) := Uniq.peek r;
let s_f := d.f; …`, not a tuple pattern), `h` is a name for the field's local, a second
`let m := &mut s.g` inside the scope names another (the same field twice is E0499), and
the scope's end rebuilds `Uniq.write r (S.mk …)`. Elsewhere (`&mut r.f` as a value) it is
`Mut.ofLens r S.fL`, and **(cohesion M4b-3c)** a field passed to a `&mut` parameter,
`f (&mut s.f)`, is a `Uniq.zoom S.fL s` scope (`zoomIn` with other handles threaded
through; on a local `s`, inside the borrow of `s`). Two fields of one struct in one call
are not supported yet (name them with `let`). `let h := &mut s.hits` where
the place is known at compile time does not create a value: inside a reborrow scope of
`s` (so `s` is a `Lent` token meanwhile, L20), the struct is unpacked
**once, before any new field value is computed** (tuple pattern `(h, m, _)`, plan §5.1
req. 1), the fields live as SSA locals while borrowed, and the struct is rebuilt with
its constructor when the last borrow of it ends — in the same block, so Perceus reuses
the cell (`#ir record` shows `reuse … ctor`). Calling a function on such borrows passes
the locals and rebinds them from the handed-back tuple. The optic form
(`Uniq.zoom S.fL s f`, and `Uniq.zoom (Lens.pair S.aL S.bL) s (… Uniq.both …)` for two
disjoint borrows, in fresh regions) is
equivalent and is what the front end uses when the place is *not* a direct field of a
local (e.g. through a returned borrow); lowered/07 shows both. (07)

**L12. `Option (&mut A)`.** Returned as `MutOpt ρ A S` (from an `Affine A S`,
`MutOpt.ofAffine`); the caller matches `.some m` (a borrow; `Mut.release m` ends it)
or `.none r` (the lender, unchanged). `if let .some x := first_mut v` is that match, in
a reborrow scope (L17) (08).

**L13. Boxes and moves.** `Box T` is `T` (the heap is implicit). Moving out of a box or
a local is just using the variable; a moved variable is never used again (the borrow
checker guarantees it), so Perceus frees or reuses it at that point. Matching an owned
enum moves its fields out; the matched cell is reused by a constructor built in the same
block (04: `#ir reverse.loop0` shows `reuse … ctor 1`).

**L14. `mem.*`.** `mem.swap x y` ↦ exchange the two values (01). `mem.take l` ↦ `let old
:= l; let l := Default` (04). `mem.replace l v` ↦ `let old := l; let l := v`.

**L15. Matching on a borrow.** `match t with | .node key left right => …` with
`t : &mut Tree` binds the fields as reborrows: `left`/`right : &mut Tree`, `key : &U64`.
Lowered: in a reborrow scope of `t`, peek `r` and match the value, borrow the field
variables (`Uniq.borrow ρ' left …`) to recurse on them, rebuild the constructor in each
branch with `Uniq.write r` and hand the whole back (05, `insert`; `partial` until structural
recursion sees through the scope's lambda, wishful: reborrow-recursion). A `&T` scrutinee binds fields by
value (shared). **(changed, 22j)** The field variables are place aliases (as L11): `*key`
is `key`, `*head := e` rebinds `head`, passing `left` where a `&mut` is expected borrows
the local. An alternative that binds no field (`.leaf`, `_`) has the borrow itself: `t`
is rebound to the scope's handle, so `*t := e` works there. Every alternative — and every
`return`/`?` inside one — rebuilds or hands back before the scope ends. (05, 11: `incr_all`)

**L16. A borrow that moves (cursor loops, R6c).** **(changed, 22j)** `let cur := r` for a
`&mut` handle `r` makes the cursor (`Mut.whole r`; `r` is unusable until the cursor's
release). `match`/`while let` on a cursor peeks it (`Mut.peek cur`); assigning one of the
bound fields to the cursor is the `Mut.comp` step. The release (`let r := Mut.release
cur`) is emitted where the function returns (also on `return`/`?`), not after the loop. `cur := left` inside a loop, where
`cur : &'a mut Tree`, composes the cursor's backward function with the child's:
`cur := Mut.comp cur (fun _ => (left, fun l => Tree.node key l right))`; the cursor
starts as `Mut.whole t` (region `ρ`: `t` moves into it), and when the loop ends,
`*cur := e; t := Mut.release cur` puts the whole tree back (05, `insert_loop`). The defunctionalised alternative (a zipper `Path`
whose frames reuse the nodes, `plug` as the backward function) is what the front end
should emit for performance (05, `insert_zip`), proven equal to the closure form later. (05, 11: `push_back`)

**L17. Regions at call sites.** **(changed, 22j)** The reborrow scope is opened for a
handle (or `&mut` of one) passed at a *lender* position of a callee that returns a borrow
— except in the tail position of a function that itself returns a borrow, where the
handle moves into the result (03 `get_mut`, 08 `first_mut`). `&x` of a `&mut` handle is
`Uniq.share`. Region arguments are inferred from the handles' types
(phantom parameters, docs/stages/22-numbers.md, 22e): `swap ra rb`, never `@swap ρ₁ ρ₂`. Outlives arguments
are passed explicitly (the evidence a scope handed out, L22). A call that only hands
`&mut` arguments back moves the handles in and rebinds them (no scope: the handed-back
handle is the same borrow). A call that **returns a borrow** of a `&mut` argument
(`get_mut v i`, `first_mut v`) runs in a reborrow scope `Uniq.reborrow v (fun ρ' h v r
=> …)`: inside, `v` is a `Lent` token until the returned borrow's last use, where it is
released (03, 08).

**L18. Specs (RD13, RD11).** `requires P ensures Q` ↦ `def f.spec (args) : Prop :=
P → Result.All (fun r => Q[result := …, old(x) := x, final(x) := …]) (f args)`; for a
returned borrow `r : Mut ρ A S`, `*result` is `r.1`, `final(result)` is a universally
quantified `fin`, and `final(v)` is `r.2 fin` (03: `get_mut.spec`, proved as
`get_mut.spec_holds`). No prophecy axioms. With linear handles (M4b) the spec is
stated on values: `f.Spec` takes each `&mut` argument's value, runs the call inside the
caller's borrow scopes (`Uniq.borrow`/`borrowIn`), and `Result.Holds` states the clauses
on the values the scopes hand back (`old(x)` is the argument, `final(x)` the lender's
final value).

**L19. Interop (RD16).** Wiz calls lowered functions as they are (`R`, handed-back
tuples, backward closures); `Result.map`, `Result.show`, `Mut.release`, `MutOpt.over`
are the helpers, and Wiz values are lent to them with `Uniq.borrow Region.static v (fun
ρ h v r => f r)` / `Shr.borrow` (`#eval`s at the end of each lowered file).

**L20. Borrow scopes (fresh regions).** A borrow of a local, `let r := &mut s` (or
`&mut s` as an argument), lasts until its last use (NLL); the front end lowers the
code from the borrow to that point into a scope whose body is polymorphic in a fresh
region:
```
Uniq.borrow σ s (fun ρ h s r => … .ok (b, r))      -- R (B × S): the lender comes back
Shr.borrow σ s (fun ρ h s => …)                     -- `&s`: here `s` is the Shr itself
Uniq.reborrow r (fun ρ' h r r' => … .ok (b, r'))    -- `&mut *r` (L17)
Uniq.share r (fun ρ' h r => …)                      -- `&*r`
Uniq.zoom l r (fun ρ' h r x => … .ok (b, x))        -- `&mut r.p`, p's lens l
Region.scope σ (fun ρ h => …)                       -- a block with its own region
```
**(changed, 22j: extents, and what a scope hands out.)** Which statements a scope
covers: the statement that borrows, and then every following statement of the block for
as long as a later statement mentions a variable tied to the scope's region (its type
mentions the region, or it is a place alias of it) — NLL for straight-line code. The
borrows of one statement nest in argument order. What leaves a scope is the tuple of L7:
the value, the outer variables the covered statements mention that can change, and the
variables declared inside that are used afterwards; with a `return`/`?` inside, a
`Flow`. `Uniq.borrow`/`Shr.borrow` hand out `Outlives σ ρ`; `Uniq.reborrow`, `Uniq.share`
and `Uniq.zoom` hand out `Outlives ρ ρ'` for the *handle's* region `ρ` (the rule used to
say `σ` for all of them; lib/Region.wiz never did).
`σ` is the innermost enclosing region: the enclosing scope's, else the function's
first region parameter, else `Region.static`. The lambda rebinds the lender's own name
(`s`, `r`): to a `Lent ρ S` token for a mutable borrow, to the `Shr ρ S` for a shared
one. Variables that live on after the scope leave it in its result `B`; `B` is
chosen outside, where `ρ` doesn't exist, so a handle of region `ρ` can't leave (as
`runST`). Each scope's body hands its borrow back last.

**L21. What is rejected, and how** (drafts/feral/rejected/, each a type mismatch).
**(22j)** The front end's checker has the same types (regions included), so it meets each
mismatch at the Feral node and names it; `#unchecked feral` shows the kernel rejecting the
lowering of the same program, and the `feral` tests require both verdicts:

| in the front end | reported |
|---|---|
| `&mut x`, a `&mut self` method or a `&mut` argument on a lender that is a `Lent` token | E0499 |
| any other use of a `Lent` lender; `&mut x` while `x` is its own shared borrow | E0502 |
| assignment to a `Lent` lender | E0506 |
| the value of the function's body tied to a scope's region | E0515 |
| anything else tied to a scope's region leaving the scope (a block's value, a variable used later) | E0597 |
| evidence `Outlives ρ ρ'` missing, `ρ` a scope's region | E0597 |
| the same between parameters' regions | "lifetime may not live long enough" |
| one local under two `&mut` in one call | E0499 (front end only: see below) |

* returning a borrow of a local (E0515): the scope's handle has the fresh region, the
  function returns a handle of a parameter's region;
* a borrow used after its lender's scope (E0597): the handle would have to leave the
  scope in `B`;
* using the lender while it is mutably borrowed, or borrowing it again (E0499, E0502):
  the lender's name is a `Lent` token, which nothing accepts (borrowing the token itself
  is allowed but useless: no operation takes a `Uniq ρ (Lent …)`);
* a reference stored into a longer-lived place, or returned as a longer-lived one,
  without an `'a : 'b` bound (E0597, "lifetime may not live long enough"): `Shr.weaken`
  or `Mut.weaken` needs evidence that isn't in scope; evidence pointing the other way
  (a scope's `Outlives σ ρ` used to lengthen a borrow, or a callee's bound the caller's
  nesting doesn't give) is a mismatch too;
* two borrows of different regions passed where one region is expected (`Uniq ρ A` and
  `Uniq ρ' A` are different types).

**(changed, cohesion M4)** Handles are linear (linear-case stage 2), so the kernel also
rejects duplicating one (`swap r r`, E0499; `swap (&mut a) (&mut a)` in Feral, on its
`#unchecked` lowering) and a handle packed with its region (`(0 r : Region) × Uniq r A`)
leaving its scope: it would have to be handed back as well. What is still **not**
rejected by the type checker, only by the lowering's shape (a known gap, pinned in test
group `regions`): the lender's outer name is only *shadowed* by the `Lent` token, and the
lender is an ω value, so a body that names the token differently can read the lender
while it is borrowed (E0502). Closing it needs linear lenders, and then a Copy notion to
read `*x` out of one (K3).

**L22. Outlives.** `'a : 'b` is `(0 h : Outlives ρa ρb)` (an opaque `Prop`: proofs come
from `Outlives.refl`/`trans`/`static` and from scopes). A scope nested in `σ` hands
out `Outlives σ ρ`, so evidence only ever shortens a region. A shared reference of
region `ρa` is used at `ρb` through `Shr.weaken h x` wherever it flows to a place of
type `Shr ρb _` (a return value, a field, a slot behind `&mut`). A returned mutable
borrow (`Mut ρa A S`) is used at `ρb` through `Mut.weaken h m` (`&'a mut T` is
covariant in `'a`) (12). A `&mut` *argument* handed back keeps its region: a shorter
borrow of it is a reborrow scope (L17). (10, 12) **(22j)** The front end finds evidence by
search (`refl`, `static`, the evidence in scope, `trans` chains); a region that is still
to be inferred is unified with the other side. Because a `&mut` argument keeps its
region, Feral is stricter than rustc here: rejected/surface/outlives_wrong_way is accepted
by rustc (which reborrows the outer `&mut` at a shorter lifetime) and rejected by Feral.

**L23. Diagnostics and modes (22j).** Errors are reported at the Feral node (a command
macro names a node of its input by path; docs/stages/22-numbers.md, 22j), the first
borrow error of each function. If any item has an error nothing is emitted. A lowered
item that the kernel rejects is reported at the item with the generated text: for an
accepted program that is a bug of the front end (and a test failure).

## 3. What the lowering guarantees about in-place execution (informal)

At every update the updated value has rc 1 when the Feral program is accepted: `&mut`
arguments are moved into the callee and back (02), struct updates unpack first (07),
enum cells matched and rebuilt in one block are reused (04, 05), element borrows go
through take/fill (natively; the model copies). The dynamic check is `--check-unique`
(R7, not yet built).
