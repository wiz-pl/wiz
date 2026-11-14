# Stage 22: numbers for hardware and systems code

Prerequisites shared by the HDL and Feral (decisions RD9, RD10/HD3).

## 22a: division, powers and bits

The Prelude defines `Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight`, `Nat.log2` (and `Nat.testBit`, `a / b`) by structural
recursion on a fuel argument that bounds the number of steps, so the kernel can unfold
them. Each is registered with `builtin nat.<op>`: on numerals the kernel computes
natively (`def t : Nat.mod 300 256 = 44 := refl 44`), as do `#eval`, `#run`, C/LLVM
(`runtime/`: machine words, GMP when big) and the self-hosted backend
(`selfhost/rt.c`; its Prelude has the same definitions). As in Lean, `n / 0 = 0`,
`Nat.mod n 0 = n` and `Nat.log2 0 = 0`. One table (`natNative?`, `Wiz/Core/Eval.lean`)
serves the kernel and both interpreters.

## 22b: `implemented_by`

`attribute [implemented_by g] f` gives a definition `f` a different implementation in
compiled code: erasure (`compileReachable`) takes `g`'s code for `f`, while the kernel,
and so every proof, keeps `f`'s definition. `g` is a Wiz definition or an `extern`, and
must have `f`'s type up to conversion (checked at the attribute; `g` can't implement
`f` otherwise). The implementation is **trusted**, as in Lean: nothing proves it agrees
with the model, so tests compare them. `#eval` and `#run` follow the attribute, except
to an `extern` (the interpreters can't call C): there they run the model, which gives a
differential test for free. `#erase f` shows `f := g`. Foreign functions may now take
and return Wiz data types, passed as they are (marshalling kind `w`).

Not yet: a *type* with a native representation (`Vec A` as an array, R0b), and the
attribute in the self-hosted backend.

## 22c: machine integers

`import Word` (`lib/Word.wiz`): `UIntN w`, a w-bit unsigned integer, and `IntN w`, w-bit
two's complement, both a number of bits below `2^w` (normalised by construction, so
arithmetic wraps around), with `ofNat`/`toNat`, wrapping `add`/`sub`/`mul`/`neg`,
`div`/`mod` (signed: `div` truncates towards zero and `rem` takes the dividend's sign,
as Rust; `x / 0 = 0` and `x % 0 = x` as Lean, where Rust panics), comparisons, bitwise
operations, shifts (`shiftLeft` by `k ≥ w` gives `0`; `IntN.shiftRight` is
arithmetic), `resize` (zero- or sign-extending, or truncating) and `toIntN`/`toUIntN`.

* **One width-indexed type** serves both clients: the HDL's `Unsigned n` needs any
  width (1, 5, 65, …) and Rust's `u32` is `U32 := UIntN 32` (also `U8 … U64`, `USize`,
  `I8 … I64`, with `U32.ofNat`, `I32.ofNeg`, …). Operations are named functions
  (`UIntN.add a b`, or `a.add b`) until the numeric classes (HD9) arrive.
* **The width is a phantom parameter** (`inductive UIntN (w : Nat) where | mk (toNat :
  Nat)`, since 22e/22h): no field mentions it, yet `UIntN 8` and `UIntN 16` are different
  types and `w` is inferred. (Before 22e it had to be an index, `mk {0 w : Nat} …`,
  leaving an erased slot in the object.)
* **Natives.** The kernel computes with the definitions, quickly on numerals (22a), and
  so do `#eval`/`#run`. Compiled code calls natives (`runtime/`, `wiz_word_*`) by
  `implemented_by`: in a `uint64_t` up to 64 bits, GMP beyond, one function per
  operation for every width. A table of operations at widths 8 to 100 gives the same
  values in the kernel (`refl`), both interpreters, C and LLVM (`examples/words.wiz`:
  an FNV-1a hash, and facts proved by `refl` about named values; an equation whose
  sides still contain an unsolved implicit width when it is computed gets stuck, so
  state facts about definitions). A word is still an
  object holding a number (above `2^62`, a GMP number); unboxed words need the type-level
  `implemented_by` (22d).

## 22d: native representations: unboxed words

`attribute [implemented_by mk get] T.mk` gives a type a **native representation** in
compiled code. `T.mk` is a constructor with one runtime field (the others erased);
`mk` has the constructor's type and `get` reads the field back. Erasure then never
builds the model's object: a constructor becomes `mk`, and `match` (and the generic
eliminators, which get the model's object back from `get`) reads the field with `get`.
The kernel and every proof keep the model. As with function-level `implemented_by`,
the natives are trusted, and the interpreters (`#eval`, `#run`) keep the model's
objects when `mk` or `get` is foreign, so the tables below compare the two.

`lib/Word.wiz` uses it for `UIntN w` and `IntN w` (and `NatObj`, a `Nat` passed to C
as the runtime number itself, possibly big). **A word is its bits**:

| bits b | representation | allocation |
|---|---|---|
| `b < 2^63` | a tagged scalar | none |
| `2^63 ≤ b < 2^64` | a raw 64-bit box (`WIZ_TAG_RAW`) | one cell |
| `b ≥ 2^64` (widths above 64) | a GMP number | as `Nat` |

* **Width-independent.** The representation depends only on b, so generic code over
  `UIntN w` (unknown `w`, any width: `BitVec n`, the HDL's `Unsigned n`) needs no width
  to build or read a word, and each value has exactly one representation (equality is
  a comparison of bits). `ofBits`/`toBits` convert from and to `Nat` (free below
  `2^62`).
* **Operations** are natives on that representation (`wiz_word_*` in `runtime/`):
  `ofNat`/`ofNeg`, `+ - *`, `div`/`mod`/`rem`, comparisons, `land`/`lor`/`xor`/`not`,
  shifts and `testBit` (a shift or index of `2^64` or more counts as infinite),
  `resize` (zero- or sign-extending), `toIntN`/`toUIntN` (free). Up to 64 bits each is
  a few instructions on a `uint64_t`; the C backend pastes the runtime into the program,
  so `cc -O2` inlines them.
* **What is not unboxed.** A 64-bit value with the top bit set still takes a cell (the
  uniform representation has 63 bits of payload). Unboxing those too needs per-variable
  representations in the IR (raw `uint64_t` locals and parameters, boxed at polymorphic
  boundaries, as Lean's `UInt64`): the next step, once a measurement says it pays.
* **Self-hosted backend:** not yet (it runs the model; see the wishful note).

## 22e: phantom parameters

```
inductive UIntN (w : Nat) where
  | mk (toNat : Nat)                     -- no field mentions `w`
def f (x : UIntN 8) : UIntN 16 := x      -- type mismatch
def width {ω w : Nat} (a : UIntN w) : Nat := w
#eval width (UIntN.mk 3 : UIntN 8)       -- 8: `w` is inferred
```

Types are structural, so a parameter that no field mentions used to be forgotten:
`UIntN 8` and `UIntN 16` were one type, `w` couldn't be inferred, and an HDL `Signal d A`
didn't keep clock domains apart. Now, for each such parameter `p : P`, the elaborator
(`phantomTail`, `Elab/Inductive.lean`) ends the type with `(0 phantom✝ : D) → Unit`
instead of `Unit`. That `Unit` is the end of the index type of an `inductive` or
`coinductive`, or of a structure's Σ. Here `D := p` if `p` is a type, and
`D := (0 x : P) × (x = p)` otherwise.

* `D` mentions `p` and is a type, not a proposition. Propositions compare by equivalence
  ([4c](04-data.md)), so `p = p` would have forgotten `p` again. Conversion now compares `p`, and
  unification solves it.
* The tail's only inhabitant is `fun _ => ()` (up to η). So it is still a singleton:
  constructors fill it in, patterns never see it, structure η and copattern index
  equations hold by `refl`, and `()` fills a structure's tail in a tuple.
* Erasure drops it, **by shape**: a function type all of whose binders have quantity `0`
  and that ends in `Unit` (`erasedFunTy`, `Compiler/Erase.lean`) has no runtime content.
  Not by the binder's name: conversion ignores names, so a user's `(0 d : D) → Unit` is the
  same type and must get the same representation (R3 of the soundness audit; group
  `repr`). Generic code may still apply such a function at a type `(0 _ : D) → A`: in the
  interpreters and in the runtime, `◾` applied is `◾`. So data, `#ir` and the
  C/LLVM code are those of the type without the parameter. Constructors, projections,
  `deriving` and `implemented_by` don't change. Nothing in the kernel changes either: it
  checks the encoding like any other declaration.
* Proof parameters get no phantom, and neither do sizes or quantities. A parameter whose
  `D` lives in a higher universe than the type also gets none, since the tail would
  raise the type's universe; it stays forgotten.
* For structures, `S 8 = S 16` computes through the Σ to `(x = 8) ↔ (x = 16)` under
  a binder `x`, so it is refutable (`Tests/Elab.lean`, group `phantom`). For an
  `inductive` the phantom is in the index type, and since 4g equality of two `μ` types
  compares their codes, index types first: `UIntN 8 = UIntN 16` is refutable too
  (`e.1` is the index types' equation, which at the phantom is `(x = 16) ↔ (x = 8)`), and
  a `cast` between them computes.
* A `def` alias (`def Mut (ρ : Region) (A : Type) : Type := A`) unfolds, so its
  parameters never count. Declare a `structure` instead.

## 22f: the trusted base: witnesses and tracked registrations

Two ways to prove `False` without writing `axiom` are closed.

* **Partial definitions need a witness.** `partial def f : T := …` is opaque to the
  kernel, so `f : T` is assumed. The kernel now takes it only with a term `w : T` it
  checks (`Decl.witness`, `addPartialDecl`; erased, so it may ignore a linear argument):
  `f` then proves nothing `w` doesn't. The elaborator finds the witness
  (`Elab/Witness.lean`): a variable of the type's `Π`s, `fun x => w`, a pair, `tt`,
  `Unit` for a sort, `Inhabited.default`, or a constant whose type ends in the type's
  head (a constructor, `StrMap.empty`) with its conclusion unified against the goal, so
  the indices must match: `mk : T .t` is no witness of `T .f`. The search proposes, the
  kernel decides. Otherwise write one: `partial (default := w) def f : T := …`, also
  inside `mutual`. The self-hosted kernel (`checkPartial`) and frontend (`wit`) do the
  same, and every partial definition of the self-hosted sources gets its witness found.
  Before, an elaborator check (`inhabitedTy`) looked only at the type's head, and
  `partial def bad : T .f := bad` proved `False`.
* **Registrations are trusted only in the library.** `builtin nat.add := K` makes `K`
  compute natively on numerals, which nothing checks against `K`'s definition. In
  `lib/` the registrations are reviewed (they match their definitions); anywhere else
  a registration is an axiom: recorded (`Globals.assumed`), warned about, and listed by
  `#print axioms d`, which shows every axiom `d` depends on through its type, value and
  witness (`axiom`s, foreign functions, `builtin key := name`; a numeral depends on the
  `nat` registrations). It also lists, marked `native`, the implementations compiled code
  runs instead of the definitions: `native f := g` for `attribute [implemented_by g] f`
  and `native T := mk/get` for a native representation (22d), the library's included
  (`UIntN.add`, `UIntN`). The kernel never runs them, so they prove nothing; they are
  trusted to agree with the definitions. Registrations are also checked for shape
  (`nat.add : N → N → N`, each operation a definition), and numerals need `nat.zero` and `nat.succ`: `builtin
  nat := E` for an empty `E` and then `(0 : E)` used to overflow the stack (the kernel
  unfolded a numeral without a registered `nat.zero`). A key is registered once and a
  constant has one key (`nat.zero` and `nat.succ` must be constructors): a second
  `builtin nat.add := K` changed how the Prelude's `Nat.add` unfolds without any user of
  it showing the assumption, and proved `False` with no axioms listed.
* **"The library" is the toolchain's own, wherever `wiz` runs.** The trusted modules
  were those of the first module root, `lib/` relative to the current directory. Run
  anywhere else (an installed toolchain, which passes its library as `-I share/wiz/lib`),
  the Prelude was untrusted: nineteen "builtin … is not checked" warnings on every
  `wiz check`, and every numeral listed by `#print axioms`; and a `lib/Prelude.wiz` in
  the current directory replaced the toolchain's and was trusted, registrations and
  all. Now the first root is the library next to the binary (`Module.toolchainLib`:
  `<dir>/lib` for `<dir>/.lake/build/bin/wiz`, which is a checkout, the Nix package's
  and the release tarball's `share/wiz`, as grail's `findStd`; `./lib` only when there is none), then the
  `-I` directories. Its modules are trusted, and since the first root that has a module
  wins, no other directory can stand in for one: a file that would (`Prelude.wiz` in an
  `-I` directory) is ignored with a warning. The language server uses the same roots.
  The elaboration cache keeps a module's trust in its key (`Cache.moduleKeys`), and so
  in its importers': before, a module elaborated untrusted and replayed in a trusted
  run (or the other way round) brought its warnings and its `#print axioms` with it.
  Tests: group *modules*, "trust is part of a module's cache key", "the toolchain's
  library is the first root …".

## 22g: regions: borrow checking as typing

```
def longest {ρa ρb : Region} (0 h : Outlives ρa ρb) (x : Shr ρa U64) (y : Shr ρb U64) : Result (Shr ρb U64) :=
  match U64.lt x.val y.val with
  | .true => .ok y
  | .false => .ok (Shr.weaken h x)                       -- without `h`: type mismatch
def bad {ρ : Region} (x : Shr ρ U64) : Result (Shr ρ U64) :=
  Shr.borrow ρ (U64.lit 5) (fun ρy hy y => .ok y)         -- E0515: type mismatch
```

`lib/Region.wiz` (`import Region`) is the lifetime layer of Feral's lowering
(`drafts/feral/`, RD12). A lifetime is an erased `ρ : Region`, and the borrow handles are
declared types, so with phantom parameters (22e) the region is part of their identity
and is inferred: `Shr ρ A` (`&'a A`), `Uniq ρ A` (`&'a mut A` passed in and handed back),
`Mut ρ A S` (a returned `&'a mut A` with its backward function to the lender `S`),
`MutOpt ρ A S`, and `Lent ρ S`, the lender while it is borrowed. Borrow checking is
typing:

* A borrow scope (`Shr.borrow`, `Uniq.borrow`, `Uniq.reborrow`, `Uniq.share`,
  `Uniq.zoom`, `Region.scope`) takes a body polymorphic in a fresh region, whose result
  type is chosen outside it (as `runST`), so no handle of the scope's region can leave
  it: returning a borrow of a local (E0515) or keeping one past its lender's scope
  (E0597) is a type mismatch.
* Inside a mutable borrow, the lender's name is rebound to a `Lent` token, which nothing
  accepts: using the lender, or borrowing it again, while the borrow lives (E0499,
  E0502) is a type mismatch.
* A reference flows to a place of a shorter region only through `Shr.weaken` (shared)
  or `Mut.weaken` (a returned `&mut`, covariant in its region), which take an
  `Outlives ρ ρ'` proof (erased). Proofs come from scopes (a scope nested in `σ` hands
  out `Outlives σ ρ`, so a borrow is shortened, never lengthened) and from a function's
  `'a : 'b` bounds (erased proof arguments); `Outlives` is opaque, so there is no other
  way to get one. A function returning one of two `&mut` arguments moves both into a
  `Mut ρb A (Uniq ρa A × Uniq ρb A)` (`Mut.ofUniq`, `Mut.mapBack`, `Mut.finish`) and
  needs `'a : 'b` for the first (`drafts/feral/lowered/12_pick.wiz`).

Scopes run their body at the enclosing region (regions are erased, so this is sound);
the separation comes from parametricity alone. `drafts/feral/rejected/` has the classic
errors, lowered, each rejected (`sh drafts/feral/check.sh`); test group `regions`.
The constructors of the handles are private to the module ([13b](13-language.md)), so
hand-written Wiz can't forge a handle either.

**Known gaps** (test group `regions`, the case marked KNOWN GAP, which checks that they
are *accepted* today; wishful: linear-case). Regions are enforced by the type checker;
*aliasing* is not. The handles are ω values, so a scope's body can use one twice
(`swap r r`: Rust's E0499), and the `Lent` token only shadows the lender's name, so a
body that names the token differently reads the lender while it is borrowed (E0502).
A handle can also leave its scope packed with its region (`B := (0 r : Region) × Shr r A`
is a closed type) and still be used. All three are rejected only because the lowering
(`drafts/feral/LOWERING.md`, L20) always rebinds the lender's name, uses each handle
once and never packs a region. Making the handles linear would
reject them in the kernel, but a linear variable can't be used inside a `match`
alternative today (`match` is built on `ind`, whose methods are scaled by ω) and
`Result`'s payload is ω, so it needs a case whose alternatives run once (R9a, a kernel
change). Linearity would still not be uniqueness: in-place updates stay with RC.
(Since cohesion M4, below, the handles are linear and gaps 1 and 3 are type errors; gap 2
stays, pinned in `regions`.)

**Linear handles (cohesion M4a, on linear-case stage 2).** `Uniq1 ρ A` is `&'a mut A`
used at quantity 1. It is a one-constructor inductive with a private constructor, because a
linear structure can't be taken apart; the value field is ω, and the handle is what is linear.
The scopes are `Uniq1.borrow` and `Uniq1.borrowIn` (inside a scope that holds other handles:
a call borrowing two locals threads the outer handle through), plus `reborrow`, `share`,
`zoom`, `both`, `read`, `write` and `end`. A body takes its handle at 1 and returns a
`Result1 B H`, whose `ok` *and* `err` carry the handle back (D8).
The kernel then rejects gaps 1 and 3 (E0499 by passing one `&mut` twice; packing a handle
with its region); see group `regions`.
Gap 2 stays: the lender is an ω value, so a body that names the `Lent` token differently
can still read it. Closing it needs linear lenders, and reading `*x` out of a linear value
then needs a Copy notion (K3, `sfix_π`).
Feral's lowering moved onto these in M4b. Since M4b-3d they are the only mutable handles:
the ω `Uniq`, `Mut` and `MutOpt` are gone, and `Uniq1`, `Mut1`, `MutOpt1` are renamed
`Uniq`, `Mut`, `MutOpt` (`Result1` and `Borrowed` keep their names).

Linearity closes the escape for `Uniq` (the body has one handle and must hand it back,
so it can't also pack it) but not for `Shr`, which is a copy. The scope is already rank-2
(`(0 ρ : Region) → … → Result B`, `B` bound outside); what's missing is that `B` may
still *quantify* over regions. Two ways to forbid that: put regions in a universe a
scope's `B : Type` can't quantify over (`Region : Type 1`; that needs phantom
parameters to count for a parameter whose phantom would raise the universe, which they
don't today, 22e), or give each scope an erased `[RegionFree B]` instance, derived
structurally and with no instance for `Σ (r : Region)` or `Π (r : Region)`. Either way
the lowering only has to state each scope's result type (it does: the variables that
live on after the borrow), and with the second it also has to request the instance.

## 22h: one bit-vector family

`BitVec n` (`lib/BitVec.wiz`) and `UIntN n` (`lib/Word.wiz`) are one type:

```
inductive UIntN (w : Nat) where | mk (toNat : Nat)   -- lib/Word.wiz: the model + natives
def BitVec (n : Nat) : Type := UIntN n               -- lib/BitVec.wiz: the HDL/proof names
def BitVec.add {ω n : Nat} (a b : BitVec n) : BitVec n := UIntN.add a b
def w (x : U32) : BitVec 32 := BitVec.add x (BitVec.ofNat 32 1)   -- no conversion
```

* **Design.** `UIntN` is the implementation: one model (a number below `2^w`), one set
  of natives (22c-d), one runtime representation (a word is its bits). `BitVec` is a
  view of it: a `def` alias plus the hardware vocabulary (`udiv`, `and`, `shl`, `lshr`,
  `ashr`, `slt`, `concat`, `extract`, `zeroExtend`, `signExtend`, `toVec`/`ofVec`, …),
  each defined as the `UIntN`/`IntN` operation it is (signed ones read the bits as
  `IntN n`, a free cast). The alias is enough because the width counts through
  `UIntN`'s phantom parameter (a `def` alias's own parameters never count, 22e):
  `BitVec 8` is not `U16`. The reverse (a `BitVec` structure `implemented_by` words)
  would need a second representation registration and conversions at every Feral/HDL
  boundary.
* **Proofs** see the definitions, which unfold to Word's model, so the BitVec lemmas
  are stated as before (`BitVec.add_comm` is `congrArg (UIntN.ofNat n)
  (Nat.add_comm …)`); `BitVec.add_eq : BitVec.add a b = UIntN.add a b` is `refl`.
  The literal tables (group `vec`) and the 34-operation and 64-bit word tables (group
  `word`) agree in the kernel, `#eval`, `#run`, C and LLVM.
* **Compiled**, a bit vector is a native word: no constructor or projection in the IR
  (group `vec`), no allocation below `2^63`. The model's object is now `⟨0 bits⟩`
  (the width no longer takes a slot), so a word read back prints as `.mk 18446744073709551613`.
* **For the HDL**: `Unsigned n`/`Signed n` (hdl-plan §2.2) can reuse the same
  representation as aliases (`def Unsigned (n : Nat) := UIntN n`, `Signed n := IntN n`);
  a `structure` wrapper would instead need its own `implemented_by mk get` to avoid a box.
  (Since 22i a one-field `structure` is unboxed anyway.)

## 22i: unboxed newtypes and `attribute [inline]`

```
structure Uniq (ρ : Region) (A : Type) where
  val : A                                  -- at run time, a Uniq ρ A is its A
attribute [inline] Uniq.borrow             -- compiled code runs the scope's body in place
def push (xs : List Nat) := Uniq.borrow Region.static xs (fun ρ h v r => push1 r)
#ir push                                   -- no pap, no ap, no handle allocated
```

The region discipline of 22g used to cost at run time: every handle was a cell
(`⟨val, ◾⟩`) and every scope a closure called through `ap`. Both are gone:

* **The last field of a structure can be unboxed: `--unbox-structs`, off by default.** A
  structure with fields ends in its phantom tail (22e) followed by a marker,
  `(0 fields✝ : Enum [fields✝]) → Unit`: `structure W where val : A` is
  `(val : A) × ((0 fields✝ : Enum [fields✝]) → Unit)`. Like a phantom tail it has one
  inhabitant (`fun _ => ()`, filled in by constructors and by `()` in a tuple), so η,
  `refl` and structure equality are as before, and it is erased (22e). With the option,
  erasure (`unboxedSigma`) represents a Σ whose second component is such an erased
  function into `Unit` by its first component: `S.mk a` is `a`, `.1` is the identity, `.2`
  is `◾`, and `#eval`/`#run`/`wiz run` read the value back the same way. So a one-field
  structure (a newtype: `Shr`, `Uniq`, `Lent`, `Mut`) is its field, and an `n`-field
  structure is `n − 1` pairs instead of `n`. Without it, every pair is a pair
  (`⟨a ◾⟩`).
* **Why it is off.** A representation must be a function of the type *up to conversion*,
  and the same for generic code and its callers (*stable under substitution*). The test
  is by shape (quantities and the final `Unit`, which conversion compares), not by the
  marker's label or a binder name, which it ignores: a hand-written Σ of the same shape
  converts to the structure and now has the same representation (R3 of the soundness
  audit). But no test on the second component is stable under substitution: generic code
  over `A × B` sees a variable `B` and keeps the pair, and `B` can be the structure's
  tail. `def first {A B : Type} (p : A × B) : A := p.1`, then `first (S.mk 5)`, reads
  field 0 of a number. So the default keeps pairs, and the unboxed layout is waiting for
  an encoding that carries it in something generic code also sees (a quantity:
  `wiz-notes/repr-shape.md`, option B). Group `repr`.
* **`attribute [inline] f`** (`Inline.lean`) substitutes `f`'s erased body where `f` is
  applied to all its arguments, then simplifies: a redex `(λ x. b) a` becomes a `let`,
  and a `let` of a variable, of `◾`, or of a lambda used once (not under a lambda) is
  substituted, so a lambda argument lands in the head of an application and is reduced.
  `lib/Region.wiz` marks its scopes and `Uniq.set`/`Shr.weaken`. The kernel never sees
  the attribute; inlining a recursive definition stops after a few levels.

* **Linear scopes (cohesion M4b).** Since `Uniq` is a linear one-constructor inductive,
  a `match` on a handle is `T.casesOn1`, whose method takes the tag and then the fields.
  Erasure now unfolds `casesOn1` and `casesOnA` calls as it does `casesOn`
  (`unfoldCases?`), and `simpKnown` (`Inline.lean`, run on every definition) removes what
  is left: a `case` on a known tag is its branch, `(case s bs) a` pushes `a` into the
  branches, a redex is a `let`, and a lambda bound once is moved to its use (a
  continuation such as `Uniq.end r (λ v. …)`). With `--unbox-structs`, a `Uniq.borrow`
  scope around `push1` went from 15 objects and 8 lifted functions to 4 objects and none,
  and two nested scopes from 29 and 23 to 6 and none (no scope: 3). What remains is the
  handle's cell: `Uniq` is an inductive, which `--unbox-structs` doesn't unbox
  (`wiz-notes/linear-scope-cost.md`).

Objects allocated on `#run`'s checked heap (`tests --allocs FILE ENTRY…`, a measuring
mode of the test driver), before → after (the "unbox" columns are with `--unbox-structs`;
the default has 22i's inlining on the boxed layout, not measured here):

| program (`drafts/feral/lowered`) | before | unboxed | + inline |
|---|---|---|---|
| 01 `main` (swap two `U64`s) | 12 | 6 | 4 |
| 01 `swapLists` | 11 | 7 | 5 |
| 02 `fill 5` | 106 | 82 | 32 |
| 02 `fill 50` | 5506 | 5302 | 302 |
| 07 `record` | 31 | 13 | 9 |
| 07 `record_optic` | 47 | 30 | 26 |

(`fill` was quadratic: `Uniq.set` was a call, so the vector inside the handle was
shared and `push` copied it; inlined, it is updated in place.) Not yet: case of a known
constructor, so the `.ok (q.2, q.1)` re-wrapping around each scope is still rebuilt (in
the same cells, by reuse); a recursive call through a scope's lambda is still not seen
as structural (`05_bst` `insert` stays `partial`; wishful: reborrow-recursion has a
design). The self-hosted toolchain doesn't have phantom tails at all yet.

## 22j: Feral, the surface language

```
import FeralCore
import Feral
feral
  fn swap {'a 'b} (x : &'a mut U64) (y : &'b mut U64) : Unit := {
    let t := *x;
    *x := *y;
    *y := t
  }
  fn main () : U64 × U64 := {
    let mut a : U64 := 1;
    let mut b : U64 := 2;
    swap (&mut a) (&mut b);
    (a, b)
  }
end
#eval Result.map (fun (p : U64 × U64) => (p.1.val, p.2.val)) main     -- .ok (2, 1)
```

**Feral** is the Rust-like language of the plan (it was "the Rust DSL"; its syntax is
Wiz's, its semantics Rust's). Until now it was a design, with programs lowered by hand
(22g). `lib/Feral.wiz` makes the surface real for the fragment the lowering rules cover:
functions with lifetime parameters and `'a : 'b` bounds, `let`/`let mut`, `&`/`&mut`
borrows and reborrows, structs and enums, `match`/`if let`, calls and library methods,
loops, `?`, `U64`, and functions that return borrows.

* **A command macro written in Wiz.** `feral … end` is ordinary `syntax` (categories
  `feral_item`, `feral_expr`, `feral_ty`, …) with a `CommandMacro` (7c) that runs in the
  interpreter: it checks the items and lowers each to Wiz **source text**, which is parsed
  and elaborated like anything else. `#lower feral … end` also shows that text: the
  function above becomes

  ```
  def swap {ρa ρb : Region} (x : (Uniq ρa U64)) (y : (Uniq ρb U64)) : Result (Unit × ((Uniq ρa U64) × (Uniq ρb U64))) :=
    let t := x.val;
    let x := (Uniq.set x y.val);
    let y := (Uniq.set y t);
    Result.ok ((), (x, y))
  ```
  and `main` is two nested `Uniq.borrow` scopes around the call. The rules are
  `drafts/feral/LOWERING.md` (L1–L23), cited in the code.
* **The checker's types carry regions.** The lowering is type-directed (`*x` is `x.val`
  on an argument borrow and `Mut.get` on a returned one), so the front end infers types,
  with regions as part of them, exactly as lib/Region.wiz has them: a borrow opens a
  scope with a fresh region, the lender becomes a `Lent` token inside, and what leaves
  the scope may not mention the region. A scope lasts from the borrow to the last
  statement that mentions something tied to its region.
* **Borrow errors, twice.** The front end reports E0499, E0502, E0506, E0515, E0597 and
  "lifetime may not live long enough" at the Feral expression. They are also type errors
  of the lowered program: `#unchecked feral … end` lowers without the front end's
  verdict, and the kernel rejects the result. The tests run every rejected program both
  ways, so the two can't drift apart.
* **What Feral is and isn't.** A Feral program *is* the Wiz program `#lower` shows;
  soundness never depends on the front end. But aliasing — one live `&mut`, no use of a
  lender while it is lent — is enforced by the **shape** of the lowering (scopes that
  rebind the lender's name, handles never emitted twice), not by linearity: handles are
  ω values (22g, known gaps). One Feral program shows it: `swap (&mut a) (&mut a)` is
  E0499 in the front end, yet its `#unchecked` lowering checks. The surface language
  never names handles, scopes or tokens, so when handles become linear only the text
  emitted for scopes changes. (Since cohesion M4b they are linear, and the kernel rejects
  that lowering too; reading a lender under a renamed `Lent` token is the gap that stays.)
* **Linear mode (cohesion M4b-1).** A block whose functions use `&mut` and stay in the
  fragment it covers (straight-line code, calls, `if`, `mem.swap/take/replace`) lowers to
  the linear handles of 22g (`Uniq1`). `&mut` parameters are taken at 1. `*x` becomes
  `let 1 (d, x) := Uniq1.peek x`, and `*x := e` becomes `let 1 x := Uniq1.write x e`.
  A function returns `Result1 v handles`, and every error exit hands the live handles
  back (D8). An `if` that changes a handle joins through `Result1`, and a call that
  borrows two locals threads the outer handle through `Uniq1.borrowIn`.
  `#lower` marks such functions `-- linear handles`. The kernel then rejects passing one
  `&mut` twice (E0499) on the `#unchecked` lowering too.
  Since M4b-2, `for` and `while` loops are covered too: the loop function takes every
  handle it mentions at 1 and hands it back in `Result1`. So is `v.push x` on a `&mut`,
  lowered to FeralCore's linear twin `Vec.push1`. Since M4b-3a, early exits (`return`
  and `?`) leave scopes, joins and loops as `Flow` values inside `Result1`, with the
  handles beside them. Since M4b-3b, shared borrows (`&x`, and `&*r` of a handle, e.g.
  for `r.len`) and indexing (`v[i]`) work beside live handles. The scopes thread those
  handles through (`Shr.borrowIn`, `Uniq1.shareIn`).
  Since M4b-3c, returned borrows are linear too. A function returning `&'a mut A` returns
  a `Borrowed (Mut1 ρ A S) H`. Its `ok` hands over the borrow, a `Mut1` whose backward
  function rebuilds the lender. Its `err` hands the lender's handle back (D8). With two
  lenders (`pick`), the one not returned rides along in the backward function
  (`Mut1.alongside`). `Option (&mut A)` is a `MutOpt1`. An error exit while a returned borrow
  is live first releases it (`Mut1.release`/`Mut1.finish`) and hands back what it held, so
  the error alternative is built from the environment at the exit. Cursors
  (`let mut cur := r`, `while let … := cur`, `cur := left`) are `Mut1.whole`/`Mut1.comp`.
  `match`/`if let` through a `&mut` is a `Uniq1.reborrow` whose body peeks the value. Its
  alternatives rebuild the constructor with `Uniq1.write`. `let h := &mut s.f` takes the
  fields out in a reborrow (L11). A field passed to a `&mut` parameter, `f (&mut s.f)`, is
  a `Uniq1.zoom` with the field's lens `S.fL`; `zoomIn` threads other handles through.
  Every surface program that uses `&mut` now lowers linearly. Not yet: two fields of one
  struct in one call (`g (&mut s.a) (&mut s.b)`; the `let` form does it).
  Since M4b-3d, linear mode is the only mode: every block lowers to the linear handles
  (renamed `Uniq`, `Mut`, `MutOpt`, 22g), the `-- linear handles` marker is gone, and
  FeralCore's `&mut` functions (`Vec.push`, `Vec.get_mut`) take linear handles. The
  hand-lowered drafts (`drafts/feral/lowered`, `rejected`) use the same API. Specs read
  handles at ω through `Uniq.get`/`Mut.store` (03's `final` spec is stated on the place's
  store).
* **Located output for command macros.** Runtime `Syntax` has no positions. A command
  macro now names a node of its input by **path** (child indices), and its output may
  contain `Syntax.errorAt path msg`, `Syntax.infoAt path msg` and
  `Syntax.sourceAt path text` (`Elab/ProcMacro.lean`, `pathInfo`): diagnostics at that
  node, and Wiz source parsed as commands and positioned there. Generated source that
  fails to check is reported at the node with its text.
* **Positions inside generated source.** Generated text may mark which parts come from
  which input node: U+E000 *path* U+E001 … U+E002 (`Elab/ProcMacro.lean`, `stripMarks`,
  `locateMarked`). The command elaborator strips the marks (the text checked, shown by
  `#lower` and in error reports is unchanged) and positions the parsed syntax: syntax
  whose range is exactly a marked part gets the input node's range, syntax inside one
  gets it as synthetic, the rest is synthetic at the item. Feral marks (`Fe.Out.at`) every
  expression's value, the function a call names (operators too), `&`/`&mut` arguments,
  and the names of functions, parameters, `let`s and named borrows. So inside a `feral`
  block a hover shows the type of a variable, a call (its value, named by the call's
  text, not by the lowering's `v_…`) or a `&mut` argument (its handle); go to definition
  on a call goes to the `fn` item (what a generated command declares is declared at its
  item); and a type error of the generated Wiz (say, of an `#unchecked` lowering) is at
  the Feral expression it is about. Types are those of the lowering (`Uniq ρ (Vec U64)`,
  `Result U64`); a method call on a variable (`r.push`) is one identifier, so it shows the
  receiver.

Specifications: a `spec f requires (P) ensures (Q)` item states `f.Spec`, a Wiz
proposition over the arguments' values, `result`, `old x` and `final x` (an `&mut`
argument's value when the borrow ends), with total correctness (`Result.Holds`), proved
in Wiz. With linear handles a `&mut` argument enters as its value and the call runs
inside the borrow scopes a caller would open, so the clauses are stated on the values the
scopes hand back; see [Resources in Wiz](../resources.md).

Limitations: the fragment (LOWERING.md §1a); loop invariants, `decreases` and `final result`
(a returned borrow) in specs are not supported, nor (with linear handles) a spec for a
function with an outlives bound or three or more `&mut` arguments; `U64` and `Vec`
are the stand-ins of `drafts/feral/lib/FeralCore.wiz`; keywords such as `if` and `mut`
are reserved only inside `feral … end` (13j), and only `feral` itself elsewhere; one borrow error per function; stricter than rustc where a `&mut` would be
implicitly reborrowed at a shorter lifetime.

## 22k: sealed types

Types are structural (stage 4): two `inductive` declarations of the same shape are one
type. For a type with a native representation (22d) that is wrong twice over: a
look-alike of `UIntN 8` would be a `UIntN 8` built as the model's object, and `IntN w`
and `UIntN w` would be one type with two meanings. **`sealed inductive T …`** makes `T`
a type of its own:

* the command declares an axiom `T.seal✝ : Type` (a name no source file can write) and
  puts it first in `T`'s index tail, like a phantom type parameter (22e):
  `(0 _ : T.seal✝) → (the phantom domains) → Unit`. A constant without a value is
  compared by name, so nothing that does not mention `T.seal✝` is convertible to `T`,
  and `T args = L args` for a look-alike `L` is stuck (not provable by `rfl`, not
  refutable). Constructors, patterns, recursors, `deriving` and the printer are
  unchanged: the seal is not a field.
* `#print axioms` lists the seal of every sealed type a definition depends on
  (`'f' depends on axioms: [W.seal✝]`): what it asserts is that `T` is only `T`.
* `sealed` applies to `inductive` only (not `structure`, `coinductive` or a `mutual`
  block). A sealed type without a native representation is still useful: it has no
  look-alikes (a brand).

**The words.** `lib/Word.wiz` declares `sealed inductive UIntN` and `IntN` with
`| private mk`: they are different types (`IntN.toUIntN`/`UIntN.toIntN` convert, natively
the identity on the bits), so instance resolution needs no special rule to give `I32`
signed and `U32` unsigned division (7e). Outside the module a word is built with `ofNat`.
(An unchecked builder for callers without the width at runtime, `UIntN.ofBitsTrusted`,
was a hole of its own and is gone: 22l.)

**Native representations are found by the seal.** `attribute [implemented_by mk get]
T.mk` requires `sealed inductive T` and a private `T.mk` (an error otherwise). Erasure and readback look for a
registered seal among the index type's domains (through an indexed family's Σ), not at
the `μ`'s display name, so the representation is a function of the type up to
conversion (`repr-shape.md` (I1)); the display name is no longer consulted.

**Who keeps a look-alike out** (three layers, `wiz-notes/repr-shape.md` §4C.6):

1. *Opacity (13b).* A native type's constructor is private (R5 below), so outside its
   module the type does not unfold for the elaborator, and its description `T.desc` and
   recursors are private: `Box _` against `T` is a rigid mismatch, and unification never
   sees the seal to write it on the user's behalf. (With a public constructor it can:
   `Box T.seal✝` is then `T`, which only matters for a type with no native
   representation.)
2. *Privacy of the name:* `T.seal✝` can't be written in source.
3. *Erasure, on kernel terms, whatever the elaborator did* (fatal errors): outside `T`'s
   module, no `con` is built at, and no `ind`/`scase` eliminates, a type with a native
   representation and a private constructor; and its seal may occur only inside a
   complete `μ` type (generic code over descriptions or types instantiated with the seal
   would treat a native value as the model's object). Erasure needs to know each
   declaration's module: `Globals.declModule`.

**R5 (out-of-range words).** `.mk (n + 300) : UIntN 8` built a word whose model is not
below `2^8`, on which the kernel and compiled code disagree. A native type's constructor
is private, so only its module builds values, and the module keeps the invariant the
natives rely on (for words, `n < 2^w`); this joins the natives' claim in the trusted base
(22f) as a module invariant.

Both frontends elaborate `sealed inductive` (the self-hosted one with the same axiom and
tail). Tests: groups `repr` (look-alikes, a native byte type in its own module
interpreted and compiled, R5 and layer 1, the layer-3 refusals on hand-made kernel
terms) and `selfhost` (the two frontends agree). Kernel rules: none, in either kernel.

## 22l: words carry their range

22k made the word constructors private so that `lib/Word.wiz` alone builds words and
keeps `toNat < 2^w`, the invariant the natives rely on. But the module also exported an
unchecked builder, `UIntN.ofBitsTrusted {0 w} (n : Nat) : UIntN w`, for `BitVec.concat`
and `BitVec.ofVec`, whose width was erased: `UIntN.ofBitsTrusted 5 : UIntN 1` had
`toNat = 5` in the kernel while compiled code computed on other bits
(`wiz-notes/soundness-probes/a3-word-ofbitstrusted.wiz`), the out-of-range disagreement of
R5 again, from any module.

Now the invariant is a field: `| private mk (toNat : Nat) (0 isLt : Nat.lt toNat (2^w) =
.true)`. The proof is erased, so a word is still just its bits at runtime (the native
representation, 22d, counts runtime fields: still one), and `implemented_by` gives the
native constructor the constructor's type (`UIntN.ofBits` takes the erased proof too).
The kernel now checks the range of every word, so the module invariant of 22k is a
theorem, available to users as `UIntN.toNat_lt` (and `IntN.toNat_lt`); `UIntN.ext`
(same bits, same word: the proofs don't count) and `UIntN.cases1 : (x : UIntN 1) → x = 0
∨ x = 1` follow.

What the proofs cost, without a `Nat` lemma library: every word the module builds is
either `ofNat` (reduced modulo `2^w`) or `below x b`, `x` clamped to a bound `b < 2^w`
(`Word.min`, through the natively computed `Nat.lt`), with `x ≤ b` true in every use
(`a / b`, `a % b`, `a &&& b` and `a >>> k` are at most `a`; `not a` and `ofNat`'s
remainder at most `2^w - 1`), so the clamp never changes a value and the natives still
agree with the definitions. Bitwise or and xor have no such bound from an argument, so
`Word.lor_lt`/`Word.xor_lt` prove it bit by bit (halving both arguments, as
`Nat.bitwise` does). `BitVec.concat` and `BitVec.ofVec` take their widths at runtime
(`{ω m n}`; the HDL's `Hw.cat` already did) and go through `ofNat`, and `BitVec.mk` is
`ofNat` with the width inferred. `IntN.min`/`IntN.max` are `ofNat` too (at width 0 they
used to be out of range). The kernel compares erased fields like any other, so every word
is built through one private constructor whose proof is canonical (`Word.canon`: for
closed numbers it computes to `refl`), and two closed words with the same bits are equal
by `rfl` however their range was proved. Groups `word`, `vec`.
