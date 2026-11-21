# Stage 13: the language, for programs this size

Writing the lexer and parser in Wiz showed what the language lacked:

* **Recursion on any argument.** The structural argument is the first one the first
  clause matches; a parameter before the colon is fixed only if no recursive call
  changes it — a changed one is elaborated as if it were after the colon (the induction
  hypothesis takes its value), and the others may be passed unchanged or left out.
* **`partial def` and `mutual … end`.** General recursion: the kernel treats the
  definition as opaque, justified by a witness of its type (22f, so no `False`), and its
  implementation (checked against the type) is what `#eval` and compiled code run. The
  parser's core is a mutual block, with no fuel.
* **Mutual inductive types.** `mutual inductive A … inductive B … end` becomes one
  family indexed by a tag type, `A_B : A_B.Tag → Type`, with `def A := A_B .A`.
  Recursion over a family at a concrete index (`SyntaxF .false`) works. The constructors
  are named per member, as for a single inductive type: `A.c`, `B.c` (two members may
  share a constructor name), and `.c` picks the expected member's; `deriving C` on a
  member derives `C` for the family (`Repr` shows `A.c …`). The family's name is
  internal.
* **`match` without an expected type**, **tuple patterns** `(a, b, c)`, and `x |> f`.
* Keywords of tactic syntax (`first`, `exact` …) are no longer reserved words.
* The prelude has `Nat.lt` (native at runtime), `Nat.le`, `Nat.max`, `Bool.and/or/not`.

## 13a: named arguments

```wiz
class BitPack (A : Type) where
  width : Nat
instance : BitPack Bool where
  width := 1
def bitWidth (0 A : Type) [BitPack A] : Nat := BitPack.width (A := A)
def sub (a b : Nat) : Nat := Nat.sub a b
#eval sub (b := 1) 5                    -- 4
#eval @BitPack.width (A := Bool) _
```

As in Lean, an argument `(x := e)` fills the parameter named `x`, wherever it is:
implicit, instance or explicit. The other arguments fill the explicit parameters in
order (with `@f`, every parameter), and implicit and instance parameters before a named
one get metavariables and instance problems. A named argument after the last positional
one fills its parameter; an explicit parameter before it with no argument is an error
(Lean would abstract it). Unknown and repeated names are errors (`inferAppNamed`,
`Elab/Term.lean`; test group `elabfix`).

A constructor's parameters and fields have names as well: with
`inductive P where | mk (x : Nat) (y : Nat)`, `P.mk (y := 2) (x := 1)` fills `x` with 1
and `y` with 2 — the telescope is walked in its own order, so a later field's type may
mention an earlier named one — and an implicit field or a parameter can be named too.
A missing field leaves a partial application (`P.mk (x := 1)` is a type mismatch at
`P`), an unknown field is `no parameter named 'z'`, and a repeated one is an error
(test groups `language`, `selfhost`). A dot-constructor (`.mk (x := 1)`, whose head needs
the expected type) and an inductive type's own parameters (`L (A := Nat)`) keep no names
yet.

## 13b: private declarations and private constructors

```wiz no-check
private def secret : Nat := 42          -- visible only in this module
structure Shr (ρ : Region) (A : Type) where
  private mk ::                         -- only this module makes a `Shr`
  val : A
```

`private` before a command makes every name it declares (a definition, an axiom, a
structure with its constructor and projections, an inductive type with its
constructors and recursors) private to its **module**: other modules get "'x' is
private to module M"; the module itself, including its later declarations, uses the
names as usual. Privacy is per module ([23c](23-grail.md): each module is elaborated in isolation and
under its own name), and the main file is a module of its own. In a module, a private
declaration (a function, axiom, foreign function or type, with a type's constructors,
fields and recursors) gets a kernel name of its own (`_private.M._0.secret`, as in Lean),
so two modules' private `secret`s don't clash; see
[23b](23-grail.md).

`private mk ::` right after a structure's `where` keeps the type and its projections
public but makes the constructor private. Types are structural, so a private name
alone would not stop another module from building a value: a tuple `(5, ())`, or a
structure of its own with the same fields, converts to the type. So outside its module
such a structure is also **opaque** to the elaborator: its definition doesn't unfold
(`Globals.elabView`), it is equal only to itself, and `p.val` reads it through the
projection function `S.val` (`p.1` doesn't work). Within the module nothing changes.
Like Lean's, privacy is enforced by the elaborator: the kernel checks every declaration
against the full environment, where an opaque structure is its Σ again (which is sound:
whatever converts with the definition hidden converts with it unfolded). Two *values* of an
opaque type are compared at its real definition (`Globals.hidden`, kept by `elabView`
for `conv` only), so that its proof fields are irrelevant and η applies, as in the
kernel: `P.mk 4 (lt_s 4) = P.mk 4 rfl` holds by `rfl` in any module. Only a yes or no
comes out of that comparison, and the kernel's own environment never has `hidden`.

**The elaborator never leaves a comparison to the kernel.** The other direction is not
sound for privacy: the kernel accepts what converts with the definition *unfolded*, so a
check that the elaborator skips is answered by shape. `rfl` used to be such a check: at a
stuck equation `X = Y` it produced `reflTy X` and let the kernel compare `X` with `Y`.
For a look-alike `structure Look (A) where val : A`, `rfl : Look Nat = Pos Nat` was
accepted, and `cast` along it made a `Pos Nat` without `Pos.mk` (against `lib/Region.wiz`,
a `Shr ρ Nat` at any region). Now `rfl` compares the two sides itself, in its own view
(`sameSides` in `Elab/Term.lean`: unification, then the type-directed conversion with
the elaborator's globals), for values as well as types, and at every equation left
inside one that has computed (`rflProof`). A false `rfl` is reported at the `rfl`
("rfl: the two sides are not definitionally equal"), not as "kernel rejected …", and
`first | rfl | …` in a tactic can fail. The proof that structural recursion passes to an
induction hypothesis at a concrete index (`trivialProof`) is compared the same way.

What this does and does not give. It stops the *elaborator* from producing an equation
between a private type and a look-alike. The kernel still considers the two types
equal, so a term that reaches the kernel without the elaborator comparing its types
would still be accepted:

| path | status |
|---|---|
| `rfl` at a type or value equation, also under pairs, functions and data types | closed |
| `refl X`, `cast e x`, `transp`, a tuple or look-alike against the type, `p.1` | closed (their types are unified in the elaborator's view) |
| `exact`, `rfl` and other tactics that elaborate syntax; macros (they produce syntax) | closed (they go through the same rules) |
| the tactic request `assign` with a term that still has holes | closed: such a term is kept in the tactic state and its type is inferred and compared with its goal at the end of the `by` block (it was a real bypass: `K x ?n : Look Nat` for a goal `Pos Nat`) |
| a hole solved by unification (the first-order approximation, or the flex-flex last resort) | closed: such a solution is picked by shape, not typed, so it is type-checked where it is guessed. Every hole records its type (`MetaEntry.type?`): the parameter's type for an implicit, instance or placeholder argument, the expected type for `_` and goals, `Sort ?u` for a hole that stands for a type, and the declared telescope for an output parameter, a simp or fold argument and a calc relation. The guess is compared with it in the elaborator's view (`checkGuess`, `Elab/Unify.lean`), so `def sel {F : Pos Nat → Type} (p : Pos Nat) (w : F p) : Pos Nat := p` and `sel _ (G.mk x)` for `G : Look Nat → Type` are rejected: `?F := G` would take `Look Nat → Type` for `Pos Nat → Type`, which agree only through the definition of `Pos` ("hidden outside its module", code `private`), with `:=` or equations. The error leads with the reason and names the hole by what it was made for ("the implicit argument F can't be G: the two types agree only through the definition of Pos (module Priv), hidden outside its module"), then shows the hole, its expected type, the guess and the guess's type, with the free variables by name; tests `elabfix`, `reject` ("a first-order solution cannot forge a private value", "… in equations"). A guess that can't be typed there (a pruned hole whose own Π lost a binder, a type that mentions a variable the hole is not applied to, a head whose type can't be read off, a comparison that still meets an unsolved hole at the end of the declaration) sets `ElabState.unifyGuessed`, and only that declaration is checked a second time against `Globals.elabView` (`checkGuessedDecl`). A comparison that meets a hole where the guess is made is kept and made again at the end of the declaration, with its holes solved (`recheckDeferredGuesses`); a forgery found then is reported as on the spot (`reject`, "a guess compared at the end of the declaration cannot forge either") |
| the self-hosted frontend (`selfhost/Frontend.wiz`) | partly closed (stage 21n): private names are module-scoped there; the type-level rules above (a type with private parts is opaque) are not implemented |
| `T.desc` of an inductive or coinductive type with private parts: `μ T.desc i` written out is the type with nothing hidden, and a raw `con` builds a value of it | closed: `T.desc` is private with the constructors and recursors (a structure has no description). Generic code over `Desc` in another module can't be pointed at such a type; it could not be applied to its values before either, since the type is opaque there. `deriving` reads the kernel's declarations, not the name, and is unaffected (a derived instance that matches on the type is refused as before) |
| inside the declaring module | by design: there the look-alike is the same type |

So privacy is **not sealed**: it holds against the rules listed as closed, not against
every term the elaborator can produce. Closing it for good needs the kernel to tell a
type from its look-alike (`wiz-notes/structural-vs-nominal.md`, §6a).

**`wiz --strict-privacy`** (off by default; an experiment to measure). Every declaration
of a module that sees a type opaque to it is checked a second time, by the kernel's
checker, against the elaborator's view (`privacyCheck`, `Elab/Command.lean`). A
declaration that passes used no hidden shape, so this also rejects a forgery that some
other rule left to the kernel: "forge depends on the definition of Pos (module Priv),
which is hidden outside its module". It is not the default because it also rejects
legitimate proofs that compute through a library operation on such a type: the
elaborator quotes evaluated values into terms, and a raw pair or projection at a type
without a definition does not type-check (`drafts/rust/lowered/03_get_mut.wiz`,
`get_mut.is_place` and `get_mut.spec_under`). With the flag a type with private parts is
abstract for proofs as well.

**`wiz --trace-guess-fallback`** (a diagnostic, off by default). Every hole a guess can
meet records its type, apart from a pruned hole whose own function type lost a binder
and a constant whose declared type is not a function there. Even so, a guess can still
reach the whole-declaration recheck: its type can mention a variable the hole is not
applied to, the guessed head's type can't be read off, or the comparison can still meet
a hole at the end of the declaration (a comparison that meets one where the guess is made
is made again there, once the holes are solved). The flag prints one line per declaration that reaches the recheck, with the
reasons: `guess-fallback: <module> <declaration> recheck=ran|skipped reasons=…`
(`skipped`: no other module's private type is in view, so the recheck has nothing to
hide). `scripts/guess-fallback-stats.sh` counts them over `lib/`, `examples/` and `tests/`
(`WIZ`), and over the programs inline in the test groups (`--tests TESTS`: the tests binary
takes the same flag, and its cases' lines name their file `GROUP#INDEX`).
The goal is zero, so the recheck can go.

The motivating use is `lib/Region.wiz` ([22g](22-numbers.md)): the constructors of the borrow handles
`Shr`, `Uniq`, `Mut` and `Lent` are private, so a handle at a region comes only from a
scope or an operation of the library, and hand-written Wiz can't forge one
(`drafts/rust/rejected/forge_handle.wiz`; test group `regions`). `MutOpt`'s constructors
stay public: their fields are handles already.

```wiz no-check
inductive Tok where
  | num (n : Nat)
  | private secret (n : Nat)            -- only this module makes a `.secret`
coinductive Signal (d : Domain) (A : Type) where
  private head : A                      -- only this module observes a signal
  private tail : Signal d A
structure Acct where
  owner : Nat
  private bal : Nat                     -- `Acct.bal` is private; `Acct.mk` isn't
```

The same opacity covers the other declarations with private parts. In each case the
private names are private to the module, and **elsewhere the type is opaque**: it is a
type constant that equals only itself, so the primitives (`con`, `cocon`, `out`, `.1`),
tuples and look-alike types don't convert to it.

* `| private c …` (an `inductive`): `T.c` is private, and so are the recursors `T.rec`,
  `T.casesOn` (and `scasesOn`, `recN`, `casesOnN`). The public constructors stay usable,
  also as `.c` against an expected `T`. Outside the module a `T` can't be **matched**,
  not even on its public constructors with a catch-all: a `match` compiles to
  `T.casesOn`, whose case for `c` hands out `c`'s fields, and the case tree needs `T`'s
  description, which is what the opacity hides. So exhaustiveness never comes up
  there; the module exports the eliminators it wants (`Tok.value`, or a fold). In a
  `mutual` block the types are one indexed family, so a private constructor makes the
  whole family opaque.
* `private f : A` (an observation of a `coinductive`): `T.f` is private, and so is the
  coconstructor `T.mk` (it would build a value from the private observation's value).
  Outside the module a `T` isn't observed through `f` (`s.f`, `T.f s`, `out s`) and
  isn't defined by **copatterns**, which give every observation ("'Signal.head' is
  private to module Signal: a Signal can't be defined by copatterns outside it"); public
  observations are read through their functions, `s.g`.
* `private f : A` (a field of a `structure`): `S.f` is private and `S` is opaque
  elsewhere, as with `private mk ::`; the constructor stays public unless it is
  `private mk ::` too. A class's methods can't be private.
* A type declared `private` (`private inductive T`) is not opaque, but its recursors are
  private, so a value of it that reaches another module (through a public definition)
  isn't matched there either.

All of this is elaboration only, as above: the kernel checks against the full
environment, and whatever the elaborator accepts with `T`'s definition hidden also
checks with it unfolded. The self-hosted frontend parses the `private` markers and
ignores them. The motivating use is the HDL's signals (`drafts/hdl/Signal.wiz`): user
code builds and observes them only through the library's combinators and `sample`
(`drafts/hdl/rejected/observe_signal.wiz`). Tests: group `elabfix`.

## 13c: `if`, `&&`, `||`, `!` in the Prelude

```wiz
import Prelude
def clamp (n : Nat) : Nat := if Nat.lt n 10 then n else 10
#eval Nat.beq 1 1 && !(Nat.beq 2 3) || Bool.false    -- .true
```

`lib/Prelude.wiz` now declares `if c then a else b` (a macro for
`match c with | .true => a | .false => b`), and `a && b`, `a || b` as macros for
`match a with | .true => b | .false => .false` and `match a with | .true => .true | .false => b`,
so both **short-circuit**: compiled code (and `#eval`) evaluates `b` only when `a` doesn't
decide. `!b` is `Bool.not b`. Precedences are Lean's: `if` is a leading term like `match`,
`||` 30, `&&` 35 (right-associative), `!` binds tightest. The kernel sees the `match`, so
`Bool.true && b` reduces to `b`, as `Bool.and Bool.true b` does, but a stuck `a && b` is a
`match` on `a` and not convertible to `Bool.and a b` (state lemmas about `Bool.and` by
cases on `a`). `if`, `then` and `else` are now reserved words in every program; `not` is
not (constructors and class fields named `not` exist in `lib/Hdl`).

The self-hosted frontend doesn't read `lib/Prelude.wiz`: it embeds its own prelude
(`preludeText`, selfhost/Frontend.wiz) and has had `if` since 19a (an application of `if`,
rewritten to a `match`). It has no `&&`, `||` or `!`, so `selfhost/*.wiz` don't use them.
Tests: group `language`.

## 13d: `Functor` and `Applicative` (`import Functor`)

```wiz no-check
import Functor
#eval Nat.add <$> Option.some 1 <*> Option.some 2          -- .some 3
#eval (fun (a b : Nat) => (a, b)) <$> List.cons 1 (List.cons 2 .nil) <*> List.cons 3 .nil
                                        -- .cons (1, 3) (.cons (2, 3) .nil)
def both : IO (String × String) := (fun (a b : String) => (a, b)) <$> IO.readFile "a" <*> IO.readFile "b"
```

`lib/Functor.wiz` has `class Functor f` (`map`), `class Applicative f` (`pure`, `seq`),
`f <$> x` (`Functor.map`, infixr 100) and `mf <*> x` (`Applicative.seq`, infixl 60), as in
Lean. Two generic instances make **every `Monad` an `Applicative`** (`seq` by two binds)
and **every `Applicative` a `Functor`** (`map g x = pure g <*> x`), so `IO`, `Eff r`,
`Eff1 ω r R`, `StateT`, `ReaderT`, `TacticM` and user monads get `<$>`/`<*>` with no more
declarations. The module also gives `Monad` instances for `Option`, `Except E` and `List`
(nondeterminism: `<*>` takes every combination), with direct `Functor` instances
(`Option.map`, `Except.map`, `List.map`). An instance declared later wins over the
generic ones (7b), which is how a type that isn't a monad (an HDL signal) declares its own
`Applicative`.

`Monad` itself is unchanged (it doesn't extend `Applicative`: classes have no `extends`
yet), so `do`, `Monad1` and `do1` are as before. The module is separate from the Prelude
because programs that import only the Prelude already define `List.map`, a class
`Functor` and `Monad Option` instances of their own (`lib/Hdl/Core.wiz`, the tests).
Tests: group `language`.

## 13e: `∃ x, P`, `¬`, and ASCII spellings

```wiz
import Logic
def two : ∃ n : Nat, n + n = 4 := Ex.intro _ 2 rfl
def swap {A : Type} {P : A → A → Prop} (h : ∃ x y, P x y) : ∃ y x, P x y :=
  Ex.elim h (fun x h' => Ex.elim h' (fun y p =>
    Ex.intro (fun y => ∃ x, P x y) y (Ex.intro (fun x => P x y) x p)))
def nope : ¬ (exists (b : Bool), b = .true ∧ b = .false) :=
  fun h => Ex.elim h (fun b p => Bool.trueNeFalse (Eq.trans (Eq.symm p.1) p.2))
```

`lib/Logic.wiz` has binder notation for its Church-encoded `Ex`: `∃ x, P` is
`Ex (fun x => P)`, with binders as in `fun` and an optional type for all of them
(`∃ x y : A, P`, `∃ (x : A) (y : B), P`, `∃ x (y : B), P`). The body extends as far as
possible, as `∀`'s does. A nested `Ex.intro` wants its motive (`Ex.intro (fun y => ∃ x, P x y) y …`):
with holes for both motives the elaborator can't solve them from the expected type. A procedural macro (`Ex.binderMacro`) builds the nested `Ex`s,
since quotations can't splice lists. `¬ P` is `Not P` (Lean's precedence: `¬ a = b` is
`¬ (a = b)`). ASCII spellings follow `->` for `→`, `fun` for `λ`, `=>` for `↦`:
`forall` for `∀` (built in, so `forall` is a reserved word now), `exists` for `∃`, `/\`
for `∧`, `\/` for `∨`, `<->` for `↔`. `lib/Logic.wiz` and `lib/HProp.wiz` state their
lemmas with them (`hexists J h` is `∃ a : A, J a h`; `star` is
`∃ h₁ h₂ : Heap V, StarAt …`). Tests: group `language`.

## 13f: `let` with tuple patterns of any length

```wiz no-check
def f (p : Nat × Nat × Nat) : Nat := let (a, b, c) := p; a + b * c
def lin (1 p : Nat × Tok × Tok) : Unit × Unit :=
  let 1 (n, s, t) := p;
  (Tok.close s, Tok.close t)
```

`let q (p₁, …, pₙ) := e; body` with three or more components is the general `let` with a
pattern of 13h: `(p₁, …, pₙ)` is the tuple pattern `(p₁, (p₂, …))` (`term.tuplePat`), so
the components may be any patterns (a nested tuple, `_`, or a constructor — the `let` is
then a `match`, so the constructors must be covered), and without a quantity the `let` is
the `match` on the tuple that 13h describes. With a quantity `q` the components must be
names: each step is a `let (x, y)` split at quantity `q` (right-nested, as tuple types
are), so with `let 1` every component of a linear tuple is bound once, which is how a
tuple holding resources is taken apart now that linear pairs aren't projected. (Two
components are `term.letPair`, the same split.) Tests: group `language`.

## 13g: as-patterns `x@p`

```wiz
def last (A : Type) (d : A) : List A → A
  | .nil => d
  | .cons x .nil => x
  | .cons _ xs@(.cons _ _) => last A d xs     -- `xs` is the tail that was matched
def dup : List Nat → List Nat
  | .nil => .nil
  | l@(.cons x _) => .cons x l
```

`x@p` (no space around the `@`; `p` an atomic pattern, so a constructor with arguments
goes in parentheses) matches `p` and binds `x` to the value that was matched. It may be
nested anywhere a pattern may, on any kind of pattern (`q@(a, b)`, `n@m@(.succ _)`).

`x` is bound exactly as a variable pattern in that position would be (`compileMatch`,
`Elab/Term.lean`): to the scrutinised variable itself, so no constructor is rebuilt,
unless the goal depends on that variable; then it is the constructor applied to the
fields, which is what has the refined type. Because `x` *is* the matched variable, an
as-pattern on a recursive field is structurally smaller: `last A d xs` above is the
induction hypothesis of the tail. (Without the as-pattern one had to write a helper
that takes the head and the tail separately: "recursive call must be on a variable".)

Limits: when the goal depends on the matched variable, `x` is the rebuilt constructor,
and a recursive call on it is not recognised ("not a recursive field"). In a term,
`x@p` is an error ("only allowed in a pattern").

Not solved by as-patterns: recursion over a family at an index that is not a variable.
`Vec.last : Vec A (Nat.succ n) → A` with `| .cons _ xs@(.cons _ _) => Vec.last xs` now
gets as far as the kernel, which rejects it ("expected: n = .succ (.succ n)"): the
induction hypothesis of a definition matched at the index `succ n` is for that same `n`
(the parameters before the colon are fixed), and the tail is a `Vec A n`. `lib/Vec.wiz`
keeps its helper `Vec.lastFrom`, whose index is a variable that the motive generalises.

Syntax: `term.asPat`, a trailing parser at the highest precedence, `x "@" p` with no
whitespace on either side of the `@`. Explicit application is unchanged, `f @g` and
also `f@g`: where both readings are as long, the application wins, so an as-pattern
whose pattern is a bare name (`x@y`, a second name for the same value) is not available;
`x@_` and `x@(y)` are. Tests: `language` ("as-patterns …"),
`parser: terms`.

## 13h: patterns on structures, `⟨…⟩`

```wiz
structure Stats where
  hits : Nat
  misses : Nat
def total (s : Stats) : Nat := match s with
  | .mk h m => Nat.add h m                 -- also `Stats.mk h m` and `⟨h, m⟩`
def total' (s : Stats) : Nat :=
  let ⟨h, m⟩ := s                           -- or `let (.mk h m) := s`
  Nat.add h m
def stats : Stats := ⟨3, 4⟩                 -- `Stats.mk 3 4`, from the expected type
```

A structure is a Σ type, not a data type, so there is no eliminator to split it with
("cannot match on a value of type Nat × Nat × …" before). A constructor pattern on a
scrutinee whose type is a structure `S` (`.mk p…`, `S.mk p…` or `⟨p…⟩`) is now
rewritten to the **tuple pattern** over the components of `S`'s Σ, which binds every
field as a projection of the scrutinee (`let h := s.1; let m := s.2.1; …`); the
sub-patterns are ordinary patterns, so structure patterns nest in constructor and tuple
patterns and the other way round, and mix with as-patterns.

**One place knows the encoding.** How the Σ of a structure is laid out (which
component is which field, and which are not fields at all: today the tail
`(0 fields✝ : …) → Unit` after the last field, 22i) is read from the declaration by
`structLayout?` (`Elab/Struct.lean`), as a list of components, each a field or a marker;
structure patterns, the pattern `let` and structure update (13i) go through it and
nothing else there looks at the Σ. It classifies the components by what the
declaration says (a Σ binder with a phantom name is a marker, the final component is a
field exactly if `S.mk` has a field left for it), so moving the marker to a 0-quantity
component before the last field needs no change here; any other re-encoding is a change
to that one function.

The anonymous constructor `⟨e₁, …, eₙ⟩` is new syntax (`term.anon`), as a term and as a
pattern. Against a structure it is `S.mk e₁ … eₙ`; against a pair, the tuple
`(e₁, …, eₙ)`; against a data type with exactly one constructor, that constructor. It
needs an expected type ("cannot infer the type of an anonymous constructor").

`let pat := e; body` with `pat` an anonymous constructor or any pattern in parentheses
(`term.letPat`) is `match e with | pat => body`, so it also works without an expected
type.

**Linear structures.** A `match` is a case at ω and projections need an unrestricted
pair, so neither takes apart a structure held at quantity 1. With a quantity,
`let 1 ⟨a, b⟩ := s; body` (or `let 1 (.mk a b) := s`) therefore elaborates to nested
splits at that quantity, one per component of the layout, as `let 1 (a, b, c) := t`
does for a tuple (and `let 1 ⟨a, b, c⟩ := t` is accepted on a tuple too); the components
are then names or `_`, and the form is check-mode only. **Today this is rejected for
every structure**: the Σ ends in the marker tail, which is not a field, and the last
split would bind it at quantity 1 and never use it. The elaborator reports that itself
("cannot take a value of the structure Stats apart at quantity 1: the Σ type of a
structure ends in a component that is not a field …") instead of leaving it to the
kernel's usage count. The check is on the layout (a marker that the Σ does not bind at
quantity 0), so once the marker is an erased component the same `let` goes through with
no change here. At quantity ω (`let ω ⟨a, b⟩ := s`) the splits are accepted today.

A structure whose constructor or fields are private to another module (13b) is opaque
there and can't be matched or taken apart ("its constructor is private to module M").

Tests: `language` ("structure patterns …", "anonymous constructors …", "let with a
structure pattern …"), `parser: terms`.

## 13i: structure update `{ s with f := v }`

```wiz no-check
def bump (s : Stats) : Stats := { s with hits := Nat.succ s.hits }
def reset (s : Stats) : Stats := { s with hits := 0, misses := 0 }
```

`{ s with f₁ := v₁, …, fₖ := vₖ }` is `S.mk` applied to the structure's parameters
(taken from the type of `s`) and to every field: `vᵢ` for a named field, checked against
the field's type, and the projection of `s` for the others. `s` is any term; unless it
is a variable it is bound once (`let s✝ := s`). The type of `s` must be a structure,
and it is the type of the result; nothing is taken from the expected type. Unknown
fields ("Stats has no field 'x' (its fields are hits, misses)") and repeated ones are
errors. With dependent fields, a kept field whose type mentions an updated one must
still fit: `{ d with n := 3 }` for `structure D where n : Nat; v : Vec Nat n` is "field
'v' keeps its value, but its type … depends on an updated field"; update both.

The projections make this an unrestricted use of `s`: a structure held at quantity 1
can't be updated this way (take it apart with the pattern `let` of 13h, once that works
for linear structures). Like 13h it reads the fields through `structLayout?`, and it is
refused for a structure that is opaque in the current module.

Syntax: `term.structUpdate`, `"{" term "with" (ident ":=" term),+ "}"`. No new reserved
word (`with` already is one). An updated field's value may itself be an update
(`{ s with inner := { t with x := 1 } }`); that is a term nested in the update, not a
field path (13p). Tests: `language` ("structure update …"), `elab` ("structure update
{ s with f := v } …"), `parser: terms`.

## 13j: keyword scopes

A keyword of a `term` or `command` rule is reserved in the whole file; a keyword of any
other category is reserved nowhere (`"if"` there matches an identifier spelled `if`).
That is right for tactics, whose names stay usable as variables, and wrong for an
embedded language with identifiers and application by juxtaposition: its `ident` rule
accepts `then` too, so `if c then a else b` is the application of `if` to five arguments.
Reserving the words globally (by listing them in a `command` rule) takes `if`, `in`,
`mut`, `fn` … away from every file that imports the language.

```
declare_syntax_cat feral_expr (keywords := feral)
declare_syntax_cat feral_stmt (keywords := feral)
```

puts the categories in the **keyword scope** `feral`. The identifier-like atoms of their
rules are the scope's keywords, and an `ident` item inside a category of the scope does
not match them:

* inside the language, `if c then a else b` is the `if` rule, and `let if := 1` is
  `expected identifier ('if' is a keyword here)`;
* outside it (in `term`, in `command`, in another language, and in a `term` nested
  inside the language) the words are ordinary identifiers;
* categories share a scope by naming it, because a keyword of statements (`return`) must
  not be an identifier of expressions (or `f x` and a `return y` on the next line are
  one application).

The scope's name is an identifier, so it can't be a word that is reserved at that point
(declare the categories before the `syntax "feral" … : command` rule, or pick another
name). A category keeps the scope it was first declared with. Symbol atoms (`+=`, `..`)
are still tokens everywhere: they never take an identifier away.

The parser stays scannerless with one token table (`Wiz/Parser/Token.lean`): the scope is
a property of the category being parsed (`ParserTables.reservedIn`, read by the `ident`
case of `runDescr`), so the memo key, which already names the category, is unchanged.
The design options are in the notes (`scoped-keywords.md`). The self-hosted parser
interprets the built-in tables, which use no scope; it dispatches `syntax` and
`declare_syntax_cat` ([21ac](21-bootstrap.md); the `selfhost-macro` group checks them),
but does not track a category's keyword scope, so a scope is accepted and not enforced
there.
Tests: `parser: commands and syntax`, `language`.

## 13k: list literals

`[a, b, c]` is `List.cons a (List.cons b (List.cons c List.nil))` and `[]` is `List.nil`,
in terms and in patterns:

```wiz
def xs : List Nat := [1, 2, 3]
def len : List Nat → Nat
  | [] => 0
  | [_] => 1
  | _ => 2
```

It is a Prelude `syntax` with a procedural macro (`ListLit.expand`), not built-in
grammar. The self-hosted toolchain cannot run a macro at elaboration time, so it adds
the same surface rule itself (`term.listLit` in `selfhost/Parse.wiz`, precedence 1024)
and rewrites the node to `List.cons`/`List.nil` in `selfhost/Frontend.wiz`; its embedded
prelude (`preludeText`) declares nothing for it. `[` already starts an instance binder in a dependent arrow
(`[Monad m] → m A`, `[inst : C A] → B`): that is one leading parser that also consumes
the arrow, so it is longer than a list literal and wins (longest match, `Wiz/Parser/Interp.lean`);
`Enum [a, b]`, `ecase t [..]` and `attribute [..]` are leading parsers that consume their
brackets in the same way. The elements are checked at the element type of the expected
`List A` (`List.cons a …` is an ordinary application), so numerals at a non-`Nat` element
type go through `OfNat` like any argument (7e).

**Patterns.** The match compiler (`patView`) reads constructors, applications, tuples and
parentheses. Patterns are now macro-expanded first (`expandPattern`, `Wiz/Elab/Term.lean`;
in `match` and in definitions by equations; inside `⟨…⟩` and `x@p` (13g–h) too): every syntax kind other than those forms is
expanded if a macro applies, so `[x, y]` becomes `List.cons x (List.cons y List.nil)`,
and a user notation whose expansion is a constructor application works in patterns too.
Tests: group `language`.

**`x :: xs`.** The Prelude declares `infixr:67 " :: " => List.cons`, so a cons cell can
be written `x :: xs` in terms and in patterns. It is right-associative at 67, the
precedence of `++` (13l), and tighter than the arrows (25): `1 :: 2 :: xs` is
`1 :: (2 :: xs)`, `x :: xs ++ ys` is `x :: (xs ++ ys)` (`++` is right-associative at
67 too, so it sits in the `::` tail), and `x :: xs → P` is `(x :: xs) → P`. A list
literal tail keeps the literal spelling: `1 :: [2]` prints as `[1, 2]`; a cons with a
variable tail prints as `x :: xs` (the inverse of the notation
rule that 11r installs for every `infix`; `set_option pp.notation false` prints
`List.cons Nat x xs`). The self-hosted prelude, `preludeText` in `selfhost/Frontend.wiz`,
declares the same `infixr`, so both frontends expand it to `List.cons` and the
`selfhost` differential case computes with it. Tests: group `language`, `reject`
(`1 :: 2`), and `selfhost`.

## 13l: `++` for lists and strings

`a ++ b` elaborates to `HAppend.hAppend a b` (`lib/Prelude.wiz`'s
`infixr:67 " ++ "`), the method of the heterogeneous class `HAppend (A B : Type)
(C : outParam Type)`. The homogeneous class `Append (A : Type)` with
`append : A → A → A` has instances for `List A` (`List.append`) and `String`
(`String.append`), and `instHAppend {A : Type} [Append A] : HAppend A A A` is registered
as a **default instance**: at a homogeneous type `++` therefore resolves to
`Append.append`, and a heterogeneous instance (like `HMul Nat V V` in 7f) resolves
without one. Other types get `++` by an `Append` instance or a heterogeneous `HAppend`
one. (`lib/Hdl/Core.wiz`'s `<+>` and `selfhost/Parse.wiz`'s `+++` are older local
spellings of `String.append`; the self-hosted prelude keeps
`infixr " ++ " => List.append`.) Tests: group `language` (`++` on lists and strings).

## 13m: local notation

A grammar command marked `local` stays in its module: modules that import it don't see
the syntax.

```wiz
local infixr:67 " & " => String.append
local syntax (name := shout) "shout" term : term
local macro_rules
  | `(term| shout $x) => `(term| $x & "!")
```

`local` applies to `syntax`, `declare_syntax_cat`, `notation`, `infixl`/`infixr`/`infix`,
`macro_rules`, `attribute [macro …]`, `attribute [simp]`, `instance`,
`app_unexpander` and `attribute [app_unexpander …]` (the ten command kinds
`Wiz/Elab/Command.lean` accepts; any other command is an error there). In the main file
it changes nothing. `local` is not a reserved word. The `language` group pins
`local instance` (11w) and the `simp` group pins `local attribute [simp]`; the
self-hosted frontend unwraps `local` and leaves the notation visible to importers
([21ac](21-bootstrap.md)).

An `import` elaborates the module's text into the importer's state, so its
syntax lands in the importer's parser tables. The state records what each `local`
command added (new node kinds and categories, and which macro rules and macro
registrations, by position), and when the import ends (`CommandState.endModule`, called
by `runFrontend` and by the command cache's import walker) those are removed: the
parsers of the kinds (and the categories), every macro rule, macro and tactic of those
kinds, and the local rules; a token that no remaining parser mentions is no longer
reserved (so a local keyword `shout` is an identifier again in the importer). Kind
names stay taken, so an importer that declares the same notation gets a new kind and
none of the dropped rules. Definitions written with the notation are unaffected (they
are terms by then). Lean also has `scoped` notation, active where a namespace is open;
Wiz's `open` (13t) scopes names, not notation, so the module is still the only notation
scope. The design notes are in the notes
(`notation.md`). `command.local` is built-in grammar (`Wiz/Parser/Builtin.lean`), so the
self-hosted parser's generated tables have it too; the self-hosted frontend also
dispatches `syntax` and `declare_syntax_cat` ([21ac](21-bootstrap.md)), but it unwraps
`local` and does not keep the command's rules in the module: a local notation or macro
rule stays visible to importers there ([21ac](21-bootstrap.md)'s "Not done"). Tests:
groups `language`, `parser: commands and syntax`.

## 13n: `rfl` at an equation that has computed

An equation at a Σ type computes as soon as it is formed: `a = b` becomes
`(0 e : a.1 = b.1) × (cast (B a.1) (B b.1) ê a.2 = b.2)`. The elaborator's `rfl` used to
prove that Σ field by field. Every field after the first then needed the cast to
disappear, and at a type variable (`B`, `List A`, a function type) it does not: regularity
holds only at inert types (P1). So `s = s` at `A × B`, `(p.1, p.2) = p`,
`Pair2.mk s.fst s.snd = s` (structure η, which conversion already has), and the field
lenses' laws all failed with "the two sides are not definitionally equal".

Now `vEq` keeps the equation's type at the end of the Σ's closure (the body doesn't use
it), and `eqSigmaSides?` reads `A`, `a`, `b` back. When `a ≡ b`, `rfl` is a single
`refl A a`, whose type computes to the same Σ, with the same cast on both sides. This is
the optional exercise 4.16, done by recording the equation in its computed form. No axiom
is used: `#print axioms` lists none for these proofs. An equation at a constructor
(`List.cons x xs = List.cons x xs`) works the same way, through its payload's Σ.

**Inside a `match` clause** the expected type is the motive, read back (`quote`) and
evaluated at the pattern. The read-back spelled the computed Σ out, so the equation was
lost and `rfl` failed there (cohesion-hardware's `step_cases`). Two changes fix this:
* `vEq` now also puts an unforgeable mark in the closure (a global whose name can't be
  written), so `eqSigmaSides?` recognises only its own Σs;
* with `Globals.quoteEqs`, which the elaborator's `getGlobals` sets, `quote` reads a
  marked Σ back as the equation `a = b`, and that evaluates to the same Σ again.

The kernel and `#reduce` leave the flag off and still show the computed form. The
elaborator's messages now print such a type as the equation.

Nothing else changed. A Σ of field equations written by hand, with a cast at a type
variable in it, is still not `rfl`. `rfl` never adds an axiom; whoever needs that
equation writes `castRefl` themselves.

`lib/Optic.wiz` now states the `Pair2` lens laws with their implicit arguments
(`@Lens.Lawful (Pair2 A B) A …`), so that the equation has computed when `rfl` sees it.
Before, they checked only because unsolved holes kept the equation from computing.
Research note: `wiz-notes/structure-eta.md`. Tests: group `elabfix`, "rfl at an equation
that has computed"; group `optic`.

## 13o: DSL conventions

The embedded languages follow one set of conventions (entering, scoping, symbols,
printing, errors, docs, tests), collected in [docs/dsls.md](../dsls.md) with a table of
the DSLs. This section's changes bring the libraries in line:

* **Helper notation is local** (13m). `∷` (HoareTactics) and `+++`, `⊕`, `▸` (Feral)
  are used only inside their modules; they were global, so every importer lost those
  symbols and (with 11r) printed `List.cons`/`String.append` with them. (Hdl.Core's
  `<+>` is the HDL libraries' shared operator — `Hdl.Prim`, `Hdl.Xdc`, `Hdl.Xilinx7`,
  `Hdl.Sim` and the examples use it — so it stays public.)
* **A reserved word says where it comes from.** An identifier position holding a keyword
  of a `term` or `command` rule says so, with the notation (its atoms, `…` between them)
  and the module that declared it: `def exists := 1` after `import Logic` is
  `expected identifier ('exists' is a keyword: the notation `exists …, …` of module
  Logic)` (`ParseError.explainKeywords`, `Wiz/Frontend/Parse.lean`; looked up only when
  the error is reported, with the declaring modules of 11q). Built-in keywords say
  `('def' is a keyword)`.
* **A constructor pattern of another type** is an error that says so, at the pattern
  (at the `match` when a macro wrote it): `if n then 1 else 2` at `n : Nat` was
  "missing case for constructor zero" (the `.true`/`.false` match `if` expands to) and is
  `the value matched has type Nat, which has no constructor .true (its constructors:
  .zero, .succ); the condition of `if`, `&&` and `||` is a Bool`. Type-ascribing the
  condition in the macro instead would lose the refinement of a variable condition in
  the branches' types.

Tests: groups `language`, `seplogic`. Audit and table: `wiz-notes/dsl-conventions.md`.

## 13p: nested structure update `{ s with a.b := v }`, printed back

```wiz
structure In where
  x : Nat
  y : Nat
structure Out where
  i : In
  n : Nat
def f (o : Out) : Out := { o with i.x := 10, n := 4 }   -- i := { o.i with x := 10 }
def g (o : Out) : Out := { o with i.x := 5, i.y := 6 }  -- one update of `i`
```

A field path `a.b := v` in a structure update (13i) updates field `b` of the structure
held in field `a`: it is `a := { s.a with b := v }`, the inner update over the
projection of `s` (bound once, like `s`). Paths into the same field are grouped, so
`i.x := 5, i.y := 6` is one inner update; paths nest to any depth (`o.i.y := 0`).
A field updated both directly and through a path, or one path given twice, is
"field 'i' is updated twice" ("field 'i.x' …"); a path through a field that is not a
structure is "field 'n' is not a structure (its type is Nat), so its fields can't be
updated"; an unknown field in a path names the inner structure ("In has no field 'z'").
A field updated through a path keeps its type, so the dependent-field rule of 13i
applies to it as to a kept field.

Updates work for every structure, since all of them are Σ types read through
`StructLayout`: with parameters, with dependent fields, and for bundles, structures
over a representation `structure Tx (r : HwTy → Type) where line : r Bit; …`
(`lib/Hdl/Core.wiz`): `{ s with line := v }` at `Tx r` keeps `r` abstract.

**Hover and go to definition.** The field name of an update is recorded as a use of
the projection `S.f`: a hover shows its type in the updated structure, and go to
definition jumps to the declaration of the structure that has the field (where the
projections are declared). A path is recorded as its last field
(`i.y` as `In.y`).

**Printed back.** The printer shows `S.mk Δ a₁ … aₙ` as `{ s with fᵢ := aᵢ, … }` when
some fields are the projections of one term `s` at their own components and the others
are not (with every field replaced it is just `S.mk a₁ … aₙ`), `let x := e; S.mk …` (an update of a non-variable `e`) as `{ e with … }`, and a
field updated with an update of its own old value as a path, so the three forms above
print as written. The layout moved to `Wiz/Core/StructLayout.lean` so that the printer
can read it (`structLayoutWith?`; `Elab/Struct.lean`'s `structLayout?` is the same
function). `set_option pp.notation false` (or `--pp-all`) prints `S.mk` as it is.

Tests: `language` ("13p: …"), `lsp` ("13p–q: an updated field's hover and definition …").

## 13q: numeral and literal patterns

```wiz no-check
def cls : Nat → Nat
  | 0 => 10
  | 1 => 11
  | n+2 => n
def sum : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + sum n      -- structural: `n + 1` is `.succ n`
def op (b : U8) : Nat := match b with
  | 0x3F => 1
  | 0 => 2
  | _ => 3                      -- required: numerals don't cover U8
```

**At `Nat`** (the `builtin nat` type) a numeral pattern is its constructors, peeled one
at a time as the match compiler splits (`natPatView`): `0` is `.zero`, `n` is
`.succ (n - 1)`, and `p + k` (as `+` expands, `Add.add p k`, with a numeral `k`) is
`.succ (p + (k - 1))`. So numeral patterns mix with constructor patterns, as-patterns
and tuples, refine types like constructor patterns (`F : Nat → Type | 0 => Bool | _ =>
Nat`), and `| n + 1 => … f n …` is structurally recursive. Recursion is still on the
immediate predecessor only: `| n + 2 => f n` is "not structurally smaller" (the case
tree splits twice, and only the first split has a hypothesis). The case tree grows with
the numeral, so a numeral pattern at `Nat` is at most 256 ("the numeral pattern 300 is
too large …; test with `Nat.beq` instead"). The self-hosted frontend already read
numeral patterns this way (`patOf`, `selfhost/Frontend.wiz`).

**At other types** a literal is an equality test. For a column of type `T` whose first
row has a literal `l`, the column is compared with `T.beq x l`, where `T` is the first
type in the chain of definitions the column's type unfolds through that has a `T.beq`
(`BitVec 8`, then `UIntN 8`; `IntN w`; `String`, with `import Text`). The literal is
elaborated at the column's type (numerals through `OfNat`, 7e). The test is a new
`Bool` column in front of the column (`compileLitTest`): rows with `l` want `.true`
(and `_` in the column), rows with another literal `.false` (keeping theirs for the next
test), and catch-all rows `_`. The branches learn nothing about `x`. Literals don't
cover a type, so the column needs a catch-all row: "a match on literals of type U8 needs
a catch-all case (`_` or a variable) after them". In the same column only literals,
`_` and variables are allowed; `n + k` is for `Nat` only; a literal on a data type
without `T.beq` is "a literal pattern needs Nat, or a type T with literals and an
equality test T.beq …". String literals are patterns by the same rule. A literal test
can't be the split of a structural recursion (the first argument is split by its
constructors).

**Hexadecimal and binary numerals.** `0x3F` and `0b1010` are numerals everywhere (the
tokenizer reads them as the decimal `num` token they denote, `Wiz/Parser/Token.lean`),
so they need no change downstream; they print in decimal.

Hover: a pattern variable under a numeral (`k` in `k + 1`) is a pattern variable like
any other; a literal compared with `T.beq` is elaborated where it is written, so its
`OfNat` instance shows in the hover as in a term. Tests: `language` ("13q: …"), `lsp`.

**The self-hosted frontend** (`selfhost/Frontend.wiz`, `selfhost/Lex.wiz`) has all of
13i, 13p and 13q, with the Lean frontend's verdicts and messages:
- `selfhost/Lex.wiz` reads `0x3F` / `0b1010` as the decimal `num` token (`radixNum`); a
  value from 2^63 on is read as 2^63, which the frontend rejects as it does the decimal
  numeral (its numbers are 63-bit words).
- Literal patterns: at `Nat` the numerals were already constructors (`patOf`); now a
  numeral above 256, a string at `Nat`, `p + k` without a numeral `k`, and a literal on
  a data type are the Lean frontend's errors (`litSplitErr`), and a literal in the first
  row of a column of another type is the `T.beq` test (`litTest`, after
  `compileLitTest`): `beqHead` finds `T` through the definitions the type unfolds
  through, the column needs a catch-all row, and the new `Bool` column goes in front.
  Numerals are `Nat` there (no `OfNat`), so in practice the literals are strings.
- Structure update (`structUpdT`): `{ s with … }` is `let upd✝ := s; S.mk …`, a path
  `a.b := v` an inner update of `S.a upd✝` (a sixth argument of the synthesized node
  carries the path, for messages), checked against the type of `s`. A structure is
  marked when declared (`Globals.markStruct`, an entry `structure S` among the
  inductive types), so a one-constructor `inductive` is not one, as in Lean. The
  self-hosted structures have no dependent fields, so the kept-field type check of 13i
  has nothing to check.
- There is no printer to read updates back: the self-hosted frontend prints kernel
  terms (`show`).

Tests: `selfhost` ("the self-hosted frontend: literal patterns …", "… structure update
…"), each program checked by both frontends: the same values (`#eval` in one,
`#reduce Nat.beq` in the other) and the same verdict for each declaration; the lexer
agreement case has hex and binary numerals. The self-hosted sources use none of these,
so the bootstrap is unaffected.

## 13r: string escapes

A string literal reads the escapes `\n`, `\t`, `\r`, `\0`, `\\`, `\"`, `\'`, `\xHH` (two
hexadecimal digits) and `\u{H}` (one to six hexadecimal digits, a Unicode scalar value:
at most `10FFFF` and not a surrogate), in both lexers (`readEscape` in
`Wiz/Parser/Token.lean`, `readEscape` in `selfhost/Lex.wiz`, with the same messages).
A bad escape is reported at its backslash ("2:22: error: unknown escape sequence \q"),
not at the start of the literal, and an unterminated literal at its opening quote. A
token that can't be read is the parse error's message by itself (`ParseError.lexical`),
not "expected unknown escape sequence …". Strings print with Lean's escapes (`\x0d` for
a carriage return). Tests: `language` ("string escapes …"); `selfhost` ("the lexer in
Wiz agrees with the Lean lexer", whose input now has every escape and a bad one).

Sections of this stage without a letter live in `13-language/`:
[`include_str`: a file's text, as a string literal](13-language/include-str.md).

## 13s: `calc` chains

A `calc` block is a chain of relations, each with a proof: adjacent steps compose, and
the chain proves the last step's relation between its first left endpoint and its last
right endpoint. It is a term (`term.calc`, `Wiz/Parser/Builtin.lean`, `elabCalc` in
`Wiz/Elab/Term.lean`):

```wiz no-check
import Nat

def t (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=
  calc a ≤ b := h1
       _ < c := h2
       _ = d := h3
```

* A step is `term := term`, where the first term is a proposition of the form `a R b`
  (a relation applied to two endpoints: `≤`, `<`, `=`, `↔`, `≈`, or a relation a program
  declares). The last two arguments of its application spine are the endpoints.
* `_` is the previous step's right endpoint; an explicit intermediate term must be the
  same (definitionally), or "the middle term does not match". The chain itself is built
  left-associated, `Trans.trans (Trans.trans h₀ h₁) h₂ …`: after each composition the
  composite relation is found, and it is the next composition's first relation.
* The steps' relations must be propositions: a relation between two terms whose result
  is not a `Prop` is rejected. The relation at the last step is the chain's; `≤` then `<`
  then `=` is `<`.
* **Composition.** `class Trans (p q : Prop) (r : outParam Prop)` with
  `trans : p → q → r` lives in `lib/Logic.wiz`. An instance composes two relations;
  `r` is an output parameter, so instance search finds the composite proposition from
  the two adjacent ones. `=` (at a type, and between propositions) and `↔` have
  instances there; `Nat`, `Int` and `Q` register `=`, `≤` and `<` (and `≈` at `Q`) in
  `lib/Nat.wiz`, `lib/IntOrder.wiz` and `lib/Rat.wiz`. A program registers its own
  relation the same way:

  ```wiz no-check
  def Same (a b : Nat) : Prop := (a ≤ b) ∧ (b ≤ a)
  infix:50 " ≈≈ " => Same
  def Same.trans {a b c : Nat} (h1 : a ≈≈ b) (h2 : b ≈≈ c) : a ≈≈ c := …
  instance {a b c : Nat} : Trans (a ≈≈ b) (b ≈≈ c) (a ≈≈ c) :=
    Trans.mk (fun h h' => Same.trans h h')
  ```
* **Errors.** A composition with no instance reports both relations and the meeting
  term ("calc: no `Trans` instance composes … at the middle term …"); a step whose proof
  has the wrong type says so with the step's relation; a step that is not a binary
  relation, or not a proposition, is rejected at the step. All are checked by the
  kernel: a calc term is a `Trans.trans` application, with no axiom and no native
  shortcut (`#print axioms`).
* **The order is a `Bool` at `Nat`.** `Nat.Le m n` is `Nat.le m n = .true` and
  `Nat.Lt m n` is `Nat.Le (succ m) n`; `Nat.le` reduces on constructors, so `a < succ b`
  and `a ≤ b` are the *same proposition* by computation. Then the `Trans` instance for
  `<` then `<` also matches a `<` then `≤` pair, through the shifted relation, and that
  answer is weaker (`a ≤ c` instead of `a < c`). The intended instance for `<` then `≤`
  is declared with `priority := 1001` (`lib/Nat.wiz`), so it is tried first. (At `Int`
  and `Q` the strict and non-strict orders are not definitionally the same, so no
  priority is needed; an overlapping user relation needs its own priority.) This is the
  price of composing propositions rather than relation *functions*: relations that are
  convertible are not told apart by instance search. A `Trans` over relation functions
  (Lean's design) would not need the priority, but `=` is not a function constant in
  Wiz, so the propositional class is the smaller, sounder fit here.
* **Scope.** `BitVec`'s `ult`/`ule` are `Bool`-valued, so they are not relations in this
  sense and have no instances; a `Prop` wrapper would be a new relation with its own
  `Trans` instances. There is no dedicated `calc` tactic: `by exact calc …` works
  (`calc` is a term). The syntax is in the Lean frontend only: `selfhost/Frontend.wiz`
  has its own parser and no type classes or macros (23m), so a self-hosted `calc` would
  need a mirrored `Trans` table there.

Tests: `calc` (the mixed chains at `Nat`, `Int` and `Q`, `↔` and propositional `=`, `_`
and explicit intermediates, a user-registered relation, and the three errors). The
unrelated `calc_e` syntax category in the `language` group is untouched.

The `simp` tactic (stage 6h) is library code written in Wiz, with only one new host
request (`Tac.rewriteAt`): [13-language/simp.md](13-language/simp.md).

## 13u: imports are a fixed header

A file's dependencies are a **syntactic fact**: `import` is not a command, but a
header declaration.

```wiz
-- comments are not commands, so they may sit anywhere in the header
/- … -/
import Prelude
import Logic

def two : Nat := 1 + 1
```

Three rules, checked by both frontends:

1. **Top level only.** An `import` inside a wrapper command (`private`, `sealed`,
   `local`, `partial`, `mutual`) is an error that names the container, at the
   `import`'s position. A term cannot contain an `import` at all (it is a reserved
   keyword, and the parser says so where it was written).
2. **Before every other command.** Once a non-import command has been elaborated, a
   later `import` is the error `imports must precede declarations` (code
   `import-order`), at the `import`'s position; it is not loaded.
   **What the header admits:** only comments (`--`, `/- … -/`, including doc
   comments) and `import`s. Every command ends it, including directives that are not
   declarations: `set_option`, `syntax`/`notation`/`macro_rules`, `#check`/`#eval`.
   The header is therefore *contiguous*, which is what makes the dependency scan a
   scan of the top of the file; and a `set_option` is about printing, so nothing an
   import means depends on one before it. (A doc comment before an import is trivia,
   not documentation of it: imports declare no names.)
3. **No extension can produce one.** `import` was removed from the extensible
   `command` category: it is `Wiz.Parser.Builtin.importDescr`, a descriptor that
   `parseCommand` tries before the category. A `syntax` rule cannot mention the token
   in a `command` quotation — `` `(command| import M) `` is a parse error — and
   `macro_rules` templates that try it do not parse. A command macro can still
   *construct* a node of kind `command.import` by hand (`Syntax.mkNode`); that node
   reaches `Wiz.Elab.Command.elabCommand`, which rejects it with the top-level-import
   error. Two layers: the grammar cannot make one, and the elaborator refuses one
   made anyway.

The self-hosted frontend (`selfhost/Parse.wiz`, `selfhost/Frontend.wiz`) agrees: its
`parseCommandAt` tries the same descriptor (`importDescr`) before the category, its
`runCommands` carries a header flag (an import after a declaration is the same error),
its `mutual`/`partial` handler rejects a nested import, and its module loader's
`modImportsAt` stops at the first command that is not an import instead of scanning the
whole file for import lines (the loader skips imports in the body, so this is where the
two frontends would otherwise drift). `selfhost/Tables.wiz` is regenerated.

**`open import M`.** The shorthand for `import M` plus a file-scope `open M`, for when a
file uses M's names unqualified. It is header-only, like `import`: `open` is not reserved,
but `import` is, so `command.open`'s `ident` cannot match it, and it is parsed with the
header (a later one is the same `import-order` error). Its `open` has no enclosing block,
so it is **file-scoped** and visible in every namespace body in the file. It exposes no
private name of M (privacy is per module). Two `open import`s that provide the same name
are ambiguous at the use (`ambiguous-name`), not at the import. `open import M in …` does
not exist (an import cannot be command-scoped).

**Payoff.** `wiz parse --imports FILE` prints the module names, one per line, in source
order — parse only, no elaboration, no module lookup, and it stops at the first
declaration. (Before the header rule, dependencies were found by scanning every line of
the file, `Module.importsOf`; that line scan remains as the loader's superset, but the
parser's answer is the authority, and `wiz parse --imports` reads only the header.) That
fact is what the module graph needs: `loadClosure`/`moduleKeys` can compute the reachable
set and the cache's input keys from the header, build ordering is the same graph, and the
namespace/aliasing work of stage 13b/13m can treat "imported by another module" as a
syntactic predicate rather than a result of elaboration.

Migration: no `.wiz` file in the tree violates the order (0 files; checked with a
comment-aware scan of every `.wiz`, and the accepted-header tests above). Tests:
`language` (the header, the three rejections) and `selfhost` (the same header and
rejections, through the self-hosted module loader).

## 13t: namespaces and `open`

A namespace groups declarations under a dotted prefix, and `open` makes a prefix's names
available without writing it.

```wiz
namespace Foo
namespace Bar
def x : Unit := ()
end Bar
def y : Unit := Bar.x     -- Foo.Bar.x, through the enclosing namespace
end Foo

#check Foo.Bar.x          -- Foo.Bar.x : Unit
```

* **Grammar.** `namespace Foo` opens a namespace; `end` (or `end Foo`) closes the
  innermost one. They are commands of their own (`command.namespace`, `command.end`:
  `Wiz/Parser/Builtin.lean`), not a `many1` block like `mutual`: a missing `end` is then
  reported at the line of the `namespace` it belongs to, and a stray `end` at its own
  line. `open Foo` and `open Foo as Alias` are commands too (`command.open`). `namespace`
  and `open` are *not reserved*, so both stay usable as names. `end` was already
  reserved (by `mutual`); its command has precedence 0, below the `mutual` body's
  precedence 1, so a `mutual … end` still terminates at its own `end`.
* **Names.** A declaration in `namespace Foo` is `Foo.bar` (nested: `A.B.x`); the
  namespace is a prefix, *not* a privacy boundary. A qualified name works with no `open`.
  Inside `namespace Foo`, an unqualified `x` first names `Foo.x`; a qualified `B.x` names
  `Foo.B.x` if `B.x` names nothing. A type's own name in its fields is rewritten with the
  prefix (`inductive T where | mk : Unit → T` inside `namespace N` is `N.T`), and a
  `mutual` block's members refer to each other unqualified.
* **Scope: block-scoped, from the `open` on.** `open Foo` makes `Foo`'s names visible
  unqualified in the **enclosing block**: inside a `namespace` body, until its `end`;
  at file top, where there is no enclosing block, to the end of the file. The enclosing
  block's opens come back at `end` (`CommandState.nsStack` saves them), so a sibling
  namespace body needs its own `open`. An `import` does not see its importer's opens,
  and a module's opens are dropped when it ends (`CommandState.endModule`). An `open`
  names a namespace that already has declarations: elaboration is single-pass, so `open`
  normally follows the namespace it opens (and a qualified name needs no `open` at all).
  `open` makes *names* visible, not notation: `notation` is not scoped by a namespace
  (13m has `local` for module-scoped grammar).
* **`open` is not transitive.** `open Foo` brings in exactly the declarations named
  `Foo.…`: a name `Foo` itself opened from `Bar` is `Bar.x`, so it needs its own
  `open Bar`; and a module's opens are dropped when the module ends, so an importer never
  inherits them. The command takes a *namespace*, not a module: a file's declarations are
  global names as written in it, so `open Math` finds nothing unless `Math.wiz` wraps
  them in `namespace Math`.
* **Local names shadow; declarations do not.** A binder, `let`, or pattern variable
  named `x` shadows an opened `A.x` (locals are looked up first and no ambiguity is
  reported). A *declaration* does not shadow: the enclosing namespace's `x`, the module's
  own `x` and an opened `A.x` are all candidates, and two distinct ones are the ambiguity
  error below.
* **Ambiguity is an error, not last-wins.** An unqualified name that two `open`s provide
  (or an `open` and a declaration), with two *different* declared names, is rejected at
  the use, naming both candidates (`ambiguous-name`):

  ```text
  'x' is ambiguous: it refers to 'A.x', 'B.x'; qualify it with a namespace
  ```

  The same declaration found twice (this namespace and an `open` of it) is one candidate.
  Candidate order is: the enclosing namespace's `x`, the module's own `x`, then each
  `open`'s `x`; only distinct resulting declarations conflict, so a bare name that
  resolved before still resolves when no new open competes with it.
* **`open M as Alias` is a prefix alias, not an open.** It makes `Alias.x` a spelling of
  `M.x` and opens *nothing* unqualified: after `open A as Al`, `x` is not `A.x`. The
  distinction is deliberate — an alias is for a long or clashing prefix, an `open` for
  unqualified use. A qualified name uses the longest matching alias, and the alias is
  applied before the name is looked up: after `open B as A`, `A.x` is `B.x` even if a
  namespace `A` exists (the real `A.…` names stay reachable unqualified through
  `open A`).
* **`private` stays module-private.** A private declaration is reachable neither through
  an `open` (an unqualified `x` skips another module's private `M.x`, so the use is
  unknown) nor through an alias (`Al.x` resolves to `M.x`, and the private check reports
  `'M.x' is private to module M`). In its own module it works as before — an `open` there
  does bring the namespace's private names in, since they are usable in that module — and
  a qualified name needs no `open`.
* **Errors.** A namespace with no `end` is reported at the `namespace` line
  (`namespace Foo is not closed: add end (or end Foo)`); `end` with no open namespace,
  and `end Bar` that does not name the innermost namespace, are errors at the `end`.
  `open Foo` when nothing is declared as `Foo.…` is an error at the `open`
  (``unknown namespace 'Foo': there is no declaration `Foo.…` ``), because elaboration
  is single-pass: the namespace must already have a declaration when the `open` is read.
* **Self-hosting.** `selfhost/Frontend.wiz` keeps the same state in its `Globals`
  (the prefix, the opens and aliases, and the open namespaces with the offset of each
  `namespace`), prefixes declaration names where a command is elaborated, and resolves
  terms and pattern constructors through `resolveNameV` with the host's order and
  ambiguity error. The parser table was regenerated with the grammar; the self-hosted
  frontend compiles the namespace cases in the `selfhost` group.

### 13t.2 Stage 3: the module path is the default namespace

The rule is one line — `CommandState.atModuleStart` sets `namespacePrefix` to
`Module.nameOf` the module's path (`lib/Scry/CstStore.wiz` is `Scry.CstStore`), and a
written `__root__.` resets it — but it renames every existing module declaration, so it is
**guarded**: `CommandState.modulePrefix` is `false` by default, and a run turns it on
together with `CommandState.legacy`, the stage-0 allowlist (`legacy-names.tsv`, one row
per declaration that keeps its current absolute name until its migration batch deletes
the row). With the two set, the default tree is unchanged; a declaration with no row gets
its module's path. The allowlist lookup is per `(module, written name)` in
`prefixDeclName`, so `__root__.x` still escapes.

Tests: `namespace` runs `runFrontend` with `modulePrefix := true` (and with and without a
`legacy` row): module `M`'s `def f` is `M.f`, and a row keeps it `f`.

### 13t.1 `__root__`: the escape to the global scope

`__root__` is Lean's `_root_`: a **leading name segment**, not a variable and not a
namespace you can declare. It resets the prefix to the empty one, so a file that must keep
global names (the Prelude, the self-hosted tree) needs one line at the top and one `end`
at the bottom instead of a marker on every declaration:

```wiz
namespace __root__
def f : Nat := 0                -- f, not Scry.CstStore.f
def A.x : Nat := 0              -- A.x, root-level
end __root__

def __root__.y : Nat := 0       -- y, even inside a namespace
namespace __root__.Shared       -- the root-level Shared
def g : Nat := __root__.y       -- names the global y
end Shared
```

`namespace __root__` (nothing after the dot) opens the root for a block; `end` or
`end __root__` closes it. `__root__.` is only meaningful as the first segment: a
declaration named exactly `__root__`, or one with `__root__` in the middle
(`A.__root__.x`), is the error `root-name`, and `__root__` alone is not a term. `open
__root__.X` opens the root-level `X` (`open __root__` is a no-op: the root is always
searched). The self-hosted frontend mirrors the leading-segment rule for `namespace`,
`end`, `open` and unqualified reads.

Tests: `namespace` (a root block; a dotted root namespace; `def __root__.x`; the two
root-name errors), and `selfhost`'s `(13v)` case.

Tests: `namespace` (nested namespaces; qualified use with no `open`; `open` then
unqualified use; the exact ambiguity error; `open … as` for qualification; `open … as`
not opening unqualified; an alias shadowing a real prefix; a local binder shadowing an
opened name; a private name through an open and through an alias; an `open` across two
modules and its non-transitivity; **an `open` that ends at its namespace's `end`**, and a
file-top `open` that reaches the end of the file; missing and stray `end`; `#check`
showing the qualified name; `mutual` under a namespace), plus two `wiz check` cases (an
`open` across two modules, and the ambiguity as a command-line error), and the `selfhost`
group's `(13t)` cases (the same resolution in the self-hosted frontend, including a
constructor of the matched type and the `end` diagnostics).
## 13v: namespaces: the compatibility baseline

The namespace model (design: `wiz-notes/namespace-plan.md`) makes a module's path its
default prefix: `lib/Scry/CstStore.wiz` is module `Scry.CstStore`, so `def lineIndexGo`
becomes `Scry.CstStore.lineIndexGo`. Stage 0 lands the compatibility baseline, with no
parser or elaborator change: every declaration that exists today keeps its current
absolute name until a migration batch deletes its row. This section describes only the
baseline; the parser, resolver and self-hosted changes are stages 1–4 of the plan.

* `legacy-names.tsv` is generated by `scripts/gen-legacy-names.py` from the six
  library/tool roots (`lib/`, `scry/src/`, `scry/gen/`, `tower/`, `web/`, `selfhost/`).
  It has one tab-separated row per declaration: module, today's absolute name, reason
  class (`module-prefixed`, `first-prefixed`, `leaf-prefixed`, `other-dotted`,
  `principal`, `bare`), source file, line. Rows are sorted by `(module, name)` and the
  file is deterministic. Before batch 1 (the train8 tree) it is **14,083 rows in 211
  files** (11,131 / 198 without `selfhost`); after batch 1 it is **10,880 rows in 198
  files**. `__root__.` declarations are not rows: they already have the true-global name
  they keep.
* `scripts/check-names.py` reports a declaration whose current name is not under its
  module prefix — the set the migration will rename. Normal mode reports and exits 0; a
  `__root__.` declaration is exempt, and a row suppresses the report. `--quiet` is the
  CI gate: it fails on a declaration with no row (a new name must regenerate the
  baseline) and on a stale row, and passes on today's tree. `--strict-names` makes
  every prefix violation an error: **12,910 declarations** before batch 1 (9,436 dotted,
  3,474 bare) and **9,707** after it (9,068 dotted, 639 bare), which is the size of the
  rename work, not a gate that is green before stage 6. A malformed row is exit 2.
* A `namespace __root__` body is explicitly global, like a `__root__.` name: the tools
  take its declarations out of the allowlist (no row), the collision checker reports
  them under the name they are written as rather than as migration names, and
  `end __root__` closes the block. It is the bulk form of the escape, for a file whose
  declarations must stay root (batch 1 below).
* The allowlist is an input of what a module elaborates to, so its SHA-256 is part of the
  cache key. The digest covers the `(module, name, reason)` rows, not the review-only
  file and line, so moving a declaration's line does not invalidate the cache.
  `Wiz/LegacyNames.lean` holds the digest; `Cache.moduleKeysAll` mixes it into the fast
  and strong module keys, and `Frontend.isoKey` into the in-process isolation key.
  `check-names.py` fails when the constant and the file disagree, so a stale cache
  cannot hide a name change. `gen-legacy-names.py --update-digest` refreshes it.
* **Batch 1 (landed)** — `namespace __root__` around `lib/Prelude.wiz` and the twelve
  `selfhost/*.wiz` files (3,203 declarations, 13 files on this tree; zero renames, zero
  ledger re-keyings). It deleted their rows: the allowlist is 14,083 → 10,880, the
  `--strict-names` count 12,910 → 9,707, and the collision checker's migration count
  10,367 → 10,000 (87 baselined, 0 unbaselined). Batch 2 (strip the 1,173
  module-prefixed declarations) is the next mechanical batch.

CI: add these two lines to the `docs_style` job's run step in
`.github/workflows/ci.yml` (after the `check-name-collisions.py` lines):

```sh
python3 scripts/check-names.py --self-test
python3 scripts/check-names.py --quiet
```
## 13w: application operators, sections, and `#eval` through `Repr`

```wiz
import Prelude
import Text
import Deriving
import Compose

#eval Nat.succ <| 4                       -- 5: `f <| x` is `f x` (infixr 10)
#eval [1, 2, 3] |> List.length            -- 3: `x |> f` is `f x` (infixl 10)

structure In where
  x : Nat
  y : Nat
structure Out where
  i : In
  n : Nat
def o : Out := Out.mk (In.mk 1 2) 3
#eval o |>.n                              -- 3: the projection `o.n`
#eval o |>.i.x                            -- 1: the same as `o.i.x`

#eval List.length (List.map (· + 1) [1, 2, 3])   -- 3: `(· + 1)` is `fun x => x + 1`
def mul : Nat → Nat → Nat := (· * ·)             -- two holes, two parameters
#eval mul 3 4                                    -- 12

#eval (Nat.succ ∘ Nat.succ) 0                    -- 2: lib/Compose.wiz
```

**`<|` and `|>`.** `|>` was already the Prelude's `pipe` (13); `<|` is its
mirror, `apply` (`f <| x` is `f x`), at `infixr:10` against `infixl:10`, as in
Lean. Both are at any universe, so proofs compose too (`h |> Eq.symm`), and both
print back as written (the infix unexpander is the `infixl`/`infixr` declaration).

**`x |>.f`.** A projection through the pipe: `term.pipeProj` is a *trailing* rule,
`term:11 "|>." ident` (a Prelude `syntax`, not built-in grammar, so the self-hosted
parser's generated tables are unchanged), and its macro expands to the `term.field`
node. It is therefore the **same** elaboration as `x.f`: `elabFields`, the same field
lookup, the same private checks and the same errors, and a dotted path works
(`x |>.a.b` is `x.a.b`). The surface form is `x |>.f` with no space: the dot is part
of the `|>.` token, as it is in `x.f`. `x |> .f` is not the projection: there the
existing `|>` operator sees `.f`, the constructor-dot form, and the space would make
the two readings differ. The left side is at precedence 11 (so `x + y |>.f` is
`(x + y).f`) and the result binds at `max`, like a field access; as with `x.f`, an
application on the left is an argument, so write `(f x) |>.f`. Printed back it is the
projection (`o.2.1` for this structure), which is the same text `o.f` prints.

**`(· + 1)`.** `·` is `term.sectionHole` (`syntax (name := sectionHole) "·" : term`).
A parenthesised term whose holes are not inside a nested parenthesis is a section:
the elaborator replaces each hole by a fresh variable (`section0✝…`, unspellable)
and checks the body as a lambda, one Π at a time, against the expected type. That
is what makes `List.map (· + 1) xs` work: the argument's expected `A → B` gives the
hole its type. `(1 + ·)` is the same, and `(· * ·)` has one parameter per hole.
Limits: the section must be parenthesised (the parentheses delimit it, as in Lean),
its expected type must be a function type (`#check (· + 1)` says so), and a hole
inside a nested `( … )` belongs to that inner section. It is check-mode syntax: a
section with no function type in view is an error rather than a guessed lambda.

**`Repr` and `#eval`.** `lib/Deriving.wiz` already had `class Repr (A) where
reprPrec : A → Nat → String` and `Repr.repr a = Repr.reprPrec a 0`; `#eval` now
uses it. When the elaborated value's type has a `Repr` instance (the wrapper
`Repr.repr e` elaborates), `#eval` runs that and prints its string; otherwise it
keeps the old term readback. So `#eval [1, 2, 3]` with `import Deriving` prints
`[1, 2, 3]` (a hand-written `Repr (List A)` replaced the derived `List.cons …`
one), while a type without an instance still prints its constructors. `#check`
and `#print` are unchanged. `Bool` is the one exception: inductive types are anonymous
`μ`s and `Enum` tags are metadata, so `Repr Bool` and the `Repr` of any other
two-constructor enum are instances of the *same* class at definitionally equal types,
and the later one wins (7b); `#eval` therefore keeps `Bool`'s constructor readback
(`.true`, `.false`), which is the stable spelling a program sees. The `Repr String`
instance now escapes as the lexer reads (`"a\nb"`, `\x0d` for a carriage return), which
is what makes printing the `Repr` result directly equal to the old readback of a
string.

**`∘`.** `lib/Compose.wiz` declares `class Compose (α β γ : Type) where compose :
(β → γ) → (α → β) → (α → γ)` and registers `infixr:90 " ∘ "`. The instance for
functions is `Compose.mk (fun g f x => g (f x))`; a type can declare its own, and
a later instance wins (stage 7b), so the operator is not hard-coded to functions.
`Compose.assoc`, `Compose.id_left` and `Compose.id_right` (with `id`) hold at
functions definitionally; `rfl` proves them and `#print axioms` lists none.

Tests: group `language` (`<|`/`|>`, `|>.`, the section forms), `deriving`
(`#eval` with and without an instance, list/string `Repr`), `std` (`Compose` and
its laws, a custom instance). Stage 13's earlier letters are 13a–13s.
