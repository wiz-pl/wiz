# A tour of Wiz

This tour is for readers who know a little functional programming (a bit of Haskell,
OCaml, Lean or Agda) and want to see what Wiz looks like. Each section has a small
program in [`examples/tour/`](../examples/tour/). The test group `tour`
(`lake test -- tour`) checks every one of them against the output shown here, so the
examples on this page run as written. The programs the tour shows being *rejected* are
collected in [`examples/tour/11-mistakes.wiz`](../examples/tour/11-mistakes.wiz), and
the same group checks that they fail with the errors shown. To follow along, [install a
toolchain](install.md) and run `wiz check FILE` on a file: it prints the result of every
`#eval` and `#check` as a message.

This is a tour, not a reference. The language is specified by the kernel's rules in
[CoreSpec.md](CoreSpec.md) and by the stage docs ([index.md](index.md)), which explain
how each feature is built; the tour links to them as it goes.

Contents: [0 A program](#0-a-program) · [1 Values and functions](#1-values-and-functions)
· [2 Inductive types](#2-inductive-types-and-pattern-matching) ·
[3 Structures](#3-structures) · [4 Type classes and numerals](#4-type-classes-and-numerals) ·
[5 Dependent types](#5-dependent-types) · [6 Propositions and proofs](#6-propositions-and-proofs) ·
[7 Quantities](#7-quantities-and-linear-resources) · [8 Codata](#8-codata) ·
[9 The C FFI](#9-the-c-ffi) · [10 Hardware](#10-hardware) ·
[11 Packages](#11-packages) · [12 Taint analysis with scry](#12-taint-analysis-with-scry) ·
[Where next](#where-next)

## 0: a program

```wiz run
import IO

def greet (name : String) : String := "hello, " ++ name

def main : IO Unit := do
  IO.println (greet "Wiz");
  IO.println (Nat.toString (6 * 7))
```

```
$ wiz run examples/tour/00-hello.wiz
hello, Wiz
42
```

A file is a list of commands. `import IO` brings in the module `lib/IO.wiz` and,
through it, the Prelude. `def name : type := value` defines a name. `main` is an `IO`
action, and `do` sequences its steps, separated by `;`. `wiz run` compiles the file to
native code through C and runs it; `wiz build FILE -o OUT` keeps the executable.
(`examples/tour/00-hello.wiz`.)

## 1: values and functions

```wiz
import Prelude

def answer : Nat := 42
#eval answer                                   -- 42

def double (n : Nat) : Nat := n + n
#eval double 21                                -- 42

-- a function is a value; `fun` makes one
def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
#eval twice (fun n => n * 3) 2                 -- 18

-- implicit arguments, in braces, are found by unification
def compose {A B C : Type} (g : B → C) (f : A → B) : A → C := fun x => g (f x)
#eval compose double double 5                  -- 20
```

Functions are curried, and application is juxtaposition: `twice f x`. Arguments in
parentheses are explicit. Arguments in braces are **implicit**: you don't write them,
and the elaborator works them out from the others (here `A`, `B` and `C` from the types
of `g` and `f`). `#eval e` evaluates `e` and prints its value; `#check e` prints its
type, and `#check @compose` shows the implicit arguments too:

```
compose : {A : Type} → {B : Type} → {C : Type} → (B → C) → (A → B) → A → C
```

Types are values like any other, of type `Type`, which is why `A` can be an argument.
The Prelude has the usual types: `Nat` (arbitrary precision), `Bool`, `String`,
`List`, `Option`, pairs `A × B`. It also has `let`, `if … then … else`, `++` and list
literals:

```wiz
def describe (n : Nat) : String :=
  let big := Nat.lt 100 n;
  if big then "big" else "small"
#eval describe 7                               -- "small"
#eval "wiz" ++ "ard"                           -- "wizard"
#eval [1, 2, 3] ++ [4]                         -- .cons 1 (.cons 2 (.cons 3 (.cons 4 .nil)))
```

Values are printed as terms: a list is its constructors. Comparisons on `Nat` are
functions that return a `Bool` (`Nat.lt`, `Nat.le`, `Nat.beq`); there are no `<` or
`==` operators yet. (`examples/tour/01-basics.wiz`.)

## 2: inductive types and pattern matching

```wiz
inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)

-- `.circle` is `Shape.circle`: the type is known from the expected type
def area : Shape → Nat
  | .circle r => 3 * r * r
  | .rect w h => w * h
#eval area (.rect 3 4)                         -- 12
```

An `inductive` type lists its constructors, which live in its namespace:
`Shape.circle`, `Shape.rect`. Where the expected type is known you can write just
`.circle`. A function can be defined by cases directly, as `area` is, or with
`match e with | … => …`. Types take parameters, and recursion is fine as long as it is
on a smaller piece of the argument (it is *structural*, so the checker knows it stops):

```wiz
inductive Tree (A : Type) where
  | leaf
  | node (l : Tree A) (x : A) (r : Tree A)

def Tree.toList {A : Type} : Tree A → List A
  | .leaf => []
  | .node l x r => Tree.toList l ++ [x] ++ Tree.toList r

def t : Tree Nat := .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)
#eval Tree.toList t                            -- .cons 1 (.cons 2 (.cons 3 .nil))
```

Matching works on several values at once, with `_` for "anything", and patterns nest:

```wiz
def zipWith {A B C : Type} (f : A → B → C) : List A → List B → List C
  | .cons a as, .cons b bs => .cons (f a b) (zipWith f as bs)
  | _, _ => .nil
```

A match must cover every case: leave one out and `wiz check` says which ("missing case
for constructor …"). Under the hood an inductive type is a *description*, a value that
says what its constructors look like, and its least fixed point. That is how the
kernel can stay small; [stages/04-data.md](stages/04-data.md) tells the story.
(`examples/tour/02-data.wiz`.)

## 3: structures

```wiz
import Deriving

structure Point where
  x : Nat
  y : Nat
  deriving Repr

def origin : Point := ⟨0, 0⟩                -- `Point.mk 0 0`, from the expected type
def p : Point := Point.mk (y := 4) (x := 3)  -- named arguments, in any order
#eval p.x + p.y                              -- 7

-- update a copy, and take a structure apart with a pattern
def shiftRight (q : Point) : Point := { q with x := q.x + 1 }
#eval Repr.repr (shiftRight p)               -- "Point.mk 4 4"

def manhattan (q : Point) : Nat :=
  let ⟨a, b⟩ := q
  a + b
```

A structure is a record: one constructor (`Point.mk`) and a projection per field
(`p.x`). The anonymous constructor `⟨…⟩` builds one when the type is known, and also
works as a pattern. `{ q with x := … }` is a copy with some fields replaced.
`deriving Repr` writes the instance that turns a point into text (type classes are
next). Wiz has no record literal of the form `{ x := 3, y := 4 }`; use the constructor,
with named arguments if you like.

A field's type may mention earlier fields. Here the second field is a *proof* about the
first (proofs are section 6):

```wiz
structure Positive where
  n : Nat
  pos : Nat.lt 0 n = .true
def five : Positive := ⟨5, rfl⟩
```

In the kernel a structure is a Σ type, a dependent pair, so `⟨5, rfl⟩` is a pair whose
second component's type depends on the first. (`examples/tour/03-structures.wiz`;
[stages/13-language.md](stages/13-language.md), 13a, 13h, 13i.)

## 4: type classes and numerals

```wiz
import Text

class Describe (A : Type) where
  describe : A → String

instance : Describe Bool where
  describe := fun b => if b then "yes" else "no"
instance : Describe Nat where
  describe := fun n => Nat.repr n
-- an instance that needs another instance
instance {A : Type} [Describe A] : Describe (List A) where
  describe := fun xs => match xs with
    | .nil => "nothing"
    | .cons x _ => "starts with " ++ Describe.describe x

#eval Describe.describe [Bool.true, Bool.false]   -- "starts with yes"

def shout {A : Type} [Describe A] (a : A) : String := Describe.describe a ++ "!"
#eval shout (7 : Nat)                              -- "7!"
```

A class is a structure of operations, and an instance is a value of it. An argument in
square brackets, `[Describe A]`, is an instance argument: the caller doesn't pass it, the
elaborator finds it by **instance resolution**, which also chains instances (the one
for `List A` uses the one for `A`). `(7 : Nat)` is a type ascription.

Arithmetic is built the same way. `a + b` is `Add.add a b`, and a numeral `5` at a type
other than `Nat` is `OfNat.ofNat 5`, so the same syntax works at every numeric type
that has instances:

```wiz
import Int
import Word

#eval (2 : Int) - 5                        -- -3
#eval (-3 : Int) * 4 + 2                   -- -10
#eval UIntN.toNat ((250 : U8) + 10)        -- 4: words wrap around
def sum {A : Type} [Add A] [OfNat A 0] : List A → A
  | .nil => 0
  | .cons x xs => x + sum xs
#eval sum [1, 2, 3]                        -- 6
#eval sum [(1 : Int), -2, -3]              -- -4
```

`Nat` subtraction stops at zero (`2 - 3 = 0`); `Int`, the machine words `U8` … `U64`
and `I8` … `I64` (`lib/Word.wiz`) and bit vectors (`lib/BitVec.wiz`) are in the library.
At `Nat` a numeral is a native number and `+` runs as native arithmetic, both in the
checker and in compiled code. (`examples/tour/04-classes.wiz`;
[stages/07-type-classes.md](stages/07-type-classes.md); the table of numeric types in
[libraries.md](libraries.md).)

## 5: dependent types

A type can depend on a value. The classic example is the vector, a list whose type says
how long it is:

```wiz
inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A .zero
  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)

-- `head` only takes vectors of length `n + 1` (`.succ n`): there is no `nil` case to write
def Vec.head {A : Type} {0 n : Nat} : Vec A (.succ n) → A
  | .cons x _ => x

-- the types say that `map` keeps the length and `zip` needs two equal ones
def Vec.zip {A B : Type} {0 n : Nat} : Vec A n → Vec B n → Vec (A × B) n
  | .nil, .nil => .nil
  | .cons a as, .cons b bs => .cons (a, b) (Vec.zip as bs)

def v : Vec Nat 3 := .cons 1 (.cons 2 (.cons 3 .nil))
#eval Vec.head v                           -- 1
```

`Vec A` is a *family* of types, one for each length. The part after the colon,
`: Nat → Type`, is the index, and each constructor says which member of the family it
builds. `Vec.head` needs no case for `nil`, because a `Vec A (.succ n)` cannot be
`nil`: the checker knows, and `Vec.head (Vec.nil : Vec Nat 0)` is a type error:

```
error: type mismatch
  expected: Vec ?m0 (.succ ?m1)
  inferred: Vec Nat 0
  (tag mismatch)
```

(`?m0` and `?m1` are the implicit arguments the elaborator was solving for.) In
`Vec.zip` there are no mismatched cases either, because both vectors have length `n`.
In `def v : Vec Nat 3` the numeral `3` and the length `.succ (.succ (.succ .zero))` that
the three `cons` build are the same number, so the definition checks.

The `0` in `{0 n : Nat}` is a **quantity**: the length is only used in types, so it is
erased, and at run time a vector is just a list (section 7). Types can also be computed
by ordinary functions:

```wiz
def NTuple : Nat → Type
  | .zero => Unit
  | .succ n => Nat × NTuple n
def triple : NTuple 3 := (1, 2, 3, ())
```

`lib/Vec.wiz` has a complete `Vec` with lemmas about it.
(`examples/tour/05-vec.wiz`.)

## 6: propositions and proofs

Propositions are types, and a proof is a value of that type. `a = b` is the proposition
that `a` and `b` are equal, and `rfl` proves it when both sides compute to the same
value:

```wiz
import Logic

def two_plus_two : 2 + 2 = 4 := rfl

def double (n : Nat) : Nat := n + n
def double_three : double 3 = 6 := rfl
```

A statement about every `n` is a function from `n` to a proof, and a proof by induction
is a recursive function. `zero_add` below recurses on `n`, and the case for `.succ n`
uses the proof for `n`:

```wiz
def congrSucc {a b : Nat} (e : a = b) : Nat.succ a = Nat.succ b :=
  transp (fun b _ => Nat.succ a = Nat.succ b) (refl (Nat.succ a)) e

def zero_add : (n : Nat) → 0 + n = n
  | .zero => rfl
  | .succ n => congrSucc (zero_add n)
```

`transp` is the eliminator of equality: from `a = b` and something that holds at `a`,
it gives the same thing at `b`. `congrSucc` uses it to show that equal numbers have
equal successors. `#print axioms zero_add` says the proof `does not depend on any
axioms`.

Chains of relations have their own notation, **`calc`**. Adjacent steps compose through
an instance of `Trans`, and the last step's relation is the result:

```
def lt_of_chain (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c ≤ d) : a < d :=
  calc a ≤ b := h1
       _ < c := h2
       _ ≤ d := h3
```

`_` is the previous step's right endpoint (an explicit middle term must be the same).
`Trans` instances for `=` and `↔` are in `lib/Logic.wiz`; `Nat`, `Int` and `Q` register
`=`, `≤` and `<` (and `≈` at `Q`) in `lib/Nat.wiz`, `lib/IntOrder.wiz` and
`lib/Rat.wiz`, and a program adds its own relation by declaring a `Trans` instance for
it. A chain elaborates to nested `Trans.trans` applications, so it is checked like any
other proof and names no axioms; a step whose proof has the wrong relation, or a pair of
relations that no instance composes, is reported at that step.
(`examples/tour/06b-calc.wiz`; [stages/13-language.md](stages/13-language.md), 13s.)

Proofs can also be written with **tactics**, after `by`. `intro`, `exact`, `apply`,
`assumption`, `rfl`, `rw` and `unfold` are in the Prelude, and since a tactic is a Wiz
function, you can write your own (`examples/tactics.wiz`):

```wiz
def double (n : Nat) : Nat := n + n

def same_double (m n : Nat) (h : m = n) : double m = double n := by
  rw h
  rfl
```

`rw h` rewrites `m` to `n` in the goal, which leaves `double n = double n`, and `rfl`
closes it. In an editor with the infoview (see [install.md](install.md#editors)), the
cursor on the `rfl` line shows the goal at that point:

```
m : Nat
n : Nat
h : m = n
⊢ double n = double n
```

(The tactic `trace_state` prints the same as a message.)

`lib/Logic.wiz` defines the connectives with Lean's names: `∧` (`And.intro`,
`h.1`, `h.2`), `∨` (`Or.inl`, `Or.inr`, `Or.elim`), `¬`, `↔` and `∃`:

```wiz
import Logic

def double (n : Nat) : Nat := n + n

def and_swap {P Q : Prop} (h : P ∧ Q) : Q ∧ P := And.intro h.2 h.1
def exists_double : ∃ n, double n = 8 := Ex.intro (fun n => double n = 8) 4 rfl
```

Equality in Wiz is **observational**: `a = b` is not an inductive type but computes
from the type of `a` and `b`. At a function type it is pointwise equality, so function
extensionality is a definition, not an axiom:

```wiz
def funext' {A B : Type} (f g : A → B) (h : (x : A) → f x = g x) : f = g := h
```

`Prop` is impredicative and proof-irrelevant: any two proofs of a proposition are
equal, and proofs (like everything at quantity 0) are erased from compiled code.
(`examples/tour/06-proofs.wiz`; [stages/04-data.md](stages/04-data.md), 4c;
[stages/24-separation-logic.md](stages/24-separation-logic.md) for the logic library
and program verification with Hoare triples; [Status.md](Status.md) for what is known
about soundness, and what isn't.)

## 7: quantities and linear resources

Every binder in Wiz carries a **quantity**, which says how often the body may use the
variable at run time:

| quantity | means | for |
|---|---|---|
| `0` | never: erased | types, proofs, indices like `Vec`'s length |
| `1` | exactly once: linear | resources: a file handle, a channel end, the world |
| `ω` | any number of times | everything else; the default for explicit **and implicit** binders |

An implicit binder is inferred and may be used freely, so `fun {n} => n` uses `n` as
data without writing `{ω n}`. An explicit quantity is still authoritative: write
`{0 A : Type}` for an erased type argument inside braces, or `{1 x}` to make an
implicit linear.

```wiz
def id {0 A : Type} (1 x : A) : A := x
def dup {0 A : Type} (x : A) : A × A := (x, x)
```

`id` uses `x` once and `A` never (only in types), so both quantities are right.
`dup` uses `x` twice, which is fine at the default `ω`. Written `(1 x : A)`, the checker
would say `variable x declared with quantity 1 but used ω`. Quantities are checked by
the kernel itself, and erasure follows them: an argument at `0` costs nothing at run
time.

Quantity `1` gives you **linear** types: a value that must be used exactly once, never
copied and never dropped. That is the right type for a resource:

```wiz
import IO

axiom Ticket : Type
axiom Ticket.buy : Nat → IO Ticket
axiom Ticket.ride : (1 t : Ticket) → IO Unit

-- `do1` sequences actions whose later steps use linear values: `t` is used once
def trip (1 t : Ticket) : IO Unit := do1
  IO.println "boarding";
  Ticket.ride t
```

(`axiom` declares a type or a function without defining it; a real library would
implement them with `extern`, section 9.) Try to cheat and the checker stops you:

```wiz no-check
def twice (1 t : Ticket) : IO Unit := do1
  Ticket.ride t;
  Ticket.ride t
-- error: kernel rejected twice: variable t declared with quantity 1 but used ω
def lose (1 t : Ticket) : IO Unit := IO.pure ()
-- error: kernel rejected lose: variable t declared with quantity 1 but used 0
```

`do1` is `do` over `IO.bind`'s linear form (its continuation is used once, so it may
capture `t`). The plain `do` uses an unrestricted continuation, so `trip` written with
`do` is rejected too.

Pairs can have linear components. A pair held linearly is taken apart with `let 1`,
which binds both components at once. A projection `p.1` would quietly drop the other
component, so the checker refuses it on a linear pair:

```wiz no-check
def swap {0 A : Type} (1 p : A × Ticket) : (1 t : Ticket) × A :=
  let 1 (a, t) := p;
  (t, a)
```

`IO` itself is built this way: `IO A` is `(1 w : World) → A × World`, a function that
takes the world exactly once and hands back the next one, so effects happen in order and
can be neither duplicated nor skipped. `#check @IO.bind` shows the linear binders:

```
IO.bind : {A : Type} → {B : Type} → (1 x : IO A) → (1 f : A → IO B) → IO B
```

Linear matching on your own data types is not there yet (a `match` uses its scrutinee
at `ω`), so linear data is written with pairs, as above, for now.
(`examples/tour/07-quantities.wiz`; [stages/09-ffi.md](stages/09-ffi.md), 9a and 9e;
[stages/25-concurrency.md](stages/25-concurrency.md) for linear channels and session
types.)

## 8: codata

An inductive type is defined by how you build its values, and a **coinductive** type by
what you can observe of them. A stream has a head and a tail, forever:

```wiz
coinductive Stream (A : Type) where
  head : A
  tail : Stream A

def Stream.from (n : Nat) : Stream Nat
  | .head => n
  | .tail => Stream.from (n + 1)

def Stream.map {A B : Type} (f : A → B) (s : Stream A) : Stream B
  | .head => f s.head
  | .tail => Stream.map f s.tail

def Stream.take {A : Type} : Nat → Stream A → List A
  | .zero, _ => .nil
  | .succ n, s => .cons s.head (Stream.take n s.tail)

def squares : Stream Nat := Stream.map (fun n => n * n) (Stream.from 0)
#eval Stream.take 6 squares                -- .cons 0 (.cons 1 (.cons 4 (.cons 9 (.cons 16 (.cons 25 .nil)))))
#eval squares.tail.tail.tail.head          -- 9
```

The definitions use **copatterns**: instead of matching on an argument, they say what
each observation (`.head`, `.tail`) of the result is. An infinite stream is fine as long
as every observation answers in finitely many steps (it is *productive*). The checker
makes sure each `.tail` is a call of the function being defined, *guarded* by the
observation. A definition that would spin forever is rejected:

```wiz no-check
def stuck (n : Nat) : Stream Nat
  | .head => n
  | .tail => (stuck n).tail
-- error: the observation .tail must be a corecursive call of stuck (guardedness)
```

(`examples/tour/08-codata.wiz`; `examples/streams.wiz`, `examples/sized.wiz` for sized
types, [stages/04-data.md](stages/04-data.md).)

## 9: the C FFI

```wiz run
-- test: run
import IO

-- one C function, with its type in Wiz (`String` is a `char*`, `Nat` a `uint64_t`)
extern "strlen" (header := "string.h") strlen : String → Nat

-- C written inline, in a checked subset of C
glue sumBelow (n : Nat) : Nat := "uint64_t s = 0; for (uint64_t i = 0; i < n; i++) s += i; return s;"

def main : IO Unit := do
  IO.println (Nat.toString (strlen "hello, C"));
  IO.println (Nat.toString (sumBelow 10))
```

```
$ wiz run examples/tour/09-ffi.wiz
8
45
```

`extern "cname" name : T` declares a function implemented in C; the arguments are
converted by their Wiz types. A foreign function that has effects should return `IO`.
`glue` writes the C body inline, in a subset that the compiler checks. `import_c "h"`
binds every function of a C header at once (`C.strlen`, …), `link_c "file.c"` and
`link_lib "m"` link your own C, and `foreign_type` wraps a C pointer with a finalizer.
Foreign functions run only in compiled code: `#eval` can't call them, so this example
is a program, and its test (the first line, `-- test: run`) runs it.
(`examples/tour/09-ffi.wiz`; `examples/foreign.wiz`, `examples/import_c.wiz`,
`examples/glue.wiz`; [stages/09-ffi.md](stages/09-ffi.md).)

## 10: hardware

`lib/Hdl/Core.wiz` is a hardware description library: circuits are Wiz values,
simulated by evaluation and turned into Verilog.

```wiz
import Hdl.Core

def B4 : HwTy := HwTy.bits 4

-- Combinational logic is a function over any representation `r` of signals: run it on
-- values to simulate it, or on wires to get a netlist.
def addThree {r : HwTy → Type} [Hw r] (x : r B4) : r B4 := Hw.add x (Hw.lit 4 3)

-- A circuit is a state type, an initial state and a step: (state, input) ↦ (next, output).
-- This one sums its inputs (mod 16) and outputs the sum so far.
def acc : Circuit B4 B4 :=
  Circuit.mk B4 (BitVec.ofNat 4 0) (fun s x => Hw.pair (Hw.add s x) s)

-- circuits compose: `acc` after `addThree`
def pipeline : Circuit B4 B4 := Circuit.seq (Circuit.comb addThree) acc

#eval Circuit.runPacked pipeline [1, 2, 3, 4]          -- .cons 0 (.cons 4 (.cons 9 (.cons 15 .nil)))
#eval Circuit.simNet Bool.true pipeline [1, 2, 3, 4]   -- the same, from the netlist
def verilog : String := Verilog.emit (Circuit.netlist "pipeline" pipeline)
```

`Hw r` is a type class whose instances are *representations* of signals. At values,
`Hw.add` adds bit vectors. At wires, it adds a node to a netlist. A circuit written once
against `[Hw r]` can be simulated, compiled to a netlist (with shared subterms
detected), and printed as Verilog. `verilog` above is:

```
module pipeline(input clk, input [3:0] x, output [3:0] y);
  reg [3:0] r_1; initial r_1 = 4'd0;
  wire [3:0] n4 = x + 4'd3;
  wire [3:0] n5 = r_1 + n4;
  always @(posedge clk) r_1 <= n5;
  assign y = r_1;
endmodule
```

The library also has bundles of named signals (`deriving Bundle`), reset and enable,
test benches, waveforms (VCD) and pin constraints, and the combinators come with
lemmas (`Circuit.run_seq`: running `seq a b` is running `b` on the outputs of `a`). A
UART for a Lattice iCEstick FPGA board is written in it.
(`examples/tour/10-hdl.wiz`; `examples/hdl.wiz`, `examples/hdl-compose.wiz`;
[libraries.md](libraries.md), H14.)

## 11: packages

A program bigger than one file is a **grail package**: a directory with a `grail.wiz`,
which is itself Wiz:

```wiz
import Grail
def package : Package := Package.new "hello"
  |> Package.lib "greet" "src"           -- the modules under src/: `import Greet` is src/Greet.wiz
  |> Package.exe "app" "App.wiz"         -- compile main to .grail/bin/app
  |> Package.tests "tests" "tests"       -- each tests/*.wiz against its .expected
```

`grail build` builds everything (in parallel, and only what changed since last time),
`grail run app` builds and runs a program, and `grail test` runs the tests: a test is a
`.wiz` file whose messages (or, with `-- test: run` on its first line, whose output) must
match the `.expected` file beside it. `grail test --update` writes the `.expected` files.
The tour's own examples are tests of exactly this kind. A `wiz-toolchain` file next to
`grail.wiz` pins the toolchain, and `Package.dep` adds a package from a git repository.
[install.md](install.md#a-first-project-with-grail) walks through a first package;
[stages/23-grail.md](stages/23-grail.md) has the rest.

A new package starts with `grail new`:

```
$ grail new hello
grail new: wrote hello (grail.wiz, src/Main.wiz, tests/hello.wiz, README.md, .gitignore)
  cd hello && grail build && grail run hello
```

It writes a library, an executable and a golden test; `grail run hello` prints
`hello from hello`, and the test checks the same line. An existing non-empty directory
is refused, so `new` never overwrites work, and the name must start with a letter.
([stages/23-grail.md](stages/23-grail.md), 23o.)

Modules are files: `import A.B` reads `A/B.wiz` from a module root (the standard
library `lib/`, a package's `lib` directories, `-I DIR`). Wiz has no namespaces yet, so
one name can be declared only once among everything a file imports. Mark helpers
`private` to keep them out of other modules.

## 12: taint analysis with scry

`scry` is a program analyser whose library is Wiz: `lib/Scry/*` has the three-address IR
(`Scry.Wil`), the CFG and reaching definitions (`Scry.Analysis`), and taint analysis as
Datalog (`Scry.Taint`). A *source* call's result is attacker-controlled, a *sanitiser*
cleans it, and a *sink* must not receive a tainted value:

```
import Scry.Taint
import Scry.TaintExamples

def spec : Scry.TaintSpec :=
  Scry.parseTaintSpec "source getenv\nsanitise sanitize\nsink system 0"

#eval Scry.alertsInFunc Scry.directFn spec      -- .cons (4, 0) .nil
#eval Scry.alertsInFunc Scry.sanitisedFn spec   -- .nil
```

The first function copies and adds `getenv`'s result before passing it to `system`, so
the analysis reports the sink and the argument; the second passes it through `sanitize`,
which kills the flow. A finding also carries its source → sink path (`Scry.findings`).
(`examples/tour/12-scry.wiz`; [libraries.md](libraries.md), "Scry".)

## Where next

* The **examples**: [`examples/`](../examples/) has one file per feature, each checked
  by the test suite (`grail test` in the repository).
* The **libraries**: `lib/`, described in [libraries.md](libraries.md): text, JSON,
  arrays, processes and files (`Sys`), effects (`Eff`), concurrency (`MVar`,
  `Session`), separation logic (`HProp`, `Hoare`), the HDL.
* **How it works**: the stage docs ([index.md](index.md)) build the language up from
  the kernel, a stage at a time, with exercises. Stage 1 is the core calculus,
  stages 3–7 the elaborator, data, erasure, macros and classes, stage 8 the compiler,
  stages 12–21 the self-hosted toolchain. [CoreSpec.md](CoreSpec.md) has the rules.
* **What is proved, and what isn't**: [Status.md](Status.md).
