import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def coinductiveGroup : Group where
  name := "copatterns"
  exercise := "stage 4e, Exercise 4.24"
  cases := [
    { name := "Stream, nats, repeat", run := fun _ => ok streamPrelude },
    { name := "observations unfold lazily", run := fun _ =>
        ok (streamPrelude ++ "#reduce (nats .zero).tail.tail.head") [".succ (.succ .zero)"] },
    { name := "parameters stay fixed, explicit arguments are the state", run := fun _ =>
        ok (streamPrelude ++ "#reduce (repeat Nat.zero).tail.tail.head") [".zero"] },
    { name := "guardedness: a recursive observation must be a corecursive call", run := fun _ =>
        fails (streamPrelude ++ "def bad (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => (bad n).tail") "guardedness" },
    { name := "every observation must be defined", run := fun _ =>
        fails (streamPrelude ++ "def bad (n : Nat) : Stream Nat\n  | .head => n") "missing copattern" },
    { name := "no corecursive observation: a cocon cell (register)", run := fun _ =>
        ok (streamPrelude ++ registerSrc ++ "#reduce (register Nat.zero (nats (.succ .zero))).tail.head")
          [".succ .zero"] },
    { name := "a copattern definition without arguments", run := fun _ =>
        ok (streamPrelude ++ "def s : Stream Nat\n  | .head => .zero\n  | .tail => nats .zero\n#reduce s.tail.tail.head")
          [".succ .zero"] },
    { name := "guardedness: no unguarded call in a cocon definition", run := fun _ =>
        fails (streamPrelude ++ "def bad (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => repeat (bad n).head") "guardedness" },
    { name := "guardedness: corecursive and plain recursive observations don't mix", run := fun _ =>
        fails ("coinductive Tree (A : Type) where\n  label : A\n  left : Tree A\n  right : Tree A\n" ++
          "def bad {A : Type} (a : A) (t : Tree A) : Tree A\n  | .label => a\n  | .left => bad a t\n  | .right => t") "guardedness" },
    { name := "the coconstructor T.mk and .mk", run := fun _ =>
        ok (streamPrelude ++ "#check @Stream.mk\ndef s : Stream Nat := .mk .zero (Stream.mk (.succ .zero) (nats .zero))\n#reduce s.tail.tail.head")
          ["Stream.mk : {A : Type} → A → Stream A → Stream A", ".zero"] },
    { name := "cocon, the kernel primitive", run := fun _ =>
        ok (streamPrelude ++ "def s : Stream Nat := cocon (.zero, nats (.succ .zero), (), ())\n#reduce s.tail.head")
          [".succ .zero"] },
    { name := "cocon needs a coinductive expected type", run := fun _ =>
        fails (streamPrelude ++ "def bad : Nat := cocon (.zero, ())") "cocon builds a coinductive value" },
    { name := "cocon at a variable size is rejected", run := fun _ =>
        fails (streamPrelude ++ "def bad (i : Size) (s : (Stream Nat)^i) : (Stream Nat)^i := cocon (.zero, s, (), ())") "size ↑s" },
    { name := "a sized register: the tail one size down", run := fun _ =>
        ok (streamPrelude ++ "def register {i : Size} (a : Nat) (s : (Stream Nat)^i) : (Stream Nat)^(↑i)\n  | .head => a\n  | .tail => s") },
    { name := "a sized register can't keep the size", run := fun _ =>
        fails (streamPrelude ++ "def bad {i : Size} (a : Nat) (s : (Stream Nat)^i) : (Stream Nat)^i\n  | .head => a\n  | .tail => s") "size ↑s or ∞" },
    { name := "cocon bumps the size", run := fun _ =>
        ok (streamPrelude ++ "def delay (i : Size) (s : (Stream Nat)^i) : (Stream Nat)^(↑i) := cocon (.zero, s, (), ())") },
    { name := "mealy machines by copatterns (coit, state = the arguments)", run := fun _ =>
        ok (streamPrelude ++ registerSrc ++ "#reduce (mealy (fun (n : Nat) (x : Nat) => (.succ n, n)) .zero (nats .zero)).tail.tail.head")
          [".succ (.succ .zero)"] },
    { name := "generalised field notation on inductives too", run := fun _ =>
        ok (matchPrelude ++ "def Vec.tail {A : Type} {n : Nat} : Vec A (.succ n) → Vec A n\n  | .cons _ xs => xs\n" ++
            "def tl {A : Type} {n : Nat} (v : Vec A (.succ (.succ n))) : Vec A n := v.tail.tail") }
  ]

builtin_initialize registerGroup coinductiveGroup

end Tests.Elab
