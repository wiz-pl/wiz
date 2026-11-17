import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `act`, failing when it takes longer than `ms` milliseconds (an exponential regression
fails instead of passing slowly). -/
def withinMs (ms : Nat) (act : IO Unit) : IO Unit := do
  let start ← IO.monoMsNow
  act
  let took := (← IO.monoMsNow) - start
  unless took ≤ ms do throw (IO.userError s!"took {took} ms (the bound is {ms} ms)")

def runGroup : Group where
  name := "eval"
  exercise := "Exercises 5.1–5.3"
  cases := [
    { name := "structural recursion runs", run := fun _ =>
        ok (runPrelude ++ "#eval add (.succ .zero) (.succ (.succ .zero))") [".succ (.succ (.succ .zero))"] },
    { name := "sized recursion runs (fib 5 = 8)", run := fun _ =>
        ok (runPrelude ++ "#eval fib (.succ (.succ (.succ (.succ (.succ .zero)))))")
          [".succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))"] },
    { name := "codata is lazy and observed with out", run := fun _ =>
        ok (runPrelude ++ "#eval (nats .zero).tail.tail.head") [".succ (.succ .zero)"] },
    { name := "pairs", run := fun _ =>
        ok (runPrelude ++ "#eval swap (Nat.zero, Nat.succ Nat.zero)") ["(.succ .zero, .zero)"] },
    -- (stage 5, sharing) without it each is 2^30 steps, minutes rather than a second
    { name := "a closed definition is computed once (a 30-deep doubling chain of constants)", run := fun _ =>
        withinMs 20000 <| okLibs ("import Prelude\ndef c0 : Nat := 1\n" ++ String.join ((List.range 30).map fun i =>
            s!"def c{i + 1} : Nat := Nat.add c{i} c{i}\n") ++ "#eval c30") ["1073741824"] },
    { name := "let- and match-bound pairs are shared (30-deep doubling chains)", run := fun _ =>
        withinMs 20000 <| okLibs ("import Prelude\ndef pr (q0 : Nat × Nat) : Nat × Nat :=\n" ++
            String.join ((List.range 30).map fun i =>
              s!"  let q{i + 1} : Nat × Nat := (Nat.add q{i}.1 q{i}.2, Nat.add q{i}.2 q{i}.1);\n") ++
            "  q30\n#eval pr (1, 0)\ndef mt (y0 : Nat) : Nat :=\n" ++
            String.join ((List.range 30).map fun i =>
              s!"  match (Nat.add y{i} y{i}, y{i}) with | (y{i + 1}, _) =>\n") ++ "  y30\n#eval mt 1")
          ["(536870912, 536870912)", "1073741824"] },
    -- (the memo is lazy: `big` is reachable from `f` and compiled, but never forced)
    { name := "an unused closed definition is not computed", run := fun _ =>
        withinMs 20000 <| okLibs ("import Prelude\ndef big0 : Nat := 1\n" ++ String.join ((List.range 30).map fun i =>
            s!"def big{i + 1} : Nat := Nat.add big{i} big{i}\n") ++
            "def f (n : Nat) : Nat := match n with | .zero => .zero | .succ _ => big30\n#eval f .zero")
          [".zero"] },
    { name := "types and proofs erase to ◾", run := fun _ =>
        ok "def id {A : Type} (x : A) : A := x\n#erase id" ["id := (λA. (λx. #0))"] },
    { name := "erased fields are gone at runtime", run := fun _ =>
        ok (runPrelude ++ "inductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n" ++
            "  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n#erase Vec.cons")
          ["Vec.cons := (λA. (λn. (λx. (λxs. ⟨1 ◾ #1 #0⟩))))"] }
  ]

builtin_initialize registerGroup runGroup

end Tests.Elab
