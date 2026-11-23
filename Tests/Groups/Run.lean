import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

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
    { name := "types and proofs erase to ◾", run := fun _ =>
        ok "def id {A : Type} (x : A) : A := x\n#erase id" ["id := (λA. (λx. #0))"] },
    { name := "erased fields are gone at runtime", run := fun _ =>
        ok (runPrelude ++ "inductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n" ++
            "  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n#erase Vec.cons")
          ["Vec.cons := (λA. (λn. (λx. (λxs. ⟨1 ◾ #1 #0⟩))))"] },
    -- (erasure audit) A position of quantity `0` is **not evaluated**: the value of a
    -- `let 0`, a `0` field of a constructor or structure, the scrutinee of a `split` at 0,
    -- and an argument of a `0`-quantity binder. The kernel checks these positions in
    -- erased mode and erasure replaces them by `◾`; both ask `QPoly.isErased`. This is the
    -- intended semantics (`docs/stages/05-erasure.md`): an effect lives in `IO`, where the
    -- world token is linear, so it cannot be in a 0 position; a call outside `IO` must be
    -- pure (`docs/stages/09-ffi.md`). The tree interpreter (`#eval`) and the IR (`#run`)
    -- both drop them; the native backends are pinned in group `ffi`.
    { name := "a 0 position is never evaluated (let at 0, 0 fields, split at 0, 0 argument; #eval and #run)", run := fun _ =>
        okLib ("import Prelude\n" ++ zeroFieldDecls ++
            "def e5 : Nat := (fun (f : (0 x : Nat) → Nat) => f (loop ())) (fun _ => 4)\n" ++
            "def e6 : Nat := let 0 (x, y) := ((loop (), 2) : Nat × Nat); 6\n" ++
            -- (the documented boundary: a call whose result is a proof is erased with its
            -- argument, even at ω — erasure is not divergence-preserving)
            "def lem (n : Nat) : 0 = 0 := rfl\n" ++
            "def e7 : Nat := ((lem (loop ()), 7) : (0 = 0) × Nat).2\n" ++
            "#eval e1\n#run e1\n#eval e2\n#run e2\n#eval e3\n#run e3\n#eval e4\n#run e4\n" ++
            "#eval e5\n#run e5\n#eval e6\n#run e6\n#eval e7\n#run e7")
          ["7", "7", "8", "8", "9", "9", "2", "2", "4", "4", "6", "6", "7", "7"] },
    -- (audit F14) a value the interpreter cannot produce is `stuck` with the reason, not
    -- a panic (which returns a default value here) and not `◾` in the function position
    { name := "a global with no code is a stuck value naming it", run := fun _ => do
        -- (`Tests.Elab.run` shadows `Wiz.run` here)
        match Wiz.run ({} : Wiz.Code) [] (.global "nowhere") with
        | .stuck m =>
          check ((m.splitOn "no code for `nowhere`").length > 1) s!"the reason does not name the global: {m}"
        | _ => throw (IO.userError "a global with no code did not produce a stuck value") },
    { name := "applying a non-function is a stuck value, not ◾", run := fun _ => do
        match Wiz.apply ({} : Wiz.Code) (.nat 7) (.nat 1) with
        | .stuck m =>
          check ((m.splitOn "not a function").length > 1) s!"the reason does not say why: {m}"
        | _ => throw (IO.userError "applying a non-function did not produce a stuck value") },
    { name := "a stuck function position is not replaced by a new failure", run := fun _ => do
        match Wiz.apply ({} : Wiz.Code) (.stuck "the real reason") (.nat 1) with
        | .stuck "the real reason" => pure ()
        | _ => throw (IO.userError "apply replaced the reason") }
  ]

builtin_initialize registerGroup runGroup

end Tests.Elab
