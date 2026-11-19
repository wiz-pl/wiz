import Tests.Elab
import Tests.Groups.Conc

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## 31: pure tasks and structured scopes (lib/Task.wiz, lib/Scope.wiz) -/

/-- Pure tasks: a sum, a list of them, a nested `both` over a `parMap`, and a race whose
two sides are equal by `rfl`. -/
def taskProg : String := "import IO
import Task
def sumTo : Nat → Nat → Nat
  | .zero, acc => acc
  | .succ n, acc => sumTo n (acc + n + 1)
def work (n : Nat) : Nat := sumTo n 0
def reps (x : Nat) : Nat → List Nat
  | .zero => .nil
  | .succ n => .cons x (reps x n)
def total : List Nat → Nat
  | .nil => 0
  | .cons x xs => x + total xs
def nested (k : Nat) : Nat :=
  let p := Task.both (fun _ => work k) (fun _ => total (Task.parMap work (reps k 4)));
  p.1 + p.2
def one : Nat := Task.get (Task.spawn (fun _ => work 1000))
def two : Nat × Nat := Task.both (fun _ => work 100) (fun _ => work 200)
def many : Nat := total (Task.parMap work (reps 3000 8))
def deep : Nat := total (Task.parMap nested (reps 100 40))
def raced : Nat := Task.race (fun _ => work 3000) (fun _ => 4501500) rfl
"

/-- The same values printed by a compiled program. -/
def taskMain : String := taskProg ++ "def main : IO Unit := do
  IO.println (Nat.toString one);
  IO.println (Nat.toString two.1);
  IO.println (Nat.toString two.2);
  IO.println (Nat.toString many);
  IO.println (Nat.toString deep);
  IO.println (Nat.toString raced)
"

/-- A scope with two tasks, joined at the close; the scope's combinators. -/
def scopeProg : String := "import IO
import Scope
def prog : IO Nat :=
  Scope.with (fun ρ s =>
    Scope.spawn s (IO.pure 20) (fun s ja =>
    Scope.spawn s (IO.pure 22) (fun s jb =>
    IO.bind (Scope.close s) (fun d =>
    IO.bind (Join.get ja) (fun a =>
    IO.bind (Join.get jb) (fun b => IO.pure (a + b, d)))))))
def total : List Nat → Nat
  | .nil => 0
  | .cons x xs => x + total xs
def count : Nat → List (IO Nat)
  | .zero => .nil
  | .succ n => .cons (IO.pure (n + 1)) (count n)
"

def taskGroup : Group where
  name := "task"
  exercise := "lib/Task.wiz, lib/Scope.wiz, runtime/ task natives (stage 31)"
  cases := [
    { name := "the model: tasks are their values (#eval, #run)", run := fun _ =>
        okLibs (taskProg ++ "#eval one\n#eval two\n#eval many\n#eval deep\n#eval raced\n#run Task.par [fun _ => 1, fun _ => 2]")
          ["500500", "(5050, 20100)", "36012000", "1010000", "4501500", ".cons 1 (.cons 2 .nil)"] },
    { name := "the model's laws, and facts about task programs, by rfl", run := fun _ =>
        okLibs (taskProg ++ "def l1 : Task.parMap work [10, 20] = [55, 210] := rfl\n" ++
          "def l2 (f : Unit → Nat) : Task.get (Task.spawn f) = f () := Task.get_spawn f\n" ++
          "def l3 (xs : List Nat) : Task.parMap work xs = List.map work xs := Task.parMap_eq work xs\n" ++
          "def l4 : raced = work 3000 := rfl\n") },
    { name := "compiled tasks agree with the model (differential), nested tasks included", run := fun _ =>
        cRunLibs taskMain "500500\n5050\n20100\n36012000\n1010000\n4501500\n" },
    { name := "a task held by a closed definition (an immortal object): its value is released at the end", run := fun _ =>
        cRunLibs ("import IO\nimport Task\ndef mk : Nat → List Nat\n  | .zero => .nil\n  | .succ n => .cons n (mk n)\n" ++
          "def t : Task (List Nat) := Task.spawn (fun _ => mk 5)\n" ++
          "def len : List Nat → Nat\n  | .nil => 0\n  | .cons _ xs => .succ (len xs)\n" ++
          "def main : IO Unit := do\n  IO.println (Nat.toString (len (Task.get t)));\n" ++
          "  IO.println (Nat.toString (len (Task.get t)))\n") "5\n5\n" },
    { name := "WIZ_NO_THREADS: the first spawn stops with a clear message", run := fun _ => do
        noThreadsFails taskMain "wiz: Task.spawn: threads are not available in this build (WIZ_NO_THREADS)"
        noThreadsFails (taskProg ++ "def main : IO Unit := IO.println (Nat.toString two.1)")
          "wiz: Task.both: threads are not available in this build (WIZ_NO_THREADS)"
        noThreadsFails (taskProg ++ "def main : IO Unit := IO.println (Nat.toString raced)")
          "wiz: Task.race: threads are not available in this build (WIZ_NO_THREADS)" },
    { name := "a task is opaque: its value is read only by Task.get", run := fun _ =>
        failsLibs "import Task\ndef peek (t : Task Nat) : Nat := t.value" "private to module Task" },
    { name := "scopes: the model runs each task at once, and the kernel computes it", run := fun _ =>
        okLibs (scopeProg ++ "def p1 : prog = IO.pure 42 := rfl\n" ++
          "def p2 : Scope.both (IO.pure 1) (IO.pure 2) = IO.pure (1, 2) := rfl\n" ++
          "def p3 : Scope.all [IO.pure 1, IO.pure 2] = IO.pure [1, 2] := rfl\n") },
    { name := "scopes, compiled: tasks on threads, all joined at the close", run := fun _ =>
        cRunLibs (scopeProg ++ "def main : IO Unit := do\n" ++
          "  n ← prog;\n  IO.println (Nat.toString n);\n" ++
          "  p ← Scope.both (IO.pure 1) (IO.pure \"two\");\n  IO.println p.2;\n" ++
          "  xs ← Scope.all (count 50);\n  IO.println (Nat.toString (total xs))\n") "42\ntwo\n1275\n" },
    { name := "scopes, WIZ_NO_THREADS: spawning stops at the thread it needs", run := fun _ =>
        noThreadsFails (scopeProg ++ "def main : IO Unit := IO.bind prog (fun n => IO.println (Nat.toString n))")
          "wiz: Chan.fork: threads are not available in this build (WIZ_NO_THREADS)" },
    { name := "a task's handle can't escape its scope (the region trick)", run := fun _ => do
        failsLibs ("import Scope\ndef escape : IO (Join Region.static Nat) :=\n" ++
          "  Scope.with (fun ρ s => Scope.spawn s (IO.pure 1) (fun s j =>\n" ++
          "    IO.bind (Scope.close s) (fun d => IO.pure (j, d))))") "type mismatch"
        failsLibs ("import Scope\ndef escape :=\n" ++
          "  Scope.with (fun ρ s => Scope.spawn s (IO.pure 1) (fun s j =>\n" ++
          "    IO.bind (Scope.close s) (fun d => IO.pure (j, d))))") "escapes the scope" },
    { name := "a scope is closed exactly once, by its own body", run := fun _ => do
        -- dropped
        failsLibs "import Scope\ndef drop {ρ : Region} (1 s : Scope ρ) (d : Done ρ) : IO (Nat × Done ρ) := IO.pure (1, d)"
          "quantity 1"
        -- closed twice
        failsLibs ("import Scope\ndef twice : IO Nat :=\n" ++
          "  Scope.with (fun ρ s => IO.bind (Scope.close s) (fun d =>\n" ++
          "    IO.bind (Scope.close s) (fun d2 => IO.pure (1, d))))") "quantity 1"
        -- captured by a task (an action is unrestricted)
        failsLibs ("import Scope\ndef inner : IO Nat :=\n" ++
          "  Scope.with (fun ρ s => Scope.spawn s (IO.bind (Scope.close s) (fun d => IO.pure 1)) (fun s j =>\n" ++
          "    IO.bind (Scope.close s) (fun d => IO.pure (1, d))))") "quantity 1"
        -- another scope's close is not this one's
        failsLibs ("import Scope\ndef other : IO Nat :=\n" ++
          "  Scope.with (fun ρ s => Scope.spawn s (IO.pure 1) (fun s j =>\n" ++
          "    Scope.with (fun ρ' s' => IO.bind (Scope.close s') (fun d' => IO.pure ((1, d'), d')))))")
          "type mismatch"
        -- no scope, and no proof of a close, from nowhere
        failsLibs "import Scope\ndef forged : Scope Region.static := Scope.mk List.nil" "private to module Scope"
        failsLibs "import Scope\ndef ignore : IO Nat :=\n  Scope.with (fun ρ s => IO.pure (1, Done.mk))"
          "private to module Scope" }
  ]

builtin_initialize registerGroup taskGroup

end Tests.Elab
