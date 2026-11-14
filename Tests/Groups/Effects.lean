import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def effectsGroup : Group where
  name := "effects"
  exercise := "Stage 10a"
  cases := [
    { name := "a program reads its command-line arguments (IO.args, 21k), C and LLVM", run := fun _ => do
        let src := "import IO\ndef printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s rest => do\n    IO.println s;\n    printAll rest\n" ++
          "def main : IO Unit := do\n  n ← IO.argCount;\n  IO.println (Nat.toString n);\n  args ← IO.args;\n  printAll args\n"
        ioRun src "0\n"
        ioRun src "2\n--rc\na b\n" (args := #["--rc", "a b"])
        ioRun src "1\nx\n" (args := #["x"]) (llvm := true) },
    { name := "state, exceptions and output, handled in turn", run := fun _ =>
        ioRun ("import Eff\ndef prog : Eff (Row.cons (State Nat) (Row.cons (Exn String) (Row.cons Console Row.nil))) Nat := do\n" ++
          "  n ← get;\n  println \"starting\";\n  put (n + 1);\n  m ← get;\n  Monad.pure (m * 10)\n" ++
          "def report : Except String (Nat × Nat) → String\n  | .ok p => Nat.toString p.1\n  | .error e => e\n" ++
          "def main : IO Unit := do\n  r ← runConsole (runExn (runState prog 4));\n  IO.println (report r)") "starting\n50\n" },
    { name := "an exception stops the computation", run := fun _ =>
        ioRun ("import Eff\ndef prog : Eff (Row.cons (Exn String) (Row.cons Console Row.nil)) Nat := do\n" ++
          "  println \"before\";\n  n ← throw \"boom\";\n  println \"after\";\n  Monad.pure n\n" ++
          "def report : Except String Nat → String\n  | .ok n => Nat.toString n\n  | .error e => e\n" ++
          "def main : IO Unit := do\n  r ← runConsole (runExn prog);\n  IO.println (report r)") "before\nboom\n" },
    { name := "fusion: one program, as a tree or directly", run := fun _ => do
        let prog := "import Eff\ndef tick {m : Type → Type} [i : Monad m] [st : MonadState Nat m] : Nat → m Unit\n" ++
          "  | .zero => Monad.pure ()\n  | .succ n => do\n    k ← MonadState.getS;\n    MonadState.putS (k + 2);\n    tick n\n" ++
          "def prog {m : Type → Type} [i : Monad m] [st : MonadState Nat m] [c : MonadConsole m] : m Nat := do\n" ++
          "  MonadConsole.printLn \"counting\";\n  tick 50;\n  MonadState.getS\n" ++
          "def report (p : Nat × Nat) : IO Unit := IO.println (Nat.toString p.1)\n"
        ioRun (prog ++ "def main : IO Unit := do\n  p ← runConsole (runState (prog : Eff (Row.cons (State Nat) (Row.cons Console Row.nil)) Nat) 0);\n  report p")
          "counting\n100\n"
        ioRun (prog ++ "def main : IO Unit := do\n  p ← (prog : StateT Nat IO Nat) 0;\n  report p") "counting\n100\n" },
    { name := "one-shot effects: a continuation may hold a linear value; Eff programs run under one-shot handlers", run := fun _ =>
        ioRun "import Eff\ndef Coin : Type := Nat\ndef Coin.mk (n : Nat) : Coin := n\ndef Coin.spend (1 c : Coin) : Nat := c\ndef prog {R : Type} (1 c : Coin) : Eff1 1 (Row.cons (State Nat) Row.nil) R Coin :=\n  Eff1.bind (do1 n ← get1; put1 (n + 1)) (fun u => Eff1.pure c)\ndef spent : Nat := Coin.spend (Eff1.run1 (evalState1 (prog (Coin.mk 5)) 10))\ndef count {R : Type} : Eff1 ω (Row.cons (State Nat) (Row.cons Console Row.nil)) R Nat := do1\n  n ← get1;\n  println1 \"counting\";\n  put1 (n + 1);\n  get1\ndef old : Eff (Row.cons (State Nat) Row.nil) Nat := do\n  n ← get;\n  put (n * 2);\n  get\ndef runOld : Nat := (Eff1.run (runState1 (Eff.toEff1 old) 21)).1\ndef main : IO Unit := do1\n  p ← runConsole1 (runState1 count 10);\n  IO.println (Nat.toString p.1);\n  IO.println (Nat.toString spent);\n  IO.println (Nat.toString runOld)" "counting\n11\n5\n42\n" },
    { name := "... which a multi-shot continuation can't", run := fun _ =>
        ioFails "import Eff\ndef Coin : Type := Nat\ndef Coin.mk (n : Nat) : Coin := n\ndef Coin.spend (1 c : Coin) : Nat := c\ndef prog (1 c : Coin) : Eff (Row.cons (State Nat) Row.nil) Coin :=\n  Eff.bind (do n ← get; put (n + 1)) (fun u => Eff.pure c)" "quantity 1 but used ω" },
    { name := "a one-shot handler resumes exactly once: not twice, not never", run := fun _ => do
        ioFails "import Eff\ndef twice {r : Row} {R A : Type} (1 m : Eff1 ω (Row.cons Console r) (Eff1 ω r R A) A) : Eff1 ω r R A :=\n  Eff1.handle (fun a => Eff1.pure a) (fun o k => Eff1.bind (k ()) (fun x => k ())) m" "variable k declared with quantity 1 but used ω"
        ioFails "import Eff\ndef abort {r : Row} {R A : Type} (d : A) (1 m : Eff1 ω (Row.cons (Exn String) r) (Eff1 ω r R A) A) : Eff1 ω r R A :=\n  Eff1.handle (fun a => Eff1.pure a) (fun o k => Eff1.pure d) m" "variable k declared with quantity 1 but used 0"
        ioRun "import Eff\ndef quiet {r : Row} {R A : Type} (1 m : Eff1 ω (Row.cons Console r) (Eff1 ω r R A) A) : Eff1 ω r R A :=\n  Eff1.handle (fun a => Eff1.pure a) (fun o k => k ()) m\ndef main : IO Unit := IO.println \"ok\"" "ok\n" },
    { name := "effects that commute: the proof is checked", run := fun _ =>
        ioRun ("import Eff\ndef ReaderM (E A : Type) : Type := E → A\ninstance {E : Type} : Monad (ReaderM E) where\n" ++
          "  pure := fun a => fun _ => a\n  bind := fun x f => fun env => f (x env) env\n" ++
          "instance {E : Type} : Handler (Reader E) (ReaderM E) where\n  handle := fun _ => fun env => env\n" ++
          "instance {E : Type} : Commute (Reader E) (Reader E) (ReaderM E) where\n  comm := fun o₁ o₂ B f => rfl\n" ++
          "def main : IO Unit := IO.println \"ok\"") "ok\n" },
    { name := "effects that don't commute: no proof", run := fun _ =>
        ioFails ("import Eff\ndef StateM (S A : Type) : Type := S → A × S\ninstance {S : Type} : Monad (StateM S) where\n" ++
          "  pure := fun a => fun s => (a, s)\n  bind := fun x f => fun s => let (a, s') := x s; f a s'\n" ++
          "instance {S : Type} : Handler (State S) (StateM S) where\n  handle := fun o => match o with\n" ++
          "    | .get => fun s => (s, s)\n    | .put s' => fun _ => ((), s')\n" ++
          "instance {S : Type} : Commute (State S) (State S) (StateM S) where\n  comm := fun o₁ o₂ B f => rfl")
          -- (13b) the elaborator compares the two sides of `rfl` itself, before the kernel
          "rfl: the two sides are not definitionally equal" }
  ]

builtin_initialize registerGroup effectsGroup

end Tests.Elab
