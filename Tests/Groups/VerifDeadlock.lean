import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## 35: deadlock freedom for a synchronous model

lib/SessionDeadlock.wiz: the configuration model, `Deadlock.progress` and
`Deadlock.stepAcyclic` (axiom-free), and the connection to `link` (docs/stages/35-deadlock.md).
The negatives are the typing rules a thread can't break: finishing with an endpoint
held, sending on a receiving end, and two senders as dual ends. Case 5 pins the *statement*
of each named theorem, so weakening one does not just leave its axiom print clean. -/

def verifDeadlockGroup : Group where
  name := "verif-deadlock"
  exercise := "lib/SessionDeadlock.wiz (stage 35)"
  cases := [
    { name := "35b progress, preservation of acyclicity and reachable progress need no axiom", run := fun _ =>
        okLibs "import SessionDeadlock\n#print axioms Deadlock.progress\n#print axioms Deadlock.stepAcyclic\n#print axioms Deadlock.reachableProgress\n"
          ["'Deadlock.progress' does not depend on any axioms",
           "'Deadlock.stepAcyclic' does not depend on any axioms",
           "'Deadlock.reachableProgress' does not depend on any axioms"] },
    { name := "35b a fork step from one main thread: the reached configuration is acyclic", run := fun _ =>
        okLibs "import SessionDeadlock\ndef P : Proto := .send Nat (fun _ => .done)\n-- main forks a child that receives a number; main sends 7; both close\ndef child (c : Nat) : Deadlock.Th 2 (.cons c (Proto.dual P) (Deadlock.Ctx.toChild .nil .nil)) :=\n  Deadlock.Act.act .nil .nil c (Proto.dual P) (refl _) (fun _ => Deadlock.Act.act .nil .nil c .done (refl _) (Deadlock.Th.halt 0))\ndef parent (c : Nat) : Deadlock.Th 2 (.cons c P (Deadlock.Ctx.toParent .nil .nil)) :=\n  Deadlock.Act.act .nil .nil c P (refl _) (7, Deadlock.Act.act .nil .nil c .done (refl _) (Deadlock.Th.halt 0))\ndef main : Deadlock.Th 3 .nil := Deadlock.Act.fork P .nil child parent\n-- one fork step from the initial configuration\ndef run : Deadlock.Steps (Deadlock.init 3 main) _ :=\n  Deadlock.Steps.step (Deadlock.Step.fork (Deadlock.init 3 main) 0 2 .nil P .nil child parent (refl _)) (Deadlock.Steps.refl _)\ndef acyc := Deadlock.reachableAcyclic 3 main run\n#print axioms acyc\n"
          ["'acyc' does not depend on any axioms"] },
    { name := "35c two Procs on the two ends of one channel are not stuck (uses castRefl)", run := fun _ =>
        okLibs "import SessionDeadlock\ndef P : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\ndef client : Proc Nat P := (3, fun r => r)\ndef server : Proc Unit (Proto.dual P) := fun n => (n + n, ())\ndef bd : Deadlock.Bounded 2 P := fun _ _ => True.intro\ndef ok := Deadlock.linkProgress 2 P bd client server\n#print axioms ok\n"
          ["'ok' depends on axioms: [castRefl]"] },
    { name := "35a a thread can't finish holding an endpoint, send on a receiving end, or pair two senders", run := fun _ => do
        failsLibs "import SessionDeadlock\ndef P : Proto := .send Nat (fun _ => .done)\n-- a thread can't finish while it still holds an endpoint\ndef quit : Deadlock.Th 1 (.cons 0 P .nil) := Deadlock.Act.ret (refl _)\n" "mismatch"
        failsLibs "import SessionDeadlock\ndef P : Proto := .recv Nat (fun _ => .done)\n-- the endpoint receives, so the thread can't send on it\ndef wrong : Deadlock.Th 2 (.cons 0 P .nil) := Deadlock.Act.act .nil .nil 0 P (refl _) (5, Deadlock.Th.halt 1)\n" "mismatch"
        failsLibs "import SessionDeadlock\n-- two senders are not dual ends of one channel\ndef bad : Deadlock.DualR (.send Nat (fun _ => .done)) (.send Nat (fun _ => .done)) := True.intro\n" "mismatch" },
    { name := "35b/35c the theorem statements are pinned (a weaker statement does not elaborate)", run := fun _ =>
        okLibs ("import SessionDeadlock\n" ++
          "-- Each theorem is ascribed its intended statement. A new hypothesis, a weakened\n" ++
          "-- conclusion, or a changed `Final`/`HasStep`/`Acyclic` shape no longer elaborates;\n" ++
          "-- `#print axioms` alone would still be clean for a weaker statement.\n" ++
          "def pinProgress : (C : Deadlock.Cfg) → Deadlock.Typed C → Deadlock.Closed C → Deadlock.Acyclic C → Deadlock.Final C ∨ Deadlock.HasStep C :=\n  Deadlock.progress\n" ++
          "def pinStepAcyclic : {C D : Deadlock.Cfg} → Deadlock.Step C D → Deadlock.Acyclic C → Deadlock.Acyclic D :=\n  Deadlock.stepAcyclic\n" ++
          "def pinStepsAcyclic : {C D : Deadlock.Cfg} → Deadlock.Steps C D → Deadlock.Acyclic C → Deadlock.Acyclic D :=\n  Deadlock.stepsAcyclic\n" ++
          "def pinReachableAcyclic : (n : Nat) → (t : Deadlock.Th n .nil) → {D : Deadlock.Cfg} → Deadlock.Steps (Deadlock.init n t) D → Deadlock.Acyclic D :=\n  Deadlock.reachableAcyclic\n" ++
          "def pinReachableProgress : (n : Nat) → (t : Deadlock.Th n .nil) → {D : Deadlock.Cfg} → Deadlock.Steps (Deadlock.init n t) D → Deadlock.Typed D → Deadlock.Closed D → Deadlock.Final D ∨ Deadlock.HasStep D :=\n  Deadlock.reachableProgress\n" ++
          "def pinLinkTyped : {A B : Type} → (n : Nat) → (p : Proto) → (bd : Deadlock.Bounded n p) → (a : Proc A p) → (b : Proc B (Proto.dual p)) →\n    Deadlock.Typed (Deadlock.linkCfg n p bd a b) :=\n  Deadlock.linkTyped\n" ++
          "def pinLinkClosed : {A B : Type} → (n : Nat) → (p : Proto) → (bd : Deadlock.Bounded n p) → (a : Proc A p) → (b : Proc B (Proto.dual p)) →\n    Deadlock.Closed (Deadlock.linkCfg n p bd a b) :=\n  Deadlock.linkClosed\n" ++
          "def pinLinkAcyclic : {A B : Type} → (n : Nat) → (p : Proto) → (bd : Deadlock.Bounded n p) → (a : Proc A p) → (b : Proc B (Proto.dual p)) →\n    Deadlock.Acyclic (Deadlock.linkCfg n p bd a b) :=\n  Deadlock.linkAcyclic\n" ++
          "def pinLinkProgress : {A B : Type} → (n : Nat) → (p : Proto) → (bd : Deadlock.Bounded n p) → (a : Proc A p) → (b : Proc B (Proto.dual p)) →\n    Deadlock.Final (Deadlock.linkCfg n p bd a b) ∨ Deadlock.HasStep (Deadlock.linkCfg n p bd a b) :=\n  Deadlock.linkProgress\n" ++
          "-- `Typed` and `Closed` are not vacuous: two senders are not dual, and a single\n" ++
          "-- holder of an endpoint is not closed. (Both are inhabited at `linkCfg` above.)\n" ++
          "def P : Proto := .send Nat (fun _ => .done)\n" ++
          "def sender (x : Nat) : Deadlock.Thread :=\n  .mk 2 (.cons 0 P .nil)\n    (Deadlock.Act.act .nil .nil 0 P (refl _)\n      (x, Deadlock.Act.act .nil .nil 0 .done (refl _) (Deadlock.Th.halt 0)))\n" ++
          "def twoSenders : Deadlock.Cfg := .cons (sender 5) (.cons (sender 6) .nil)\n" ++
          "def twoSendersNotTyped : Deadlock.Typed twoSenders → False :=\n  fun h => h 0 1 0 P P (fun e => Deadlock.zeroNeOne e) (Or.inl (refl 0, refl P)) (Or.inl (refl 0, refl P))\n" ++
          "def oneOpen : Deadlock.Cfg := .cons (sender 5) .nil\n" ++
          "def holdsOneOnly : (j : Nat) → Deadlock.Holds oneOpen j 0 → j = 0\n  | .zero, _ => refl 0\n  | .succ _, h => absurd h\n" ++
          "def oneOpenNotClosed : Deadlock.Closed oneOpen → False :=\n  fun h => Ex.elim (h 0 0 (Or.inl (refl 0))) (fun j hj => hj.1 (Eq.symm (holdsOneOnly j hj.2)))\n") }
  ]

builtin_initialize registerGroup verifDeadlockGroup

end Tests.Elab
