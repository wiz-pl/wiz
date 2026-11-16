import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## 33: deadlock freedom, proved

lib/SessionDeadlock.wiz: the configuration model, `Deadlock.progress` and
`Deadlock.stepAcyclic` (axiom-free), and the connection to `link` (docs/stages/33-deadlock.md).
The negatives are the typing rules a thread can't break: finishing with an endpoint
held, sending on a receiving end, and two senders as dual ends. -/

def verifDeadlockGroup : Group where
  name := "verif-deadlock"
  exercise := "lib/SessionDeadlock.wiz (stage 33)"
  cases := [
    { name := "33b progress, preservation of acyclicity and reachable progress need no axiom", run := fun _ =>
        okLibs "import SessionDeadlock\n#print axioms Deadlock.progress\n#print axioms Deadlock.stepAcyclic\n#print axioms Deadlock.reachableProgress\n"
          ["'Deadlock.progress' does not depend on any axioms",
           "'Deadlock.stepAcyclic' does not depend on any axioms",
           "'Deadlock.reachableProgress' does not depend on any axioms"] },
    { name := "33b a fork step from one main thread: the reached configuration is acyclic", run := fun _ =>
        okLibs "import SessionDeadlock\ndef P : Proto := .send Nat (fun _ => .done)\n-- main forks a child that receives a number; main sends 7; both close\ndef child (c : Nat) : Deadlock.Th 2 (.cons c (Proto.dual P) (Deadlock.Ctx.toChild .nil .nil)) :=\n  Deadlock.Act.act .nil .nil c (Proto.dual P) (refl _) (fun _ => Deadlock.Act.act .nil .nil c .done (refl _) (Deadlock.Th.halt 0))\ndef parent (c : Nat) : Deadlock.Th 2 (.cons c P (Deadlock.Ctx.toParent .nil .nil)) :=\n  Deadlock.Act.act .nil .nil c P (refl _) (7, Deadlock.Act.act .nil .nil c .done (refl _) (Deadlock.Th.halt 0))\ndef main : Deadlock.Th 3 .nil := Deadlock.Act.fork P .nil child parent\n-- one fork step from the initial configuration\ndef run : Deadlock.Steps (Deadlock.init 3 main) _ :=\n  Deadlock.Steps.step (Deadlock.Step.fork (Deadlock.init 3 main) 0 2 .nil P .nil child parent (refl _)) (Deadlock.Steps.refl _)\ndef acyc := Deadlock.reachableAcyclic 3 main run\n#print axioms acyc\n"
          ["'acyc' does not depend on any axioms"] },
    { name := "33c two Procs on the two ends of one channel are not stuck (uses castRefl)", run := fun _ =>
        okLibs "import SessionDeadlock\ndef P : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\ndef client : Proc Nat P := (3, fun r => r)\ndef server : Proc Unit (Proto.dual P) := fun n => (n + n, ())\ndef bd : Deadlock.Bounded 2 P := fun _ _ => True.intro\ndef ok := Deadlock.linkProgress 2 P bd client server\n#print axioms ok\n"
          ["'ok' depends on axioms: [castRefl]"] },
    { name := "33a a thread can't finish holding an endpoint, send on a receiving end, or pair two senders", run := fun _ => do
        failsLibs "import SessionDeadlock\ndef P : Proto := .send Nat (fun _ => .done)\n-- a thread can't finish while it still holds an endpoint\ndef quit : Deadlock.Th 1 (.cons 0 P .nil) := Deadlock.Act.ret (refl _)\n" "mismatch"
        failsLibs "import SessionDeadlock\ndef P : Proto := .recv Nat (fun _ => .done)\n-- the endpoint receives, so the thread can't send on it\ndef wrong : Deadlock.Th 2 (.cons 0 P .nil) := Deadlock.Act.act .nil .nil 0 P (refl _) (5, Deadlock.Th.halt 1)\n" "mismatch"
        failsLibs "import SessionDeadlock\n-- two senders are not dual ends of one channel\ndef bad : Deadlock.DualR (.send Nat (fun _ => .done)) (.send Nat (fun _ => .done)) := True.intro\n" "mismatch" }
  ]

builtin_initialize registerGroup verifDeadlockGroup

end Tests.Elab
