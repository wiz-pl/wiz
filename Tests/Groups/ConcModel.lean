import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/Conc.wiz` (stage 32, docs/stages/32-conc-model.md): the `Conc` effect over
`Eff1`, the pure scheduler (round-robin and scripted), the stateless model checker on a
correct program, a lost update and a deadlock, and the round-robin proofs. Everything
runs in the frontend (`#eval`), so the group needs no C toolchain. -/
def concModelGroup : Group where
  name := "conc-model"
  exercise := "Stage 32"
  cases := [
    { name := "the library checks, and the scheduler, the checker and the proofs use no axiom", run := fun _ =>
        okLibs ("import Conc\n" ++
          "#print axioms Conc.run\n" ++
          "#print axioms Conc.check\n" ++
          "#print axioms Conc.pick_rr_progress\n" ++
          "#print axioms Conc.pick_ready\n")
          [
            "'Conc.run' does not depend on any axioms",
            "'Conc.check' does not depend on any axioms",
            "'Conc.pick_rr_progress' does not depend on any axioms",
            "'Conc.pick_ready' does not depend on any axioms"
          ] },
    { name := "a correct counter: round-robin returns 2, and so does every interleaving (no deadlock either)", run := fun _ =>
        okLibs ("import Conc\n" ++
          "def worker (c : Conc.MVar) : Conc Nat Unit := do\n" ++
          "  v ← Conc.take c;\n" ++
          "  Conc.put c (Nat.succ v)\n" ++
          "def counter : Conc Nat Nat := do\n" ++
          "  c ← Conc.newMVarWith 0;\n" ++
          "  d1 ← Conc.newMVar;\n" ++
          "  d2 ← Conc.newMVar;\n" ++
          "  Conc.fork (do worker c; Conc.put d1 0);\n" ++
          "  Conc.fork (do worker c; Conc.put d2 0);\n" ++
          "  Conc.take d1;\n" ++
          "  Conc.take d2;\n" ++
          "  Conc.take c\n" ++
          "#eval Conc.Outcome.show Nat.repr (Conc.runRR 0 100 counter).outcome\n" ++
          "#eval Conc.Report.show Nat.repr (Conc.check (Conc.Cfg.mk 0 100 1000) counter (Conc.returns (fun v => Nat.beq v 2)))\n" ++
          "#eval Conc.Report.show Nat.repr (Conc.findDeadlock (Conc.Cfg.mk 0 100 1000) counter)\n")
          [
            "\"done 2\"",
            "\"ok: 39 runs, every interleaving\"",
            "\"ok: 39 runs, every interleaving\""
          ] },
    { name := "a lost update: round-robin returns 2, the checker finds a run that returns 1, and its script replays it", run := fun _ =>
        okLibs ("import Conc\n" ++
          "def incr (c : Conc.MVar) : Conc Nat Unit := do\n" ++
          "  v ← Conc.read c;\n" ++
          "  Conc.take c;\n" ++
          "  Conc.put c (Nat.succ v)\n" ++
          "def pause : Nat → Conc Nat Unit\n" ++
          "  | .zero => Conc.ret ()\n" ++
          "  | .succ n => Conc.andThen Conc.yield (pause n)\n" ++
          "def lostUpdate : Conc Nat Nat := do\n" ++
          "  c ← Conc.newMVarWith 0;\n" ++
          "  d1 ← Conc.newMVar;\n" ++
          "  d2 ← Conc.newMVar;\n" ++
          "  Conc.fork (do incr c; Conc.put d1 0);\n" ++
          "  Conc.fork (do pause 4; incr c; Conc.put d2 0);\n" ++
          "  Conc.take d1;\n" ++
          "  Conc.take d2;\n" ++
          "  Conc.take c\n" ++
          "#eval Conc.Outcome.show Nat.repr (Conc.runRR 0 100 lostUpdate).outcome\n" ++
          "#eval Conc.Report.show Nat.repr (Conc.check (Conc.Cfg.mk 0 100 1000) lostUpdate (Conc.returns (fun v => Nat.beq v 2)))\n" ++
          "#eval Conc.Outcome.show Nat.repr (Conc.run 0 100 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 1 (.cons 1 (.cons 1 (.cons 1 .nil))))))))) lostUpdate).outcome\n")
          [
            "\"done 2\"",
            "\"failed on run 5: done 1\\nscript [0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]\\n0: newMVar m0\\n0: put m0 0\\n0: newMVar m1\\n0: newMVar m2\\n0: fork 1\\n0: fork 2\\n2: yield\\n2: yield\\n2: yield\\n1: take m0 = 0\\n2: yield\\n1: put m0 0\\n2: take m0 = 0\\n2: put m0 0\\n1: take m0 = 0\\n1: put m0 1\\n2: take m0 = 1\\n1: put m1 0\\n1: exit\\n0: take m1 = 0\\n2: put m0 1\\n2: put m2 0\\n2: exit\\n0: take m2 = 0\\n0: take m0 = 1\\n0: return 1\"",
            "\"done 1\""
          ] },
    { name := "a deadlock (lock-order inversion): round-robin finishes, findDeadlock finds the cycle, and its script replays it", run := fun _ =>
        okLibs ("import Conc\n" ++
          "def pause : Nat → Conc Nat Unit\n" ++
          "  | .zero => Conc.ret ()\n" ++
          "  | .succ n => Conc.andThen Conc.yield (pause n)\n" ++
          "def lockOrder : Conc Nat Nat := do\n" ++
          "  a ← Conc.newMVarWith 0;\n" ++
          "  b ← Conc.newMVarWith 0;\n" ++
          "  d ← Conc.newMVar;\n" ++
          "  Conc.fork (do pause 3; x ← Conc.take b; y ← Conc.take a; Conc.put a y; Conc.put b x; Conc.put d 0);\n" ++
          "  x ← Conc.take a;\n" ++
          "  y ← Conc.take b;\n" ++
          "  Conc.put b y;\n" ++
          "  Conc.put a x;\n" ++
          "  Conc.take d\n" ++
          "#eval Conc.Outcome.show Nat.repr (Conc.runRR 0 100 lockOrder).outcome\n" ++
          "#eval Conc.Report.show Nat.repr (Conc.findDeadlock (Conc.Cfg.mk 0 100 1000) lockOrder)\n" ++
          "#eval Conc.Outcome.show Nat.repr (Conc.run 0 100 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 1 (.cons 0 (.cons 1 (.cons 1 (.cons 1 .nil))))))))))) lockOrder).outcome\n")
          [
            "\"done 0\"",
            "\"failed on run 19: deadlock (blocked: 0, 1)\\nscript [0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1]\\n0: newMVar m0\\n0: put m0 0\\n0: newMVar m1\\n0: put m1 0\\n0: newMVar m2\\n0: fork 1\\n0: take m0 = 0\\n1: yield\\n1: yield\\n1: yield\\n1: take m1 = 0\"",
            "\"deadlock (blocked: 0, 1)\""
          ] },
    { name := "round-robin interleaves yields; the step bound and the run bound make a report bounded", run := fun _ =>
        okLibs ("import Conc\n" ++
          "def spin : Nat → Conc Nat Unit\n" ++
          "  | .zero => Conc.ret ()\n" ++
          "  | .succ n => Conc.andThen Conc.yield (spin n)\n" ++
          "def three : Conc Nat Nat := do\n" ++
          "  Conc.fork (spin 2);\n" ++
          "  Conc.fork (spin 2);\n" ++
          "  spin 2;\n" ++
          "  Conc.ret 0\n" ++
          "#eval Conc.Res.show Nat.repr (Conc.runRR 0 100 three)\n" ++
          "#eval Conc.Outcome.show Nat.repr (Conc.runRR 0 5 three).outcome\n" ++
          "#eval Conc.Report.show Nat.repr (Conc.check (Conc.Cfg.mk 0 5 1000) three (Conc.returns (fun v => .true)))\n" ++
          "#eval Conc.Report.show Nat.repr (Conc.check (Conc.Cfg.mk 0 100 50) three (Conc.returns (fun v => .true)))\n" ++
          "#eval Conc.Report.show Nat.repr (Conc.check (Conc.Cfg.mk 0 100 1000) three (Conc.returns (fun v => .true)))\n")
          [
            "\"done 0\\nscript [0, 0, 0, 0, 0, 0, 0, 0]\\n0: fork 1\\n1: yield\\n0: fork 2\\n1: yield\\n1: exit\\n2: yield\\n0: yield\\n2: yield\\n2: exit\\n0: yield\\n0: return 0\"",
            "\"out of fuel\"",
            "\"ok: 33 runs, bounded\"",
            "\"ok: 50 runs, bounded\"",
            "\"ok: 103 runs, every interleaving\""
          ] },
    { name := "main returning ends the run (a blocked child is killed); main blocked on its own MVar is a deadlock", run := fun _ =>
        okLibs ("import Conc\n" ++
          "def orphan : Conc Nat Nat := do\n" ++
          "  m ← Conc.newMVar;\n" ++
          "  Conc.fork (do v ← Conc.take m; Conc.put m v);\n" ++
          "  Conc.ret 5\n" ++
          "#eval Conc.Res.show Nat.repr (Conc.runRR 0 100 orphan)\n" ++
          "def selfLock : Conc Nat Nat := do\n" ++
          "  m ← Conc.newMVar;\n" ++
          "  Conc.take m\n" ++
          "#eval Conc.Res.show Nat.repr (Conc.runRR 0 100 selfLock)\n")
          [
            "\"done 5\\nscript [0, 0]\\n0: newMVar m0\\n0: fork 1\\n0: return 5\"",
            "\"deadlock (blocked: 0)\\nscript [0]\\n0: newMVar m0\""
          ] },
    { name := "a thread keeps a linear token across yields (one-shot continuations)", run := fun _ =>
        okLibs ("import Conc\n" ++
          "inductive Tok where\n" ++
          "  | mk\n" ++
          "def Tok.free (1 t : Tok) : Conc Nat Unit := match t with\n" ++
          "  | .mk => Conc.ret ()\n" ++
          "def holder (1 t : Tok) : Conc Nat Unit :=\n" ++
          "  Monad1.bind1 Conc.yield (fun _ => Monad1.bind1 Conc.yield (fun _ => Tok.free t))\n" ++
          "def holdMain : Conc Nat Nat := do\n" ++
          "  d ← Conc.newMVar;\n" ++
          "  Conc.fork (Conc.andThen (holder Tok.mk) (Conc.put d 7));\n" ++
          "  Conc.take d\n" ++
          "#eval Conc.Res.show Nat.repr (Conc.runRR 0 100 holdMain)\n")
          [
            "\"done 7\\nscript [0, 0, 0, 0, 0, 0]\\n0: newMVar m0\\n0: fork 1\\n1: yield\\n1: yield\\n1: put m0 7\\n1: exit\\n0: take m0 = 7\\n0: return 7\""
          ] },
    { name := "the proofs: picks by rfl, round-robin progress and pick-readiness applied", run := fun _ =>
        okLibs ("import Conc\n" ++
          "def pickEx : Conc.pick (fun t => Nat.beq t 2) (.cons 1 (.cons 2 (.cons 3 .nil))) 0 = .some (2, .cons 1 (.cons 3 .nil)) := rfl\n" ++
          "def pickEx2 : Conc.pick (fun t => Nat.beq (Nat.mod t 2) 1) (.cons 1 (.cons 2 (.cons 3 .nil))) 1 = .some (3, .cons 1 (.cons 2 .nil)) := rfl\n" ++
          "def fairEx (q : List Nat) (h : 4 ∈ q) : Conc.RRStep 4 q (Conc.pick (fun t => Nat.beq t 4) q 0) :=\n" ++
          "  Conc.pick_rr_progress (fun t => Nat.beq t 4) 4 rfl q h\n" ++
          "def readyEx (q : List Nat) (c : Nat) : Conc.Picked (fun t => Nat.lt t 3) (Conc.pick (fun t => Nat.lt t 3) q c) :=\n" ++
          "  Conc.pick_ready (fun t => Nat.lt t 3) q c\n" ++
          "#check Conc.pick_rr_progress\n" ++
          "#check Conc.pick_ready\n")
          [
            "Conc.pick_rr_progress : (ready : Nat → Bool) → (u : Nat) → ready u = .true → (q : List Nat) → u ∈ q → Conc.RRStep u q (Conc.pick ready q 0)",
            "Conc.pick_ready : (ready : Nat → Bool) → (q : List Nat) → (c : Nat) → Conc.Picked ready (Conc.pick ready q c)"
          ] },
    { name := "linearity: a token used twice, or a suspended thread dropped, is a quantity error", run := fun _ => do
        failsLibs ("import Conc\ninductive Tok where\n  | mk\n" ++
          "def Tok.free (1 t : Tok) : Conc Nat Unit := match t with\n  | .mk => Conc.ret ()\n" ++
          "def twice (1 t : Tok) : Conc Nat Unit :=\n  Monad1.bind1 (Tok.free t) (fun _ => Tok.free t)\n") "used ω"
        failsLibs "import Conc\ndef dropK {V : Type} (1 k : Conc.Thread V) : Unit := ()\n" "used 0" }
  ]

builtin_initialize registerGroup concModelGroup

end Tests.Elab
