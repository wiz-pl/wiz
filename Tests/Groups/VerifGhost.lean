import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## Ghost state: lib/GhostState.wiz (24h, plan S-b) -/

/-- The update modality, allocation, agreement, the authoritative algebra and the ghost
counter, used from outside the library. -/
def verifGhostEx : String := "import GhostState\n-- owning ◯2 and ●5 together: the fragment is included in the authority\ndef incl (v : (authPCM natAdd).valid ((authPCM natAdd).op (Auth.auth natAdd 5) (Auth.frag 2))) :\n    PCM.Incl natAdd 2 5 :=\n  Auth.included natAdd v\n-- an authority over a counter and a fragment step up together\ndef bump (n k : Nat) : PCM.Update (authPCM natAdd)\n    ((authPCM natAdd).op (Auth.auth natAdd n) (Auth.frag k))\n    ((authPCM natAdd).op (Auth.auth natAdd (n + 1)) (Auth.frag (k + 1))) :=\n  Auth.update natAdd (PCM.local_update_op natAdd n k 1 ())\n-- the update modality, written |==>[M]: owning tickets can be updated to owning them\ndef keep : RProp.Entails (RProp.own natAdd 2) (|==>[natAdd] RProp.own natAdd 2) :=\n  RProp.bupd_intro natAdd (RProp.own natAdd 2)\n-- an exclusive value is updated under the modality\ndef swap : RProp.Entails (RProp.own (exclPCM Nat) (Excl.ex 1)) (|==>[exclPCM Nat] RProp.own (exclPCM Nat) (Excl.ex 9)) :=\n  RProp.own_update (exclPCM Nat) (Excl.update 1 9)\n-- allocate 7 tickets at a fresh ghost name\ndef fresh (r : Nat → Option Nat) :\n    RProp.bupd (gmapPCM natAdd) (fun r' => Ex (fun (γ : Nat) => ownG natAdd γ 7 r')) r :=\n  ghost_alloc_new natAdd () r\n-- agreement: two copies of a value agree, and knowledge can be copied\ndef same {a b : Nat} (v : (agreePCM Nat).valid ((agreePCM Nat).op (Agree.ag a) (Agree.ag b))) : a = b :=\n  Agree.ag_agree v\ndef copy := RProp.own_ag_dup (A := Nat) 3\n-- a ghost counter: three threads, five increments in this interleaving\ndef trace : List Nat := [0, 1, 0, 2, 1]\ndef five : (Ctr.run trace Ctr.init).cell = 5 :=\n  (Ctr.run_counts 3 trace (rfl, (rfl, (rfl, (rfl, (rfl, ())))))).2\n#eval (Ctr.run trace Ctr.init).cell\n#eval (Ctr.run trace Ctr.init).frag 0\n#eval Nat.sumBelow (Ctr.run trace Ctr.init).frag 3\n"

def verifGhostGroup : Group where
  name := "verif-ghost"
  exercise := "lib/GhostState.wiz (stage 24h)"
  cases := [
    { name := "GhostState: modality, allocation, Agree, Auth and the counter check; the counter computes", run := fun _ =>
        okLibs verifGhostEx ["5", "2", "5"] },
    { name := "GhostState: the counter theorem and allocation use no axiom", run := fun _ =>
        okLibs "import GhostState\n#print axioms Ctr.run_counts\n#print axioms ghost_alloc\n#print axioms Auth.update\n#print axioms Agree.no_update\n"
          ["'Ctr.run_counts' does not depend on any axioms", "'ghost_alloc' does not depend on any axioms",
           "'Auth.update' does not depend on any axioms", "'Agree.no_update' does not depend on any axioms"] },
    { name := "GhostState: agreement can't change; two authorities clash; a fragment can't outgrow its authority", run := fun _ => do
        failsLibs "import GhostState\n-- agreement cannot be changed: ag 1 does not update to ag 2\ndef bad : PCM.Update (agreePCM Nat) (Agree.ag 1) (Agree.ag 2) := PCM.update_refl (agreePCM Nat) (Agree.ag 1)\n" "mismatch"
        failsLibs "import GhostState\n-- two authorities are never valid together\ndef bad : (authPCM natAdd).valid ((authPCM natAdd).op (Auth.auth natAdd 1) (Auth.auth natAdd 1)) :=\n  Auth.valid_auth_self natAdd (a := 1) ()\n" "mismatch"
        failsLibs "import GhostState\n-- the fragment 5 is not included in the authority 2\ndef bad : (authPCM natAdd).valid ((authPCM natAdd).op (Auth.auth natAdd 2) (Auth.frag 5)) :=\n  Auth.valid_auth_self natAdd (a := 2) ()\n" "mismatch" },
    { name := "GhostState: a fragment can't change without the authority; the counter needs every thread below m; |==> can't be dropped", run := fun _ => do
        failsLibs "import GhostState\n-- a thread cannot change its fragment without the authority\ndef bad : PCM.Update (authPCM (exclPCM Nat)) (Auth.frag (Excl.ex 1)) (Auth.frag (Excl.ex 2)) :=\n  Auth.update (exclPCM Nat) (Excl.local_update 1 1 2)\n" "mismatch"
        failsLibs "import GhostState\n-- thread 3 is not one of the threads 0, 1\ndef bad : (Ctr.run [0, 3] Ctr.init).cell = 2 := (Ctr.run_counts 2 [0, 3] (rfl, (rfl, ()))).2\n" "rfl"
        failsLibs "import GhostState\n-- an update modality cannot be removed without a valid resource\ndef bad (P : RProp Nat) : RProp.Entails (RProp.bupd natAdd P) P := fun r b => b\n" "mismatch" }
  ]

builtin_initialize registerGroup verifGhostGroup

end Tests.Elab
