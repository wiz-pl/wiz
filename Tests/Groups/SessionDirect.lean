import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## 25g, 25i, 25j: direct-style sessions, recursive protocols, delegation

The examples are `examples/session-direct/*.wiz`; compiled, each `main` runs its servers
in threads. The negatives are the three ways to misuse an endpoint (twice, dropped, the
wrong protocol) at each stage. -/

def sessionDirectGroup : Group where
  name := "conc-sessions"
  exercise := "lib/Session.wiz §4, lib/SessionRec.wiz (stages 25g, 25i, 25j)"
  cases := [
    { name := "25g direct style: ping-pong, a calculator, a stream of known length, CPS and direct on one channel", run := fun _ =>
        cRunLibs (← IO.FS.readFile "examples/session-direct/finite.wiz") "42\n[7, 12, 8]\n5050\n2\n" },
    { name := "25g an endpoint used twice, dropped, or on the wrong step; natives private", run := fun _ => do
        failsLibs "import IO\nimport Session\n-- the endpoint is used twice: two messages where the protocol has one\ndef twice (1 c : Chan (.send Nat (fun _ => .done))) : IO Unit := do1\n  d ⇐ Chan.sendD c 1;\n  e ⇐ Chan.sendD c 2;\n  Chan.closeD d;\n  Chan.closeD e\n" "quantity 1"
        failsLibs "import IO\nimport Session\ndef PingPong : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n-- the endpoint is dropped after the first step\ndef drop (1 c : Chan PingPong) : IO Unit := do1\n  c ⇐ Chan.sendD c 1;\n  IO.pure ()\n" "quantity 1"
        failsLibs "import IO\nimport Session\ndef PingPong : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n-- the protocol says send, this receives\ndef wrong (1 c : Chan PingPong) : IO Unit := do1\n  (m, c) ⇐ Chan.recvD c;\n  Chan.closeD c\n" "mismatch"
        failsLibs "import IO\nimport Session\ndef PingPong : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n-- the wrong message type\ndef wrong (1 c : Chan PingPong) : IO Unit := do1\n  c ⇐ Chan.sendD c Bool.true;\n  (m, c) ⇐ Chan.recvD c;\n  Chan.closeD c\n" "mismatch"
        failsLibs "import IO\nimport Session\ndef PingPong : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n-- both ends follow the same protocol, not dual ones\ndef child (1 c : Chan PingPong) : IO Unit := do1\n  c ⇐ Chan.sendD c 1;\n  (m, c) ⇐ Chan.recvD c;\n  Chan.closeD c\ndef bad : IO Unit := do1\n  c ⇐ Chan.forkD PingPong child;\n  c ⇐ Chan.sendD c 1;\n  (m, c) ⇐ Chan.recvD c;\n  Chan.closeD c\n" "mismatch"
        failsLibs "import IO\nimport Session\ndef PingPong : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n-- the raw natives are private\ndef forge (1 c : Chan PingPong) : IO (Chan (.recv Nat (fun _ => .done))) := Chan.sendRaw c 1\n" "private" },
    { name := "25g (verif-d1-sa's draft) a direct client and server", run := fun _ =>
        cRunLibs ("import IO\nimport Session\ndef P : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n" ++
          "def serveD (1 c : Chan (Proto.dual P)) : IO Unit := do1\n  (n, c) ⇐ Chan.recvD c;\n  c ⇐ Chan.sendD c (n + n);\n  Chan.closeD c\n" ++
          "def clientD (m : Nat) : IO Nat := do1\n  c ⇐ Chan.forkD P serveD;\n  c ⇐ Chan.sendD c m;\n  (r, c) ⇐ Chan.recvD c;\n  IO.then1 (Chan.closeD c) (IO.pure r)\n" ++
          "def main : IO Unit := IO.bind (clientD 21) (fun r => IO.println (Nat.toString r))\n") "42\n" },
    { name := "25i recursive protocols: ping-pong rounds, a calculator loop, a pulled stream", run := fun _ =>
        cRunLibs (← IO.FS.readFile "examples/session-direct/recursive.wiz") "5\n[7, 12, 1]\n45\n" },
    { name := "25i a loop endpoint used twice, dropped, past its bound; the child at the wrong system", run := fun _ => do
        failsLibs "import IO\nimport Session\nimport SessionRec\ndef Ping : Unit → RProto Unit := fun _ => .send Nat (fun _ => .recv Nat (fun _ => .jump ()))\n-- a loop endpoint used twice: two rounds sent on one endpoint\ndef twice (1 c : Chan (Proto.loop Ping 1 ())) : IO Unit := do1\n  d ⇐ Chan.sendD c 1;\n  e ⇐ Chan.sendD c 2;\n  (x, d) ⇐ Chan.recvD d;\n  (y, e) ⇐ Chan.recvD e;\n  Chan.closeD d;\n  Chan.closeD e\n" "quantity 1"
        failsLibs "import IO\nimport Session\nimport SessionRec\ndef Ping : Unit → RProto Unit := fun _ => .send Nat (fun _ => .recv Nat (fun _ => .jump ()))\n-- the server stops answering before the bound: the endpoint is dropped\ndef quit : (n : Nat) → (1 c : Chan (Proto.loop (RProto.dualSys Ping) n ())) → IO Unit\n  | .zero => fun c => Chan.closeD c\n  | .succ n => fun c => do1\n      (x, c) ⇐ Chan.recvD c;\n      IO.pure ()\n" "quantity 1"
        failsLibs "import IO\nimport Session\nimport SessionRec\ndef Ping : Unit → RProto Unit := fun _ => .send Nat (fun _ => .recv Nat (fun _ => .jump ()))\n-- a round too many: after two rounds the protocol is done, not another send\ndef extra (1 c : Chan (Proto.loop Ping 2 ())) : IO Unit := do1\n  c ⇐ Chan.sendD c 1;\n  (x, c) ⇐ Chan.recvD c;\n  c ⇐ Chan.sendD c 2;\n  (y, c) ⇐ Chan.recvD c;\n  c ⇐ Chan.sendD c 3;\n  Chan.closeD c\n" "mismatch"
        failsLibs "import IO\nimport Session\nimport SessionRec\ndef Ping : Unit → RProto Unit := fun _ => .send Nat (fun _ => .recv Nat (fun _ => .jump ()))\n-- the child follows the system, not its dual\ndef child : (n : Nat) → (1 c : Chan (Proto.loop Ping n ())) → IO Unit\n  | .zero => fun c => Chan.closeD c\n  | .succ n => fun c => do1\n      c ⇐ Chan.sendD c 1;\n      (x, c) ⇐ Chan.recvD c;\n      child n c\ndef bad : IO Unit := do1\n  c ⇐ Chan.forkLoop Ping 1 () (child 1);\n  c ⇐ Chan.sendD c 1;\n  (x, c) ⇐ Chan.recvD c;\n  Chan.closeD c\n" "mismatch" },
    { name := "25j delegation of a finite, a recursive and a stream session", run := fun _ =>
        cRunLibs (← IO.FS.readFile "examples/session-direct/delegation.wiz") "42\n18\n45\n" },
    { name := "25j a delegated endpoint used again, dropped by the worker, of the wrong protocol, used out of order", run := fun _ => do
        failsLibs "import IO\nimport Session\nimport SessionRec\ndef PP : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n-- the delegated endpoint is used again after it was handed over\ndef again (1 d : Chan PP) (1 c : Chan (Proto.sendCh PP Proto.done)) : IO Unit := do1\n  c ⇐ Chan.delegate PP d c;\n  Chan.closeD c;\n  d ⇐ Chan.sendD d 1;\n  (x, d) ⇐ Chan.recvD d;\n  Chan.closeD d\n" "quantity 1"
        failsLibs "import IO\nimport Session\nimport SessionRec\ndef PP : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n-- the worker drops the endpoint delegated to it\ndef worker (1 c : Chan (Proto.recvCh PP Proto.done)) : IO Unit := do1\n  c ⇐ Chan.sendD c 1;\n  IO.pure ()\n" "quantity 1"
        failsLibs "import IO\nimport Session\nimport SessionRec\ndef PP : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n-- delegating an endpoint of the wrong protocol (the dual end instead)\ndef wrongEnd (1 d : Chan (Proto.dual PP)) (1 c : Chan (Proto.sendCh PP Proto.done)) : IO Unit := do1\n  c ⇐ Chan.delegate PP d c;\n  Chan.closeD c\n" "mismatch"
        failsLibs "import IO\nimport Session\nimport SessionRec\ndef PP : Proto := .send Nat (fun _ => .recv Nat (fun _ => .done))\n-- the receiver uses the delegated session out of order (receives first)\ndef worker (1 c : Chan (Proto.recvCh PP Proto.done)) : IO Unit := do1\n  (x, c) ⇐ Chan.recvD c;\n  Chan.closeD c\n" "mismatch" },
    { name := "25i the pure model: `link` runs a loop protocol, the server cast along `Proto.dual_loop`", run := fun _ =>
        okLibs "import IO\nimport Session\nimport SessionRec\ndef Ping : Unit → RProto Unit := fun _ => .send Nat (fun _ => .recv Nat (fun _ => .jump ()))\ndef client : (n : Nat) → Nat → Proc Nat (Proto.loop Ping n ())\n  | .zero, x => x\n  | .succ n, x => (x, fun y => client n y)\ndef server : (n : Nat) → Proc Unit (Proto.loop (RProto.dualSys Ping) n ())\n  | .zero => ()\n  | .succ n => fun x => (x + 1, server n)\ndef serverD (n : Nat) : Proc Unit (Proto.dual (Proto.loop Ping n ())) :=\n  Eq.substBack (fun p => Proc Unit p) (Proto.dual_loop Ping n ()) (server n)\n#eval (link (Proto.loop Ping 4 ()) (client 4 10) (serverD 4)).1\n" ["14"] },
    { name := "the examples check (no threads needed)", run := fun _ => do
        okLibs (← IO.FS.readFile "examples/session-direct/finite.wiz")
        okLibs (← IO.FS.readFile "examples/session-direct/recursive.wiz")
        okLibs (← IO.FS.readFile "examples/session-direct/delegation.wiz") }
  ]

builtin_initialize registerGroup sessionDirectGroup

end Tests.Elab
