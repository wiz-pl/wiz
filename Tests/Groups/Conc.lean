import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## 25: concurrency (runtime/ threads, lib/Session.wiz, lib/MVar.wiz) -/

/-- The dependent protocol of docs/stages/25-concurrency.md: send a length `n`, then `n`
numbers, receive their sum; the server and client as pure processes and over channels. -/
def concSum : String := "import IO
import Session
def sendMany (k : Proto) : Nat → Proto
  | .zero => k
  | .succ n => .send Nat (fun _ => sendMany k n)
def ack : Proto := .recv Nat (fun _ => .done)
def sumProto : Proto := .send Nat (fun n => sendMany ack n)
def nums : (n : Nat) → Proc Nat (sendMany ack n)
  | .zero => fun s => s
  | .succ n => (n + 1, nums n)
def client (m : Nat) : Proc Nat sumProto := (m, nums m)
def serverMany : (n : Nat) → (acc : Nat) → Proc Unit (Proto.dual (sendMany ack n))
  | .zero, acc => (acc, ())
  | .succ n, acc => fun x => serverMany n (acc + x)
def server : Proc Unit (Proto.dual sumProto) := fun n => serverMany n 0
def serveMany : (n : Nat) → (acc : Nat) → (1 c : Chan (Proto.dual (sendMany ack n))) → IO Unit
  | .zero, acc => fun c => Chan.send c acc (fun c' => Chan.close c' (IO.pure ()))
  | .succ n, acc => fun c =>
      Chan.recv c (fun x c' => serveMany n (acc + x) c')
def serve (1 c : Chan (Proto.dual sumProto)) : IO Unit :=
  Chan.recv c (fun n c' => serveMany n 0 c')
def sendNums : (n : Nat) → (1 c : Chan (sendMany ack n)) → IO Nat
  | .zero => fun c => Chan.recv c (fun s c' => Chan.close c' (IO.pure s))
  | .succ n => fun c => Chan.send c (n + 1) (fun c' => sendNums n c')
def runClient (m : Nat) (1 c : Chan sumProto) : IO Nat :=
  Chan.send c m (fun c' => sendNums m c')
"

/-- A chain of threads: each adds one to every element of a list and passes it on; the
last sums, and the sum travels back up. -/
def concChain : String := "import IO
import Session
def Q : Proto := .send (List Nat) (fun _ => .recv Nat (fun _ => .done))
def bump : List Nat → List Nat
  | .nil => .nil
  | .cons x xs => .cons (x + 1) (bump xs)
def total : List Nat → Nat
  | .nil => 0
  | .cons x xs => x + total xs
def upto : Nat → List Nat
  | .zero => .nil
  | .succ n => .cons n (upto n)
def stage : Nat → (1 c : Chan (Proto.dual Q)) → IO Unit
  | .zero => fun c => Chan.recv c (fun xs c' =>
      Chan.send c' (total xs) (fun c'' => Chan.close c'' (IO.pure ())))
  | .succ n => fun c => Chan.recv c (fun xs c' =>
      Chan.fork Q (stage n) (fun d => Chan.send d (bump xs) (fun d' =>
        Chan.recv d' (fun s d'' => Chan.close d''
          (Chan.send c' s (fun c'' => Chan.close c'' (IO.pure ())))))))
def shared : List Nat := upto 100
def main : IO Unit := Chan.fork Q (stage 50) (fun d =>
  Chan.send d shared (fun d' => Chan.recv d' (fun s d'' =>
    Chan.close d'' (IO.bind (IO.println (Nat.toString s)) (fun _ => IO.println (Nat.toString (total shared)))))))
"

/-- A cancellable protocol (decision CS13): up to `n` numbers, each one a value or a
cancel. -/
def concCancel : String := "import IO
import Session
def items : Nat → Proto
  | .zero => .done
  | .succ n => Proto.sendC Nat (fun _ => items n)
def onMsg (n acc : Nat) (serve : (acc : Nat) → (1 c : Chan (Proto.dual (items n))) → IO Unit) :
    (m : Msg Nat) → (1 c : Chan (Proto.dual (Msg.next (fun _ => items n) m))) → IO Unit
  | .val x => fun c => serve (acc + x) c
  | .cancel => fun c => Chan.close c (IO.println (String.append \"cancelled after \" (Nat.toString acc)))
def serveItems : (n : Nat) → (acc : Nat) → (1 c : Chan (Proto.dual (items n))) → IO Unit
  | .zero, acc => fun c => Chan.close c (IO.println (String.append \"all: \" (Nat.toString acc)))
  | .succ n, acc => fun c =>
      Chan.recv c (fun m c' => onMsg n acc (serveItems n) m c')
def client (1 c : Chan (items 3)) : IO Unit :=
  Chan.send c (.val 10) (fun c1 =>
    Chan.send c1 (.val 20) (fun c2 =>
      Chan.cancel c2 (IO.pure ())))
def full (1 c : Chan (items 2)) : IO Unit :=
  Chan.send c (.val 1) (fun c1 =>
    Chan.send c1 (.val 2) (fun c2 => Chan.close c2 (IO.pure ())))
def main : IO Unit := Chan.fork (items 3) (serveItems 3 0) (fun c => client c)
"

/-- Eight threads bump one counter a thousand times each (MVar.modify: the linear
borrow/fill discipline), under a lock, and report through an MVar. The counter is the
MVar, which is atomic by itself, so this case does not test that the lock excludes; the
two cases below do. -/
def concCounter : String := "import IO
import Session
import MVar
def worker (m : MVar Nat) (l : Lock) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ n => IO.bind (MVar.modify m (fun x => x + 1)) (fun _ =>
      IO.bind (Lock.with l (IO.pure ())) (fun _ => worker m l n))
def spawnN (m : MVar Nat) (l : Lock) (done : MVar Nat) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ k => Chan.fork Proto.done (fun c => Chan.close c (IO.bind (worker m l 1000) (fun _ => MVar.put done 1)))
      (fun c => Chan.close c (spawnN m l done k))
def waitN (done : MVar Nat) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ k => IO.bind (MVar.take done) (fun _ => waitN done k)
def main : IO Unit := do1
  m ← MVar.newFull 0;
  l ← Lock.new;
  done ← MVar.new (A := Nat);
  spawnN m l done 8;
  waitN done 8;
  n ← MVar.take m;
  IO.println (Nat.toString n)
"

/-- Two threads observe one lazy stream (shared lazy cells are not overwritten, 25a). -/
def concStream : String := "import IO
import Session
import MVar
coinductive Stream (A : Type) where
  head : A
  tail : Stream A
def natsFrom (n : Nat) : Stream Nat
  | .head => n
  | .tail => natsFrom (n + 1)
def sumN : Nat → Stream Nat → Nat
  | .zero, _ => 0
  | .succ k, s => s.head + sumN k s.tail
def main : IO Unit := IO.bind (MVar.new (A := Nat)) (fun r =>
  let s := natsFrom 0;
  Chan.fork Proto.done (fun c => Chan.close c (MVar.put r (sumN 2000 s)))
    (fun c => Chan.close c (IO.bind (MVar.take r) (fun a =>
      IO.println (Nat.toString (a + sumN 2000 s))))))
"

/-- (15i) Closed definitions first used by several threads at once: each may build the
table (the first to publish wins), and the memoised suspension inside the constant is
forced under the lock. -/
def concCaf : String := "import IO
import Session
import MVar
def range : Nat → List Nat → List Nat
  | .zero, acc => acc
  | .succ n, acc => range n (.cons n acc)
def sum : List Nat → Nat
  | .nil => 0
  | .cons x xs => x + sum xs
def table : List Nat := range 2000 .nil
def lazySum : Unit → Nat := memo (fun _ => sum table)
def work : Nat → Nat → Nat
  | .zero, acc => acc
  | .succ k, acc => work k (acc + sum table + lazySum ())
def spawnN (done : MVar Nat) : Nat → IO Unit
  | .zero => IO.pure ()
  | .succ k => Chan.fork Proto.done (fun c => Chan.close c (MVar.put done (work 100 0)))
      (fun c => Chan.close c (spawnN done k))
def waitN (done : MVar Nat) : Nat → Nat → IO Nat
  | .zero, acc => IO.pure acc
  | .succ k, acc => IO.bind (MVar.take done) (fun n => waitN done k (acc + n))
def main : IO Unit := do1
  done ← MVar.new (A := Nat);
  spawnN done 8;
  n ← waitN done 8 0;
  IO.println (Nat.toString n)
"

/-- (conc-02) One `Child` waited on by two threads at once. Both `waitpid`s block until
the child exits; without a lock one reaps it and the other never gets a status (it
blocked for ever and the case timed out), so a well-typed program hangs or reports a
spurious failure. With the handle's `waitmu` the second waiter sees the status the
first recorded, and the program prints `2`. -/
def concWaitTwice : String := "import Sys
import Session
import MVar
def verdict (r : Except String ExitStatus) : Nat :=
  match r with
  | .ok st => match st with
    | .exited 0 => 1
    | _ => 0
  | .error _ => 0
def both (c : Child) (m : MVar Nat) : IO Unit :=
  Chan.fork Proto.done
    (fun ch => Chan.close ch (IO.bind (Child.wait c) (fun r => MVar.put m (verdict r))))
    (fun ch => Chan.close ch (IO.bind (Child.wait c) (fun r => MVar.put m (verdict r))))
def main : IO Unit := do
  c ← Process.spawnRaw \"sleep\" (.cons \"0.3\" .nil) 0 1 1;
  m ← MVar.new (A := Nat);
  both c m;
  a ← MVar.take m;
  b ← MVar.take m;
  IO.println (Nat.toString (a + b))
"

/-- (conc-02) The File half of the race, as a stress case: the child reads a file to the
end again and again while the parent closes the same handle 10 ms later. Without the
lock this is a `FILE *` use-after-free (a reader can load `h->f` just before `fclose`
frees it); whether that faults depends on the compiler and the interleaving, so the
deterministic repro of conc-02 is the `Child.wait` case above. With the lock the
in-flight read finishes and the next one is `EBADF`, so the child prints `closed`. -/
def concFileRace : String := "import Sys
import Session
import MVar
def line : String := \"0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789\\n\"
def fill : Nat → String → String
  | .zero, acc => acc
  | .succ k, acc => fill k (String.append acc line)
def spin (f : File) : Nat → IO Nat
  | .zero => IO.pure 0
  | .succ k => IO.bind (File.readAll f) (fun r =>
      match r with
      | .ok _ => IO.bind (File.seek f (.start 0)) (fun s =>
          match s with
          | .ok _ => spin f k
          | .error _ => IO.pure 1)
      | .error _ => IO.pure 1)
def main : IO Unit := EIO.toIO (do
  d ← FS.createTempDir;
  let p := Path.join d \"race.txt\";
  FS.writeFile p (fill 400 \"\");
  f ← File.open p \"r\";
  m ← EIO.lift (MVar.new (A := Nat));
  n ← EIO.lift (Chan.fork Proto.done
    (fun ch => Chan.close ch (IO.bind (spin f 100000) (fun x => MVar.put m x)))
    (fun ch => Chan.close ch (IO.bind (Clock.sleep (Duration.millis 10)) (fun _ =>
      IO.bind (File.close f) (fun _ => MVar.take m)))));
  FS.removeAll d;
  EIO.lift (IO.println (match Nat.beq n 1 with | .true => \"closed\" | .false => \"finished\")))
"

/-- (conc-02) Using a handle in a fork after it was closed, twice, and waited on twice:
the deterministic primitive checks. A second `File.close` and `Child.closeStdin` are
`EBADF` (no second `fclose`/`close(2)`), a read after close is `EBADF` (never a
`FILE *` use after free), and a second `Child.wait` gives the same status. -/
def concHandlePrims : String := "import Sys
def errTag (e : Nat) : String :=
  match Nat.beq e 0 with
  | .true => \"ok\"
  | .false => \"err\"
def waitTag (n e : Nat) : String :=
  match Nat.beq e 0 with
  | .true => ExitStatus.toString (ExitStatus.ofNat n)
  | .false => \"err\"
def main : IO Unit := EIO.toIO (do
  d ← FS.createTempDir;
  let p := Path.join d \"x.txt\";
  FS.writeFile p \"one\\ntwo\\n\";
  f ← File.open p \"r\";
  EIO.lift (File.readLineRaw f);
  e0 ← EIO.lift Sys.errno;
  e1 ← EIO.lift (File.closeRaw f);
  e2 ← EIO.lift (File.closeRaw f);
  EIO.lift (File.readLineRaw f);
  e3 ← EIO.lift Sys.errno;
  EIO.lift (IO.println (String.append (errTag e0) (String.append \" \" (String.append (errTag e1) (String.append \" \" (String.append (errTag e2) (String.append \" \" (errTag e3))))))));
  c ← Process.spawn \"cat\" .nil .piped .piped .inherit;
  w1 ← EIO.lift (Child.closeStdinRaw c);
  w2 ← EIO.lift (Child.closeStdinRaw c);
  s1 ← EIO.lift (Child.waitRaw c);
  se1 ← EIO.lift Sys.errno;
  s2 ← EIO.lift (Child.waitRaw c);
  se2 ← EIO.lift Sys.errno;
  FS.removeAll d;
  EIO.lift (IO.println (String.append (errTag w1) (String.append \" \" (String.append (errTag w2) (String.append \" \" (String.append (waitTag s1 se1) (String.append \" \" (waitTag s2 se2)))))))))
"

/-- (conc-02) The safe capture: a handle opened in the child and used only there still
works (an endpoint's `1` closure moves into the fork; a `File` can be moved the same
way, it is just not checked). -/
def concHandleMoved : String := "import Sys
import Session
import MVar
def show (r : Except String (Option String)) : String :=
  match r with
  | .ok opt => match opt with
    | .some s => s
    | .none => \"eof\"
  | .error _ => \"read failed\"
def reader (p : String) (m : MVar String) : IO Unit :=
  IO.bind (File.open p \"r\") (fun r =>
    match r with
    | .ok f =>
        IO.bind (File.readLine f) (fun l =>
          IO.bind (File.close f) (fun _ =>
            MVar.put m (show l)))
    | .error _ => MVar.put m \"open failed\")
def main : IO Unit := EIO.toIO (do
  d ← FS.createTempDir;
  let p := Path.join d \"moved.txt\";
  FS.writeFile p \"moved\\n\";
  m ← EIO.lift (MVar.new (A := String));
  EIO.lift (Chan.fork Proto.done
    (fun ch => Chan.close ch (reader p m))
    (fun ch => Chan.close ch (IO.bind (MVar.take m) (fun s =>
      IO.bind (FS.removeAll d) (fun _ => IO.println s))))))
"

/-- The lock tests of `Tests/tsan/` (the programs `scripts/tsan-conc.sh` also runs under
ThreadSanitizer, 25a): a plain, non-atomic C counter that only the lock protects.
`link_c "lock.c"` resolves relative to `main.wiz`, so both go in the temporary tree. -/
def lockSumFiles : IO (List (String × String)) := do
  pure [("main.wiz", ← IO.FS.readFile "Tests/tsan/lock-sum.wiz"),
        ("lock.c", ← IO.FS.readFile "Tests/tsan/lock.c")]

/-- The contended case: a second thread must wait for the holder to release. -/
def lockOrderFiles : IO (List (String × String)) := do
  pure [("main.wiz", ← IO.FS.readFile "Tests/tsan/lock-order.wiz"),
        ("lock.c", ← IO.FS.readFile "Tests/tsan/lock.c")]

/-- (R2) Build `main` with the C backend and extra C flags, with every library
importable; the program's output, or why it failed. `none`: no C toolchain. Only a
*build* failure that is a `.toolchain` one skips (9c); a program that ran and failed is
returned as `.error` (its stderr may mention a missing file and is still a failure). -/
def cRunLibsFlags (src : String) (cflags : List String) :
    IO (Option (Except Build.RunError String)) := do
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let dir ← IO.FS.createTempDir
  let tc ← toolchain
  match ← Build.runGlobal { tc with cflags := tc.cflags ++ cflags } s "main" dir (timeout := some 120) with
  | .error e =>
    if e.isToolchain then
      skip "no toolchain"
      pure none
    else pure (some (.error e))
  | r => pure (some r)

/-- (R2) Built with `-DWIZ_NO_THREADS` (the Wasm pages' one-thread runtime), `main` stops
with exit 3 and `message` on stderr. -/
def noThreadsFails (src : String) (message : String) : IO Unit := do
  match ← cRunLibsFlags src ["-DWIZ_NO_THREADS"] with
  | none => pure ()
  | some (.ok out) => throw (IO.userError s!"expected the program to stop, it printed: {out}")
  | some (.error e) =>
    unless (e.message.splitOn "the program failed (3)").length > 1 &&
        (e.message.splitOn message).length > 1 do
      throw (IO.userError s!"expected exit 3 and '{message}', got: {e.message}")

def concGroup : Group where
  name := "conc"
  exercise := "lib/Session.wiz, lib/MVar.wiz, runtime threads (stage 25)"
  parallel := true
  cases := [
    { name := "a dependent protocol: the pure semantics `link` runs it", run := fun _ =>
        okLibs (concSum ++ "#eval (link sumProto (client 100) server).1") ["5050"] },
    { name := "the same protocol over a channel, server in a new thread", run := fun _ =>
        cRunLibs (concSum ++ "def main : IO Unit := Chan.fork sumProto serve (fun c =>\n" ++
          "  IO.bind (runClient 1000 c) (fun s => IO.println (Nat.toString s)))") "500500\n" },
    { name := "Proc.runLinked: the model is `link` and starts no thread; compiled code runs one (differential: the fork count must be 1)", run := fun _ => do
        okLibs (concSum ++ "#eval (link sumProto (client 300) server).1") ["45150"]
        cRunLibs (concSum ++ "def main : IO Unit := IO.bind (Proc.runLinked sumProto (client 300) server)\n" ++
          "  (fun r => IO.bind Chan.forks (fun k =>\n" ++
          "    IO.println (String.append (Nat.toString r.1) (String.append \" forks \" (Nat.toString k)))))")
          "45150 forks 1\n" },
    { name := "a chain of 51 threads; endpoints move into children", run := fun _ =>
        cRunLibs concChain "9950\n4950\n" },
    { name := "cancellation is a branch of the protocol", run := fun _ => do
        cRunLibs concCancel "cancelled after 30\n"
        cRunLibs (concCancel.replace "def main : IO Unit := Chan.fork (items 3) (serveItems 3 0) (fun c => client c)" "" ++
          "def main : IO Unit := Chan.fork (items 2) (serveItems 2 0) (fun c => full c)") "all: 3\n" },
    { name := "owned handles (lib/Handle.wiz): released exactly once, no use after release", run := fun _ => do
        cRunLibs ("import Handle\n" ++
          "-- write a file through an owned handle, release it, read it back\n" ++
          "def writeLog (p : String) : EIO Unit :=\n" ++
          "  File.withOwned p \"w\" (fun f o =>\n" ++
          "    Handle.use f o (fun f => File.write f \"one\\n\") (fun r1 o =>\n" ++
          "    Handle.use f o (fun f => File.write f \"two\\n\") (fun r2 o =>\n" ++
          "    File.releaseOwned f o (fun r => IO.pure r))))\n" ++
          "def main : IO Unit := EIO.toIO (EIO.bind FS.createTempDir (fun d =>\n" ++
          "  let p := Path.join d \"log.txt\";\n" ++
          "  EIO.bind (writeLog p) (fun _ => EIO.bind (FS.readFile p) (fun s =>\n" ++
          "    EIO.bind (FS.removeAll d) (fun _ => EIO.lift (IO.print s))))))\n") "one\ntwo\n"
        failsLibs "import Handle\n-- a handle that is never released\ndef leak (p : String) : EIO Unit := File.withOwned p \"w\" (fun f o => EIO.pure ())" "quantity 1"
        failsLibs "import Handle\n-- released twice\ndef twice (p : String) : EIO Unit := File.withOwned p \"w\" (fun f o =>\n  File.releaseOwned f o (fun _ => File.releaseOwned f o (fun r => IO.pure r)))" "quantity 1"
        failsLibs "import Handle\n-- used after release\ndef after (p : String) : EIO Unit := File.withOwned p \"w\" (fun f o =>\n  File.releaseOwned f o (fun _ => Handle.use f o (fun f => File.write f \"x\") (fun r o => File.releaseOwned f o (fun r => IO.pure r))))" "quantity 1"
        failsLibs "import Handle\ndef forge (f : File) : IO (Owned f) := Owned.mint" "private"
        failsLibs "import Handle\n-- a second token for an owned handle (natives-review M6-1): Handle.own is private\ndef twice (p : String) : EIO Unit := File.withOwned p \"w\" (fun f o => Handle.own f (fun o2 =>\n  File.releaseOwned f o (fun _ => Handle.use f o2 (fun f => File.write f \"after release\\n\") (fun r o2 =>\n  File.releaseOwned f o2 (fun r => IO.pure r)))))" "private"
        failsLibs "import Handle\n-- re-owning an existing handle through `with` (natives-review M6-1): Handle.with is private\ndef again (f : File) : EIO Unit := Handle.with (EIO.pure f) (fun g o => File.releaseOwned g o (fun r => IO.pure r))" "private" },
    { name := "IO1: actions with a linear result, `x ⇐ e` in do1; owned handles in direct style", run := fun _ => do
        cRunLibs ("import Handle\n" ++
          "-- direct style: the token is threaded through `do1`\n" ++
          "def writeLog (p : String) : EIO Unit :=\n" ++
          "  File.withOwned p \"w\" (fun f o => do1\n" ++
          "    (r1, o) ⇐ File.writeOwned f o \"one\\n\";\n" ++
          "    (r2, o) ⇐ File.writeOwned f o \"two\\n\";\n" ++
          "    File.closeOwned f o)\n" ++
          "def main : IO Unit := EIO.toIO (EIO.bind FS.createTempDir (fun d =>\n" ++
          "  let p := Path.join d \"log.txt\";\n" ++
          "  EIO.bind (writeLog p) (fun _ => EIO.bind (FS.readFile p) (fun s =>\n" ++
          "    EIO.bind (FS.removeAll d) (fun _ => EIO.lift (IO.print s))))))\n") "one\ntwo\n"
        okLibs "import IO\naxiom Tok : Type\naxiom Tok.new : IO1 Tok\naxiom Tok.use : (1 t : Tok) → (n : Nat) → IO1 ((r : Nat) × Tok)\naxiom Tok.close : (1 t : Tok) → IO Unit\ndef prog : IO Nat := do1\n  t ⇐ Tok.new;\n  (r, t) ⇐ Tok.use t 3;\n  Tok.close t;\n  IO.pure r"
        failsLibs "import IO\naxiom Tok : Type\naxiom Tok.new : IO1 Tok\naxiom Tok.close : (1 t : Tok) → IO Unit\n-- the token is dropped\ndef leak : IO Nat := do1\n  t ⇐ Tok.new;\n  IO.pure 3" "quantity 1"
        failsLibs "import Handle\n-- the token is not given back to a release (a leak)\ndef leak (p : String) : EIO Unit :=\n  File.withOwned p \"w\" (fun f o => do1\n    (r1, o) ⇐ File.writeOwned f o \"one\\n\";\n    IO.pure r1)" "quantity 1" },
    { name := "handles (conc-02): one Child waited on by two threads: both get the status", run := fun _ =>
        cRunLibs concWaitTwice "2\n" },
    { name := "handles (conc-02): a File read while another thread closes it ends in EBADF (stress)", run := fun _ =>
        cRunLibs concFileRace "closed\n" },
    { name := "handles (conc-02): close twice, read after close, wait twice: errors, not a second close", run := fun _ =>
        cRunLibs concHandlePrims "ok ok err err\nok err exit code 0 exit code 0\n" },
    { name := "handles (conc-02): a handle opened and used only in the forked child still works", run := fun _ =>
        cRunLibs concHandleMoved "moved\n" },
    { name := "handles (conc-02): the ω capture the types allow compiles (the runtime serialises it)", run := fun _ =>
        okLibs ("import Sys\nimport Session\n" ++
          "def shared (f : File) : IO Unit := Chan.fork Proto.done\n" ++
          "  (fun c => Chan.close c (IO.bind (File.readLine f) (fun _ => IO.pure ())))\n" ++
          "  (fun c => Chan.close c (IO.bind (File.close f) (fun _ => IO.pure ())))") },
    { name := "Ref: cells owned by linear points-to tokens; a function's type is its triple", run := fun _ => do
        cRunLibs ("import Ref\n" ++
          "-- swap through two tokens: the type is the triple {p ↦ a ⋆ q ↦ b} swap {p ↦ b ⋆ q ↦ a}\n" ++
          "def swap {V B : Type} (p q : Loc V) {0 a b : V} (1 tp : Pts p a) (1 tq : Pts q b)\n" ++
          "    (1 k : (1 tp : Pts p b) → (1 tq : Pts q a) → IO B) : IO B :=\n" ++
          "  Ref.get p tp (fun x ex tp => Ref.get q tq (fun y ey tq =>\n" ++
          "    Ref.set p y tp (fun tp => Ref.set q x tq (fun tq =>\n" ++
          "      k (Pts.cast ey tp) (Pts.cast ex tq)))))\n" ++
          "def main : IO Unit :=\n" ++
          "  Ref.new 1 (fun p tp => Ref.new 2 (fun q tq =>\n" ++
          "    swap p q tp tq (fun tp tq =>\n" ++
          "      Ref.get p tp (fun x _ tp => Ref.get q tq (fun y _ tq =>\n" ++
          "        Ref.free p tp (Ref.free q tq (IO.println (String.append (Nat.toString x) (String.append \" \" (Nat.toString y))))))))))\n") "2 1\n"
        failsLibs "import Ref\n-- a token can't be dropped\ndef leak : IO Unit := Ref.new 1 (fun p tp => IO.pure ())" "quantity 1"
        failsLibs "import Ref\n-- the triple in the type is checked: this isn't swap\ndef notSwap {V B : Type} (p q : Loc V) {0 a b : V} (1 tp : Pts p a) (1 tq : Pts q b)\n    (1 k : (1 tp : Pts p b) → (1 tq : Pts q a) → IO B) : IO B := k tp tq" "mismatch"
        failsLibs "import Ref\n-- tokens can't be forged\ndef forge {V : Type} (l : Loc V) (v : V) : IO ((l : Loc V) × Pts l v) := Ref.newRaw v" "private"
        -- no use after free: the token is gone
        failsLibs "import Ref\ndef uaf : IO Nat := Ref.new 1 (fun p tp => Ref.free p tp (Ref.get p tp (fun x _ tp => Ref.free p tp (IO.pure x))))" "quantity 1"
        failsLibs "import Ref\n-- a stale token can't read: the cell was written, the old token is gone\ndef stale : IO Nat := Ref.new 1 (fun p tp => Ref.set p 5 tp (fun tp' => Ref.get p tp (fun x _ t => Ref.free p t (Ref.free p tp' (IO.pure x)))))" "quantity 1" },
    { name := "MVars and locks: eight threads, one counter", run := fun _ =>
        cRunLibs concCounter "8000\n" },
    { name := "a lock is mutual exclusion: eight threads bump a non-atomic C counter", run := fun _ => do
        linkRun (← lockSumFiles) "counter 8000\noverlap 0\n" },
    { name := "a lock makes the second thread wait (ordering, not timing)", run := fun _ => do
        linkRun (← lockOrderFiles) "holder in\nsecond wants\nholder checks\nholder out\nsecond in\noverlap 0\nsecond got it\n" },
    { name := "the same programs under ThreadSanitizer report no data races", run := fun _ => do
        let tsan := ["-O1", "-g", "-fsanitize=thread"]
        linkRun (← lockSumFiles) "counter 8000\noverlap 0\n" (cflags := tsan)
        linkRun (← lockOrderFiles) "holder in\nsecond wants\nholder checks\nholder out\nsecond in\noverlap 0\nsecond got it\n" (cflags := tsan)
        cRunLibs (← IO.FS.readFile "Tests/tsan/spawn.wiz") "spawned 20\n" (cflags := tsan) },
    { name := "a lazy stream shared between threads", run := fun _ =>
        cRunLibs concStream "3998000\n" },
    { name := "closed definitions (CAFs, 15i) used by eight threads at once: a table and a memoised suspension in it", run := fun _ =>
        cRunLibs concCaf "3198400000\n" },
    { name := "WIZ_NO_THREADS (R2): forking, and the waits only another thread could end (empty MVar, full MVar, held lock), stop with a clear message; MVars and locks that never wait work", run := fun _ => do
        noThreadsFails concCounter "wiz: Chan.fork: threads are not available in this build (WIZ_NO_THREADS)"
        noThreadsFails (concSum ++ "def main : IO Unit := Chan.fork sumProto serve (fun c =>\n" ++
          "  IO.bind (runClient 10 c) (fun s => IO.println (Nat.toString s)))")
          "wiz: Chan.fork: threads are not available in this build (WIZ_NO_THREADS)"
        noThreadsFails ("import IO\nimport MVar\ndef main : IO Unit := do1\n  m ← MVar.new (A := Nat);\n" ++
          "  n ← MVar.take m;\n  IO.println (Nat.toString n)\n")
          "wiz: MVar.take of an empty MVar would wait forever: threads are not available in this build"
        noThreadsFails ("import IO\nimport MVar\n-- a join: read a value another thread was to write\ndef main : IO Unit := do1\n" ++
          "  m ← MVar.new (A := Nat);\n  n ← MVar.read m;\n  IO.println (Nat.toString n)\n")
          "wiz: MVar.read of an empty MVar would wait forever: threads are not available in this build"
        noThreadsFails ("import IO\nimport MVar\n-- a contended cell: it is already full\ndef main : IO Unit := do1\n" ++
          "  m ← MVar.newFull 1;\n  MVar.put m 2\n")
          "wiz: MVar.put into a full MVar would wait forever: threads are not available in this build"
        noThreadsFails ("import IO\nimport MVar\n-- a contended lock: acquired again while held\ndef main : IO Unit := do1\n" ++
          "  l ← Lock.new;\n  Lock.acquire l (fun g =>\n    Lock.acquire l (fun g2 =>\n" ++
          "      Lock.release l g2 (Lock.release l g (IO.pure ()))))\n")
          "wiz: Lock.acquire of a held lock would wait forever: threads are not available in this build"
        match ← cRunLibsFlags ("import IO\nimport MVar\ndef main : IO Unit := do1\n  m ← MVar.newFull 41;\n" ++
            "  l ← Lock.new;\n  k ← MVar.modify m (fun x => x + 1);\n  u ← Lock.with l (IO.pure ());\n" ++
            "  n ← MVar.take m;\n  IO.println (Nat.toString n)\n") ["-DWIZ_NO_THREADS"] with
        | some (.ok out) => checkEq "42\n" out
        | some (.error e) => throw (IO.userError e.message)
        | none => pure () },
    { name := "an endpoint can't be used twice, dropped, or closed twice", run := fun _ => do
        failsLibs (concSum ++ "def twice (1 c : Chan sumProto) : IO Nat :=\n" ++
          "  Chan.send c 1 (fun c' => runClient 1 c)") "quantity 1"
        failsLibs "import IO\nimport Session\ndef leak (1 c : Chan Proto.done) : IO Unit := IO.pure ()" "quantity 1"
        failsLibs "import IO\nimport Session\ndef dupe (1 c : Chan Proto.done) : IO Unit := Chan.close c (Chan.close c (IO.pure ()))" "quantity 1" },
    { name := "a closure that captured an endpoint is linear itself", run := fun _ =>
        failsLibs ("import IO\nimport Session\n" ++
          "def capture (1 c : Chan Proto.done) : Unit → IO Unit := fun _ => Chan.close c (IO.pure ())\n" ++
          "def dupf (1 c : Chan Proto.done) : IO Unit := let f := capture c; IO.bind (f ()) (fun _ => f ())") "quantity" },
    { name := "the protocol is checked: wrong message type, wrong step", run := fun _ => do
        failsLibs (concSum ++ "def bad (1 c : Chan sumProto) : IO Unit :=\n" ++
          "  Chan.send c Bool.true (fun c' => Chan.close c' (IO.pure ()))") "mismatch"
        failsLibs (concSum ++ "def bad (1 c : Chan sumProto) : IO Unit := Chan.close c (IO.pure ())") "mismatch" },
    { name := "endpoints can't be forged, retyped, sent, or stored", run := fun _ => do
        failsLibs "import IO\nimport Session\ndef bad (1 c : Chan Proto.done) : Chan (.send Nat (fun _ => .done)) := c" "mismatch"
        failsLibs ("import IO\nimport Session\ndef bad (1 c : Chan (.send Nat (fun _ => .done))) : IO (Chan (.recv Nat (fun _ => .done))) :=\n" ++
          "  Chan.sendRaw c 1") "private"
        -- an endpoint is not a message (no delegation: the channel graph stays a forest)
        failsLibs ("import IO\nimport Session\ndef bad (1 c : Chan (.send (Chan Proto.done) (fun _ => .done))) (1 d : Chan Proto.done) : IO Unit :=\n" ++
          "  Chan.send c d (fun c' => Chan.close c' (IO.pure ()))") "quantity 1"
        failsLibs ("import IO\nimport Session\nimport MVar\ndef bad (m : MVar (Chan Proto.done)) (1 d : Chan Proto.done) : IO Unit :=\n" ++
          "  MVar.put m d") "quantity 1" },
    { name := "a lock guard and an MVar hole must be given back exactly once", run := fun _ => do
        failsLibs "import IO\nimport MVar\ndef bad (l : Lock) : IO Unit := Lock.acquire l (fun g => IO.pure ())" "quantity 1"
        failsLibs ("import IO\nimport MVar\ndef bad {B : Type} (l : Lock) (b : B) : IO B :=\n" ++
          "  Lock.acquire l (fun g => Lock.release l g (Lock.release l g (IO.pure b)))") "quantity 1"
        failsLibs "import IO\nimport MVar\ndef bad (m : MVar Nat) : IO Nat := MVar.borrow m (fun a h => IO.pure a)" "quantity 1"
        failsLibs "import IO\nimport MVar\ndef forge (l : Lock) : IO (Lock.Guard l) := Lock.acquireRaw l" "private" },
    -- (conc-05) The harness used to treat *any* error containing "No such file" as a
    -- missing toolchain: a program that failed at run time with ENOENT (a Handle test, a
    -- missing fixture, a `Process.output` of a command not on PATH) was recorded as
    -- `⊘ skipped (no toolchain)`, not as a failure. Only a *build* failure that names the
    -- compiler or the headers may skip; the program's stderr never can.
    { name := "a program that fails with ENOENT at run time is a failure, not a missing toolchain", run := fun _ => do
        let src := "import IO\nimport Sys\n" ++
          "def main : IO Unit := IO.bind (IO.ePrintln \"open log.txt: No such file or directory\") (fun _ => Process.exit 3)\n"
        match ← cRunLibsOut src with
        | .ok v => throw (IO.userError s!"the program passed: {v}")
        | .error e =>
          if e.isToolchain then skip "no toolchain"
          else do
            -- the failure reports the exit code and the program's own stderr
            check ((e.message.splitOn "the program failed (3)").length > 1) e.message
            check ((e.message.splitOn "open log.txt: No such file or directory").length > 1) e.message
            -- and `cRunLibs` fails the case instead of recording a skip
            let skipped ← try
                cRunLibs src ""
                pure true
              catch _ => pure false
            check (!skipped) "cRunLibs recorded a run-time failure as a skip" },
    -- (engine-trampoline) Native builds arm no boundary: `Process.exit` still ends the
    -- process with its own code (the Wasm playground is the one place `wiz_stop_run`
    -- catches it, runtime/rt_con.inc).
    { name := "a program's own exit is still the process's exit status", run := fun _ => do
        match ← cRunLibsOut "import IO\nimport Sys\ndef main : IO Unit := Process.exit 3\n" with
        | .ok v => throw (IO.userError s!"the program ran to the end: {v}")
        | .error e =>
          if e.isToolchain then skip "no toolchain"
          else check ((e.message.splitOn "the program failed (3)").length > 1) e.message },
    { name := "a program that writes 'No such file' on stderr and exits 0 still passes", run := fun _ =>
        cRunLibs ("import IO\nimport Sys\n" ++
          "def main : IO Unit := IO.bind (IO.ePrintln \"open log.txt: No such file or directory\") (fun _ => IO.println \"ok\")\n") "ok\n" },
    -- The other half: a build that cannot start the compiler is still a genuine "no
    -- toolchain" skip. Run the passing case above in a child driver whose `--cc` does not
    -- exist, and check that it is reported SKIPPED (exit 3), not failed.
    { name := "a build that cannot find the compiler is still a 'no toolchain' skip", run := fun _ => do
        let self ← IO.appPath
        let target := "a program that writes 'No such file' on stderr and exits 0 still passes"
        let listed ← IO.Process.output { cmd := self.toString, args := #["--list-cases", "=conc"] }
        let some i := (listed.stdout.splitOn "\n").findSome? fun l =>
            match l.splitOn "\t" with
            | [g, i, n] => if g == "conc" && n == target then i.toNat? else none
            | _ => none
          | throw (IO.userError s!"`--list-cases =conc` has no case named {target}")
        let args := #["--run", "conc", toString i, "--cc", "/nonexistent/wiz-test-cc"]
        let r ← IO.Process.output { cmd := self.toString, args }
        check (r.exitCode == 3) s!"exit {r.exitCode}, not 3 (a skip):\n{r.stdout}{r.stderr}"
        check ((r.stdout.splitOn "⊘").length > 1) r.stdout
        check ((r.stdout.splitOn "SKIPPED (no toolchain)").length > 1) r.stdout },
    -- The classifier itself: a build that cannot start a program, or cannot find GMP's
    -- header, is a missing toolchain; a compiler that ran and rejected the program (or a
    -- missing test input file) is not; and no program failure ever is.
    { name := "only a missing compiler, llc, gmp.h or gmp library is classified as 'no toolchain'", run := fun _ => do
        let tc : Wiz.Toolchain := {}
        check (Build.missingToolchain tc "cc failed:\ncould not execute external process 'cc'") "a missing cc"
        check (Build.missingToolchain tc "llc failed:\ncould not execute external process 'llc'") "a missing llc"
        check (Build.missingToolchain tc "cc: no such file or directory (error code: 2)") "cc could not start"
        check (Build.missingToolchain tc "cc failed:\nfatal error: gmp.h: No such file or directory") "gmp.h"
        check (Build.missingToolchain tc "cc failed:\nld: cannot find -lgmp: No such file or directory") "the gmp library at link time"
        check (!Build.missingToolchain tc "cc failed:\ncc: error: c/helper.c: No such file or directory") "a missing link_c file"
        check (!Build.missingToolchain tc "cc failed:\nmain.c:3:1: error: 'x' undeclared") "a rejected program"
        check (!(Build.RunError.run 3 "No such file or directory").isToolchain) "a program failure"
        check (!(Build.RunError.build "cc failed").isToolchain) "a build failure"
        check (!(Build.RunError.timeout).isToolchain) "a timeout"
        check (!(Build.RunError.readback "could not read").isToolchain) "a readback failure" }
  ]

builtin_initialize registerGroup concGroup

end Tests.Elab
