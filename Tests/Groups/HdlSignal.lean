import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- At least one error, and every error mentions `fragment`, with every library
importable (a sized copattern that fails reports its mismatch once per elaboration
attempt, so `failsLibs`'s exactly-one does not fit). -/
def failsLibsEvery (input : String) (fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  if errs.isEmpty then throw (IO.userError "expected an error, got none")
  for e in errs do
    unless (e.splitOn fragment).length > 1 do
      throw (IO.userError s!"error does not mention '{fragment}':\n{e}")

/-- The P2.1 laws of `hdl/src/Hdl/Signal.wiz`, by name. The group `#check`s each, so the
rendered statement is the pinned text: changing a law's statement fails the case. -/
def hdlSignalLaws : List String := [
  "Signal.mapS_at", "Signal.zipWithS_at", "Signal.zipWith3S_at", "Signal.mapS_head", "Signal.mapS_tail", "Signal.zipWithS_head", "Signal.zipWithS_tail", "Signal.zipWith3S_head",
  "Signal.registerS_head", "Signal.registerS_eq_register", "Signal.mapS_id", "Signal.mapS_comp", "Signal.zipWithS_fst", "Signal.zipWithS_snd", "Signal.fix_unfold", "Signal.register_fixed_unique",
  "Signal.fix_pure", "Signal.fix_delay_eq_circuit", "Signal.counter_sample", "Signal.counterLoop_sample", "Signal.Eqv.map", "Signal.Eqv.mapS", "Signal.Eqv.zipWith", "Signal.Eqv.zipWithS",
  "Signal.Eqv.zipWith3S", "Signal.Eqv.register", "Signal.Eqv.registerS", "Signal.Eqv.mealy", "Signal.Eqv.ofCircuit"]

/-- The laws whose `#print axioms` is clean: the algebraic ones. The five that are only
`#check`ed mention a `Circuit` or compute `BitVec` literals, so they inherit the
library's trusted `Hw HwTy.El` instance and `UIntN` natives (the same trust as
`Signal.ofCircuit_at`/`ofCircuit_delay`), not an axiom of the law. -/
def hdlSignalCleanLaws : List String := [
  "Signal.mapS_at", "Signal.zipWithS_at", "Signal.zipWith3S_at", "Signal.mapS_head", "Signal.mapS_tail", "Signal.zipWithS_head", "Signal.zipWithS_tail", "Signal.zipWith3S_head",
  "Signal.registerS_head", "Signal.registerS_eq_register", "Signal.mapS_id", "Signal.mapS_comp", "Signal.zipWithS_fst", "Signal.zipWithS_snd", "Signal.fix_unfold", "Signal.register_fixed_unique",
  "Signal.fix_pure", "Signal.Eqv.map", "Signal.Eqv.mapS", "Signal.Eqv.zipWith", "Signal.Eqv.zipWithS", "Signal.Eqv.zipWith3S", "Signal.Eqv.register", "Signal.Eqv.registerS",
  "Signal.Eqv.mealy"]

/-- `import Hdl.Signal`, the counter's value sample (the `0, 1, 2, …` datum through the
named `Signal.counter`), then the laws. -/
def hdlSignalLawSource : String :=
  "import Hdl.Signal\n#eval Signal.sample 10 (Signal.map BitVec.toNat (Signal.counter (d := ClockDomain.sys)))\n"
    ++ String.join (hdlSignalLaws.map (fun n => s!"#check {n}\n"))
    ++ String.join (hdlSignalCleanLaws.map (fun n => s!"#print axioms {n}\n"))

/-- The expected messages, in order: the counter sample, each law's `#check` text, then
the clean `#print axioms` lines. -/
def hdlSignalLawExpected : List String := [
  "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]",
  "Signal.mapS_at : {d : ClockDomain} → {A : Type} → {B : Type} → (f : A → B) → (s : Signal d A) → (t : Nat) → Signal.at d B (Signal.mapS d A B ∞ f s) t = f (Signal.at d A s t)",
  "Signal.zipWithS_at : {d : ClockDomain} → {A : Type} → {B : Type} → {C : Type} → (f : A → B → C) → (a : Signal d A) → (b : Signal d B) → (t : Nat) → Signal.at d C (Signal.zipWithS d A B C ∞ f a b) t = f (Signal.at d A a t) (Signal.at d B b t)",
  "Signal.zipWith3S_at : {d : ClockDomain} → {A : Type} → {B : Type} → {C : Type} → {D : Type} → (f : A → B → C → D) → (a : Signal d A) → (b : Signal d B) → (c : Signal d C) → (t : Nat) → Signal.at d D (Signal.zipWith3S d A B C D ∞ f a b c) t = f (Signal.at d A a t) (Signal.at d B b t) (Signal.at d C c t)",
  "Signal.mapS_head : {d : ClockDomain} → {A : Type} → {B : Type} → {i : Size} → (f : A → B) → (s : Signal^↑i d A) → f (out s).1 = f (out s).1",
  "Signal.mapS_tail : {d : ClockDomain} → {A : Type} → {B : Type} → (f : A → B) → (s : Signal d A) → scofix (fun j _ => Signal^j d A) (fun j rec idx a => cocon (f (out a).1, rec idx (out a).2.1, fun phantom✝ => (), ())) ∞ (fun phantom✝ => ()) (out s).2.1 = Signal.mapS d A B ∞ f (out s).2.1",
  "Signal.zipWithS_head : {d : ClockDomain} → {A : Type} → {B : Type} → {C : Type} → {i : Size} → (f : A → B → C) → (a : Signal^↑i d A) → (b : Signal^↑i d B) → f (out a).1 (out b).1 = f (out a).1 (out b).1",
  "Signal.zipWithS_tail : {d : ClockDomain} → {A : Type} → {B : Type} → {C : Type} → (f : A → B → C) → (a : Signal d A) → (b : Signal d B) → scofix (fun j _ => Signal^j d A × Signal^j d B) (fun j rec idx p => cocon (f (out p.1).1 (out p.2).1, rec idx ((out p.1).2.1, (out p.2).2.1), fun phantom✝ => (), ())) ∞ (fun phantom✝ => ()) ((out a).2.1, (out b).2.1) = Signal.zipWithS d A B C ∞ f (out a).2.1 (out b).2.1",
  "Signal.zipWith3S_head : {d : ClockDomain} → {A : Type} → {B : Type} → {C : Type} → {D : Type} → {i : Size} → (f : A → B → C → D) → (a : Signal^↑i d A) → (b : Signal^↑i d B) → (c : Signal^↑i d C) → f (out a).1 (out b).1 (out c).1 = f (out a).1 (out b).1 (out c).1",
  "Signal.registerS_head : {d : ClockDomain} → {A : Type} → {i : Size} → (init : A) → Signal^i d A → init = init",
  "Signal.registerS_eq_register : {d : ClockDomain} → {A : Type} → (init : A) → (s : Signal d A) → Signal.Eqv d A (Signal.registerS d A ∞ init s) (Signal.register d A init s)",
  "Signal.mapS_id : {d : ClockDomain} → {A : Type} → (s : Signal d A) → Signal.Eqv d A (Signal.mapS d A A ∞ (fun x => x) s) s",
  "Signal.mapS_comp : {d : ClockDomain} → {A : Type} → {B : Type} → {C : Type} → (f : B → C) → (g : A → B) → (s : Signal d A) → Signal.Eqv d C (Signal.mapS d B C ∞ f (Signal.mapS d A B ∞ g s)) (Signal.mapS d A C ∞ (fun x => f (g x)) s)",
  "Signal.zipWithS_fst : {d : ClockDomain} → {A : Type} → {B : Type} → (a : Signal d A) → (b : Signal d B) → Signal.Eqv d A (Signal.zipWithS d A B A ∞ (fun x y => x) a b) a",
  "Signal.zipWithS_snd : {d : ClockDomain} → {A : Type} → {B : Type} → (a : Signal d A) → (b : Signal d B) → Signal.Eqv d B (Signal.zipWithS d A B B ∞ (fun x y => y) a b) b",
  "Signal.fix_unfold : {d : ClockDomain} → {A : Type} → (g : (i : Size) → Signal^i d A → Signal^↑i d A) → Signal.Eqv d A (Signal.fix d A g) (g ∞ (Signal.fix d A g))",
  "Signal.register_fixed_unique : {d : ClockDomain} → {A : Type} → (init : A) → (h : Signal d A) → Signal.Eqv d A h (Signal.register d A init h) → Signal.Eqv d A h (Signal.pure d A init)",
  "Signal.fix_pure : {d : ClockDomain} → {A : Type} → (init : A) → Signal.Eqv d A (Signal.fix d A (fun i c => Signal.registerS (d.1, d.2.1, d.2.2) A i init (Signal.pureS (d.1, d.2.1, d.2.2) A init i))) (Signal.pure d A init)",
  "Signal.fix_delay_eq_circuit : {d : ClockDomain} → (t : HwTy) → (init : HwTy.El t) → Signal.Eqv d (HwTy.El t) (Signal.fix d (HwTy.El t) (fun i c => Signal.registerS (d.1, d.2.1, d.2.2) (HwTy.El t) i init (Signal.pureS (d.1, d.2.1, d.2.2) (HwTy.El t) init i))) (Signal.ofCircuit d t t (Circuit.delay t init) (Signal.pure d (HwTy.El t) init))",
  "Signal.counter_sample : {d : ClockDomain} → Signal.sample d Nat 10 (Signal.map d (BitVec 8) Nat (BitVec.toNat 8) (Signal.counter d)) = .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 (.cons 6 (.cons 7 (.cons 8 (.cons 9 .nil)))))))))",
  "Signal.counterLoop_sample : {d : ClockDomain} → Signal.sample d Nat 10 (Signal.map d (BitVec 8) Nat (BitVec.toNat 8) (Signal.ofCircuit d (.bits 0) (.bits 8) Signal.counterLoop (Signal.pure d (BitVec 0) (BitVec.ofNat 0 0)))) = .cons 0 (.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 (.cons 6 (.cons 7 (.cons 8 (.cons 9 .nil)))))))))",
  "Signal.Eqv.map : {d : ClockDomain} → {A : Type} → {B : Type} → (f : A → B) → {s : Signal d A} → {s' : Signal d A} → Signal.Eqv d A s s' → Signal.Eqv d B (Signal.map d A B f s) (Signal.map d A B f s')",
  "Signal.Eqv.mapS : {d : ClockDomain} → {A : Type} → {B : Type} → (f : A → B) → {s : Signal d A} → {s' : Signal d A} → Signal.Eqv d A s s' → Signal.Eqv d B (Signal.mapS d A B ∞ f s) (Signal.mapS d A B ∞ f s')",
  "Signal.Eqv.zipWith : {d : ClockDomain} → {A : Type} → {B : Type} → {C : Type} → (f : A → B → C) → {a : Signal d A} → {a' : Signal d A} → Signal.Eqv d A a a' → {b : Signal d B} → {b' : Signal d B} → Signal.Eqv d B b b' → Signal.Eqv d C (Signal.zipWith d A B C f a b) (Signal.zipWith d A B C f a' b')",
  "Signal.Eqv.zipWithS : {d : ClockDomain} → {A : Type} → {B : Type} → {C : Type} → (f : A → B → C) → {a : Signal d A} → {a' : Signal d A} → Signal.Eqv d A a a' → {b : Signal d B} → {b' : Signal d B} → Signal.Eqv d B b b' → Signal.Eqv d C (Signal.zipWithS d A B C ∞ f a b) (Signal.zipWithS d A B C ∞ f a' b')",
  "Signal.Eqv.zipWith3S : {d : ClockDomain} → {A : Type} → {B : Type} → {C : Type} → {D : Type} → (f : A → B → C → D) → {a : Signal d A} → {a' : Signal d A} → Signal.Eqv d A a a' → {b : Signal d B} → {b' : Signal d B} → Signal.Eqv d B b b' → {c : Signal d C} → {c' : Signal d C} → Signal.Eqv d C c c' → Signal.Eqv d D (Signal.zipWith3S d A B C D ∞ f a b c) (Signal.zipWith3S d A B C D ∞ f a' b' c')",
  "Signal.Eqv.register : {d : ClockDomain} → {A : Type} → (init : A) → {s : Signal d A} → {s' : Signal d A} → Signal.Eqv d A s s' → Signal.Eqv d A (Signal.register d A init s) (Signal.register d A init s')",
  "Signal.Eqv.registerS : {d : ClockDomain} → {A : Type} → (init : A) → {s : Signal d A} → {s' : Signal d A} → Signal.Eqv d A s s' → Signal.Eqv d A (Signal.registerS d A ∞ init s) (Signal.registerS d A ∞ init s')",
  "Signal.Eqv.mealy : {d : ClockDomain} → {S : Type} → {I : Type} → {O : Type} → (f : S → I → S × O) → (st : S) → {xs : Signal d I} → {xs' : Signal d I} → Signal.Eqv d I xs xs' → Signal.Eqv d O (Signal.mealy d S I O f st xs) (Signal.mealy d S I O f st xs')",
  "Signal.Eqv.ofCircuit : {d : ClockDomain} → {i : HwTy} → {o : HwTy} → (c : Circuit i o) → {xs : Signal d (HwTy.El i)} → {xs' : Signal d (HwTy.El i)} → Signal.Eqv d (HwTy.El i) xs xs' → Signal.Eqv d (HwTy.El o) (Signal.ofCircuit d i o c xs) (Signal.ofCircuit d i o c xs')",
  "'Signal.mapS_at' does not depend on any axioms",
  "'Signal.zipWithS_at' does not depend on any axioms",
  "'Signal.zipWith3S_at' does not depend on any axioms",
  "'Signal.mapS_head' does not depend on any axioms",
  "'Signal.mapS_tail' does not depend on any axioms",
  "'Signal.zipWithS_head' does not depend on any axioms",
  "'Signal.zipWithS_tail' does not depend on any axioms",
  "'Signal.zipWith3S_head' does not depend on any axioms",
  "'Signal.registerS_head' does not depend on any axioms",
  "'Signal.registerS_eq_register' does not depend on any axioms",
  "'Signal.mapS_id' does not depend on any axioms",
  "'Signal.mapS_comp' does not depend on any axioms",
  "'Signal.zipWithS_fst' does not depend on any axioms",
  "'Signal.zipWithS_snd' does not depend on any axioms",
  "'Signal.fix_unfold' does not depend on any axioms",
  "'Signal.register_fixed_unique' does not depend on any axioms",
  "'Signal.fix_pure' does not depend on any axioms",
  "'Signal.Eqv.map' does not depend on any axioms",
  "'Signal.Eqv.mapS' does not depend on any axioms",
  "'Signal.Eqv.zipWith' does not depend on any axioms",
  "'Signal.Eqv.zipWithS' does not depend on any axioms",
  "'Signal.Eqv.zipWith3S' does not depend on any axioms",
  "'Signal.Eqv.register' does not depend on any axioms",
  "'Signal.Eqv.registerS' does not depend on any axioms",
  "'Signal.Eqv.mealy' does not depend on any axioms"]

/-- Stage 34a: Clash-style signals (`hdl/src/Hdl/Signal.wiz`, lane L1 of the Clash HDL plan).
The positive file is `hdl/examples/hdl-signal.wiz`: counters as Mealy machines, registers
with reset and enable, `Hw` code and a derived `Bundle` on signals, an every-cycle
temporal property, and wiz-rv's baud generator as a signal (`Signal.ofCircuit`), equal to
`Circuit.trace` for every input and to `Circuit.run` on ten cycles by `rfl`. 34b adds
lane L2/L3: a size-preserving `mapS` (a sized copattern compiled to `scofix`), `+`/`if`
at size `i`, `Signal.fix`, the Clash counter and the baud generator check; a register
that keeps the size, a sized copattern that recurses at the same size, and a
combinational loop through `Signal.fix` are size errors. Signals of two clock domains
still do not mix. -/
def hdlSignalGroup : Group where
  name := "hdl-signal"
  exercise := "HDL 34a (Clash-style signals)"
  cases := [
    { name := "34a: signals, registers, Hw code and bundles on signals, the baud generator through Signal.ofCircuit (hdl/examples/hdl-signal.wiz)", run := fun _ => do
        okLibs (← IO.FS.readFile "hdl/examples/hdl-signal.wiz") [
          "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]",
          "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]",
          "[7, 0, 1, 2, 3, 4]",
          "[0, 0, 0, 2, 0, 4]",
          "[7, 7, 7, 2, 3, 4]",
          "[1, 2, 3, 4, 5]",
          "[0, 0, 0, 1, 0]",
          "[0, 0, 0, 1, 0]",
          "[0, 2, 4]",
          "[0, 0, 0, 1, 0, 0, 0, 1, 0, 0]",
          "10"] },
    { name := "34a: a register that keeps the size is rejected (a combinational loop as a size error)", run := fun _ => do
        failsLibs "import Hdl.Signal\ndef badReg {d : ClockDomain} {A : Type} {i : Size} (init : A) (s : (Signal d A)^i) : (Signal d A)^i\n  | .head => init\n  | .tail => s\n" "builds a value of size ↑s or ∞, not i" },
    { name := "34a: a size-preserving map checks (sized copattern → scofix, lane L2)", run := fun _ => do
        okLibs "import Hdl.Signal\ndef mapS {d : ClockDomain} {A B : Type} {i : Size} (f : A → B) (s : (Signal d A)^i) : (Signal d B)^i\n  | .head => f s.head\n  | .tail => mapS f s.tail\n#eval Signal.sample 3 (Signal.map BitVec.toNat (mapS (d := ClockDomain.sys) (i := ∞) (fun (x : BitVec 8) => BitVec.add x (BitVec.ofNat 8 1)) (Signal.pureS (i := ∞) (BitVec.ofNat 8 250))))\n"
          ["[251, 251, 251]"] },
    { name := "34a: a sized copattern that recurses at the same size is a size error, not a loop", run := fun _ => do
        failsLibsEvery "import Hdl.Signal\ndef bad {d : ClockDomain} {i : Size} (s : (Signal d (BitVec 8))^i) : (Signal d (BitVec 8))^i\n  | .head => s.head\n  | .tail => bad s\n" "type mismatch" },
    { name := "34a: signals of two clock domains do not mix", run := fun _ => do
        failsLibs "import Hdl.Signal\ndef crossDomain (s : Signal ClockDomain.sys Nat) : Signal (ClockDomain.named \"fast\") Nat := s\n" "type mismatch" },
    { name := "34b: L3 partial: `pureS` (pure at any size) and a numeral at a sized signal check; at ∞ they are `pure`", run := fun _ => do
        okLibs "import Hdl.Signal\ndef p {d : ClockDomain} {A : Type} (a : A) : Signal d A := Signal.pureS (i := ∞) a\ndef numS {d : ClockDomain} {i : Size} : (Signal d (BitVec 8))^i := 3\ndef reg {d : ClockDomain} {i : Size} (a : Nat) (s : (Signal d Nat)^i) : (Signal d Nat)^(↑i) := Signal.registerS a s\ndef regPure {d : ClockDomain} {i : Size} : (Signal d Nat)^(↑i) := reg 0 (Signal.pureS (i := i) 5)\n#eval Signal.sample 3 (p 5 : Signal ClockDomain.sys Nat)\n#eval Signal.sample 3 (Signal.map BitVec.toNat (numS (d := ClockDomain.sys) (i := ∞) : Signal ClockDomain.sys (BitVec 8)))\n"
          ["[5, 5, 5]", "[3, 3, 3]"] },
    { name := "34b: L3: `+`/`if` at size i, `Signal.fix` counter, and the baud generator (lane L2)", run := fun _ => do
        okLibs "import Hdl.Signal\ndef addS {d : ClockDomain} {i : Size} (a b : (Signal d (BitVec 8))^i) : (Signal d (BitVec 8))^i := a + b\ndef ifS {d : ClockDomain} {i : Size} (c : (Signal d (BitVec 1))^i) (a b : (Signal d (BitVec 8))^i) : (Signal d (BitVec 8))^i := if c then a else b\ndef counter {d : ClockDomain} : Signal d (BitVec 8) := Signal.fix (fun (i : Size) (c : (Signal d (BitVec 8))^i) => Signal.registerS (BitVec.ofNat 8 0) (c + 1))\n#eval Signal.sample 10 (Signal.map BitVec.toNat (counter : Signal ClockDomain.sys (BitVec 8)))\n#eval Signal.sample 3 (Signal.map BitVec.toNat (addS (d := ClockDomain.sys) (i := ∞) (Signal.pureS (i := ∞) (BitVec.ofNat 8 7)) (Signal.pureS (i := ∞) (BitVec.ofNat 8 9))))\n"
          ["[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]",
           "[16, 16, 16]"] },
    { name := "34b: a combinational loop through Signal.fix is a size error (no register in the body)", run := fun _ => do
        -- `c + 1` keeps the size; the body of `fix` must produce `Signal^(↑i)`, and only
        -- `registerS` raises the size. This is the whole point of the lane.
        failsLibs "import Hdl.Signal\ndef bad {d : ClockDomain} : Signal d (BitVec 8) := Signal.fix (fun (i : Size) (c : (Signal d (BitVec 8))^i) => c + 1)\n" "rigid mismatch" },
    { name := "34b: raw `scofix` is a term former (the primitive behind the sized definitions)", run := fun _ => do
        okLibs "import Hdl.Signal\ndef raw {d : ClockDomain} {A : Type} (g : (i : Size) → (Signal d A)^i → (Signal d A)^(↑i)) : Signal d A := scofix (fun (j : Size) => fun _ => Unit) (fun j rec idx a => g j (rec idx a)) ∞ () ()\n"
          [] },
    { name := "34c: P2.1: the mapS/zipWithS/fix laws and Signal.Eqv congruence, pinned by #check and #print axioms (hdl/src/Hdl/Signal.wiz)", run := fun _ => do
        okLibs hdlSignalLawSource hdlSignalLawExpected } ]

builtin_initialize registerGroup hdlSignalGroup

end Tests.Elab
