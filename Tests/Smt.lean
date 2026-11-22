import Wiz
import Tests.Harness
import Tests.Elab

/-!
# Solvers: `sat_decide` with LRAT proofs checked by the kernel (stage 28b)

The group `sat`. Cases that need the solver skip (with the reason) when it is not on PATH;
CI's Nix shell has it (flake.nix: cadical).
-/

open Wiz

set_option compiler.extract_closed false

namespace Tests.Smt

def render (s : CommandState ZeroOneMany) : List String :=
  s.messages.toList.map fun m =>
    s!"{match m.severity with | .error => "error" | .warning => "warning" | .info => "info"}: {m.text}"

/-- Every message of `input`, with all of `lib/` importable, and `--trust-native` if
`trust`. -/
def msgs (input : String) (cfg : Smt.Config := {}) (trust : Bool := false) : IO (List String) := do
  let loader ← Elab.libLoader
  pure (render (runFrontend (R := ZeroOneMany) input
    { loader, trustedModule := Tests.libModule, smt := cfg, trustNative := trust }))

/-- `msgs` with an explicit loader (and modules that are *not* trusted, so the case can
supply its own `Word`): the range case below needs it. -/
def msgsWith (loader : Name → Option String) (input : String) (untrusted : List String := [])
    (cfg : Smt.Config := {}) : IO (List String) := do
  let s := runFrontend (R := ZeroOneMany) input
    { loader, trustedModule := fun m => m != "" && !untrusted.contains m, smt := cfg }
  pure (render s)

/-- A `Word` module that is *not* the library's: `UIntN` has a public constructor and no
range proof. It is the shape a future trusted constructor (the pre-22l
`UIntN.ofBitsTrusted`) would have; the translator must refuse it, not assume its words
are in range (R3). -/
def fakeWord : String :=
  "inductive UIntN (w : Nat) where\n  | mk (n : Nat)\n" ++
  "def UIntN.toNat {w : Nat} : UIntN w → Nat\n  | .mk n => n\n" ++
  "def UIntN.not {w : Nat} : UIntN w → UIntN w\n  | .mk n => .mk 0\n"

def has (ms : List String) (fragment : String) : Bool := ms.any fun m => (m.splitOn fragment).length > 1

def expect (ms : List String) (fragment : String) : IO Unit :=
  unless has ms fragment do throw (IO.userError s!"no message mentions '{fragment}':\n{"\n".intercalate ms}")

def noErrors (ms : List String) : IO Unit := do
  let errs := ms.filter (·.startsWith "error")
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs}")

/-- Is `cmd` on PATH? -/
def onPath (cmd : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd, args := #["--version"] }
    pure (out.exitCode == 0)
  catch _ => pure false

def needs (cmd : String) (k : IO Unit) : IO Unit := do
  if ← onPath cmd then k else skip s!"no {cmd} on PATH (nix develop has it)"

/-! ## Cache entries (R5)

The on-disk format is documented in `Wiz/Smt/Process.lean`: `wiz-smt-cache-v2`, then
`kind proof`, `exit`, `out-sha256`, then the proof, the query and the solver's stdout,
joined by a separator containing NULs. The tests split it themselves so that a format
change is visible here. -/

def cacheSep : String :=
  "\n" ++ String.singleton (Char.ofNat 0) ++ "wiz-smt" ++
    String.singleton (Char.ofNat 0) ++ "\n"

/-- The `.ans` entries of a cache directory. -/
def cacheEntries (dir : String) : IO (List System.FilePath) := do
  let d := System.FilePath.mk dir / "smt"
  if !(← d.isDir) then return []
  let mut out := []
  for e in ← d.readDir do
    if e.path.extension == some "ans" then out := out.push e.path
  pure out

structure Entry where
  meta : String
  proof : String
  query : String
  stdout : String

def parseEntry (txt : String) : Option Entry :=
  match txt.splitOn (cacheSep ++ "query" ++ cacheSep) with
  | [metaAndProof, rest] =>
    match rest.splitOn (cacheSep ++ "stdout" ++ cacheSep), metaAndProof.splitOn cacheSep with
    | [q, out], [meta, proof] => some { meta, proof, query := q, stdout := out }
    | _, _ => none
  | _ => none

def Entry.render (e : Entry) : String :=
  e.meta ++ cacheSep ++ e.proof ++ cacheSep ++ "query" ++ cacheSep ++ e.query ++
    cacheSep ++ "stdout" ++ cacheSep ++ e.stdout

/-- Replace the `out-sha256` line of an entry's metadata. -/
def Entry.withDigest (e : Entry) (digest : String) : Entry :=
  { e with meta := "\n".intercalate ((e.meta.splitOn "\n").map fun l =>
      if l.startsWith "out-sha256 " then "out-sha256 " ++ digest else l) }

/-- The four clauses over two variables, refuted by CaDiCaL (its LRAT, by hand). -/
def tinyCnf : String :=
  "import Sat\n" ++
  "def P (v : Nat) : Sat.Lit := Sat.Lit.mk v .true\ndef N (v : Nat) : Sat.Lit := Sat.Lit.mk v .false\n" ++
  "def cnf : List (List Sat.Lit) := [[P 1, P 2], [N 1, P 2], [P 1, N 2], [N 1, N 2]]\n" ++
  "def proof : List Sat.Step := [Sat.Step.add 5 [P 1] [1, 3], Sat.Step.add 6 [P 2] [5, 2], Sat.Step.add 7 [] [5, 6, 4]]\n"

def group : Group where
  name := "sat"
  exercise := "—"
  cases := [
    { name := "lib/Sat.wiz: the checker and its soundness proof check, with no axioms", run := fun _ => do
        let ms ← msgs ("import Sat\n#print axioms Sat.lratCheck_sound\n#print axioms Sat.decide_sound\n")
        noErrors ms
        expect ms "info: 'Sat.lratCheck_sound' does not depend on any axioms"
        expect ms "info: 'Sat.decide_sound' does not depend on any axioms" },
    { name := "an LRAT proof is checked by the kernel; a wrong one is not accepted", run := fun _ => do
        let ms ← msgs (tinyCnf ++ "def ok : Sat.lratCheck cnf proof = .true := rfl\n" ++
          "def unsat (τ : Nat → Bool) (h : Sat.Cnf.eval τ cnf = .true) : False := Sat.lratCheck_sound cnf proof ok τ h\n")
        noErrors ms
        -- a hint that does not propagate (clause 2 is not unit under ¬1)
        let ms ← msgs (tinyCnf ++ "def bad : Sat.lratCheck cnf [Sat.Step.add 5 [P 1] [2, 3], Sat.Step.add 7 [] [5, 4]] = .true := rfl\n")
        check (has ms "error") s!"a wrong proof was accepted: {ms}"
        -- a proof that never derives the empty clause
        let ms ← msgs (tinyCnf ++ "def bad : Sat.lratCheck cnf [Sat.Step.add 5 [P 1] [1, 3]] = .true := rfl\n")
        check (has ms "error") s!"an unfinished proof was accepted: {ms}" },
    { name := "sat_decide: Bool identities, checked by the kernel, no axioms", run := fun _ => needs "cadical" do
        let ms ← msgs ("import SatTactic\n" ++
          "def demorgan (a b : Bool) : Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) := by sat_decide\n" ++
          "def xorAssoc (a b c : Bool) : Bool.xor a (Bool.xor b c) = Bool.xor (Bool.xor a b) c := by sat_decide\n" ++
          "def excluded : (a : Bool) → Bool.or a (Bool.not a) = .true := by sat_decide\n" ++
          "def atoms (m n : Nat) : Bool.or (Nat.lt m n) (Bool.not (Nat.lt m n)) = .true := by sat_decide\n" ++
          "#print axioms demorgan\n#print axioms atoms\n")
        noErrors ms
        expect ms "info: 'demorgan' does not depend on any axioms"
        expect ms "info: 'atoms' does not depend on any axioms" },
    { name := "sat_decide: circuit equivalence (a 2-bit adder: ripple carry against the majority form)", run := fun _ => needs "cadical" do
        let ms ← msgs ("import SatTactic\n" ++
          "def maj (a b c : Bool) : Bool := Bool.or (Bool.or (Bool.and a b) (Bool.and a c)) (Bool.and b c)\n" ++
          "def carry (a b c : Bool) : Bool := Bool.or (Bool.and a b) (Bool.and c (Bool.xor a b))\n" ++
          "def carry_maj (a b c : Bool) : carry a b c = maj a b c := by\n  unfold carry, maj\n  sat_decide\n" ++
          "def add2 (a0 a1 b0 b1 c : Bool) : Bool.xor (Bool.xor a1 b1) (carry a0 b0 c) = Bool.xor (Bool.xor b1 a1) (maj b0 a0 c) := by\n  unfold carry, maj\n  sat_decide\n" ++
          "#print axioms add2\n")
        noErrors ms
        expect ms "info: 'add2' does not depend on any axioms" },
    { name := "sat_decide with sharing (28c): a 4-bit carry chain over definitions, not unfolded", run := fun _ => needs "cadical" do
        let maj := "def maj (a b c : Bool) : Bool := Bool.or (Bool.or (Bool.and a b) (Bool.and a c)) (Bool.and b c)\n"
        let carry := "def carry (a b c : Bool) : Bool := Bool.or (Bool.and a b) (Bool.and c (Bool.xor a b))\n"
        let c1 := "(carry a2 b2 (carry a1 b1 (carry a0 b0 Bool.false)))"
        let c2 := "(maj b2 a2 (maj b1 a1 (maj b0 a0 Bool.false)))"
        let ms ← msgs ("import SatTactic\n" ++ maj ++ carry ++
          s!"def eq4 (a0 b0 a1 b1 a2 b2 a3 b3 : Bool) : Bool.xor (Bool.xor a3 b3) {c1} = Bool.xor (Bool.xor b3 a3) {c2} := by sat_decide\n" ++
          "#print axioms eq4\n#print axioms Sat.dag_sound\n")
        noErrors ms
        expect ms "info: 'eq4' does not depend on any axioms"
        expect ms "info: 'Sat.dag_sound' does not depend on any axioms" },
    { name := "sat_decide_native (28e): refused without --trust-native", run := fun _ => needs "cadical" do
        -- the tactic asks the solver first and refuses only when it builds the native check
        -- (`SatT.checkProof`), so without cadical the message is the solver's
        let ms ← msgs ("import SatTactic\n" ++
          "def demorgan (a b : Bool) : Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) := by sat_decide_native\n")
        expect ms "error: native evaluation is not enabled"
        expect ms "--trust-native" },
    { name := "sat_decide_native (28e): the check run compiled, an axiom per check that #print axioms lists", run := fun _ => needs "cadical" do
        let ms ← msgs ("import SatTactic\n" ++
          "def demorgan (a b : Bool) : Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) := by sat_decide_native\n" ++
          "def use (a b : Bool) : Bool.not (Bool.and a b) = Bool.or (Bool.not a) (Bool.not b) := demorgan a b\n" ++
          "#print axioms demorgan\n#print axioms use\n#print axioms Sat.dag_sound\n") (trust := true)
        noErrors ms
        expect ms "not checked by the kernel"
        expect ms "info: 'demorgan' depends on axioms: [demorgan.sat3.native✝]"
        expect ms "info: 'use' depends on axioms: [demorgan.sat3.native✝]"
        expect ms "info: 'Sat.dag_sound' does not depend on any axioms" },
    { name := "sat_decide_native (28e): the same fragment (a 4-bit carry chain); a false goal is the solver's", run := fun _ => needs "cadical" do
        let maj := "def maj (a b c : Bool) : Bool := Bool.or (Bool.or (Bool.and a b) (Bool.and a c)) (Bool.and b c)\n"
        let carry := "def carry (a b c : Bool) : Bool := Bool.or (Bool.and a b) (Bool.and c (Bool.xor a b))\n"
        let c1 := "(carry a2 b2 (carry a1 b1 (carry a0 b0 Bool.false)))"
        let c2 := "(maj b2 a2 (maj b1 a1 (maj b0 a0 Bool.false)))"
        let ms ← msgs ("import SatTactic\n" ++ maj ++ carry ++
          s!"def eq4 (a0 b0 a1 b1 a2 b2 a3 b3 : Bool) : Bool.xor (Bool.xor a3 b3) {c1} = Bool.xor (Bool.xor b3 a3) {c2} := by sat_decide_native\n" ++
          "#print axioms eq4\n") (trust := true)
        noErrors ms
        expect ms "info: 'eq4' depends on axioms: [eq4.sat3.native✝]"
        let ms ← msgs ("import SatTactic\ndef wrong (a b : Bool) : Bool.and a b = Bool.or a b := by sat_decide_native\n") (trust := true)
        expect ms "sat_decide: the goal is false; a counterexample:"
        let ms ← msgs ("import SatTactic\ndef notEq (a : Bool) : Bool := by sat_decide_native\n") (trust := true)
        expect ms "sat_decide: the goal is not an equation of booleans" },
    { name := "bv_decide (28d): word equations by bit-blasting, checked by the kernel", run := fun _ => needs "cadical" do
        let ms ← msgs ("import BvDecide\nimport BitVec\n" ++
          "def t1 (x y : UIntN 4) : UIntN.land x (UIntN.lor x y) = x := by bv_decide\n" ++
          "def t2 (x y : UIntN 4) : UIntN.xor x (UIntN.xor y x) = y := by bv_decide\n" ++
          "def t3 (x : UIntN 4) : UIntN.lor x (UIntN.ofNat 4 15) = UIntN.ofNat 4 15 := by bv_decide\n" ++
          "def t4 (x y : BitVec 4) : BitVec.and x y = BitVec.and y x := by bv_decide\n" ++
          "#print axioms t1\n")
        noErrors ms
        -- (UIntN's own seal and natives only: no axiom from the proof)
        expect ms "info: 't1' depends on axioms: [native UIntN.toNat := UIntN.toBits, UIntN.seal✝"
        check (!(has ms "smt✝") && !(has ms "native✝")) s!"bv_decide used an axiom: {ms}"
        let ms ← msgs ("import BvDecide\ndef bad (x y : UIntN 4) : UIntN.land x y = UIntN.lor x y := by bv_decide\n")
        expect ms "the goal is false; a counterexample" },
    { name := "bv_decide (28d): + - ~~~ neg and shifts, at widths 1, 3 and 4 (their BitVec names and the shift boundaries too)", run := fun _ => needs "cadical" do
        let ms ← msgs ("import BvDecide\nimport BitVec\n" ++
          "def a1 (x y : UIntN 4) : UIntN.add x y = UIntN.add y x := by bv_decide\n" ++
          "def a2 (x : UIntN 4) : UIntN.not (UIntN.not x) = x := by bv_decide\n" ++
          "def a3 (x y : UIntN 3) : UIntN.sub (UIntN.add x y) y = x := by bv_decide\n" ++
          "def a4 (x : UIntN 4) : UIntN.add x (UIntN.neg x) = UIntN.zero 4 := by bv_decide\n" ++
          "def a5 (x : UIntN 3) : UIntN.shiftLeft x 1 = UIntN.add x x := by bv_decide\n" ++
          "def a6 (x : UIntN 4) : UIntN.shiftRight (UIntN.shiftLeft x 2) 2 = UIntN.land x (UIntN.ofNat 4 3) := by bv_decide\n" ++
          "def a7 (x : UIntN 4) : UIntN.add x (UIntN.not x) = UIntN.ofNat 4 15 := by bv_decide\n" ++
          "def a8 (x y : UIntN 1) : UIntN.add x y = UIntN.xor x y := by bv_decide\n" ++
          "def a9 (x y : BitVec 4) : BitVec.sub x y = BitVec.add x (BitVec.neg y) := by bv_decide\n" ++
          "def a10 (x : BitVec 4) : BitVec.not (BitVec.not x) = x := by bv_decide\n" ++
          "def a11 (x : BitVec 4) : BitVec.shl x 0 = x := by bv_decide\n" ++
          "def a12 (x : BitVec 4) : BitVec.shl x 4 = BitVec.zero 4 := by bv_decide\n" ++
          "def a13 (x : BitVec 4) : BitVec.lshr x 4 = BitVec.zero 4 := by bv_decide\n" ++
          "def a14 : UIntN.add (UIntN.ofNat 4 3) (UIntN.ofNat 4 5) = UIntN.ofNat 4 8 := by bv_decide\n" ++
          "#print axioms a3\n#print axioms Bits.wadd_bit\n#print axioms Bits.wsub_bit\n#print axioms Bits.wshr_out\n")
        noErrors ms
        check (!(has ms "smt✝") && !(has ms "native✝") && !(has ms "sorry")) s!"bv_decide used an axiom: {ms}"
        -- only Word's own natives (not the solver, not a new axiom):
        expect ms "info: 'a3' depends on axioms:"
        check (has ms "native UIntN.add := UIntN.addNative") s!"a3's proof does not rest on UIntN.add: {ms}"
        check (has ms "native UIntN.sub := UIntN.subNative") s!"a3's proof does not rest on UIntN.sub: {ms}"
        expect ms "info: 'Bits.wadd_bit' depends on axioms:"
        check (has ms "native UIntN.add := UIntN.addNative") s!"wadd_bit's proof does not rest on UIntN.add: {ms}"
        expect ms "info: 'Bits.wshr_out' depends on axioms:"
        check (has ms "native UIntN.shiftRight := UIntN.shiftRightNative") s!"wshr_out's proof does not rest on UIntN.shiftRight: {ms}"
        let ms ← msgs ("import BvDecide\ndef bad (x y : UIntN 4) : UIntN.add x y = UIntN.sub x y := by bv_decide\n")
        expect ms "the goal is false; a counterexample" },
    { name := "bv_decide (28d): unsigned comparisons in boolean goals", run := fun _ => needs "cadical" do
        let ms ← msgs ("import BvDecide\nimport BitVec\n" ++
          "def c1 (x y : UIntN 4) : Bool.or (UIntN.lt x y) (UIntN.le y x) = .true := by bv_decide\n" ++
          "def c2 (x : UIntN 4) : UIntN.lt x x = .false := by bv_decide\n" ++
          "def c3 (x : UIntN 4) : UIntN.lt x (UIntN.add x (UIntN.ofNat 4 1)) = Bool.not (UIntN.le (UIntN.ofNat 4 15) x) := by bv_decide\n" ++
          "def c4 (x y : UIntN 3) : UIntN.le (UIntN.land x y) x = .true := by bv_decide\n" ++
          "def c5 (x y : BitVec 4) : BitVec.ult x y = Bool.not (BitVec.ule y x) := by bv_decide\n" ++
          "#print axioms c3\n#print axioms Bits.wlt_bits\n")
        noErrors ms
        check (!(has ms "smt✝") && !(has ms "native✝") && !(has ms "sorry")) s!"bv_decide used an axiom: {ms}"
        let ms ← msgs ("import BvDecide\ndef bad (x y : UIntN 4) : UIntN.lt x (UIntN.add x y) = .true := by bv_decide\n")
        expect ms "the goal is false; a counterexample" },
    { name := "sat_decide: a false goal fails with a counterexample", run := fun _ => needs "cadical" do
        let ms ← msgs ("import SatTactic\ndef wrong (a b : Bool) : Bool.and a b = Bool.or a b := by sat_decide\n")
        expect ms "sat_decide: the goal is false; a counterexample:" },
    { name := "the flags: --sat-solver and --solver-timeout are taken and passed on; not settings", run := fun _ => do
        let (t, rest) := ({} : Toolchain).parseFlags ["--sat-solver", "kissat", "--solver-timeout", "500", "check", "f.wiz"]
        checkEq ["check", "f.wiz"] rest
        checkEq "kissat" t.smt.satSolver
        checkEq 500 t.smt.timeoutMs
        let (t', _) := ({} : Toolchain).parseFlags t.toFlags
        check (t'.smt == t.smt) "toFlags does not round-trip"
        let (u, _) := ({} : Toolchain).parseFlags ["check", "f.wiz"]
        check (Cache.smtKey u.smt == none) "the default settings must not change cache keys"
        check (Cache.smtKey t.smt != none) "the solver settings are not in the cache keys"
        -- a grail file (`Toolchain.set`) can't name a program for wiz to run
        check (({} : Toolchain).set "sat-solver" "/bin/sh").isNone "sat-solver is a setting" }
  ]

def trusted : Smt.Config := { trust := true }

def smtGroup : Group where
  name := "smt"
  exercise := "—"
  cases := [
    { name := "smt: refused without --trust-smt", run := fun _ => do
        let ms ← msgs ("import Prelude\ndef t (a b : Nat) : Nat.add a b = Nat.add b a := by smt\n")
        expect ms "error: SMT solving is not enabled"
        expect ms "--trust-smt" },
    { name := "smt: linear Nat arithmetic, Bool, hypotheses; an axiom per use with the solver's name", run := fun _ => needs "z3" do
        let ms ← msgs ("import Prelude\n" ++
          "def comm (a b : Nat) : Nat.add a b = Nat.add b a := by smt\n" ++
          "def trans (a b c : Nat) (h₁ : Nat.lt a b = .true) (h₂ : Nat.lt b c = .true) : Nat.lt a c = .true := by smt\n" ++
          "def sub0 (a : Nat) : Nat.sub a (Nat.add a 1) = 0 := by smt\n" ++
          "def div0 (a : Nat) : Nat.div a 0 = 0 := by smt\n" ++
          "def mod0 (a : Nat) : Nat.mod a 0 = a := by smt\n" ++
          "def b (x y : Bool) : Bool.and x y = Bool.and y x := by smt\n" ++
          "def use (a b : Nat) : Nat.add a b = Nat.add b a := comm a b\n" ++
          "#print axioms comm\n#print axioms use\n") trusted
        noErrors ms
        expect ms "comm is accepted on the word of an SMT solver (--trust-smt)"
        expect ms "info: 'comm' depends on axioms: [comm.smt✝1⟨z3"
        expect ms "info: 'use' depends on axioms: [comm.smt✝1⟨z3"
        expect ms "trusted are the solver named in the axiom" },
    { name := "smt: Nat's truncated subtraction and division by zero are Wiz's, not SMT-LIB's", run := fun _ => needs "z3" do
        -- over the integers `a - b + b = a`; in Wiz `0 - 1 + 1 = 1`
        let ms ← msgs ("import Prelude\ndef wrong (a b : Nat) : Nat.add (Nat.sub a b) b = a := by smt\n") trusted
        expect ms "smt: the solver found a counterexample"
        -- SMT-LIB's `bvudiv x 0` is all ones; Wiz's `x / 0` is 0
        let ms ← msgs ("import Word\ndef d (x : UIntN 8) : UIntN.div x (UIntN.zero 8) = UIntN.zero 8 := by smt\n") trusted
        noErrors ms },
    { name := "smt: words, with no range hypotheses (every UIntN is in range, 22l)", run := fun _ => needs "z3" do
        let ms ← msgs ("import Word\n" ++
          "def nn (x : UIntN 8) : UIntN.not (UIntN.not x) = x := by smt\n" ++
          "def ac (x y : UIntN 16) : UIntN.add x y = UIntN.add y x := by smt\n" ++
          "def xs (x : UIntN 32) : UIntN.xor x x = UIntN.zero 32 := by smt\n" ++
          "def lt (x : UIntN 8) : Nat.lt (UIntN.toNat x) 256 = .true := by smt\n") trusted
        noErrors ms
        let ms ← msgs ("import Word\ndef bad (x : UIntN 8) : UIntN.add x x = x := by smt\n") trusted
        expect ms "smt: the solver found a counterexample" },
    { name := "smt: only the library's definitions are read as SMT operations", run := fun _ => needs "z3" do
        -- a file of its own `UIntN` (no `import Word`): not bit vectors
        let ms ← msgs ("import Prelude\ninductive UIntN (w : Nat) where\n  | mk (n : Nat)\n" ++
          "def UIntN.toNat {w : Nat} : UIntN w → Nat\n  | .mk n => n\ndef UIntN.not {w : Nat} : UIntN w → UIntN w\n  | .mk n => .mk 0\n" ++
          "def fake (x : UIntN 8) : UIntN.not (UIntN.not x) = x := by smt\n") trusted
        expect ms "smt: the goal is not in the fragment" },
    { name := "R3: a word type that is not sealed with a private constructor is refused, not assumed in range", run := fun _ => needs "z3" do
        -- The fake `Word`'s `UIntN` has a public constructor and no range proof; its
        -- `not` is constant 0, so `not (not x) = x` is FALSE. Read as an 8-bit vector
        -- with the range assumed, z3 proves it unsat and `smt` would accept a false
        -- theorem. The translation must refuse the type instead (R3).
        let loader : Name → Option String := fun m => if m == "Word" then some fakeWord else none
        let ms ← msgsWith loader ("import Word\n" ++
          "def bad (x : UIntN 8) : UIntN.not (UIntN.not x) = x := by smt\n") ["Word"] trusted
        expect ms "error: smt: UIntN is not sealed with a private constructor"
        -- the library's sealed `UIntN` still translates (the words case above checks
        -- that the translated goal is actually proved by the solver)
        let ms ← msgs ("import Word\ndef ok (x : UIntN 8) : UIntN.not (UIntN.not x) = x := by smt\n") trusted
        noErrors ms },
    { name := "R3: the seal/private-constructor predicate holds for lib/Word's UIntN (and not for an unsealed type)", run := fun _ => do
        let loader ← Elab.libLoader
        let s := runFrontend (R := ZeroOneMany) "import Word\n" { loader, trustedModule := Tests.libModule }
        check (Smt.sealedPrivate s.globals "UIntN")
          "lib/Word's UIntN does not look sealed: the SMT range check would refuse every word"
        check (!Smt.sealedPrivate s.globals "Nat") "Nat (no seal, no private constructor) satisfies the seal check" },
    { name := "smt: a false goal fails with a counterexample in the user's names", run := fun _ => needs "z3" do
        let ms ← msgs ("import Prelude\ndef wrong (apples pears : Nat) (h : Nat.lt apples pears = .true) : Nat.lt pears apples = .true := by smt\n") trusted
        expect ms "smt: the solver found a counterexample"
        expect ms "apples" },
    { name := "smt: a constructor is read by its position, not its label (smt-review B1)", run := fun _ => needs "z3" do
        -- `Flip.true` is `Bool.false` (tag 0): types are structural, labels cosmetic
        let ms ← msgs ("import Prelude\ninductive Flip where\n  | true\n  | false\ndef x : Bool := Flip.true\n" ++
          "def isFalse : x = Bool.false := rfl\ndef bad (b : Bool) (h : b = x) : b = Bool.true := by smt\n") trusted
        expect ms "smt: the solver found a counterexample"
        let ms ← msgs ("import Prelude\ninductive Flip where\n  | true\n  | false\n" ++
          "def bad3 (b : Bool) (h : Bool.and b (Flip.false : Bool) = .true) : False := by smt\n") trusted
        expect ms "smt: the solver found a counterexample"
        let ms ← msgs ("import Prelude\ninductive Flip where\n  | true\n  | false\ndef x : Bool := Flip.true\n" ++
          "def good (b : Bool) (h : b = x) : b = Bool.false := by smt\n") trusted
        noErrors ms },
    { name := "smt: universe parameters of the definition are the axiom's (smt-review B4)", run := fun _ => needs "z3" do
        let ms ← msgs ("import Prelude\ndef lp.{u} (A : Type u) (a : Nat) : Nat.add a 0 = a := by smt\n#print axioms lp\n") trusted
        noErrors ms
        expect ms "lp.smt✝1⟨z3" },
    { name := "the flags: --trust-smt and --smt-solver are taken and passed on; not settings", run := fun _ => do
        let (t, rest) := ({} : Toolchain).parseFlags ["--trust-smt", "--smt-solver", "cvc5", "check", "f.wiz"]
        check t.trustSmt "--trust-smt not taken"
        checkEq ["check", "f.wiz"] rest
        checkEq "cvc5" t.smt.solver
        let (t', _) := ({} : Toolchain).parseFlags t.toFlags
        check (t'.trustSmt && t'.smt == t.smt) "toFlags does not round-trip"
        let (u, _) := ({} : Toolchain).parseFlags ["check", "f.wiz"]
        check (!u.trustSmt) "--trust-smt must be off by default"
        check (({} : Toolchain).set "smt-solver" "/bin/sh").isNone "smt-solver is a setting"
        check (({} : Toolchain).set "trust-smt" "true").isNone "trust-smt is a setting" },
    { name := "the answer cache is keyed by SHA-256 (known vectors)", run := fun _ => do
        checkEq "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" (Smt.Sha256.hex "")
        checkEq "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" (Smt.Sha256.hex "abc")
        checkEq "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
          (Smt.Sha256.hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") },
    { name := "R5: sat_decide with a cache stores an LRAT certificate, and a SAT model is not cached", run := fun _ => needs "cadical" do
        let dir ← IO.FS.createTempDir
        let cfg : Smt.Config := { cacheDir := some dir.toString }
        let ms ← msgs ("import SatTactic\ndef t (a b : Bool) : Bool.and a b = Bool.and b a := by sat_decide\n") cfg
        noErrors ms
        let es ← cacheEntries dir.toString
        check (es.length == 1) s!"expected one certificate entry, got {es.length}"
        let txt ← IO.FS.readFile es.head!
        check ((txt.splitOn "wiz-smt-cache-v2").length > 1) s!"an entry without the v2 marker: {txt.take 200}"
        check ((txt.splitOn "kind proof").length > 1) "the entry does not say it is a proof"
        check ((txt.splitOn "out-sha256 ").length > 1) "the entry does not record the proof's digest"
        check ((← parseEntry txt).isSome) s!"the test cannot read its own entry format: {txt.take 200}"
        -- a SAT answer (exit 10, no proof file) must not become a cached counterexample
        let ms ← msgs ("import SatTactic\ndef bad (a b : Bool) : Bool.and a b = Bool.or a b := by sat_decide\n") cfg
        expect ms "sat_decide: the goal is false; a counterexample:"
        check ((← cacheEntries dir.toString).length == 1) "a SAT model was cached as a verdict" },
    { name := "R5: a cached proof is re-checked on load (a tampered proof with a matching digest is used and rejected)", run := fun _ => needs "cadical" do
        let dir ← IO.FS.createTempDir
        let cfg : Smt.Config := { cacheDir := some dir.toString }
        let src := "import SatTactic\ndef t (a b : Bool) : Bool.and a b = Bool.and b a := by sat_decide\n"
        noErrors (← msgs src cfg)
        let es ← cacheEntries dir.toString
        check (es.length == 1) s!"expected one certificate entry, got {es.length}"
        let some e ← parseEntry (← IO.FS.readFile es.head!)
          | throw (IO.userError "cannot parse the cache entry")
        -- replace the proof and update the digest: the entry is still served (its bytes
        -- match the record), and only the re-parse/kernel check can reject it
        let bad : Entry := e.withDigest (Smt.Sha256.hexBytes "this is not LRAT".toUTF8)
        IO.FS.writeFile es.head! (bad.render)
        let ms ← msgs src cfg
        expect ms "LRAT: bad line"
        -- replace the proof without updating the digest: the entry is a miss, so the
        -- solver runs again and the goal is proved
        IO.FS.writeFile es.head! ({ e with proof := "also not LRAT" }.render)
        noErrors (← msgs src cfg) },
    { name := "R5: a cache entry without a certificate (a legacy verdict) is refused", run := fun _ => needs "z3" do
        let dir ← IO.FS.createTempDir
        let cfg : Smt.Config := { cacheDir := some dir.toString }
        let args := ["-smt2", "-T:10", "{in}"]
        let input := "(set-logic QF_LIA)\n(assert false)\n(check-sat)\n"
        let id ← Smt.solverIdentity "z3"
        let key := Smt.queryKey id args input
        let ansFile := System.FilePath.mk s!"{dir}/smt/{key}.ans"
        IO.FS.createDirAll ansFile.parent.getD "."
        -- the pre-R5 format: exit, stdout, out-file, query. It claims `sat` for a
        -- script that is `unsat`: replaying it would be wrong, so it must be ignored.
        let query := id ++ cacheSep ++ String.intercalate cacheSep args ++ cacheSep ++ input
        IO.FS.writeFile ansFile s!"0{cacheSep}sat{cacheSep}{cacheSep}query{cacheSep}{query}"
        match Smt.runSolver cfg "z3" args input "smt2" true (fun _ => true) with
        | .ok (_, a) =>
          check (a.stdout.contains "unsat")
            s!"the forged legacy verdict was replayed: stdout `{a.stdout.trimAscii.toString}`"
        | .error e => throw (IO.userError s!"running z3 failed: {e}") },
    { name := "R5: only a non-empty proof file is cached; a verdict (no {out}) is never written", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let cfg : Smt.Config := { cacheDir := some dir.toString }
        let mk (body : String) : List String := ["-c", body, "sh", "{out}"]
        -- (a) `wantOut = false`: the answer is a verdict, so it must not be kept
        let r ← Smt.runSolver cfg "sh" (mk "printf 'unsat\\n'; exit 0") "q" "smt2" false (fun a => a.exitCode == 0)
        (match r with | .ok _ => pure () | .error e => throw (IO.userError e))
        check ((← cacheEntries dir.toString).isEmpty) "a verdict (wantOut = false) was cached"
        -- (b) `wantOut = true` but the solver wrote no proof: also not a certificate
        let r ← Smt.runSolver cfg "sh" (mk "printf 's UNSATISFIABLE\\n'; : > \"$1\"; exit 20") "q" "smt2" true (fun a => a.exitCode == 20)
        (match r with | .ok _ => pure () | .error e => throw (IO.userError e))
        check ((← cacheEntries dir.toString).isEmpty) "an answer with an empty proof file was cached"
        -- (c) a non-empty proof is cached, and a changed proof with a stale digest is a miss
        let marker := (dir / "run-marker").toString
        let body := s!"if [ -f {marker} ]; then exit 3; else printf 'PROOF1' > \"$1\"; exit 20; fi"
        let r ← Smt.runSolver cfg "sh" (mk body) "q2" "smt2" true (fun a => a.exitCode == 20)
        let (_, a) ← match r with
          | .ok x => pure x
          | .error e => throw (IO.userError e)
        checkEq "PROOF1" a.outFile
        let es ← cacheEntries dir.toString
        check (es.length == 1) s!"expected one entry, got {es.length}"
        let path := es.head!
        let some e ← parseEntry (← IO.FS.readFile path) | throw (IO.userError "cannot parse the entry")
        -- (c1) digest updated: served from the cache, without running the solver
        IO.FS.writeFile (System.FilePath.mk marker) ""
        IO.FS.writeFile path ((e.withDigest (Smt.Sha256.hexBytes "PROOF2".toUTF8)).render)
        match Smt.runSolver cfg "sh" (mk body) "q2" "smt2" true (fun a => a.exitCode == 20) with
        | .ok (_, a) => checkEq "PROOF2" a.outFile
        | .error e => throw (IO.userError s!"a digest-matching cached proof was not served: {e}")
        -- (c2) digest stale: a miss, so the solver runs (and the marker makes it exit 3)
        IO.FS.writeFile path ({ e with proof := "PROOF3" }.render)
        match Smt.runSolver cfg "sh" (mk body) "q2" "smt2" true (fun a => a.exitCode == 20) with
        | .ok (_, a) => check (a.exitCode == 3) "a proof with a stale digest was served"
        | .error _ => pure () },
    { name := "lib/ never uses smt", run := fun _ => do
        for e in ← System.FilePath.readDir "lib" do
          if e.path.extension == some "wiz" && e.path.fileName != some "Prelude.wiz" then
            let src ← IO.FS.readFile e.path
            let ws := ((src.replace "\n" " ").replace ";" " ").splitOn " "
            check (!ws.contains "smt") s!"{e.path} uses the smt tactic" }
  ]

def groups : List Group := [group, smtGroup]

end Tests.Smt
