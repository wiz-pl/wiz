import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## Quantity-polymorphic results (`ResultQ`, `ResultH`)

`ResultQ q A` (lib/Result.wiz) is `Result` with the success value at `%q`: `q = ω` is
`Result` definitionally, `q = 1` has a linear success value, `q = 0` an erased one.
`ResultH q B H` (lib/Region.wiz) is `Result1` with the handle on both branches at `%q`;
`q = 1` is `Result1` definitionally. See `wiz-notes/result-q.md`. -/

def rqPrelude : String := "import Result\nimport Region\n"

/-- The aliases: `ResultQ ω`/`Result` and `ResultH 1`/`Result1` are convertible both
ways (`refl`), and the conversion functions round-trip and compute. -/
def rqAliases : String := rqPrelude ++
  "def toR (x : ResultQ ω Nat) : Result Nat := x\n" ++
  "def fromR (x : Result Nat) : ResultQ ω Nat := x\n" ++
  "def eqR (A : Type) : ResultQ ω A = Result A := refl (Result A)\n" ++
  "def eqRb (A : Type) : Result A = ResultQ ω A := refl (ResultQ ω A)\n" ++
  "def eqH (B H : Type) : ResultH 1 B H = Result1 B H := refl (Result1 B H)\n" ++
  "def eqHb (B H : Type) : Result1 B H = ResultH 1 B H := refl (ResultH 1 B H)\n" ++
  "def throughR (x : Result Nat) : Result Nat := ResultQ.toResult (Result.toResultQ x)\n" ++
  "def throughMap (x : Result Nat) : Result Nat := ResultQ.toResult (ResultQ.map (fun (ω n : Nat) => n) (Result.toResultQ x))\n" ++
  "def throughBind (x : Result Nat) : Result Nat := ResultQ.toResult (ResultQ.bind (Result.toResultQ x) (fun (ω n : Nat) => .ok n))\n" ++
  "#reduce throughR (.ok 5)\n" ++
  "#reduce throughMap (.ok 5)\n" ++
  "#reduce throughBind (.ok 5)\n" ++
  "#reduce throughR (.err .overflow)\n"

/-- Construction and elimination at `q = ω`, `q = 1` and `q = 0`. -/
def rqInstances : String := rqPrelude ++
  "def w : ResultQ ω Nat := ResultQ.map Nat.succ (.ok 20)\n" ++
  "def wElim : Nat := ResultQ.elim (fun n => n) (fun _ => 0) w\n" ++
  "def z : ResultQ 0 Nat := .ok 99\n" ++
  "def zElim : Nat := match z with | .ok _ => 7 | .err _ => 0\n" ++
  "def o : ResultQ 1 Nat := ResultQ.bind (.ok 40) (fun (1 n : Nat) => .ok n)\n" ++
  "def oMap : ResultQ 1 Nat := ResultQ.map (fun (1 n : Nat) => n) o\n" ++
  "def oElim : Nat := ResultQ.elim (fun (1 n : Nat) => n) (fun _ => 0) oMap\n" ++
  "#reduce wElim\n#reduce zElim\n#reduce oElim\n"

/-- `ResultH` at `q = ω` (a droppable handle) and `q = 1` (linear). -/
def rqHandle : String := rqPrelude ++
  "def hW : ResultH ω Nat Nat := ResultH.map Nat.succ (.ok 1 2)\n" ++
  "#reduce match hW with | .ok n h => Nat.add n h | .err _ h => h\n" ++
  "inductive Tok where | mk\n" ++
  "def endTok (1 t : Tok) : Nat := match t with | .mk => 0\n" ++
  "def linOk (1 t : Tok) : ResultH 1 Nat Tok := .ok 42 t\n" ++
  "def linBind (1 t : Tok) : ResultH 1 Nat Tok :=\n" ++
  "  ResultH.bind (linOk t) (fun n (1 u : Tok) => .ok (Nat.add n 1) u)\n" ++
  "def asR1 (1 t : Tok) : Result1 Nat Tok := linBind t\n" ++
  "def rt1 (1 x : Result1 Nat Tok) : Result1 Nat Tok := ResultH.toResult1 (Result1.toResultH x)\n" ++
  "def linElim (1 t : Tok) : Nat :=\n" ++
  "  ResultH.elim (fun n (1 u : Tok) => endTok u) (fun _ (1 u : Tok) => endTok u) (linBind t)\n" ++
  "#reduce linElim (.mk)\n"

/-- The compiled program: `q = ω`, `q = 1`, `q = 0` and a `ResultH 1`. -/
def rqRun : String := rqPrelude ++ "import IO\n" ++
  "inductive Tok where | mk\n" ++
  "def endTok (1 t : Tok) : Nat := match t with | .mk => 5\n" ++
  "def errNat (e : Error) : Nat := 0\n" ++
  "def w : ResultQ ω Nat := ResultQ.map (fun (ω n : Nat) => Nat.add n 1) (.ok 20)\n" ++
  "def W : Nat := ResultQ.elim (fun n => n) (fun e => errNat e) w\n" ++
  "def o : ResultQ 1 Tok := ResultQ.bind (.ok (Tok.mk)) (fun (1 t : Tok) => .ok t)\n" ++
  "def O : Nat := match o with | .ok t => endTok t | .err e => errNat e\n" ++
  "def z : ResultQ 0 Nat := .ok 99\n" ++
  "def Z : Nat := match z with | .ok _ => 7 | .err _ => 0\n" ++
  "def h1 : ResultH 1 Nat Tok := ResultH.bind (.ok 1 (Tok.mk)) (fun n (1 t : Tok) => .ok (Nat.add n 40) t)\n" ++
  "def H : Nat := match h1 with | .ok n t => (match t with | .mk => n) | .err e t => (match t with | .mk => errNat e)\n" ++
  "def main : IO Unit := IO.println (Nat.toString (Nat.add W (Nat.add O (Nat.add Z H))))\n"

def rqGroup : Group where
  name := "result-q"
  exercise := "lib/Result.wiz, lib/Region.wiz (quantity-polymorphic results)"
  cases := [
    { name := "ResultQ ω is Result and ResultH 1 is Result1, definitionally both ways", run := fun _ =>
        okLibs rqAliases [".ok 5", ".ok 5", ".ok 5", ".err .overflow"] },
    { name := "construction and elimination at q = ω, 1, 0", run := fun _ =>
        okLibs rqInstances ["21", "7", "40"] },
    { name := "ResultH: q = ω and a linear q = 1 threaded and converted to Result1", run := fun _ =>
        okLibs rqHandle ["4", "0"] },
    { name := "a q = 0 success value cannot be used at quantity 1", run := fun _ =>
        failsLibs (rqPrelude ++
          "def bad0 (x : ResultQ 0 Nat) : Nat := match x with | .ok a => a | .err _ => 0\n")
          "quantity" },
    { name := "a q = 1 success value cannot be duplicated", run := fun _ =>
        failsLibs (rqPrelude ++
          "def bad1 (x : ResultQ 1 Nat) : Nat × Nat :=\n  match x with | .ok a => (a, a) | .err _ => (0, 0)\n")
          "quantity" },
    { name := "a ResultH 1 handle cannot be duplicated", run := fun _ =>
        failsLibs (rqPrelude ++
          "inductive Tok where | mk\n" ++
          "def endTok (1 t : Tok) : Nat := match t with | .mk => 0\n" ++
          "def bad (1 t : Tok) : Nat × Nat :=\n  match (.ok 1 t : ResultH 1 Nat Tok) with\n  | .ok _ u => (endTok u, endTok u)\n  | .err _ u => (endTok u, endTok u)\n")
          "quantity" },
    { name := "compiled run: ResultQ at ω, 1, 0 and ResultH 1", run := fun _ =>
        cRunLibs rqRun "74\n" }
  ]

builtin_initialize registerGroup rqGroup

end Tests.Elab
