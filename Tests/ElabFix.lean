import Tests.Elab

/-!
# Elaborator bug fixes (agent/elab-bugs)

Regression tests for elaborator bugs that other work ran into and worked around: each
case is a minimal reproducer.
-/

open Wiz

set_option compiler.extract_closed false

namespace Tests.ElabFix

open Tests.Elab

/-- The peak resident set size of this process, in MB (Linux: `VmHWM` in
`/proc/self/status`); the cases run in a child process each, so this is the case's. -/
def peakMB : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  for l in s.splitOn "\n" do
    if l.startsWith "VmHWM:" then
      let kb := ((l.drop 6).trimAscii.toString.takeWhile Char.isDigit).toNat!
      return kb / 1024
  throw (IO.userError "no VmHWM in /proc/self/status")

/-- `okLib`, and the case stays under `mb` megabytes. -/
def okLibBounded (mb : Nat) (input : String) (infos : List String := []) : IO Unit := do
  okLib input infos
  let peak ← peakMB
  unless peak ≤ mb do throw (IO.userError s!"used {peak} MB (bound: {mb} MB)")

/-- A state monad over `Nat`, for `do` blocks without `Sys`. -/
def stateM : String := "import Prelude
def M (A : Type) : Type := Nat → (_ : A) × Nat
instance : Monad M where
  pure := fun a s => (a, s)
  bind := fun x f s => f (x s).1 (x s).2
def get : M Nat := fun s => (s, s)
def put (n : Nat) : M Unit := fun _ => ((), n)
"

/-- `allBelow` and the two halves of a conjunction (the icestick-uart proofs). -/
def allBelowSrc : String := "import Prelude
def allBelow : Nat → (Nat → Bool) → Bool
  | .zero, p => .true
  | .succ n, p => Bool.and (p 0) (allBelow n (fun (k : Nat) => p (Nat.succ k)))
def and_left : (a b : Bool) → Bool.and a b = .true → a = .true
  | .true, b, h => refl Bool.true
  | .false, b, h => absurd h.1
def and_right : (a b : Bool) → Bool.and a b = .true → b = .true
  | .true, b, h => h
  | .false, b, h => absurd h.1
"

/-- The shape of `Hw` (lib/Hdl/Core.wiz) that `Hw.cat (Hw.lit 1 1) d` needs. -/
def hwSrc : String := "import Prelude
inductive HwTy where
  | bits (n : Nat)
def HwTy.bit : HwTy := HwTy.bits 1
class Hw (r : HwTy → Type) where
  lit : (ω n : Nat) → Nat → r (HwTy.bits n)
  cat : {ω m n : Nat} → r (HwTy.bits m) → r (HwTy.bits n) → r (HwTy.bits (Nat.add m n))
"

/-- `p.1` and `p.2` of a glued global `p := (a, a)` stay glued: the spine records the
projection and `p` is not unfolded (elab-bugs-from-hdl 2). -/
def gluedProjections : IO Unit := do
  let pairTy : Raw Unit := .sigma "x" () "A" "A"
  let g : Globals Unit := [Raw.axiom "A" (.sort 0), Raw.axiom "a" "A",
    Raw.defn "p" pairTy (.pair "a" "a")].foldl Globals.insert {}
  let pv := eval g [] (.const "p" [])
  for (which, v) in [("fst", vFst pv), ("snd", vSnd pv)] do
    match v with
    | .unfold "p" _ sp _ =>
      unless sp.size == 1 do throw (IO.userError s!"{which}: spine of size {sp.size}")
    | _ => throw (IO.userError s!"{which}: the projection unfolded p")
    -- and it still computes
    checkEq "a" (quote g 0 (whnf v)).pretty

/-- (13b) The messages of `input`, with `lib/Prelude.wiz` and the module `Priv` (`priv`)
importable: privacy is per module. -/
def runPriv (priv input : String) : IO (Array String × Array String) := do
  let lib ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := fun m => if m == "Priv" then some priv else lib m }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  pure (errs, (s.messages.filter (·.severity != .error)).map (·.text))

def okPriv (priv input : String) (infos : List String := []) : IO Unit := do
  let (errs, msgs) ← runPriv priv input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr msgs.toList).pretty

def failsPriv (priv input fragment : String) : IO Unit := do
  let (errs, _) ← runPriv priv input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- A module with private names: a definition, a structure with a private constructor
(and a smart constructor), a private structure. -/
def privMod : String :=
  "import Prelude\nprivate def secret : Nat := 42\ndef reveal : Nat := secret\n" ++
  "structure Pos (A : Type) where\n  private mk ::\n  val : A\n" ++
  "def Pos.one : Pos Nat := Pos.mk 1\ndef Pos.dbl (p : Pos Nat) : Pos Nat := Pos.mk (Nat.add p.val p.val)\n" ++
  "def Pos.pair (p : Pos Nat) : Nat × Nat := (p.val, p.1)\n" ++
  "private structure Hidden where\n  x : Nat\n"

/-- (13b) A module with a private constructor of an inductive, private observations of a
coinductive, a private field of a structure, and a private inductive type. -/
def privMod2 : String :=
  "import Prelude\ninductive Tok where\n  | num (n : Nat)\n  | private secret (n : Nat)\n" ++
  "def Tok.hide (n : Nat) : Tok := Tok.secret n\n" ++
  "def Tok.value (t : Tok) : Nat := match t with\n  | .num n => n\n  | .secret n => Nat.add n 100\n" ++
  "coinductive Sig (A : Type) where\n  private head : A\n  private tail : Sig A\n  name : Nat\n" ++
  "def Sig.const {A : Type} (a : A) : Sig A\n  | .head => a\n  | .tail => Sig.const a\n  | .name => 7\n" ++
  "def Sig.sample {A : Type} (s : Sig A) : A := s.head\n" ++
  "def Sig.next {A : Type} (s : Sig A) : Sig A := s.tail\n" ++
  "structure Acct where\n  owner : Nat\n  private bal : Nat\n" ++
  "def Acct.balance (a : Acct) : Nat := a.bal\n" ++
  "private inductive Color where\n  | red\n  | blue\n" ++
  "def fav : Color := .red\n"

/-- A `Type 1` inductive with a function field over a `Type` (stored lifted, as
`fun h => k (down h)`), and an abstract channel type indexed by it (lib/Session.wiz's
`Proto` and `Chan`, in small). -/
def protoLike : String :=
  "import Prelude\ninductive P : Type 1 where\n  | step (A : Type) (k : A → P)\n  | stop\n" ++
  "def P.flip : P → P\n  | .step A k => .step A (fun a => P.flip (k a))\n  | .stop => .stop\n" ++
  "axiom Ch : P → Type\n" ++
  "axiom Ch.next : {A : Type} → {k : A → P} → Ch (P.step A k) → (a : A) → Ch (k a)\n"

def group : Group where
  name := "elabfix"
  parallel := true
  exercise := "elaborator bugs"
  cases := [
    { name := "x - 55296 with x stuck doesn't unfold the numeral (memory bound)", run := fun _ =>
        okLibBounded 1000 ("import Prelude\ndef f (hi : Nat) : Nat := (hi - 55296) * 2 + 1\n" ++
          "def s (hi lo : Nat) : Nat := 65536 + (hi - 55296) * 1024 + (lo - 56320)\n" ++
          "#eval f 55300\n#eval s 55296 56320") ["9", "65536"] },
    { name := "x - n with x stuck still computes once x is known", run := fun _ =>
        okLib ("import Prelude\ndef f (hi : Nat) : Nat := (hi - 55296) * 2 + 1\n" ++
          "def t : f 55300 = 9 := refl 9\n" ++
          "def u (n : Nat) : Nat.succ (Nat.succ n) - 1 = Nat.succ n := refl (Nat.succ n)\n" ++
          "def v (n : Nat) : n - 3 = n - 3 := refl (n - 3)") },
    { name := "holes in an equation-style definition's parameter types are solved", run := fun _ =>
        okLib ("import Prelude\ndef g {A : Type} (x : A) : A := x\n" ++
          "def f (n : Nat) (h : (x : Nat) → g x = x) : Bool → Nat\n  | .true => n\n  | .false => n\n" ++
          "def f2 (n : Nat) (h : (x : Nat) → g x = x) : (b : Bool) → g n = n → Nat\n" ++
          "  | .true, e => n\n  | .false, e => n") },
    { name := "@f on the recursive call of an equation-style definition", run := fun _ =>
        okLib ("import Prelude\ndef len {A : Type} : List A → Nat\n  | .nil => 0\n" ++
          "  | .cons _ xs => @len A xs + 1\n" ++
          "def len2 {A : Type} : List A → Nat\n  | .nil => 0\n  | .cons _ xs => @len2 _ xs + 1\n" ++
          "#eval len2 (List.cons 1 (List.cons 2 List.nil))") ["2"] },
    { name := "@f on a recursive call must pass the implicit parameters unchanged", run := fun _ =>
        failsLib ("import Prelude\ndef len {A : Type} : List A → Nat\n  | .nil => 0\n" ++
          "  | .cons _ xs => @len Nat xs + 1") "must pass the parameter A unchanged" },
    { name := ".c constructors inside tuple components get the expected type", run := fun _ =>
        okLib ("import Prelude\ndef p : Option (List Nat × Nat) := .some (.nil, 3)\n" ++
          "def q : Option (Nat × Bool × List Nat) := .some (1, .true, .cons 2 .nil)") },
    { name := "match on an expression generalises the hypotheses about it", run := fun _ =>
        okLib ("import Prelude\ndef t (n : Nat) (h : Nat.pred n = 0) : Nat :=\n" ++
          "  match Nat.pred n, h with\n  | .zero, _ => 0\n  | .succ m, h' => absurd h'.1") },
    { name := "(x).f y is a field access, like x.f y", run := fun _ =>
        okLib ("import Prelude\ndef a (x y : Nat) : Nat := x.sub y\ndef b (x y : Nat) : Nat := (x).sub y\n" ++
          "def c (x y : Nat) : Nat := Nat.add (x).succ y\n#eval b 5 2\n#eval c 1 1") ["3", "3"] },
    { name := "an equation whose sides have holes solved later (eq-pending-metas)", run := fun _ =>
        okLib ("import Word\n" ++
          "def wraps : (UIntN.add (U8.ofNat 250) (U8.ofNat 10)).toNat = 4 := refl 4\n" ++
          "def w {ω n : Nat} (a : UIntN n) : Nat := n\n" ++
          "def t : w (U8.ofNat 3) = 8 := refl 8\n" ++
          "def t' : w (U8.ofNat 3) = 8 := rfl") },
    { name := "an instance problem in a definition's type is solved before its body", run := fun _ =>
        okLib ("import Prelude\nclass C (A : Type) where\n  f : A → Nat\n" ++
          "instance : C Bool := C.mk (fun _ => 3)\ndef t5 : C.f Bool.true = 3 := refl 3") },
    { name := "a definition's implicit widths are solved before its body (elab-solve-type-before-body)", run := fun _ =>
        okLibs "import BitVec\ndef t : (BitVec.add (BitVec.ofNat 8 200) (BitVec.ofNat 8 100)).toNat = 44 := refl 44" },
    { name := "the unifier meets an equation with its computed form (unify-computed-equations)", run := fun _ =>
        okOptic ("import Optic\n" ++
          "def t3 (x : Nat) (xs ys : List Nat) (h : xs = ys) : List.cons x xs = List.cons x ys :=\n" ++
          "  Eq.congrArg (List.cons x) h\n" ++
          "def t4 (a b : Nat) (h : a = b) : Nat.succ a = Nat.succ b := Eq.congrArg Nat.succ h") },
    -- agent/elab-stretch
    { name := "numerals and notation in class field types (numerals-in-class-decls)", run := fun _ =>
        okLib ("import Prelude\ninductive HwTy where\n  | bits (n : Nat)\nclass Hw (r : HwTy → Type) where\n" ++
          "  eq : {n : Nat} → r (HwTy.bits n) → r (HwTy.bits n) → r (HwTy.bits 1)\n" ++
          "  cat : {m n : Nat} → r (HwTy.bits m) → r (HwTy.bits n) → r (HwTy.bits (m + n))") },
    { name := "structure projections as functions (projection-functions)", run := fun _ =>
        okLib ("import Prelude\nstructure BV (n : Nat) where\n  toNat : Nat\n  0 ok : Nat.lt toNat 100 = .true\n" ++
          "structure P (A : Type) where\n  x : A\n  y : List A\n" ++
          "def lm {A B : Type} (f : A → B) : List A → List B\n  | .nil => .nil\n  | .cons x xs => .cons (f x) (lm f xs)\n" ++
          "def m (vs : List (BV 8)) : List Nat := lm BV.toNat vs\n" ++
          "structure Sg where\n  n : Nat\n  v : BV n\ndef h (s : Sg) : BV (Sg.n s) := Sg.v s\n" ++
          "def f (v : BV 8) : Nat := v.toNat\n" ++
          "#eval P.y (P.mk 1 (List.cons 2 List.nil))\n#eval lm P.x (List.cons (P.mk 3 List.nil) List.nil)")
          [".cons 2 .nil", ".cons 3 .nil"] },
    { name := "erased fields get no projection function", run := fun _ =>
        failsLib ("import Prelude\nstructure BV (n : Nat) where\n  toNat : Nat\n  0 ok : Nat.lt toNat 100 = .true\n" ++
          "def g := BV.ok") "the field ok of BV has no projection function" },
    { name := "trailing instance arguments are inserted (trailing-instance-args)", run := fun _ =>
        okLib ("import Prelude\nclass BitPack (A : Type) where\n  width : Nat\ninstance : BitPack Bool := BitPack.mk 1\n" ++
          "def bitWidth (0 A : Type) [BitPack A] : Nat := @BitPack.width A _\n" ++
          "def two : Nat := bitWidth Bool + bitWidth Bool\ndef w3 := bitWidth Bool\n" ++
          "#eval two\n#eval @BitPack.width Bool _\n#eval w3") ["2", "1", "1"] },
    { name := "constructor parameters from the expected type (ctor-params-from-expected-type)", run := fun _ =>
        okLib ("import Prelude\ninductive Fin (n : Nat) where\n  | mk (val : Nat) (0 isLt : Nat.lt val n = .true)\n" ++
          "def Fin.succ {0 n : Nat} : Fin n → Fin (Nat.succ n)\n  | .mk i h => .mk (Nat.succ i) h\n" ++
          "def three : Fin 5 := Fin.mk 3 rfl\ndef four : Fin 5 := .mk 4 rfl") },
    { name := "lambda arguments wait for the arguments that fix their domains (elab-postpone-lambdas)", run := fun _ =>
        okLib ("import Prelude\n" ++
          "def zipWith3 {A B C D : Type} (f : A → B → C → D) : List A → List B → List C → List D\n" ++
          "  | .cons a as, .cons b bs, .cons c cs => .cons (f a b c) (zipWith3 f as bs cs)\n  | _, _, _ => .nil\n" ++
          "def sel (c : List Bool) (t e : List Nat) : List Nat := zipWith3 (fun b x y => match b with | .true => x | .false => y) c t e\n" ++
          "def sel2 (c : List Bool) (t e : List Nat) := zipWith3 (fun b x y => match b with | .true => x | .false => y) c t e\n" ++
          "def mealy {S I O : Type} (f : S → I → S × O) : S → List I → List O\n  | _, .nil => .nil\n" ++
          "  | s, .cons i is => .cons (f s i).2 (mealy f (f s i).1 is)\n" ++
          "def cnt (inp : List Bool) : List Nat := mealy (fun s i => match i with | .true => (Nat.succ s, s) | .false => (s, s)) 0 inp\n" ++
          "#eval sel2 (List.cons .true (List.cons .false .nil)) (List.cons 1 (List.cons 2 .nil)) (List.cons 3 (List.cons 4 .nil))\n" ++
          "#eval cnt (List.cons .true (List.cons .true .nil))")
          [".cons 1 (.cons 4 .nil)", ".cons 0 (.cons 1 .nil)"] },
    { name := "a constructor with a pair argument in a match branch (placeholders solved directly)", run := fun _ =>
        okLib ("import Prelude\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A .zero\n" ++
          "  | cons {0 n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n" ++
          "def zip {A B : Type} {n : Nat} : Vec A n → Vec B n → Vec (A × B) n\n" ++
          "  | .nil, .nil => .nil\n  | .cons a as, .cons b bs => .cons (a, b) (zip as bs)") },
    { name := "an argument naming a tuple pattern's component, before a postponed lambda (no scope escape)", run := fun _ =>
        okLib ("import Prelude\nstructure P where\n  a : Nat\n  b : Nat\n" ++
          "def app {S B : Type} (s : S) (k : S → B) : B := k s\n" ++
          "def f (p : P) : Nat := match p with\n  | (x, y, _) => app x (fun x => Nat.add x y)\n" ++
          "#eval f (P.mk 2 3)") ["5"] },
    { name := "named arguments: explicit, implicit and instance parameters (13a)", run := fun _ =>
        okLib ("import Prelude\nclass BitPack (A : Type) where\n  width : Nat\ninstance : BitPack Bool := BitPack.mk 1\n" ++
          "def bitWidth (0 A : Type) [BitPack A] : Nat := BitPack.width (A := A)\n" ++
          "def sub (a b : Nat) : Nat := Nat.sub a b\ndef ident {A : Type} (x : A) : A := x\n" ++
          "def pick {A : Type} (x y : A) (b : Bool) : A := match b with\n  | .true => x\n  | .false => y\n" ++
          "#eval bitWidth Bool\n#eval sub (b := 1) 5\n#eval sub (a := 7) (b := 2)\n#eval ident (A := Nat) 3\n" ++
          "#eval @ident (A := Nat) 4\n#eval @ident (x := 5) Nat\n#eval pick (b := .false) 1 2\n" ++
          "#eval BitPack.width (A := Bool)\n#eval @BitPack.width (A := Bool) _\ndef n : Nat := sub (b := 1) (Nat.succ 5)\n#eval n")
          ["1", "4", "5", "3", "4", "5", "2", "1", "1", "5"] },
    { name := "named arguments: errors (13a)", run := fun _ => do
        failsLib "import Prelude\ndef sub (a b : Nat) : Nat := Nat.sub a b\ndef x := sub (c := 1) 2" "no parameter named 'c'"
        failsLib "import Prelude\ndef sub (a b : Nat) : Nat := Nat.sub a b\ndef x := sub (b := 1) (b := 2)" "already given"
        failsLib "import Prelude\ndef sub (a b : Nat) : Nat := Nat.sub a b\ndef x : Nat := sub (b := 1)" "has no argument"
        failsLib "import Prelude\ndef x : Nat := (b := 1)" "only allowed as an argument" },
    { name := "private names are visible only in their module (13b)", run := fun _ => do
        okPriv privMod "import Priv\n#eval reveal\n#eval Pos.dbl Pos.one\n#eval (Pos.dbl Pos.one).val\n#eval Pos.val Pos.one\n#eval Pos.pair Pos.one"
          ["42", "(2, ())", "2", "1", "(1, 1)"]
        failsPriv privMod "import Priv\ndef x : Nat := secret" "'secret' is private to module Priv"
        failsPriv privMod "import Priv\ndef x : Nat := Hidden.mk 1" "private to module Priv"
        -- in their own module (the main file) private names are ordinary
        okPriv "" (privMod ++ "#eval secret\n#eval (Pos.mk 3 : Pos Nat).val\ndef h : Hidden := Hidden.mk 2\n#eval h.x") ["42", "3", "2"] },
    { name := "a private constructor: no forging from another module (13b)", run := fun _ => do
        failsPriv privMod "import Priv\ndef x : Pos Nat := Pos.mk 5" "'Pos.mk' is private to module Priv"
        failsPriv privMod "import Priv\ndef x : Pos Nat := @Pos.mk Nat 5" "private"
        -- the type is opaque here: no tuple, no look-alike structure
        failsPriv privMod "import Priv\ndef x : Pos Nat := (5, ())" "Pos"
        failsPriv privMod "import Priv\nstructure Fake (A : Type) where\n  val : A\ndef x : Pos Nat := Fake.mk 5" "mismatch"
        failsPriv privMod "import Priv\ndef x (p : Pos Nat) : Nat := p.1" "cannot project" },
    { name := "two values of another module's opaque type: compared at its definition, proofs irrelevant (13b)", run := fun _ => do
        -- wiz-notes/soundness-probes/opaque-proof-irrelevance: `P.mk 4 (lt_s 4)` and
        -- `P.mk 4 rfl` are equal in PM, and the kernel (which sees `P`) agrees; outside PM
        -- `P` is opaque, and its values used to be compared field by field, proofs included
        let pm := "import Prelude\ndef lt_s : (n : Nat) → Nat.lt n (Nat.succ n) = .true\n  | .zero => rfl\n  | .succ n => lt_s n\ninductive P where\n  | private mk (x : Nat) (0 h : Nat.lt x 5 = .true)\ndef P.a : P := .mk 4 (lt_s 4)\ndef P.b : P := .mk 4 rfl\ndef P.c (n : Nat) (h : Nat.lt n 5 = .true) : P := .mk n h\ndef P.d (n : Nat) (h : Nat.lt n 5 = .true) : P := .mk n (transp (fun t _ => Nat.lt n 5 = t) (refl (Nat.lt n 5)) h)\ndef inside : P.a = P.b := rfl\ndef insideSym (n : Nat) (h : Nat.lt n 5 = .true) : P.c n h = P.d n h := rfl\n"
        okPriv "" pm
        let sig := "(n : Nat) (h : Nat.lt n 5 = .true)"
        okPriv pm "import Priv\ndef outside : P.a = P.b := rfl\n"
        okPriv pm s!"import Priv\ndef outsideSym {sig} : P.c n h = P.d n h := rfl\n"
        okPriv pm "import Priv\ndef o3 : P.a = P.b := refl P.a\n"
        okPriv pm s!"import Priv\ndef o4 {sig} : P.c n h = P.d n h := refl (P.c n h)\n"
        -- the other fields still count
        let neq := "rfl: the two sides are not definitionally equal"
        failsPriv pm "import Priv\ndef no : P.a = P.c 3 rfl := rfl\n" neq
        failsPriv pm s!"import Priv\ndef no {sig} (m : Nat) (k : Nat.lt m 5 = .true) : P.c n h = P.c m k := rfl\n" neq
        -- the kernel's environment never has the hidden definitions (only the elaborator's
        -- view does): the kernel decides as before, and the elaborator now agrees with it
        let lib ← preludeLoader
        let s := runFrontend (R := ZeroOneMany) "import Priv\ndef outside : P.a = P.b := rfl\n"
          { trustedModule := Tests.libModule, loader := fun m => if m == "Priv" then some pm else lib m }
        check s.globals.hidden.isEmpty "the command state's globals have hidden definitions"
        check (s.globals.elabView.hidden.contains "P") "the elaborator's view hides P"
        check (s.globals.find? "outside" |>.isSome) "outside was not added" },
    { name := "rfl compares the two sides in the elaborator's view: no equation with a look-alike (13b)", run := fun _ => do
        let look := "import Priv\nstructure Look (A : Type) where\n  val : A\n"
        let neq := "rfl: the two sides are not definitionally equal"
        -- the kernel compares by shape, so `reflTy Look : Look = Pos` would check there,
        -- and `cast` along it would make a `Pos` without `Pos.mk`
        failsPriv privMod (look ++ "def e : Look Nat = Pos Nat := rfl") neq
        failsPriv privMod (look ++ "def e : Pos Nat = Look Nat := rfl") neq
        failsPriv privMod (look ++ "def e (A : Type) : Look A = Pos A := rfl") neq
        failsPriv privMod (look ++ "def forge (x : Look Nat) : Pos Nat := cast rfl x") neq
        failsPriv privMod (look ++ "def e : Look Nat = Pos Nat := refl (Look Nat)") "mismatch"
        -- inside an equation that computes first (a pair, a function, a parameter of a data type)
        failsPriv privMod (look ++ "def p : Type × Nat := (Look Nat, 1)\ndef e : p = (Pos Nat, 1) := rfl") neq
        failsPriv privMod (look ++ "def e : (fun (A : Type) => Look A) = (fun (A : Type) => Pos A) := rfl") neq
        failsPriv privMod (look ++ "def e : List (Look Nat) = List (Pos Nat) := rfl") neq
        -- inductive and coinductive types, a structure with a private field (4g makes
        -- these equations compute in the kernel)
        let fake := "import Priv\ninductive Fake where\n  | num (n : Nat)\n  | secret (n : Nat)\n"
        failsPriv privMod2 (fake ++ "def e : Fake = Tok := rfl") neq
        failsPriv privMod2 (fake ++ "def e : Tok = Fake := rfl") neq
        failsPriv privMod2 ("import Priv\ncoinductive Fake (A : Type) where\n  head : A\n  tail : Fake A\n  name : Nat\n" ++
          "def e : Fake Nat = Sig Nat := rfl") neq
        failsPriv privMod2 "import Priv\nstructure Fake where\n  owner : Nat\n  bal : Nat\ndef e : Fake = Acct := rfl" neq
        -- controls: a type and itself, through a definition, values; in its own module a
        -- look-alike is still the same type
        okPriv privMod ("import Priv\ndef a : Pos Nat = Pos Nat := rfl\ndef T : Type := Pos Nat\ndef b : T = Pos Nat := rfl\n" ++
          "def c (p : Pos Nat) : p = p := rfl\ndef d : Nat.add 1 1 = 2 := rfl\ndef f : List Nat = List Nat := rfl\n" ++
          "def g (A : Type) : List A = List A := rfl\ndef i : (fun (n : Nat) => Nat.add 0 n) = (fun n => n) := rfl\n" ++
          "def l (x : Nat) : (x, 1) = (x, Nat.add 0 1) := rfl")
        okPriv privMod2 "import Priv\ndef e : Tok = Tok := rfl\ndef j : Sig Nat = Sig Nat := rfl\ndef k : Acct = Acct := rfl"
        okPriv "" (privMod ++ "structure Look (A : Type) where\n  val : A\ndef e : Look Nat = Pos Nat := rfl\n" ++
          "def forge (x : Look Nat) : Pos Nat := cast e x\n#eval (forge (Look.mk 4)).val") ["4"] },
    { name := "the tactic request assign: a term with holes is type-checked at the end of the block (13b)", run := fun _ => do
        let tac (body : String) := "syntax (name := viaHole) \"viaHole\" : tactic\ndef Tactic.viaHole : Tactic := fun _ => do\n" ++
          "  g ← TacticM.mainGoal;\n  ng ← TacticM.newGoal g (.const \"Nat\");\n  e ← TacticM.goalExpr ng;\n" ++
          "  TacticM.assign g (" ++ body ++ ");\n  TacticM.replaceMainGoal (.cons ng .nil)\n" ++
          "attribute [tactic tactic.viaHole] Tactic.viaHole\n"
        -- `K x ?n : Look Nat` given to a goal `Pos Nat`: with the hole the type was never
        -- inferred, and the kernel takes the look-alike for the private type
        failsPriv privMod ("import Priv\nstructure Look (A : Type) where\n  val : A\n" ++
          "def K (x : Look Nat) (n : Nat) : Look Nat := x\n" ++ tac "Expr.app (.app (.const \"K\") (.var 0)) e" ++
          "def forge (x : Look Nat) : Pos Nat := by\n  viaHole\n  exact 0") "mismatch"
        -- control: a term with a hole of the goal's type (what `apply` does)
        okLib ("import Prelude\n" ++ tac "Expr.app (.const \"Nat.succ\") e" ++ "def three : Nat := by\n  viaHole\n  exact 2\n#eval three") ["3"]
        okLib ("import Prelude\ndef ap : (A B : Type) → (A → B) → A → B := by\n  intro A; intro B; intro f; intro a\n  apply f\n  assumption") },
    { name := "OPEN (13b): a first-order unification solution forges a value of a private type", run := fun _ => do
        -- not wanted: this records that the path is open. `?F ?p =?= G x` is solved by
        -- `?F := G`, `?p := x`; nobody type-checks the solutions, and the kernel takes
        -- `Look Nat` for `Pos Nat` by shape. When this test fails, the path was closed:
        -- turn it into a `failsPriv` and update docs/stages/13-language.md, 13b.
        okPriv privMod ("import Priv\nstructure Look (A : Type) where\n  val : A\n" ++
          "inductive G : Look Nat → Type where\n  | mk (l : Look Nat) : G l\n" ++
          "def sel {F : Pos Nat → Type} (p : Pos Nat) (w : F p) : Pos Nat := p\n" ++
          "def forge (x : Look Nat) : Pos Nat := sel _ (G.mk x)\n#eval (forge (Look.mk 11)).val") ["11"] },
    { name := "rfl is checked by the elaborator, not left to the kernel (wishful: elab-rfl-unchecked)", run := fun _ => do
        failsLib "import Prelude\ndef w (r a : Nat) : r = Nat.succ a := rfl" "rfl: the two sides are not definitionally equal"
        failsLib "import Prelude\ndef z (a : Nat) : a = a + 0 := rfl" "rfl: the two sides are not definitionally equal"
        okLib "import Prelude\ndef k (a : Nat) : 0 + a = a := rfl\ndef m (xs : List Nat) : List.append List.nil xs = xs := rfl"
        -- (agent elab-whnf's case) under a constructor whose motive is a hole: the kernel
        -- used to answer "expected False, inferred True"
        failsLibs "import Logic\ndef t : Ex (fun (m : Nat) => 3 = m) := Ex.intro _ 4 rfl" "rfl: the two sides are not definitionally equal"
        okLibs "import Logic\ndef t : Ex (fun (m : Nat) => 3 = m) := Ex.intro _ 3 rfl"
        -- so a tactic can try it: `rfl` fails, and the alternative runs
        okLib "import Prelude\ndef a (r x : Nat) (h : r = Nat.succ x) : r = Nat.succ x := by first | rfl | exact h"
        failsLib "import Prelude\ndef c (r x : Nat) : r = Nat.succ x := by rfl" "rfl: the two sides are not definitionally equal"
        -- η still holds by `rfl`, also at an equation formed while a type was a hole
        okLib ("import Prelude\ndef GP {S : Type} (f : S → S) : Prop := (s : S) → f s = s\nstructure One where\n  a : Nat\n" ++
          "def x2 : GP (fun (s : One) => One.mk s.a) := fun s => rfl\ndef x6 : GP (fun (s : Unit) => ()) := fun s => rfl") },
    { name := "rfl at a computed equation inside a match clause: the clause's type was read back, the equation survives (13n)", run := fun _ => do
        -- the motive of a clause is the expected type read back (`quote`) and evaluated at
        -- the pattern; the read-back used to spell the computed Σ out, so `rfl` no longer saw
        -- the equation and proved it field by field (a cast at a type variable: stuck).
        -- From cohesion-hardware (examples/hardware-tour.wiz, step_cases)
        okLib ("import Prelude\nstructure Pair2 (A B : Type) where\n  fst : A\n  snd : B\n" ++
          "def r1 {A : Type} (a : A) : (b : Bool) → (Bool.not b, a) = (Bool.not b, a)\n  | .true => rfl\n  | .false => rfl\n" ++
          "def r2 {A : Type} (a : A) (b : Bool) : (b, a) = (b, a) :=\n  match b with\n  | .true => rfl\n  | .false => rfl\n" ++
          "def r3 {A : Type} (s : Pair2 Bool A) : (b : Bool) → Pair2.mk s.fst s.snd = s\n  | .true => rfl\n  | .false => rfl\n" ++
          "#print axioms r1\n#reduce fun (A : Type) (p q : Bool × A) => p = q\n")
          ["'r1' does not depend on any axioms", "fun A p q => (0 e : p.1 = q.1) × cast (transp (fun y _ => A = A) (refl A) e) p.2 = q.2"]
        failsLib "import Prelude\ndef r4 {A : Type} (a c : A) : (b : Bool) → (b, a) = (b, c)\n  | .true => rfl\n  | .false => rfl"
          "rfl: the two sides are not definitionally equal" },
    { name := "rfl at an equation that has computed: one refl when the sides are convertible, no axiom (structure eta)", run := fun _ => do
        let pair2 := "import Prelude\nstructure Pair2 (A B : Type) where\n  fst : A\n  snd : B\n"
        let lens := "def Store (A S : Type) : Type := A × (A → S)\ndef Lens (S A : Type) : Type := S → Store A S\n" ++
          "def Lens.GetPut {S A : Type} (l : Lens S A) : Prop := (s : S) → (l s).2 (l s).1 = s\n" ++
          "def Pair2.fstL {A B : Type} : Lens (Pair2 A B) A := fun s => (s.fst, fun a => Pair2.mk a s.snd)\n" ++
          "def Pair2.sndL {A B : Type} : Lens (Pair2 A B) B := fun s => (s.snd, fun b => Pair2.mk s.fst b)\n"
        -- an equation at a Σ computes to field equations with a cast on every field after the
        -- first; at a type variable that cast does not reduce (P1), so field by field these
        -- failed. Now: one `refl` for the whole equation, and no axiom
        okLib (pair2 ++ lens ++
          "def g3 {A B : Type} (s : Pair2 A B) : Pair2.mk s.fst s.snd = s := rfl\n" ++
          "def g5 {A B : Type} (s : Pair2 A B) : s = s := rfl\n" ++
          "def g6 {A B : Type} (s : A × B) : (s.1, s.2) = s := rfl\n" ++
          "def g7 {A B : Type} (s : A × B) : s = s := rfl\n" ++
          "def l1 {A : Type} (x : A) (xs : List A) : List.cons x xs = List.cons x xs := rfl\n" ++
          "def l4 {A : Type} (p : A × (A → A)) : p = p := rfl\n" ++
          -- the lens laws with their implicit arguments given, so that the equation is computed
          -- when `rfl` sees it (lib/Optic.wiz's spelling leaves it uncomputed)
          "def gp1 {A B : Type} : @Lens.GetPut (Pair2 A B) A (@Pair2.fstL A B) := fun s => rfl\n" ++
          "def gp2 {A B : Type} : @Lens.GetPut (Pair2 A B) B (@Pair2.sndL A B) := fun s => rfl\n" ++
          "def gp3 {A B : Type} (s : Pair2 A B) : (Pair2.fstL s).2 (Pair2.fstL s).1 = s := rfl\n" ++
          "#print axioms g3\n#print axioms l1\n#print axioms gp1\n")
          ["'g3' does not depend on any axioms", "'l1' does not depend on any axioms", "'gp1' does not depend on any axioms"]
        -- still only convertible sides
        failsLib (pair2 ++ "def bad {A B : Type} (s t : Pair2 A B) : Pair2.mk s.fst t.snd = s := rfl")
          "rfl: the two sides are not definitionally equal"
        failsLib "import Prelude\ndef bad {A B : Type} (p q : A × B) : (p.1, q.2) = p := rfl"
          "rfl: the two sides are not definitionally equal"
        -- a field equation written by hand with a cast at a type variable is not proved by
        -- `rfl` (no axiom is added silently: write `castRefl`)
        failsLib "import Prelude\ndef h {A B : Type} (s : A × B) : (0 e : s.1 = s.1) × ((cast (refl B) s.2 : B) = s.2) := rfl"
          "rfl: the two sides are not definitionally equal"
        failsLib "import Prelude\ndef h2 {B : Type} (b : B) : (cast (refl B) b : B) = b := rfl"
          "rfl: the two sides are not definitionally equal" },
    { name := "private constructors, observations and fields: the public API (13b)", run := fun _ => do
        okPriv privMod2 ("import Priv\n#eval Tok.value (Tok.num 3)\n#eval Tok.value (Tok.hide 4)\n#eval Tok.value (.num 5)\n" ++
          "#eval Sig.sample (Sig.next (Sig.const 3))\n#eval (Sig.const 2).name\n" ++
          "#eval Acct.balance (Acct.mk 1 50)\n#eval (Acct.mk 1 50).owner")
          ["3", "104", "5", "3", "7", "50", "1"]
        -- in their own module everything is ordinary
        okPriv "" (privMod2 ++ "#eval Tok.value (.secret 1)\n#eval (Sig.const 4).tail.head\n#eval (Acct.mk 1 2).bal\n" ++
          "def f (t : Tok) : Nat := match t with\n  | .num _ => 0\n  | .secret _ => 1\n#eval f (Tok.hide 0)")
          ["101", "4", "2", "1"] },
    { name := "a private constructor of an inductive: no forging, no matching (13b)", run := fun _ => do
        failsPriv privMod2 "import Priv\ndef x : Tok := Tok.secret 1" "'Tok.secret' is private to module Priv"
        failsPriv privMod2 "import Priv\ndef x : Tok := .secret 1" "'Tok.secret' is private to module Priv"
        -- opaque here: a look-alike doesn't convert, and `match` (even on the public
        -- constructor, with a catch-all) would see the representation
        failsPriv privMod2 "import Priv\ninductive Fake where\n  | num (n : Nat)\n  | secret (n : Nat)\ndef x : Tok := Fake.secret 1" "mismatch"
        failsPriv privMod2 "import Priv\ndef f (t : Tok) : Nat := match t with\n  | .num n => n\n  | _ => 0" "opaque outside module Priv"
        failsPriv privMod2 "import Priv\ndef f (t : Tok) : Nat := match t with\n  | .secret n => n\n  | _ => 0" "opaque"
        -- the recursors would hand out the private constructor's fields
        failsPriv privMod2 "import Priv\ndef f := @Tok.casesOn" "'Tok.casesOn' is private to module Priv"
        failsPriv privMod2 "import Priv\ndef f := @Tok.rec" "private"
        -- the description is private too: `μ Tok.desc ()` is the type with nothing hidden
        failsPriv privMod2 "import Priv\ndef raw : μ Tok.desc () := con ('secret, 7, (), ())" "'Tok.desc' is private to module Priv"
        failsPriv privMod2 "import Priv\ndef D := @Sig.desc" "'Sig.desc' is private to module Priv"
        -- a type declared private: values of it can't be matched elsewhere either
        failsPriv privMod2 "import Priv\ndef f : Nat := match fav with\n  | .red => 1\n  | .blue => 2" "private to module Priv" },
    { name := "private observations of a coinductive: no observing, no building (13b)", run := fun _ => do
        failsPriv privMod2 "import Priv\ndef f (s : Sig Nat) : Nat := s.head" "'Sig.head' is private to module Priv"
        failsPriv privMod2 "import Priv\ndef f (s : Sig Nat) : Sig Nat := Sig.tail s" "'Sig.tail' is private to module Priv"
        failsPriv privMod2 "import Priv\ndef s : Sig Nat := Sig.mk 1 (Sig.const 1) 2" "'Sig.mk' is private to module Priv"
        failsPriv privMod2 "import Priv\ndef s : Sig Nat := .mk 1 (Sig.const 1) 2" "private"
        failsPriv privMod2 "import Priv\ndef s : Sig Nat\n  | .head => 1\n  | .tail => Sig.const 1\n  | .name => 0"
          "'Sig.head' is private to module Priv: a Sig can't be defined by copatterns"
        -- opaque here: the primitives don't see a `ν` either
        failsPriv privMod2 "import Priv\ndef f (s : Sig Nat) : Nat := (out s).1" "out expects a coinductive value"
        failsPriv privMod2 "import Priv\ndef s : Sig Nat := cocon (1, Sig.const 1, 2, ())" "cocon builds a coinductive value" },
    { name := "a private field of a structure (13b)", run := fun _ => do
        failsPriv privMod2 "import Priv\ndef f (a : Acct) : Nat := a.bal" "'Acct.bal' is private to module Priv"
        failsPriv privMod2 "import Priv\ndef f (a : Acct) : Nat := a.2.1" "project"
        failsLib "import Prelude\nclass C (A : Type) where\n  private m : A" "can't be private" },
    { name := "`private def` right after a structure (13b)", run := fun _ =>
        okLib "import Prelude\nstructure P where\n  x : Nat\nprivate def q : P := P.mk 1\n#eval q.x" ["1"] },
    { name := "a projection of an inline application doesn't run it (elab-bugs-from-hdl 2)", run := fun _ =>
        -- `(mk n).b` used to evaluate `mk n` (100000 nested matches) to find the type of
        -- `.b`: the evaluator overflowed the stack. Projections of glued values stay glued.
        okLibBounded 2000 ("import Prelude\nstructure S where\n  a : Nat\n  b : List Nat\n" ++
          "def step (p : Nat × List Nat) : Nat × List Nat := match p with\n  | (a, b) => (a + 1, .cons a b)\n" ++
          "def go : Nat → Nat × List Nat\n  | .zero => (0, .nil)\n  | .succ n => step (go n)\n" ++
          "def mk (n : Nat) : S := match go n with\n  | (a, b) => S.mk a b\n" ++
          "def len : Nat := List.length (mk 100000).b\ndef len2 : Nat := List.length (go 100000).2\n" ++
          "#eval List.length (mk 3).b") ["3"] },
    { name := "projections of a glued value stay glued (elab-bugs-from-hdl 2)", run := fun _ => gluedProjections },
    { name := "a two-row match with a catch-all covers the other constructors (elab-bugs-from-hdl 3)", run := fun _ =>
        okLib ("import Prelude\ninductive Op where\n  | input (port : Nat)\n  | const (v : Nat)\n  | add\n  | sub\n  | slice (lo : Nat)\n" ++
          "def Op.isAdd : Op → Bool\n  | .add => .true\n  | _ => .false\n" ++
          "def Op.isAdd2 (o : Op) : Bool := match o with\n  | .add => .true\n  | _ => .false\n" ++
          "def Op.lo : Op → List Nat → Nat\n  | .slice lo, _ => lo\n  | _, _ => 0\n" ++
          "#eval Op.isAdd (Op.input 0)\n#eval Op.isAdd2 Op.add\n#eval Op.lo (Op.slice 4) List.nil") [".false", ".true", "4"] },
    { name := "every form of `let` in a `do` block scopes over the rest of the block (do-let-omega-scope)", run := fun _ =>
        -- `let ω x := e; s₁; s₂`, `let x : T := e; …` and `let (a, b) := e; …` used to
        -- parse as a term-level `let` whose body was `s₁` alone: `x` was unknown in `s₂`
        okLib (stateM ++ "def a (d : Nat) : M Nat := do\n  let ω n := Nat.add d 1;\n  put n;\n  Monad.pure n\n" ++
          "def b (d : Nat) : M Nat := do\n  let n : Nat := Nat.add d 2;\n  put n;\n  Monad.pure n\n" ++
          "def c (p : (_ : Nat) × Nat) : M Nat := do\n  let (x, y) := p;\n  put x;\n  Monad.pure y\n" ++
          "#eval (a 1 0).1\n#eval (b 1 0).1\n#eval (c (3, 4) 0).2") ["2", "3", "3"] },
    { name := "structural recursion doesn't depend on the order of the matched arguments (B4)", run := fun _ =>
        -- the recursive call's result type `?p ?k = .true` met the expected `p (succ k) =
        -- .true` before the arguments were elaborated, and the first-order guess
        -- `?k := succ k` was kept (see "When unification approximates", Unify.lean)
        okLib (allBelowSrc ++
          "def spec1 : (n k : Nat) → (p : Nat → Bool) → allBelow n p = .true → Nat.lt k n = .true → p k = .true\n" ++
          "  | .zero, .zero, p, h, hk => absurd hk.1\n  | .zero, .succ k, p, h, hk => absurd hk.1\n" ++
          "  | .succ n, .zero, p, h, hk => and_left (p 0) (allBelow n (fun (j : Nat) => p (Nat.succ j))) h\n" ++
          "  | .succ n, .succ k, p, h, hk =>\n    spec1 n k (fun (j : Nat) => p (Nat.succ j))\n" ++
          "      (and_right (p 0) (allBelow n (fun (j : Nat) => p (Nat.succ j))) h) hk\n" ++
          "def spec2 : (k n : Nat) → (p : Nat → Bool) → allBelow n p = .true → Nat.lt k n = .true → p k = .true\n" ++
          "  | .zero, .zero, p, h, hk => absurd hk.1\n  | .succ k, .zero, p, h, hk => absurd hk.1\n" ++
          "  | .zero, .succ n, p, h, hk => and_left (p 0) (allBelow n (fun (j : Nat) => p (Nat.succ j))) h\n" ++
          "  | .succ k, .succ n, p, h, hk =>\n    spec2 k n (fun (j : Nat) => p (Nat.succ j))\n" ++
          "      (and_right (p 0) (allBelow n (fun (j : Nat) => p (Nat.succ j))) h) hk\n") },
    { name := "approximation: no guess for a hole an unelaborated explicit argument determines", run := fun _ =>
        -- `?p ?k =?= ok (base + k)`: `?p`, `?k` stand for the explicit arguments
        -- `(fun j => ok (base + j))` and `k`; guessing `?k := base + k` was wrong
        okLib (allBelowSrc ++
          "def spec : (k n : Nat) → (p : Nat → Bool) → allBelow n p = .true → Nat.lt k n = .true → p k = .true\n" ++
          "  | .zero, .zero, p, h, hk => absurd hk.1\n  | .succ k, .zero, p, h, hk => absurd hk.1\n" ++
          "  | .zero, .succ n, p, h, hk => and_left (p 0) (allBelow n (fun (j : Nat) => p (Nat.succ j))) h\n" ++
          "  | .succ k, .succ n, p, h, hk =>\n    spec k n (fun (j : Nat) => p (Nat.succ j))\n" ++
          "      (and_right (p 0) (allBelow n (fun (j : Nat) => p (Nat.succ j))) h) hk\n" ++
          "def ok (b : Nat) : Bool := Nat.beq b 3\n" ++
          "def t (base : Nat) (h : allBelow 16 (fun (j : Nat) => ok (base + j)) = .true) (k : Nat)\n" ++
          "    (hk : Nat.lt k 16 = .true) : ok (base + k) = .true :=\n  spec k 16 (fun (j : Nat) => ok (base + j)) h hk\n" ++
          -- (a rigid result is still propagated: `Fin`-like indices come from the expected type)
          "def t2 (p : Nat → Bool) (h : allBelow 16 p = .true) (k : Nat) (hk : Nat.lt k 16 = .true) : p k = .true :=\n" ++
          "  spec k 16 p h hk\n") },
    { name := "approximation: flex-rigid outside the pattern fragment still guesses (`?m ?A =?= M Nat`)", run := fun _ =>
        okLib (stateM ++ "def g : M Nat := Monad.bind get (fun x => Monad.pure (Nat.add x 1))\n#eval (g 4).1") ["5"] },
    { name := "approximation: flex-flex waits for the other arguments (Hw.cat (Hw.lit 1 1) d)", run := fun _ =>
        -- `?r (.bits ?m) =?= ?r' (.bits 1)`: neither side is a pattern; the argument waits
        -- until `d` fixes `?r`, then it is flex-rigid
        okLib (hwSrc ++ "def frame9 {r : HwTy → Type} [Hw r] (d : r (HwTy.bits 8)) : r (HwTy.bits 9) :=\n" ++
          "  Hw.cat (Hw.lit 1 1) d\n" ++
          "def hiFirst {r : HwTy → Type} [Hw r] (hi : r HwTy.bit) (d : r (HwTy.bits 8)) : r (HwTy.bits 9) :=\n" ++
          "  Hw.cat hi d\n") },
    { name := "approximation: flex-flex guesses only as the last resort", run := fun _ =>
        -- both arguments are flex-flex against the result: nothing else can make progress
        okLib (hwSrc ++ "def two {r : HwTy → Type} [Hw r] : r (HwTy.bits 2) :=\n  Hw.cat (Hw.lit 1 1) (Hw.lit 1 0)\n") },
    { name := "approximation: a repeated variable in a hole's spine (not a pattern) falls back to first order", run := fun _ =>
        -- `?m Γ i' =?= r i'` with `i'` in `Γ`: pruning the repeated `i'` loses it, so the
        -- solution is first-order from the repeated variable on (hdl-usability)
        okLibs ("import Hdl.Core\nstructure CombT (i o : HwTy) where\n  run : {r : HwTy → Type} → [Hw r] → r i → r o\n" ++
          "def mapIn {ω i' i o : HwTy} (f : CombT i' i) (c : Circuit i o) : Circuit i' o :=\n" ++
          "  Circuit.mk c.st c.init (fun s x => c.step s (f.run x))\n") },
    { name := "a variable whose type is the expected definition is not η-expanded through it (hdl-cleanup)", run := fun _ =>
        -- `f : Comb i o` against `Comb ?i ?o` (`def Comb … := {r} → [Hw r] → …`) became
        -- `fun {r} [_] => f`, with an instance hole made while `?r` was unsolved: "could not
        -- infer instance" on the binary of #92. Now the two types are unified first, as Lean
        -- does, and `f` stays `f` (the `#check`).
        okLibs "import Logic\ninductive HwTy where\n  | bits (n : Nat)\nclass Hw (r : HwTy → Type) where\n  lit : (ω n : Nat) → Nat → r (HwTy.bits n)\ndef El : HwTy → Type\n  | .bits n => Nat\ninstance : Hw El where\n  lit := fun n k => k\ndef Comb (i o : HwTy) : Type 1 := {r : HwTy → Type} → [Hw r] → r i → r o\ndef Comb.el {i o : HwTy} (f : Comb i o) (x : El i) : El o := f x\ndef mapL {A B : Type} (f : A → B) : List A → List B\n  | .nil => .nil\n  | .cons a as => .cons (f a) (mapL f as)\ndef consEq {A : Type} (x : A) {xs ys : List A} (e : xs = ys) : List.cons x xs = List.cons x ys :=\n  Eq.congrArg (List.cons x) e\ndef h {i o : HwTy} (f : Comb i o) : (xs : List (El i)) → mapL (Comb.el f) xs = mapL (fun (x : El i) => Comb.el f x) xs\n  | .nil => refl (@List.nil (El o))\n  | .cons x xs => consEq (Comb.el f x) (h f xs)\n\n#check fun (f : Comb (HwTy.bits 1) (HwTy.bits 2)) => Comb.el f" ["fun f => Comb.el (.bits 1) (.bits 2) f : Comb (.bits 1) (.bits 2) → El (.bits 1) → El (.bits 2)"] },
    { name := "a clause definition's type: instance holes still pending are solved before it is closed (hdl-cleanup)", run := fun _ =>
        -- `Comb.el f` checks `f : Comb i o` against `Comb ?i ?o`, which η-expands `f` to
        -- `fun {r} [_] => f ?inst` while `?r` is unsolved: `?inst` is pending, and the type
        -- of a definition by equations was closed before it was retried
        okLibs ("import Hdl.Core\n" ++
          "def t {i o : HwTy} (f : Comb i o) : (s : Nat) → (xs : List (HwTy.El i)) → Hdl.map (Comb.el f) xs = Hdl.map (Comb.el f) xs\n" ++
          "  | _, .nil => refl (@List.nil (HwTy.El o))\n" ++
          "  | s, .cons x xs => Hdl.consEq (f x) (t f s xs)\n") },
    { name := "dotted names: the longest prefix that names something, then fields by the type's name (cohesion-hardware)", run := fun _ =>
        -- `Q.origin.x` was the fields `origin.x` of `Q`; and `p.sum` for a structure `P`
        -- found no field `sum` (generalised field notation only knew inductive types)
        okLib ("import Prelude\nstructure P where\n  x : Nat\n  y : Nat\n" ++
          "def P.sum (p : P) : Nat := Nat.add p.x p.y\ndef Q.origin : P := P.mk 1 2\n" ++
          "def a : Nat := Q.origin.x\ndef b : Nat := Q.origin.sum\ndef c (p : P) : Nat := p.sum\n" ++
          "#eval a\n#eval b\n#eval c (P.mk 3 4)") ["1", "3", "7"] },
    { name := "dotted names through a derived definition: `Cnt.bundle.toEl` (cohesion-hardware)", run := fun _ =>
        okLibs "import Hdl.Core\ndef B4 : HwTy := HwTy.bits 4\ndef Bit : HwTy := HwTy.bit\nstructure Cnt (r : HwTy → Type) where\n  count : r B4\n  up : r Bit\n  deriving Bundle\ndef z : Cnt HwTy.El := Cnt.mk (BitVec.ofNat 4 3) (BitVec.ofNat 1 1)\ndef e1 : HwTy.El Cnt.bundle.code := Bundle.toEl Cnt.bundle z\ndef e2 : HwTy.El Cnt.bundle.code := Cnt.bundle.toEl z\n" },
    { name := "an equation at a product type: η for projected holes, stale casts (cohesion-hardware)", run := fun _ =>
        -- `Eq.congrArg f e`/`fstEq e` with `e : f y = (y, y)`: the expected `?p = ?q` computes
        -- to `(?p.1 = ?q.1) × …` and `?q.1 =?= y` is solved by η (`?q := (?a, ?b)`); a cast
        -- computed while the second component's type was a hole is dropped once its two
        -- types are the same (it would compute away)
        okLibs "import Logic\ndef fstEq {A B : Type} {p q : (_ : A) × B} (e : p = q) : p.1 = q.1 := Eq.congrArg (fun (r : (_ : A) × B) => r.1) e\ndef t1 (f : Nat → (_ : Nat) × Nat) (h : (x : Nat) → f x = (x, x)) (y : Nat) : (f y).1 = y := fstEq (h y)\ndef t2 (f : Nat → (_ : Nat) × Nat) (y : Nat) (h : f y = (y, y)) : (f y).1 = y := fstEq h\ndef t3 (f : Nat → (_ : Nat) × Nat) (h : (x : Nat) → f x = (x, x)) (y : Nat) : (f y).1 = y :=\n  Eq.congrArg (fun (r : (_ : Nat) × Nat) => r.1) (h y)\n" },
    { name := "pruning: a `let` of an inferred `match` (icestick-cpu C6)", run := fun _ =>
        -- the match's type `?T n` meets `List (?A n x✝)` from a branch, where `x✝` (the
        -- scrutinee) is in scope: `?A` can't depend on `x✝`, so it is pruned to `?A' n`
        okLib ("import Prelude\ndef size (n : Nat) : List String :=\n  let ω s := match Nat.lt 256 n with\n" ++
          "    | .true => List.cons \"big\" List.nil\n    | .false => List.nil;\n  List.append s s\n" ++
          "def size2 (n : Nat) : List String :=\n  let s := match Nat.lt 256 n with\n" ++
          "    | .true => List.nil\n    | .false => List.cons \"small\" List.nil;\n  List.append s s\n" ++
          "#eval size 300\n#eval size2 3") [".cons \"big\" (.cons \"big\" .nil)", ".cons \"small\" (.cons \"small\" .nil)"] },
    { name := "a `match` bound by `←` in a `do` block gets its type from its alternatives (do-match-expected-type)", run := fun _ =>
        -- the goal `M ?A`: its universe comes from `?A`'s (an implicit `{A : Type}`), and
        -- the scrutinee isn't abstracted inside `?A b` (that would leave the pattern fragment)
        okLib (stateM ++ "def a1 (b : Bool) : M Nat := do\n  t ← get;\n  x ← (match b with | .true => get | .false => Monad.pure 1);\n  Monad.pure (Nat.add x t)\n" ++
          "def a2 (o : Option Nat) : M Nat := do\n  t ← get;\n  let r := (match o with | .some w => w | .none => t);\n  Monad.pure r\n" ++
          "def a3 (b : Bool) : M Nat := do\n  t ← get;\n  match t, b with\n  | .zero, .true => Monad.pure 1\n  | _, _ => Monad.pure 2\n" ++
          "#eval (a1 .true 3).1\n#eval (a1 .false 3).1\n#eval (a2 .none 7).1") ["6", "4", "7"] },
    { name := "a type in a message is bounded (P1)", run := fun _ => do
        -- an equation between two long lists computes to a Σ of `True`s; printed in full,
        -- with primes for each shadowed binder, it was tens of kilobytes
        let n := 120
        let lst := (List.range n).foldr (fun i acc => s!"(List.cons {i} {acc})") "List.nil"
        let src := s!"import Prelude\ndef L : List Nat := {lst}\ndef bad (h : L = L) : Nat := h\n"
        let loader ← preludeLoader
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
        let errs := s.messages.filter (·.severity == .error)
        unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}")
        let t := errs[0]!.text
        check (t.length < 4000) s!"the message has {t.length} characters"
        check ((t.splitOn "characters left out").length > 1) s!"nothing was left out: {t.take 300}" },
    -- agent/elab-whnf
    { name := "a constructor field with a lifted domain: `?k (down h)` is a pattern (gap 7)", run := fun _ =>
        okLib (protoLike ++
          "def Q : P := .step Nat (fun _ => .step Bool (fun _ => .stop))\n" ++
          "def many : Nat → P\n  | .zero => .stop\n  | .succ n => .step Nat (fun _ => many n)\n" ++
          -- the inferred index is a definition that computes to a constructor
          "def t1 (c : Ch (P.flip Q)) : Ch (P.flip (.step Bool (fun _ => .stop))) := Ch.next c 3\n" ++
          "def t2 (c : Ch (P.flip Q)) : Ch P.stop := Ch.next (Ch.next c 3) Bool.true\n" ++
          -- in a match branch, with the scrutinee replaced by a constructor
          "def t3 : (n : Nat) → Ch (many n) → Nat\n  | .zero, c => 0\n  | .succ n, c => t3 n (Ch.next c 5)\n" ++
          "def t4 (c : Ch Q) := Ch.next c 1") },
    { name := "... and still fails at once on different constructors or a wrong message", run := fun _ => do
        failsLib (protoLike ++ "def bad (c : Ch P.stop) : Ch P.stop := Ch.next c 3") "type mismatch"
        failsLib (protoLike ++ "def Q : P := .step Nat (fun _ => .stop)\n" ++
          "def bad (c : Ch Q) : Ch P.stop := Ch.next c Bool.true") "mismatch" },
    { name := "nested Ex.intro with motive holes: no ill-typed first-order solution (vApp panic)", run := fun _ => do
        okLibs ("import Logic\n" ++
          "def t : Ex (fun (n : Nat) => Ex (fun (m : Nat) => n = m)) := Ex.intro _ 3 (Ex.intro _ 3 rfl)\n" ++
          "def t' : Ex (fun (n : Nat) => Ex (fun (m : Nat) => n = m)) := Ex.intro _ 3 (Ex.intro (fun (m : Nat) => 3 = m) 3 rfl)")
        -- without an expected type the motives can't be inferred: an error, not a panic
        -- (since agent/elab-bugs the inner `Ex.intro` waits for nothing better and no
        -- ill-typed guess is made: `rfl` meets the unsolved motive `?P ?w`)
        failsLibs "import Logic\ndef t := Ex.intro _ 3 (Ex.intro _ 3 rfl)" "rfl: the expected type is not an equation" },
    { name := "a universe level fixed only by an implicit argument's type is solved (wiz-cats B1)", run := fun _ =>
        -- `eqSymm.{?u}` under a binder in a constructor argument: `?A := B.R x x` is solved,
        -- and `?u` comes from its type (the binder's type was a hole when `?A` was made)
        okLib ("import Logic\n" ++
          "def eqSymm.{u} {A : Type u} {a b : A} (0 e : a = b) : b = a := transp (fun b _ => b = a) (refl a) e\n" ++
          "structure Box.{u, v} where\n  T : Type u\n  R : T → T → Type v\n  r : (x : T) → R x x\n" ++
          "structure S2.{u, v} (B : Box.{u, v}) where\n  law : (x : B.T) → B.r x = B.r x\n" ++
          "def bad.{u, v} (B : Box.{u, v}) (s : S2 B) : S2 B := S2.mk (fun x => eqSymm (s.law x))\n" ++
          "def bad2.{u, v} (B : Box.{u, v}) (s : S2 B) : S2 B := S2.mk.{u, v} (fun x => eqSymm (s.law x))\n" ++
          -- the levels of the implicit argument `{B : Box.{?u, ?v}}` of `S2.mk`, which only
          -- the type of `B` fixes (no expected type)
          "def e.{u, v} (B : Box.{u, v}) (s : S2 B) : Nat := (fun _ => 0) (S2.mk s.law)\n") },
    { name := "an unsolved universe level is reported at the constant it belongs to", run := fun _ => do
        let msgs ← msgsLib "import Prelude\ndef k.{u} : Nat := 0\ndef bad : Nat :=\n  Nat.succ k\n"
        unless msgs.any (fun m => (m.splitOn "the universe level u of k").length > 1) do
          throw (IO.userError s!"no 'the universe level u of k' in {msgs}") },
    { name := "a recursive call in equations inserts the implicit arguments (wiz-reals B1)", run := fun _ =>
        okLib ("import Logic\n" ++
          "def f : (k : Nat) → {m : Nat} → m = m → Nat\n  | .zero, _, _ => 0\n  | .succ k, _, e => f k e\n" ++
          -- the old form, every matched argument with `_` at the implicit ones, still works
          "def g : (k : Nat) → {m : Nat} → m = m → Nat\n  | .zero, _, _ => 0\n  | .succ k, _, e => g k _ e\n" ++
          "def h (n : Nat) : (k : Nat) → {m : Nat} → m = m → Nat\n  | .zero, _, _ => n\n  | .succ k, _, e => h n k e\n" ++
          "#eval @f 3 2 (refl 2)\n#eval @h 7 3 2 (refl 2)") ["0", "7"] },
    { name := "a structure-valued hole under a projection is solved from the projection (wiz-cats B5)", run := fun _ =>
        -- `(?C).2.2.1 ?X ?Y ?Z ?f ?g =?= C.2.2.1 X Y Z f g`: `?C := C`, then the arguments
        -- (a first-order guess, like Lean's for `Category.comp ?C`: the kernel rechecks)
        okLib ("import Logic\n" ++
          "structure Cat where\n  Obj : Type\n  Hom : Obj → Obj → Type\n  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z\n" ++
          "def lem {ω C : Cat} {X Y Z : C.Obj} (0 f : C.Hom X Y) (0 g : C.Hom Y Z) (0 h : C.Hom X Z) (0 e : C.comp f g = h) : h = C.comp f g :=\n" ++
          "  transp (fun x _ => x = C.comp f g) (refl (C.comp f g)) e\n" ++
          "def use {ω C : Cat} {X Y Z : C.Obj} (0 f : C.Hom X Y) (0 g : C.Hom Y Z) (0 h : C.Hom X Z) (0 e : C.comp f g = h) : h = C.comp f g :=\n" ++
          "  lem _ _ _ e\n") },
    -- error messages (wiz-notes/error-audit.md)
    { name := "messages: unknown names get a suggestion, `T.f` with T a type is a name", run := fun _ => do
        failsLib "import Prelude\ndef f (count : Nat) : Nat := cuont" "unknown identifier 'cuont'; did you mean 'count'?"
        failsLib "import Prelude\ndef f (n : Nat) : Nat := Nat.ad n 1" "unknown identifier 'Nat.ad'; did you mean 'Nat.add'?"
        failsLib "import Prelude\ndef f (xs : List Nat) : Nat := List.lenght xs" "unknown identifier 'List.lenght'; did you mean 'List.length'?"
        failsLib "import Prelude\ndef f (n : Nat) : Nat := f n" "recursive call to f in a definition without equations"
        failsLib "def f : Nat := 1" "Nat is defined in the Prelude: add `import Prelude`" },
    { name := "messages: fields, patterns, constructors", run := fun _ => do
        failsLib "import Prelude\nstructure P where\n  x : Nat\n  y : Nat\ndef f (p : P) : Nat := p.z" "P has no field 'z' (its fields are x, y)"
        failsLib "import Prelude\ndef f : Nat → Nat\n  | .zero => 0\n  | .succx n => n" "4:5: error: the value matched has type Nat, which has no constructor .succx (its constructors: .zero, .succ)"
        failsLib "import Prelude\ndef f : Nat → Nat\n  | .zero => 0" "missing case for constructor succ: add an alternative for .succ n"
        failsLib "import Prelude\ninductive T where\n  | a\n  | a" "4:5: error: the constructor a is declared twice in T"
        failsLib "import Prelude\ninstance : Frob Nat where\n  x := 1" "unknown class 'Frob'" },
    { name := "messages: quantities are the user's errors, explained", run := fun _ => do
        failsLib "import Prelude\ndef f (0 n : Nat) : Nat := n" "variable n declared with quantity 0 but used 1\n  (n is erased"
        failsLib "import Prelude\ndef f (1 n : Nat) : Nat × Nat := (n, n)" "and n is used more than once" },
    { name := "messages: parse errors name the category and what was found", run := fun _ => do
        failsLib "import Prelude\ndef p : Nat := by frobnicate" "unexpected 'frobnicate'; expected tactic"
        failsLib "import Prelude\ndef f (n : Nat) : Nat := (n" "unexpected end of input; expected" },
    { name := "a failing unification under a binder fails fast (wiz-reals S1: one unfolding order per layer)", run := fun _ =>
        -- each `Int.ofPair` is `Nat.sub` five definitions deep; trying both unfolding orders
        -- at every layer took 17 s
        failsLibsWithin 8 ("import Int\nimport Logic\n" ++
          "def Int.ofPair (a b : Nat) : Int := Int.subNatNat a b\n" ++
          "axiom ofPair_negate (a b : Nat) : -(Int.ofPair a b) = Int.ofPair b a\n" ++
          "axiom ofPair_add (a b c d : Nat) : Int.ofPair a b + Int.ofPair c d = Int.ofPair (a + c) (b + d)\n" ++
          "def r (a b c d : Nat) : Int.ofPair a b + -(Int.ofPair c d) = Int.ofPair (a + d) (b + c) :=\n" ++
          "  Eq.trans (Eq.congrArg (fun y => Int.ofPair _ _ + y) (ofPair_negate _ _)) (ofPair_add _ _ _ _)\n")
          "outside the pattern fragment" },
    { name := "a recursive call may pass the parameters and only the structural argument (wiz-reals P12)", run := fun _ =>
        okLib ("import Prelude\n" ++
          "def go (n : Nat) : Nat → Nat → Nat\n  | .zero, lo => Nat.add lo n\n" ++
          "  | .succ f, lo => (fun (g : Nat → Nat) => g (Nat.succ lo)) (go n f)\n#eval go 3 2 1") ["6"] },
    { name := "a binder's type with a hole solved later computes when applied (wiz-cats B7)", run := fun _ =>
        -- `α : NT F G` with the codomain category a hole when `α` is bound: the naturality
        -- equation is stuck on it, and is evaluated again (a Π, by funext) when applied
        okLib (
          "import Logic\n" ++
          "structure Cat.{u, v} where\n" ++
          "  Obj : Type u\n" ++
          "  Hom : Obj → Obj → Type v\n" ++
          "def Types : Cat.{1, 0} := Cat.mk Type (fun A B => A → B)\n" ++
          "structure Fn.{a, b, c, d} (C : Cat.{a, b}) (D : Cat.{c, d}) where\n" ++
          "  obj : C.Obj → D.Obj\n" ++
          "structure NT.{a, b, c, d} {C : Cat.{a, b}} {D : Cat.{c, d}} (F G : Fn C D) where\n" ++
          "  app : (X : C.Obj) → D.Hom (F.obj X) (G.obj X)\n" ++
          "  nat : (X : C.Obj) → app X = app X\n" ++
          "def use.{a, b} {C : Cat.{a, b}} {F G : Fn C Types} (α : NT F G) (X : C.Obj) (x : F.obj X) : α.app X x = α.app X x :=\n" ++
          "  α.nat X x\n") },
    { name := "`|>` at any universe, so on proofs too (wiz-reals P8)", run := fun _ =>
        okLib "import Logic\ndef p (a b : Nat) (h : a = b) : b = a := h |> Eq.symm\n" },
    { name := "Nat.toString of numbers of 2^64 and above (wiz-reals B3)", run := fun _ =>
        ioRun ("import IO\ndef main : IO Unit := do\n  IO.println (Nat.toString (Nat.pow 10 30));\n" ++
          "  IO.println (Nat.toString (Nat.add (Nat.pow 10 36) 7));\n  IO.println (Nat.toString 1000000000000000000);\n" ++
          "  IO.println (Nat.toString 42)")
          "1000000000000000000000000000000\n1000000000000000000000000000000000007\n1000000000000000000\n42\n" },
    { name := "rw in a context whose variables' types had holes when bound (wiz-cats B6)", run := fun _ =>
        -- the kernel takes a hole in a variable's type as rigid ("expected: Cat, inferred:
        -- Cat"); the rewrite's equation is inferred again with the variables' types zonked
        okLib (
          "import Logic\n" ++
          "structure Cat.{u, v} where\n" ++
          "  Obj : Type u\n" ++
          "  Hom : Obj → Obj → Type v\n" ++
          "def Types : Cat.{1, 0} := Cat.mk Type (fun A B => A → B)\n" ++
          "structure Fn.{a, b, c, d} (C : Cat.{a, b}) (D : Cat.{c, d}) where\n" ++
          "  obj : C.Obj → D.Obj\n" ++
          "structure NT.{a, b, c, d} {C : Cat.{a, b}} {D : Cat.{c, d}} (F G : Fn C D) where\n" ++
          "  app : (X : C.Obj) → D.Hom (F.obj X) (G.obj X)\n" ++
          "  nat : (X : C.Obj) → app X = app X\n" ++
          "axiom natEq.{a, b} {C : Cat.{a, b}} {F G : Fn C Types} (α : NT F G) (X : C.Obj) (x : F.obj X) : α.app X x = α.app X x\n" ++
          "def use.{a, b} {C : Cat.{a, b}} {F G : Fn C Types} (α : NT F G) (X : C.Obj) (x : F.obj X) : α.app X x = α.app X x := by\n" ++
          "  rw (natEq α X x)\n" ++
          "  exact rfl\n") },
    { name := "two `let`s on one line, the body on the next (wiz-reals P6)", run := fun _ =>
        -- the position the body's application is checked against is the enclosing one, not
        -- the second `let`'s column
        okLib ("import Prelude\ndef t (a b : Nat) : Nat :=\n  let x := a; let y := b;\n  Nat.add x y\n#eval t 2 3\n" ++
          "def u (a : Nat) : Nat :=\n  let x := a\n  Nat.add x x\n#eval u 4") ["5", "8"] },
    { name := "a `let` of an `if` between signals, without an ascription (wiz-rv: pruning a hole applied to a non-variable)", run := fun _ =>
        -- `?r Γ mx x (.bits 1)` (the signal type of `Hw.lit 1 0` in a branch) against the
        -- `let`'s type hole: the branch's variables are pruned, `.bits 1` stays
        okLibs ("import Hdl.Core\n" ++
          "def f {r : HwTy → Type} [Hw r] (mx : Bool) (a : r (HwTy.bits 1)) : r (HwTy.bits 1) :=\n" ++
          "  let x := if mx then a else Hw.lit 1 0;\n  x\n" ++
          "def g {r : HwTy → Type} [Hw r] (mx : Bool) : r (HwTy.bits 1) :=\n" ++
          "  let x := if mx then Hw.lit 1 1 else Hw.lit 1 0;\n  x\n") },
    { name := "signal `if`s without type annotations: in a bundle constructor, a `let`, nested (icestick B6)", run := fun _ =>
        okLibs (
          "import Hdl.Core\n" ++
          "structure Ctl (n : Nat) (r : HwTy → Type) where\n" ++
          "  a : r (HwTy.bits 6)\n" ++
          "  b : r (HwTy.bits n)\n" ++
          "def c1 {r : HwTy → Type} [Hw r] (ready : r HwTy.bit) (x : r (HwTy.bits 6)) (y : r (HwTy.bits 3)) : Ctl 3 r :=\n" ++
          "  Ctl.mk (if ready then Hw.lit 6 1 else x) y\n" ++
          "def c2 {r : HwTy → Type} [Hw r] (light : r HwTy.bit) : r (HwTy.bits 16) :=\n" ++
          "  let fl := if light then Hw.lit 16 1 else Hw.lit 16 2;\n" ++
          "  fl\n" ++
          "def c3 {r : HwTy → Type} [Hw r] (p q : r HwTy.bit) (a b c : Nat) : r (HwTy.bits 21) :=\n" ++
          "  let w := if p then Hw.lit 21 a else if q then Hw.lit 21 b else Hw.lit 21 c;\n" ++
          "  w\n") },
    { name := "a broken module's errors are reported once, not nested in every importer (wiz-reals P9)", run := fun _ => do
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let mods : List (String × String) := [("Prelude", prelude),
          ("A", "import Prelude\ndef a : Nat := Bool.true\n"), ("B", "import A\ndef b : Nat := 0\n")]
        let s := runFrontend (R := ZeroOneMany) "import B\ndef c : Nat := 0\n"
          { trustedModule := Tests.libModule, loader := fun m => mods.lookup m }
        let errs := s.messages.filter (·.severity == .error)
        unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.map (·.text)}")
        let t := errs[0]!.text
        unless (t.splitOn "imported module B → module A has errors:").length == 2 && (t.splitOn "type mismatch").length == 2 &&
            (t.splitOn "A:2:16: error").length == 2 do
          throw (IO.userError s!"unexpected message:\n{t}") },
    -- agent/bugfix-elab
    { name := "a module reaching a duplicate declaration through an import stops there: an error, not a run of its macros (dup-import-macro-panic)", run := fun _ => do
        -- `DupMap` declares lib/Text.wiz's `List.map`; lib/Deriving.wiz imports Text and then
        -- runs its derivers (`deriving instance … for Bool, Option, List`). Text is dropped
        -- for the clash: Deriving's later commands, replayed from its own isolated run,
        -- once ran without it, and the macro interpreter panicked
        let lib ← libLoader
        let dup := "import Prelude\ndef List.map {A B : Type} (f : A → B) : List A → List B\n" ++
          "  | .nil => .nil\n  | .cons x xs => .cons (f x) (List.map f xs)\n"
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => if m == "DupMap" then some dup else lib m }
        for src in ["import DupMap\nimport Deriving\n", "import DupMap\nimport Hdl.Core\ndef x : Nat := 1\n"] do
          for (how, st) in [("runFrontend", runFrontend src init), ("wiz check", ← Cache.elaborateUncached src init)] do
            let errs := (st.messages.filter (·.severity == .error)).map (·.text)
            check (errs.any (·.startsWith "'List.map' is declared by both module DupMap and module Text"))
              s!"{how}: {src}: {errs}" },
    { name := "soundness: a lemma about lib/Text's List.map never meets another module's List.map (dup-import-macro-panic)", run := fun _ => do
        -- `BadMap.List.map` returns `.nil`; `M` (and `N`, through `M`) prove
        -- `List.map id [x] = [x]` about Text's. Replayed next to BadMap's, that lemma would
        -- give `[] = [0]`. On every path (the cache cold and warm, without it, the
        -- frontend) the module that reaches the clash is dropped, or re-checked
        let lib ← libLoader
        let mods : List (Name × String) := [
          ("BadMap", "import Prelude\ndef List.map {A B : Type} (f : A → B) (xs : List A) : List B := .nil\n"),
          ("M", "import Prelude\nimport Text\ndef lem (x : Nat) : List.map (fun (y : Nat) => y) (List.cons x List.nil) = List.cons x List.nil := rfl\n"),
          ("N", "import M\ndef lem2 (x : Nat) : List.map (fun (y : Nat) => y) (List.cons x List.nil) = List.cons x List.nil := lem x\n")]
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := fun m => (mods.lookup m).orElse fun _ => lib m }
        let cache ← IO.FS.createTempDir
        let bad := "def bad : (List.nil : List Nat) = List.cons 0 List.nil := "
        for src in ["import BadMap\nimport M\n" ++ bad ++ "lem 0\n", "import BadMap\nimport N\n" ++ bad ++ "lem2 0\n",
                    "import N\nimport BadMap\n" ++ bad ++ "lem2 0\n", "import M\nimport BadMap\n" ++ bad ++ "lem 0\n"] do
          let cold := (← Cache.elaborateCached (some cache) [] src init 0).1
          let warm := (← Cache.elaborateCached (some cache) [] src init 0).1
          for (how, st) in [("cold cache", cold), ("warm cache", warm), ("no cache", ← Cache.elaborateUncached src init),
                            ("runFrontend", runFrontend src init)] do
            check (st.messages.any fun m => m.severity == .error && (m.text.splitOn "is declared by both").length > 1)
              s!"{how}: no clash reported for\n{src}"
            check (!st.globals.contains "bad") s!"{how}: [] = [0] was accepted for\n{src}"
        IO.FS.removeDirAll cache },
    { name := "a module kept from an isolated run is kept per pp.notation setting, and the other Globals options (isokey-settings)", run := fun _ => do
        -- the first run keeps Prelude's isolated state (with notation on); the second, with
        -- notation off from the start (`wiz check --pp-all`), once got that state, notation on
        let loader ← preludeLoader
        let src := "import Prelude\n#check [1]\n"
        let texts (s : CommandState ZeroOneMany) := s.messages.toList.map (·.text)
        let on := runFrontend src ({ loader, trustedModule := Tests.libModule } : CommandState ZeroOneMany)
        checkEq (repr ["[1] : List Nat"]).pretty (repr (texts on)).pretty
        let off := runFrontend src ({ loader, trustedModule := Tests.libModule, globals := { pp := { useNotation := false } } } : CommandState ZeroOneMany)
        checkEq (repr ["List.cons Nat 1 (List.nil Nat) : List Nat"]).pretty (repr (texts off)).pretty
        -- and the options the key didn't have: each gives its own key
        let base : CommandState ZeroOneMany := { loader, trustedModule := Tests.libModule }
        let k := isoKey base "Prelude"
        check k.isSome "no key for an initial state"
        for (opt, st) in [("pp.notation", { base with globals := { pp := { useNotation := false } } }),
                          ("pushCalls", { base with globals := { pushCalls := false } }),
                          ("strictPrivacy", { base with globals := { strictPrivacy := true } }),
                          ("quoteErasesProofs", { base with globals := { quoteErasesProofs := true } }),
                          ("assumed", { base with globals := { assumed := [("a", "b")] } })] do
          check (isoKey st "Prelude" != k) s!"{opt} is not in isoKey" },
    { name := "a recursive `def … := match` on its parameters is its equations (def-match-recursion)", run := fun _ => do
        okLib ("import Prelude\n" ++
          -- the match on the second parameter, under a `fun`, and directly
          "def Fe.f (x : Nat) : List Nat → Nat := fun ps => match ps with\n  | .nil => x\n  | .cons _ t => Fe.f x t\n" ++
          "def Fe.g (x : Nat) (ps : List Nat) : Nat := match ps with\n  | .nil => x\n  | .cons _ t => Nat.succ (Fe.g x t)\n" ++
          -- a parameter after the scrutinee, and the scrutinee used in a right-hand side
          "def Fe.h (ps : List Nat) (acc : Nat) : Nat := match ps with\n  | .nil => acc\n  | .cons _ t => Fe.h t (Nat.succ acc)\n" ++
          "def Fe.len (ps : List Nat) : Nat := match ps with\n  | .nil => 0\n  | .cons _ t => Nat.succ (Fe.len t)\n" ++
          "def Fe.k (ps : List Nat) : Nat := match ps with\n  | .nil => 0\n  | .cons _ t => Nat.add (Fe.len ps) (Fe.k t)\n" ++
          -- two scrutinees
          "def Fe.zip (xs : List Nat) (ys : List Nat) : Nat := match xs, ys with\n  | .cons _ a, .cons _ b => Nat.succ (Fe.zip a b)\n  | _, _ => 0\n" ++
          "#eval Fe.f 7 (.cons 1 (.cons 2 .nil))\n#eval Fe.g 7 (.cons 1 (.cons 2 .nil))\n#eval Fe.h (.cons 1 (.cons 2 .nil)) 5\n" ++
          "#eval Fe.k (.cons 1 (.cons 2 .nil))\n#eval Fe.zip (.cons 1 (.cons 2 .nil)) (.cons 3 .nil)\n")
          ["7", "9", "7", "3", "1"]
        -- not structurally recursive: the equations' error
        failsLib "import Prelude\ndef f (ps : List Nat) : Nat := match ps with\n  | .nil => 0\n  | .cons _ t => f ps\n"
          "recursive call of f on ps" },
    { name := "a recursive call in a plain `def … :=` that isn't a match on its parameters says what's wrong (def-match-recursion)", run := fun _ => do
        failsLib "import Prelude\ndef Fe.f (x : Nat) : Nat := Nat.succ (Fe.f x)\n"
          "recursive call to Fe.f in a definition without equations"
        failsLib "import Prelude\ndef f (x : Nat) (ps : List Nat) : Nat := Nat.add 1 (match ps with\n  | .nil => x\n  | .cons _ t => f x t)\n"
          "recursive call to f in a definition without equations"
        -- a local of that name is still a local
        okLib "import Prelude\ndef f (x : Nat) : Nat := let f := x; f\n" },
    { name := "a match on a structure with a field at quantity 0 binds it at 0 (struct-erased-field-match)", run := fun _ => do
        let hdr := "import Prelude\nstructure S0 where\n  0 n : Nat\n  m : Nat\n"
        okLib (hdr ++ "def s0mt (s : S0) : Nat := match s with\n  | .mk n m => m\n" ++
          "def s0a (s : S0) : Nat := match s with\n  | ⟨_, m⟩ => Nat.succ m\n" ++
          -- the erased field in an erased position (a type)
          "def s0t (s : S0) : Type := match s with\n  | .mk n m => Nat\n" ++
          "#eval s0mt (S0.mk 3 4)\n") ["4"]
        -- used at runtime it is an error (not a projection at ω behind the user's back)
        failsLib (hdr ++ "def bad (s : S0) : Nat := match s with\n  | .mk n m => n\n") "n" },
    { name := "#266: an unknown qualified name is an unknown identifier, not a field access", run := fun _ => do
        failsLibW "import Prelude\ndef x : Option Nat := Option.bind (.some 1) (fun n => .some n)\n" "unknown identifier 'Option.bind'"
        failsLibW "import Prelude\ndef x : Nat := Nat.nope 3\n" "unknown identifier 'Nat.nope'"
        -- a field of a value is still a field
        failsLibW "import Prelude\nstructure P where\n  a : Nat\ndef p : P := P.mk 1\ndef x : Nat := p.b\n" "no field 'b'" },
    { name := "#261: refl is a contextual keyword: a constructor may be called refl", run := fun _ =>
        okLib ("import Prelude\ninductive R : Nat → Type where\n  | refl (n : Nat) : R n\n" ++
          "def r : R 3 := R.refl 3\ndef r2 : R 4 := .refl 4\n" ++
          "def f : R 3 → Nat\n  | .refl n => n\n" ++
          "def e : f r = 3 := refl 3\ndef refl2 (n : Nat) : n = n := refl n\n#eval f r") ["3"] },
    { name := "#258: absurd sees through a computed constructor equation", run := fun _ => do
        okLib ("import Prelude\ndef f (h : Bool.false = Bool.true) : False := absurd h\n" ++
          "def g (n : Nat) (h : Nat.succ n = 0) : Nat := absurd h\n" ++
          "def k (h : @Option.some Nat 1 = .none) : Bool := absurd h\n")
        failsLibW "import Prelude\ndef f (n : Nat) (h : n = n) : False := absurd h\n" "absurd expects a proof of False or Empty" },
    -- agent/dogfood-fixes
    { name := "auto-share: an ill-kinded instance match does not apply; no evaluator panic (autoshare-illkinded-panic)", run := fun _ =>
        -- `ShareLet (r a) (r b)` matched `S T.El` first order with r := S, a := T.El
        okLib "import Prelude\n-- the auto-share hook of Hdl.Core, alone (docs/libraries.md, H14 S0)\nclass ShareLet (A B : Type) where\n  share : A → (A → B) → B\ninductive T where\n  | bits (n : Nat)\ndef T.El : T → Type\n  | .bits n => Nat\nclass Hw (r : T → Type) where\n  lit : (n : Nat) → r (T.bits n)\ninstance : Hw T.El where\n  lit := fun n => n\ninstance {r : T → Type} [Hw r] {a b : T} : ShareLet (r a) (r b) where\n  share := fun x f => f x\nstructure S (r : T → Type) where\n  x : r (T.bits 3)\n  y : r (T.bits 8)\ndef base : S T.El := S.mk 1 2\n-- `S T.El` is taken for `r a` with r := S, a := T.El: ill-kinded\ndef f (k : Nat) : S T.El :=\n  let b := base;\n  S.mk b.x k\n" },
    { name := "#249: recursion over a family refines later arguments at non-variable indices", run := fun _ =>
        okLib ("import Prelude\ninductive R : Nat → Nat → Type where\n  | done (s : Nat) : R s s\n" ++
          "  | step (s t u : Nat) (r : R t u) : R s u\n" ++
          "def v5 (P : Nat → Prop) (f : (a b : Nat) → P a → P b) : {s u : Nat} → R s u → P s → P u\n" ++
          "  | _, _, .done x, h => h\n  | _, _, .step a b c r, h => v5 P f r (f a b h)\n" ++
          "def v6 (P : Nat → Prop) (f : (a b : Nat) → P a → P b) : (s u : Nat) → R s u → P s → P u\n" ++
          "  | _, _, .done x, h => h\n  | _, _, .step a b c r, h => v6 P f b c r (f a b h)\n" ++
          "inductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A 0\n" ++
          "  | cons {n : Nat} (x : A) (xs : Vec A n) : Vec A (n + 1)\n" ++
          "def map {A B : Type} (f : A → B) : {n : Nat} → Vec A n → Vec B n\n" ++
          "  | _, .nil => .nil\n  | _, .cons x xs => .cons (f x) (map f xs)\n" ++
          "def len {A : Type} : {n : Nat} → Vec A n → (k : Nat) → Nat\n" ++
          "  | _, .nil, k => k\n  | _, .cons x xs, k => len xs (k + 1)\n" ++
          "#eval len (map (fun n => n + 1) (Vec.cons 1 (Vec.cons 2 Vec.nil))) 10") ["12"] },
    { name := "#250: the body of an impossible arm is type checked; an empty match", run := fun _ => do
        let hdr := "import Prelude\ninductive T : Bool → Type where\n  | mk : T .true\n"
        failsLibW (hdr ++ "def f (t : T .false) : False := match t with\n  | .mk => \"hello\"\n") "type mismatch"
        -- a well-typed body on an impossible arm is still accepted
        okLib (hdr ++ "def f (t : T .false) (h : False) : False := match t with\n  | .mk => h\n")
        -- no arms when every case is impossible
        okLib (hdr ++ "def f (t : T .false) : False := match t with\n" ++
          "def g : T .false → False := fun t => match t with\n" ++
          "def h (n : Nat) : (b : Bool) → T b → b = .false → Nat\n  | _, .mk, e => absurd e.1\n" ++
          "def k : {b : Bool} → T b → b = .false → False\n  | _, .mk, e => absurd e.1\n")
        failsLibW (hdr ++ "def f (t : T .true) : False := match t with\n") "missing case for constructor mk"
        failsLibW (hdr ++ "def g : (b : Bool) → T b → False := fun b t => match t with\n") "missing case for constructor mk" }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  group ::
  []

end Tests.ElabFix
