import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! (13s) `calc` blocks: a chain of relations and proofs. Adjacent steps compose through
an instance of `Trans p q r` (`lib/Logic.wiz`), so the steps may use different relations
and the last one is the chain's. `_` is the previous step's right endpoint.

The tests cover the order of `Nat`, `Int` and `Q`, `↔` and `=` between propositions, a
relation a test source registers itself, and the three errors (no composable relation, a
mismatched middle term, a proof of the wrong type). -/

def natCalc : String := "import Nat
def t (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=
  calc a ≤ b := h1
       _ < c := h2
       _ = d := h3
def t2 (a b c d : Nat) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) : a < d :=
  calc a < b := h1
       _ ≤ c := h2
       _ < d := h3
def t3 (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c ≤ d) : a < d :=
  calc a ≤ b := h1
       _ < c := h2
       _ ≤ d := h3
def t4 (a b c : Nat) (h1 : a = b) (h2 : b ≤ c) : a ≤ c :=
  calc a = b := h1
       _ ≤ c := h2
def t5 (a b c : Nat) (h1 : a ≤ b) (h2 : b = c) : a ≤ c :=
  calc a ≤ b := h1
       _ = c := h2
def t6 (a b c : Nat) (h1 : a < b) (h2 : b = c) : a < c :=
  calc a < b := h1
       _ = c := h2
def t7 (a b c d e : Nat) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) : a ≤ e :=
  calc a ≤ b := h1
       _ ≤ c := h2
       _ ≤ d := h3
       _ ≤ e := h4
#print axioms t
"

def intCalc : String := "import IntOrder
def t (a b c d : Int) (h1 : a ≤ b) (h2 : b < c) (h3 : c = d) : a < d :=
  calc a ≤ b := h1
       _ < c := h2
       _ = d := h3
def t2 (a b c d : Int) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) : a < d :=
  calc a < b := h1
       _ ≤ c := h2
       _ < d := h3
def t3 (a b c : Int) (h1 : a = b) (h2 : b ≤ c) : a ≤ c :=
  calc a = b := h1
       _ ≤ c := h2
#print axioms t
"

def ratCalc : String := "import Rat
def t (p q r s : Q) (h1 : p ≈ q) (h2 : q ≤ r) (h3 : r < s) : p < s :=
  calc p ≈ q := h1
       _ ≤ r := h2
       _ < s := h3
def t2 (p q r : Q) (h1 : p ≤ q) (h2 : q ≈ r) : p ≤ r :=
  calc p ≤ q := h1
       _ ≈ r := h2
def t3 (p q r s : Q) (h1 : p ≈ q) (h2 : q ≈ r) (h3 : r ≈ s) : p ≈ s :=
  calc p ≈ q := h1
       _ ≈ r := h2
       _ ≈ s := h3
#print axioms t
"

def propCalc : String := "import Logic
def t (P Q R S : Prop) (h1 : P ↔ Q) (h2 : Q ↔ R) (h3 : R ↔ S) : P ↔ S :=
  calc P ↔ Q := h1
       _ ↔ R := h2
       _ ↔ S := h3
def t2 (P Q R : Prop) (h1 : P = Q) (h2 : Q = R) : P = R :=
  calc P = Q := h1
       _ = R := h2
def t3 {A : Type} (a b c d : A) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d :=
  calc a = b := h1
       _ = c := h2
       _ = d := h3
#print axioms t
"

/-- The equality lemmas at two universes: each is used at `Type` and at `Type 1` (with
the carrier a variable, so the equations stay neutral and are not computed away). The
`Type`-only versions cannot check the second use. `calc` stays at `Type`: its `Trans`
instance must be monomorphic or level inference fails (see `lib/Logic.wiz`). -/
def levelEquality : String := "import Logic
-- Eq.symm at Type 0 and Type 1
def symm0 {A : Type} {a b : A} (e : a = b) : b = a := Eq.symm e
def symm1 {A : Type 1} {a b : A} (e : a = b) : b = a := Eq.symm e
-- Eq.trans at each
def trans0 {A : Type} {a b c : A} (e1 : a = b) (e2 : b = c) : a = c := Eq.trans e1 e2
def trans1 {A : Type 1} {a b c : A} (e1 : a = b) (e2 : b = c) : a = c := Eq.trans e1 e2
-- Eq.congrArg at each
def congr0 {A B : Type} (f : A → B) {a b : A} (e : a = b) : f a = f b := Eq.congrArg f e
def congr1 {A B : Type 1} (f : A → B) {a b : A} (e : a = b) : f a = f b := Eq.congrArg f e
-- Eq.congrArg2 at each
def congr2a {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B} (e : a = a') (e' : b = b') :
    f a b = f a' b' := Eq.congrArg2 f e e'
def congr2b {A B C : Type 1} (f : A → B → C) {a a' : A} {b b' : B} (e : a = a') (e' : b = b') :
    f a b = f a' b' := Eq.congrArg2 f e e'
-- Eq.substProp at each
def subst0 {A : Type} {a b : A} (P : A → Prop) (e : a = b) (h : P a) : P b :=
  Eq.substProp P e h
def subst1 {A : Type 1} {a b : A} (P : A → Prop) (e : a = b) (h : P a) : P b :=
  Eq.substProp P e h
-- Eq.mp'/Eq.mpr' at each
def mp0 {A : Type} {a b : A} (P : A → Prop) (e : a = b) (h : P a) : P b := Eq.mp' P e h
def mp1 {A : Type 1} {a b : A} (P : A → Prop) (e : a = b) (h : P a) : P b := Eq.mp' P e h
def mpr0 {A : Type} {a b : A} (P : A → Prop) (e : a = b) (h : P b) : P a := Eq.mpr' P e h
def mpr1 {A : Type 1} {a b : A} (P : A → Prop) (e : a = b) (h : P b) : P a := Eq.mpr' P e h
-- Eq.via at each
def via0 {A : Type} {a b c : A} (h1 : a = b) (h2 : b = c) : a = c := Eq.via b h1 h2
def via1 {A : Type 1} {a b c : A} (h1 : a = b) (h2 : b = c) : a = c := Eq.via b h1 h2
-- funext and congrFun at each
def fun0 {A B : Type} (f g : A → B) (h : (x : A) → f x = g x) : f = g := funext h
def fun1 {A B : Type 1} (f g : A → B) (h : (x : A) → f x = g x) : f = g := funext h
def cf0 {A B : Type} (f g : A → B) (e : f = g) (x : A) : f x = g x := congrFun e x
def cf1 {A B : Type 1} (f g : A → B) (e : f = g) (x : A) : f x = g x := congrFun e x
-- calc over = at Type 0 (unchanged: the Trans instance stays monomorphic)
def chain {A : Type} {a b c : A} (e1 : a = b) (e2 : b = c) : a = c :=
  calc a = b := e1
       _ = c := e2
#print axioms chain
"

def placeholders : String := "import Nat
def t (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c < d) : a < d :=
  calc a ≤ b := h1
       _ < c := h2
       _ < d := h3
def explicit (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a < c :=
  calc a ≤ b := h1
       b < c := h2
def mixed (a b c d : Nat) (h1 : a ≤ b) (h2 : b < c) (h3 : c < d) : a < d :=
  calc a ≤ b := h1
       _ < c := h2
       c < d := h3
"

/-- A relation a *program* registers, with its own transitivity lemma: `Same` is the
order in both directions (a setoid-like relation, not an equality). -/
def userCalc : String := "import Nat
def Same (a b : Nat) : Prop := (a ≤ b) ∧ (b ≤ a)
infix:50 \" ≈≈ \" => Same
def Same.trans {a b c : Nat} (h1 : a ≈≈ b) (h2 : b ≈≈ c) : a ≈≈ c :=
  And.intro (Nat.le_trans a b c h1.1 h2.1) (Nat.le_trans c b a h2.2 h1.2)
instance {a b c : Nat} : Trans (a ≈≈ b) (b ≈≈ c) (a ≈≈ c) :=
  Trans.mk (fun h h' => Same.trans h h')
def t (a b c : Nat) (h1 : a ≈≈ b) (h2 : b ≈≈ c) : a ≈≈ c :=
  calc a ≈≈ b := h1
       _ ≈≈ c := h2
#print axioms t
"

/-- No `Trans` instance for `≤` followed by `Same`: the error names both relations and
their meeting term. -/
def noInstance : String := "import Nat
def Same (a b : Nat) : Prop := (a ≤ b) ∧ (b ≤ a)
infix:50 \" ≈≈ \" => Same
def bad (a b c : Nat) (h1 : a ≤ b) (h2 : b ≈≈ c) : a ≈≈ c :=
  calc a ≤ b := h1
       _ ≈≈ c := h2
"

/-- An explicit intermediate term that is not the previous right endpoint. -/
def middleMismatch : String := "import Nat
def bad (a b c d : Nat) (h1 : a ≤ b) (h2 : c < d) : a < d :=
  calc a ≤ b := h1
       c < d := h2
"

/-- A step proof of the wrong relation. -/
def wrongProof : String := "import Nat
def bad (a b c : Nat) (h1 : b < c) : a ≤ c :=
  calc a ≤ b := h1
       _ ≤ c := Nat.le_refl c
"

def calcGroup : Group where
  name := "calc"
  exercise := "Stage 13s"
  parallel := true
  cases := [
    { name := "mixed chains at Nat: ≤/<, </≤, ≤/< then ≤, and =/≤, ≤/=, </=; a long ≤ chain", run := fun _ =>
        okLibs natCalc ["'t' does not depend on any axioms"] },
    { name := "mixed chains at Int: ≤/<, </≤, =/≤", run := fun _ =>
        okLibs intCalc ["'t' does not depend on any axioms"] },
    { name := "mixed chains at Q: ≈/≤/<, ≤/≈, and ≈", run := fun _ =>
        okLibs ratCalc ["'t' does not depend on any axioms"] },
    { name := "↔ chains, = between propositions, and = at a type variable", run := fun _ =>
        okLibs propCalc ["'t' does not depend on any axioms"] },
    { name := "equality lemmas and `calc` at `Type` and `Type 1`", run := fun _ =>
        okLib levelEquality ["'chain' does not depend on any axioms"] },
    { name := "`_` placeholders and an explicit intermediate term", run := fun _ =>
        okLibs placeholders },
    { name := "a relation registered by the program (`Same`, with its own `Trans` instance)", run := fun _ =>
        okLibs userCalc ["'t' does not depend on any axioms"] },
    { name := "no `Trans` instance: both relations and the meeting term are reported", run := fun _ =>
        failsLibs noInstance "no `Trans` instance composes" },
    { name := "a middle term that does not match the previous right endpoint", run := fun _ =>
        failsLibs middleMismatch "the middle term does not match" },
    { name := "a step proof of the wrong type", run := fun _ =>
        failsLibs wrongProof "has the wrong type" }
  ]

builtin_initialize registerGroup calcGroup

end Tests.Elab
