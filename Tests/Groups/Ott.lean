import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def substDef : String :=
  "def subst {A : Type} (P : A → Type) {a b : A} (e : a = b) (pa : P a) : P b :=\n" ++
  "  cast (transp (fun b _ => P a = P b) (refl (P a)) e) pa\n"

/-- The same program with the box inside a second box (`Box2 P` has a field of type
`Box P`): the outer box's field is not inert (it has a `Prop` field inside), so the cast
at `Box2` stays structural, and the program checks without regularity. -/
def abelCoquandNested : String :=
  ((abelCoquand (body := s!"ind (fun _ _ => A) (fun i xs ih => xs.1.2) (ind (fun _ _ => Box A) (fun i xs ih => xs.1.2) " ++
      s!"(cast (apTy Prop Box2 T2 A (tautext T2 A id2 a)) (mk2 (mk {acDelta}) : Box2 T2) : Box2 A))")).replace
    "def omega : Top := fun A a => unbox (cast (apTy Prop Box T2 A (tautext T2 A id2 a)) (mk delta))\n"
    ("def Box2D (P : Prop) : Desc Unit := Desc.arg 1 ((_ : Enum [u]) × Box P) (fun _ => Desc.ret ())\n" ++
     "def Box2 (P : Prop) : Type := μ (Box2D P) ()\n" ++
     "def mk2 {P : Prop} (b : Box P) : Box2 P := con (('u, b), (), ())\n" ++
     "def unbox2 {P : Prop} (b : Box2 P) : Box P := ind (fun _ _ => Box P) (fun i xs ih => xs.1.2) b\n" ++
     "def omega : Top := fun A a => unbox (unbox2 (cast (apTy Prop Box2 T2 A (tautext T2 A id2 a)) (mk2 (mk delta))))\n"))

/-- Abel–Coquand's own step `cast T2 T2 e δ ▷ δ` (a cast between propositions): Wiz
applies the equivalence `e` instead, here `fun _ => id2`, so the step gives `id2`. (Their
term itself can't be written: `cast` to a variable proposition `A` needs a proof of a
type equation `T2 = A`, which stays stuck while `A` is a variable.) -/
def abelCoquandLiteral : String :=
  "def Top : Prop := (A : Prop) → A → A\n" ++
  "def T2 : Prop := Top → Top\n" ++
  "def id2 : T2 := fun x => x\n" ++
  "def delta : T2 := fun z => z T2 id2 z\n" ++
  "def tautext (A B : Prop) (a : A) (b : B) : A = B := ((fun _ => b), (fun _ => a))\n" ++
  "#reduce (cast (tautext T2 T2 id2 id2) delta : T2)\n"

/-- (P2) Checking `input` under `mode` (`full+eager`: without `lazyProofs`) finishes, without
errors, within `secs` seconds (in a child process, as `checkDiverges`). -/
def checkTerminates (input mode : String) (secs : Nat := 20) : IO Unit := do
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "input.wiz") input
  let self ← IO.appPath
  let out ← IO.Process.output { cmd := "sh", cwd := dir, args := #["-c",
    s!"ulimit -v 8000000; exec timeout {secs} \"$0\" --check {mode} input.wiz", self.toString] }
  unless out.exitCode == 0 do
    throw (IO.userError s!"expected success, got exit code {out.exitCode}: {out.stderr.take 1000}")

/-- (P1) The probe of `wiz-notes/inert-regularity-probe.wiz`: an inert indexed family
whose index can hide a proof (`f p`), and statements that need InReg (regularity at inert
types). Each declaration is checked on its own. -/
def p1Prelude : String :=
  "inductive N where\n  | z\n  | s (n : N)\n" ++
  "inductive Fin2 : N → Type where\n  | fz {0 n : N} : Fin2 (.s n)\n  | fs {0 n : N} (k : Fin2 n) : Fin2 (.s n)\n" ++
  "def two : N := .s (.s .z)\n"

def p1Decls : List (String × String) := [
  -- control: no regularity at a type variable
  ("t5", "def t5 (A : Type) (k : A) (e : A = A) : (cast e k : A) = k := rfl"),
  -- InReg at an open index (`f p`)
  ("t1", "def t1 (P : Prop) (f : (0 _ : P) → N) (p : P) (k : Fin2 (f p)) (e : Fin2 (f p) = Fin2 (f p)) : (cast e k : Fin2 (f p)) = k := rfl"),
  -- the same, at convertible but not syntactically equal types
  ("t2", "def t2 (P : Prop) (f : (0 _ : P) → N) (p q : P) (k : Fin2 (f p)) (e : Fin2 (f p) = Fin2 (f q)) : (cast e k : Fin2 (f q)) = k := rfl"),
  -- two casts at convertible types
  ("h", "def h (P : Prop) (f : (0 _ : P) → N) (p q r : P) (k : Fin2 (f p)) (e1 : Fin2 (f p) = Fin2 (f r)) (e2 : Fin2 (f p) = Fin2 (f q)) : (cast e1 k : Fin2 (f r)) = (cast e2 k : Fin2 (f q)) := rfl"),
  -- h's instance r := p, by rfl: the δβ-reduct of h3 (P1: it was rejected)
  ("h2", "def h2 (P : Prop) (f : (0 _ : P) → N) (p q : P) (k : Fin2 (f p)) (e1 : Fin2 (f p) = Fin2 (f p)) (e2 : Fin2 (f p) = Fin2 (f q)) : (cast e1 k : Fin2 (f p)) = (cast e2 k : Fin2 (f q)) := rfl"),
  ("h3", "def h (P : Prop) (f : (0 _ : P) → N) (p q r : P) (k : Fin2 (f p)) (e1 : Fin2 (f p) = Fin2 (f r)) (e2 : Fin2 (f p) = Fin2 (f q)) : (cast e1 k : Fin2 (f r)) = (cast e2 k : Fin2 (f q)) := rfl\n" ++
    "def h3 (P : Prop) (f : (0 _ : P) → N) (p q : P) (k : Fin2 (f p)) (e1 : Fin2 (f p) = Fin2 (f p)) (e2 : Fin2 (f p) = Fin2 (f q)) : (cast e1 k : Fin2 (f p)) = (cast e2 k : Fin2 (f q)) := h P f p q p k e1 e2"),
  -- InReg at a closed index, on a variable
  ("g1", "def g1 (k : Fin2 (.s (.s .z))) (e : Fin2 (.s (.s .z)) = Fin2 (.s (.s .z))) : (cast e k : Fin2 (.s (.s .z))) = k := rfl"),
  -- ... through a definition (a glued name and its unfolding)
  ("g2", "def g2 (k : Fin2 two) (e : Fin2 two = Fin2 (.s (.s .z))) : (cast e k : Fin2 (.s (.s .z))) = k := rfl"),
  -- a generic statement at an open index, and its closed instance (by rfl)
  ("g3", "def g3 (n : N) (k : Fin2 n) (e1 e2 : Fin2 n = Fin2 n) : (cast e1 k : Fin2 n) = (cast e2 k : Fin2 n) := rfl\n" ++
    "def g3i (k : Fin2 two) (e1 e2 : Fin2 two = Fin2 two) : (cast e1 k : Fin2 two) = (cast e2 k : Fin2 two) := rfl")]

/-- The declarations of `p1Decls` that check under the given InReg mode. -/
def p1Accepted (m : InertReg) : List String :=
  p1Decls.filterMap fun (n, d) =>
    let s := runFrontend (R := ZeroOneMany) (p1Prelude ++ d ++ "\n") { globals := { inertReg := m } }
    if s.messages.any (·.severity == .error) then none else some n

/-- `TyOf a` is `a`'s type (as the elaborator built it) -/
def tyOfDef : String := "def TyOf {ω A : Type} (a : A) : Type := A\n"

def ottGroup : Group where
  name := "observational equality"
  exercise := "Exercises 4.10–4.14"
  cases := [
    { name := "function extensionality is definitional", run := fun _ =>
        ok "def funext {A B : Type} (f g : A → B) (h : (x : A) → f x = g x) : f = g := h" },
    { name := "propositional extensionality", run := fun _ =>
        ok "def propext (P Q : Prop) (pq : P → Q) (qp : Q → P) : P = Q := (pq, qp)" },
    { name := "proof irrelevance", run := fun _ =>
        ok "def irr (P : Prop) (p q : P) (C : P → Type) (c : C p) : C q := c" },
    -- nu-transp (P6): at a Σ with a proof component, the equation of the components was
    -- formed at a proposition (`eq`, or `transp` along the first component), which the
    -- kernel rejects: `let h2 := h.2` for `h : p = q` made the declaration fail
    { name := "an equation at a Σ with a proof component is well typed (nu-transp)", run := fun _ =>
        ok ("inductive N where\n  | z\n  | s (n : N)\n" ++
          "def f1 (p q : (x : N) × x = x) (h : p = q) : True :=\n  let h2 := h.2\n  ()\n" ++
          "def f2 (B : Type) (p q : (0 k : True) × B) (h : p = q) : True :=\n  let h2 := h.2\n  ()\n" ++
          "#reduce fun (p q : (x : N) × x = x) => p = q\n" ++
          "#reduce fun (B : Type) (p q : (0 k : True) × B) => p = q")
          ["fun p q => (0 e : p.1 = q.1) × True", "fun B p q => (0 e : True) × cast (refl B) p.2 = q.2"] },
    -- the rule `a =_P b ↦ True` at a proposition `P` never gives `False`: two different
    -- proofs are equal, and the equation proves nothing
    { name := "an equation at a proposition is True, not False (nu-transp)", run := fun _ => do
        let p := "def pf (f : Unit → True) : Unit × True := ((), f ())\n"
        ok (p ++ "#reduce fun (f : Unit → True) => pf f = ((), ())\n" ++
          "def e (f : Unit → True) : pf f = ((), ()) := ((), ())")
          ["fun f => (0 e : True) × True"]
        fails (p ++ "def bad (f : Unit → True) (h : pf f = ((), ())) : False := h.2") "mismatch" },
    -- (closed by mandatory sorts; it was a known gap, pinned) a *neutral* proposition (`P q.1`
    -- for a variable `P : A → Prop`, or `P : Prop`): the Σ rule reads whether a component is
    -- a proposition off the Σ's component sorts, so both rules fire: `g1`'s second
    -- component's equation is `True`, and `g2`'s first is `True` with `ê = reflTy`
    { name := "an equation at a Σ with a neutral proof component (nu-transp; closed by mandatory sorts)", run := fun _ => do
        ok ("def g1 (A : Type) (P : A → Prop) (p q : (x : A) × P x) (h : p = q) : True :=\n  let h2 := h.2\n  ()\n" ++
          "def g2 (P : Prop) (B : Type) (p q : (0 k : P) × B) (h : p = q) : True :=\n  let h2 := h.2\n  ()\n" ++
          "#reduce fun (P : Prop) (B : Type) (p q : (0 k : P) × B) => p = q\n" ++
          "#reduce fun (A : Type) (P : A → Prop) (p q : (x : A) × P x) => p = q")
          ["fun P B p q => (0 e : True) × cast (refl B) p.2 = q.2", "fun A P p q => (0 e : p.1 = q.1) × True"] },
    -- (msorts review F1) `refl` at a Σ whose second component is a proposition, the pair's
    -- type inferred (`fun x => x` with its domain a hole): checked against the computed
    -- equation, by its sides (`eqSigmaSides?`), not by inferring `x = x` first
    { name := "refl at a Σ with a proof component, the pair's type inferred (msorts review F1)", run := fun _ =>
        ok ("def B2 : Type := (x : Unit) × (True → True)\n" ++
          "def P (h : ((), fun (x : True) => x) = (((), fun x => x) : B2)) : Prop := True\n" ++
          "def t3 (h : ((), fun (x : True) => x) = (((), fun x => x) : B2)) : P h := ()\n" ++
          "def t5 : P (refl ((), fun x => x)) := t3 (refl ((), fun x => x))\n" ++
          "def t4 : P (refl ((), fun x => x)) := t3 _\n" ++
          "def t8 : (((), fun (x : True) => x) : B2) = ((), fun x => x) := refl _\n" ++
          "def t9 : (((), fun (x : True) => x) : B2) = ((), fun x => x) := rfl") },
    { name := "equality at Unit is True", run := fun _ =>
        ok "def uu (u v : Unit) : u = v := rfl" },
    { name := "η for pairs, via refl", run := fun _ =>
        ok "def peq {A B : Type} (p : A × B) : p = (p.1, p.2) := refl p" },
    { name := "different type formers are unequal", run := fun _ =>
        ok "def noconf (e : Unit = Empty) : False := e" },
    -- F2 (`wiz-notes/soundness-audit.md`): `vAbsurd` had no case for a glued value, so
    -- `absurd (lem h)` panicked and evaluated to `Sort 0`: `g h` was `Prop`
    { name := "F2: absurd on a lemma's result is stuck, not Prop", run := fun _ => do
        let p := "def lem (h : False) : False := h\ndef g (h : False) : Type := absurd (lem h)\n"
        ok (p ++ "def r (h : False) (x : g h) : g h := x\n#reduce fun (h : False) => g h") ["fun h => absurd h"]
        fails (p ++ "def u (h : False) : g h := True\n") "mismatch" },
    -- D1: no regularity by default: a cast at a variable type stays a cast
    { name := "cast along a variable `A = A` is not the identity (no regularity; it is with --regularity full)", run := fun _ => do
        let reg := "def reg (A : Type) (e : A = A) (a : A) : cast e a = a := rfl"
        fails reg "rfl: the two sides are not definitionally equal"
        okWith .full reg },
    { name := "J from transp and cast", run := fun _ =>
        ok substDef },
    { name := "J computes on refl at a data type, not at a variable family (no regularity)", run := fun _ => do
        let substRefl := substDef ++ "def substRefl {A : Type} (P : A → Type) (a : A) (pa : P a) : subst P (refl a) pa = pa := rfl"
        fails substRefl "rfl: the two sides are not definitionally equal"
        okWith .full substRefl
        ok (substDef ++ "inductive N where\n  | z\n  | s (n : N)\n" ++
          "def substN {A : Type} (a : A) : subst (fun _ => N) (refl a) (N.s N.z) = N.s N.z := rfl") },
    { name := "cast computes on function types (and stays stuck at a variable type)", run := fun _ =>
        ok "#reduce fun (A : Type) (e : (A → A) = (A → A)) (f : A → A) => (cast e f : A → A)"
          ["fun A e f x => cast (e.2 x) (f (cast e.1 x))"] },
    { name := "cast computes on data, constructor by constructor (D1)", run := fun _ =>
        ok ("inductive N where\n  | z\n  | s (n : N)\n" ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {0 n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "#reduce fun (e : N = N) => (cast e (N.s N.z) : N)\n" ++
          "#reduce N.s N.z = N.s N.z\n" ++
          "#reduce fun (n m : N) => (V N n = V N m)\n" ++
          "#reduce fun (e : V N (.s .z) = V N (.s .z)) => (cast e (V.cons N.z V.nil : V N (.s .z)) : V N (.s .z))")
          ["fun e => .s .z", "True", "fun n m => (0 e : (0 e : (0 e : True) × (0 e' : (0 e' : True) × ((0 x : Enum [z, s]) → cast (transp (fun y _ => (0 e'' : Unit = y) × ((0 x' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e).1 (ecase x [Desc.ret (), Desc.rec ω () (Desc.ret ())]) = ecase x [Desc.ret (), Desc.rec ω () (Desc.ret ())])) × True) × ((0 x : N) → True)) × (0 e' : (0 e' : True) × ((0 x : Enum [nil, cons]) → cast (transp (fun y _ => (0 e'' : (N × Unit) = y) × ((0 x' : Desc (N × Unit)) → (N × Unit) = y)) (refl (Desc (N × Unit) × N × Unit)) e).1 (ecase x [Desc.ret (.z, ()), Desc.arg 0 N (fun n' => Desc.arg ω N (fun x' => Desc.rec ω (n', ()) (Desc.ret (.s n', ()))))]) = ecase x [Desc.ret (.z, ()), Desc.arg 0 N (fun n' => Desc.arg ω N (fun x' => Desc.rec ω (n', ()) (Desc.ret (.s n', ()))))])) × (0 e'' : n = m) × True",
           "fun e => .cons .z .z .nil"] },
    { name := "type equality", run := fun _ =>
        ok "def t : Type = Type := refl Type" },
    { name := "propositions in a function type's domain compare by equivalence", run := fun _ =>
        ok "#reduce (True → Unit) = ((True → True) → Unit)"
          ["(0 e : (0 _ : (0 x : True → True) → True) × ((0 x : True) → True → True)) × ((0 x : True → True) → True)"] },
    { name := "equivalent propositions of different shapes don't prove False", run := fun _ =>
        -- `True = (True → True)` at `Prop`, carried into `Type` by congruence; comparing
        -- the domains by shape made the equation `False`
        fails ("def apTy (A : Type) (F : A → Type) (a b : A) (e : a = b) : F a = F b :=\n" ++
          "  transp (fun b _ => F a = F b) (refl (F a)) e\n" ++
          "def G : Prop → Type := fun X => X → Unit\n" ++
          "def e : True = (True → True) := ((fun u => fun v => v), (fun f => ()))\n" ++
          "def bad : G True = G (True → True) := apTy Prop G True (True → True) e\n" ++
          "def anyType (A : Type) : A := let (x, y) := bad; absurd x") "absurd expects" },
    -- the types the elaborator builds (a definition's telescope, constructor types)
    -- carry their sorts too, so equations between them compute instead of waiting
    { name := "a definition's type carries its sort: propositions in the domain", run := fun _ =>
        ok (tyOfDef ++ "def f (x : True) : Unit := ()\ndef g (x : True → True) : Unit := ()\n" ++
          "#reduce TyOf f = TyOf g")
          ["(0 e : (0 _ : (0 x : True → True) → True) × ((0 x : True) → True → True)) × ((0 x : True → True) → True)"] },
    { name := "a definition's type carries its sort: other types", run := fun _ =>
        ok (tyOfDef ++ "inductive N where\n  | z\n  | s (n : N)\ndef h (x : N) : N := x\n" ++
          "#reduce TyOf h = (N → N)\n" ++
          "#reduce fun (e : TyOf h = (N → N)) (u : TyOf h) => (cast e u : N → N)")
          ["(0 e : (0 e : True) × (0 e' : (0 e' : True) × ((0 x : Enum [z, s]) → cast (transp (fun y _ => (0 e'' : Unit = y) × ((0 x' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e).1 (ecase x [Desc.ret (), Desc.rec ω () (Desc.ret ())]) = ecase x [Desc.ret (), Desc.rec ω () (Desc.ret ())])) × True) × ((0 x : N) → (0 e' : True) × (0 e'' : (0 e'' : True) × ((0 x' : Enum [z, s]) → cast (transp (fun y _ => (0 e''' : Unit = y) × ((0 x'' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e').1 (ecase x' [Desc.ret (), Desc.rec ω () (Desc.ret ())]) = ecase x' [Desc.ret (), Desc.rec ω () (Desc.ret ())])) × True)", "fun e u x => u x"] },
    { name := "a constructor's type carries its sort", run := fun _ =>
        ok (tyOfDef ++ "inductive Box (A : Type) where\n  | mk (a : A)\n" ++
          "#reduce TyOf (@Box.mk Unit) = (Unit → Box Unit)")
          ["(0 e : True) × ((0 x : Unit) → (0 e' : True) × (0 e'' : (0 e'' : True) × ((0 x' : Enum [mk]) → cast (transp (fun y _ => (0 e''' : Unit = y) × ((0 x'' : Desc Unit) → Unit = y)) (refl (Desc Unit × Unit)) e').1 (ecase x' [Desc.arg ω Unit (fun a => Desc.ret ())]) = ecase x' [Desc.arg ω Unit (fun a => Desc.ret ())])) × True)"] },
    { name := "a match on several scrutinees whose types mention a variable", run := fun _ =>
        ok "def pick (A : Type) (x y : A) : A := match x, y with\n  | a, b => b" },
    { name := "equality of proofs is rejected", run := fun _ =>
        fails "def bad (P : Prop) (p q : P) : p = q := rfl" "equality is for types" },
    { name := "wrong equation", run := fun _ =>
        fails "def bad (A : Type) (a b : A) : a = b := rfl" "rfl: the two sides are not definitionally equal" },
    -- D1: regularity beyond the inert types is off by default, and the program checks. It
    -- used to loop with `--regularity full` and an evaluator that runs proofs
    -- (`--eager-proofs`): regularity was then a rule of evaluation, decided by comparing the
    -- two types as written. Now regularity is decided by conversion only, so the evaluator
    -- never fires it, and the program checks in every mode
    { name := "D1 (Abel–Coquand): the program checks (no regularity: the box's cast casts its proof field)", run := fun _ => do
        ok (abelCoquand "omega")
        ok (abelCoquand) },
    { name := "D1 (Abel–Coquand): with regularity and eager proofs the program checks too (regularity is a rule of conversion, not of evaluation)", run := fun _ =>
        checkTerminates (abelCoquand) "full+eager" },
    { name := "D1 (Abel–Coquand): a box in a box is not inert either (checks, with regularity and eager proofs too)", run := fun _ => do
        unless (abelCoquandNested.splitOn "unbox2").length > 2 do throw (IO.userError "variant not built")
        ok abelCoquandNested
        checkTerminates abelCoquandNested "full+eager" },
    -- (from PR #40) The cast's source type written by name, `Box T2`, or as inferred,
    -- `Box (Top → Top)`: the syntactic rule fired for one spelling and not for the other, so
    -- the same program looped or terminated depending on how a type was written. Decided by
    -- conversion, the two spellings behave alike, in every mode
    { name := "D1 (Abel–Coquand): the cast's source type by name or as inferred: the same verdict and the same termination in every mode", run := fun _ => do
        let named := abelCoquand
        let inferred := named.replace ": Box T2)" ": Box (Top → Top))"
        unless named != inferred && (named.splitOn ": Box T2)").length == 2 do throw (IO.userError "variant not built")
        for p in [named, inferred] do
          ok p
          for mode in ["off", "full", "full+eager", "off+eager"] do checkTerminates p mode },
    { name := "regularity at inert types: an indexed recursor computes at a data motive (Vec.length)", run := fun _ =>
        ok ("inductive N where\n  | z\n  | s (n : N)\n" ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {0 n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "def len {A : Type} {0 n : N} : V A n → N\n  | .nil => .z\n  | .cons _ xs => .s (len xs)\n" ++
          "def lenCons {A : Type} {0 n : N} (x : A) (xs : V A n) : len (V.cons x xs) = N.s (len xs) := rfl\n" ++
          "def castN (e : N = N) (n : N) : (cast e n : N) = n := rfl\n") },
    { name := "no regularity at a type with a variable parameter", run := fun _ =>
        fails ("inductive L (A : Type) where\n  | nil\n  | cons (x : A) (xs : L A)\n" ++
          "def castL (A : Type) (e : L A = L A) (l : L A) : (cast e l : L A) = l := rfl\n") "rfl: the two sides are not definitionally equal" },
    -- P1: regularity at inert types is decided by conversion (InReg_conv, the default): all
    -- eight probes check, and the control at a type variable does not
    { name := "P1: InReg decided by conversion accepts the eight probes, open indices too (the default)", run := fun _ => do
        checkEq (repr ["t1", "t2", "h", "h2", "h3", "g1", "g2", "g3"]).pretty (repr (p1Accepted .conv)).pretty
        let dflt := p1Decls.filterMap fun (n, d) =>
          if (runFrontend (R := ZeroOneMany) (p1Prelude ++ d ++ "\n")).messages.any (·.severity == .error) then none else some n
        checkEq (repr ["t1", "t2", "h", "h2", "h3", "g1", "g2", "g3"]).pretty (repr dflt).pretty },
    -- the evaluator's fast path alone (`--inert ground`) is stable under substitution (h3
    -- checks, and so does its reduct h2) but gives up a neutral value at an open index
    { name := "P1: the fast path alone (ground) is stable, and rejects t1 and t2", run := fun _ =>
        checkEq (repr ["h", "h2", "h3", "g1", "g2", "g3"]).pretty (repr (p1Accepted .ground)).pretty },
    { name := "D1: with eager proofs, a cast between propositions applies the equivalence, not regularity", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) abelCoquandLiteral { globals := { lazyProofs := false } }
        checkEq (repr ["fun x => x"]).pretty (repr (s.messages.toList.map (·.text))).pretty },
    { name := "D1 (off): without regularity the program checks", run := fun _ =>
        okWith .off (abelCoquand) },
    -- P2 (the default): proofs are never evaluated, so the loop, which lives in a proof,
    -- is never run, even with full regularity
    { name := "P2: proofs are never evaluated, so Abel–Coquand checks even with full regularity (and nested)", run := fun _ => do
        checkTerminates (abelCoquand) "full"
        checkTerminates abelCoquandNested "full"
        checkTerminates (abelCoquand) "off" },
    { name := "P2: a cast between propositions is stuck (a proof), not the equivalence applied", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) abelCoquandLiteral
        let out := (s.messages.map (·.render abelCoquandLiteral)).toList
        unless out.any (·.contains "cast") do throw (IO.userError s!"expected a stuck cast, got {out}") }
  ]

builtin_initialize registerGroup ottGroup

end Tests.Elab
