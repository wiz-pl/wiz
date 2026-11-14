import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- A language server with `src` open: the server and what it sent (the diagnostics). -/
def tacticLsp (src : String) : IO (LSP.Server × Array Lean.Json) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let srv : LSP.Server :=
    { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", prelude), trusted := ["Prelude"] }
  let json (s : String) : Lean.Json := (Lean.Json.parse s).toOption.get!
  let (srv, _) := LSP.handle srv (json "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}")
  pure (LSP.handle srv (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
    ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])]))

/-- A recursive representation predicate in the style of separation logic, for `unfold`. -/
def unfoldPrelude : String := "import Prelude
def len : List Nat → Nat
  | .nil => 0
  | .cons _ xs => Nat.succ (len xs)
def Wrap (n : Nat) : Prop := n = n
def And' (A B : Prop) : Prop := (R : Prop) → (A → B → R) → R
def Pred : Type := Nat → Prop
def ex (J : Nat → Pred) : Pred := fun h => (R : Prop) → ((n : Nat) → J n h → R) → R
def cell (p x n : Nat) : Pred := fun h => h = Nat.add p (Nat.add x n)
def star (A B : Pred) : Pred := fun h => And' (A h) (B h)
def MList : List Nat → Nat → Pred
  | .nil, p => fun h => p = 0
  | .cons x L, p => ex (fun n => star (cell p x n) (MList L n))
def Ent (A B : Pred) : Prop := (h : Nat) → A h → B h
"

/-- Data in goals, and a tactic `dump` that traces the goal as a tree of head names. -/
def reflectPrelude : String := "import Prelude
inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A 0
  | cons {n : Nat} (x : A) (xs : Vec A n) : Vec A (Nat.succ n)
inductive Prog : Type where
  | ret (n : Nat)
  | get (l : Nat) (k : Nat → Prog)
def swap (p : Nat) : Prog := Prog.get p (fun v => Prog.ret v)
def P (xs : List Nat) : Prop := True
def Q (c : Prog) : Prop := True
def V {n : Nat} (v : Vec Bool n) : Prop := True
def Expr.dumpL : Nat → List Expr → String
  | .zero, _ => \"…\"
  | _, .nil => \"\"
  | .succ f, .cons e es => String.append \" \" (String.append (match Expr.view e with
      | .const n .nil => n
      | .const n args => String.append \"(\" (String.append n (String.append (Expr.dumpL f args) \")\"))
      | .var i .nil => \"#\"
      | .var i args => String.append \"(#\" (String.append (Expr.dumpL f args) \")\")
      | .lit n => \"lit\"
      | .sort u => \"Sort\"
      | .pi _ _ _ _ _ => \"Π\"
      | .lam x b => String.append \"(λ\" (String.append x (String.append \".\" (String.append (Expr.dumpL f (.cons b .nil)) \")\")))
      | .other _ _ => \"?\") (Expr.dumpL f es))
def Expr.dump (e : Expr) : String := Expr.dumpL 1000 (.cons e .nil)
syntax (name := dump) \"dump\" : tactic
def dumpTac : Tactic := fun _ => do
  g ← TacticM.mainGoal;
  ty ← TacticM.goalType g;
  TacticM.trace (Expr.dump ty)
attribute [tactic tactic.dump] dumpTac
"

def tacticGroup : Group where
  name := "tactics"
  exercise := "Exercises 6.4–6.6"
  cases := [
    { name := "intro and exact", run := fun _ =>
        okLib "import Prelude\ndef id' : (A : Type) → A → A := by\n  intro A\n  intro x\n  exact x\n#check id'"
          ["id' : (A : Type) → A → A"] },
    { name := "tactics separated by ;", run := fun _ =>
        okLib "import Prelude\ndef k : Nat → Bool → Nat := by intro n; intro b; exact n" },
    { name := "assumption (Exercise 6.6)", run := fun _ =>
        okLib "import Prelude\ndef k : Nat → Bool → Nat := by intro n; intro b; assumption" },
    { name := "rfl is a tactic macro", run := fun _ =>
        okLib "import Prelude\ndef two : 1 + 1 = 2 := by rfl" },
    { name := "apply makes goals for the arguments", run := fun _ =>
        okLib "import Prelude\ndef ap : (A B : Type) → (A → B) → A → B := by\n  intro A; intro B; intro f; intro a\n  apply f\n  assumption" },
    { name := "first and try", run := fun _ =>
        okLib "import Prelude\ndef t : Nat := by try exact Bool.true; first | exact Bool.true | exact 3" },
    { name := "unsolved goals are reported with their context", run := fun _ =>
        failsLib "import Prelude\ndef bad : Nat → Bool := by intro n" "unsolved goals:\nn : Nat\n⊢ Bool" },
    { name := "a failing tactic is an error at the tactic", run := fun _ =>
        failsLib "import Prelude\ndef bad : Nat := by assumption" "assumption: no hypothesis matches the goal" },
    { name := "the proof term is checked by the kernel", run := fun _ =>
        okLib "import Prelude\ndef k : Nat → Nat := by intro n; exact (n + 1)\n#eval k 41" ["42"] },
    { name := "a user-defined tactic, written in Wiz", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := intros2) \"intros2\" : tactic\n" ++
          "def myIntros : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  g1 ← TacticM.intro g \"a\";\n  g2 ← TacticM.intro g1 \"b\";\n" ++
          "  TacticM.replaceMainGoal (.cons g2 .nil)\nattribute [tactic tactic.intros2] myIntros\n" ++
          "def k : Nat → Nat → Nat := by intros2; exact b") },
    -- trace (docs/stages/06-macros.md, 6d)
    { name := "trace is an info message at the tactic; trace_state shows the goals", run := fun _ => do
        let src := "import Prelude\ndef k : Nat → Bool → Nat := by\n  intro n\n  trace \"hello\"\n  trace_state\n  intro b\n  exact n"
        okLib src ["hello", "n : Nat\n⊢ Bool → Nat"]
        let loader ← preludeLoader
        let s := runFrontend (R := ZeroOneMany) src { loader, trustedModule := Tests.libModule }
        checkEq ["4:3: info: hello"] ((s.messages.toList.take 1).map (·.render src)) },
    { name := "trace_state: several goals, and none", run := fun _ =>
        okLib ("import Prelude\ndef ap : (A B : Type) → (A → B) → A → B := by\n  intro A; intro B; intro f; intro a\n" ++
          "  apply f\n  trace_state\n  assumption\n  trace_state")
          ["A : Type\nB : Type\nf : A → B\na : A\n⊢ A", "no goals"] },
    { name := "a trace in a branch that fails is dropped with it", run := fun _ =>
        okLib "import Prelude\ndef t : Nat := by\n  try (trace \"dropped\"; exact Bool.true)\n  first | (trace \"dropped too\"; assumption) | (trace \"kept\"; exact 3)"
          ["kept"] },
    { name := "the traces before an error are still shown", run := fun _ => do
        checkEq ["info: one", "error: assumption: no hypothesis matches the goal"]
          (← msgsLib "import Prelude\ndef bad : Nat := by\n  trace \"one\"\n  assumption\n  trace \"never\"")
        let ms ← msgsLib "import Prelude\ndef bad : Nat := by\n  trace \"one\"\n  exact Bool.true"
        checkEq "info: one" (ms.headD "")
        checkEq 2 ms.length },
    { name := "TacticM.trace from a user tactic and from a macro; #check keeps traces", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := say) \"say\" : tactic\n" ++
          "def sayTac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  s ← TacticM.ppGoal g;\n  t ← TacticM.goalType g;\n  u ← TacticM.ppExpr g t;\n" ++
          "  TacticM.trace (String.append \"goal: \" (String.append s (String.append \" / \" u)))\nattribute [tactic tactic.say] sayTac\n" ++
          "def k : Nat → Nat := by intro n; say; exact n\n" ++
          "syntax (name := tw) \"tw!\" term : term\ndef twMacro : Macro := fun stx => do\n  u ← TacticM.trace \"expanding\";\n  MacroM.pure (Syntax.getArg stx 1)\n" ++
          "attribute [macro term.tw] twMacro\ndef z : Nat := tw! 3\n#check (by trace \"checking\"; exact 1 : Nat)")
          ["goal: n : Nat\n⊢ Nat / Nat", "expanding", "checking", "1 : Nat"] },
    -- names (docs/stages/06-macros.md, 6e)
    { name := "intros takes the binders' names, inaccessible; rename_i names them", run := fun _ => do
        okLib ("import Prelude\ndef k : (n : Nat) → (b : Bool) → Nat → Nat := by\n  intros\n  trace_state\n  rename_i c, m\n  trace_state\n  exact m")
          ["n✝ : Nat\nb✝ : Bool\nx✝ : Nat\n⊢ Nat", "n✝ : Nat\nc : Bool\nm : Nat\n⊢ Nat"]
        okLib "import Prelude\ndef k : (n : Nat) → (n : Nat) → Nat := by\n  intros\n  trace_state\n  rename_i a\n  exact a"
          ["n✝ : Nat\nn✝1 : Nat\n⊢ Nat"]
        failsLib "import Prelude\ndef k : Nat → Nat := by\n  intros\n  rename_i a, b\n  exact a" "rename_i: more names than inaccessible hypotheses" },
    { name := "an inaccessible name cannot be written", run := fun _ => do
        let ms ← msgsLib "import Prelude\ndef bad : (n : Nat) → Nat := by\n  intros\n  exact n"
        checkEq ["error: unknown identifier 'n'; the hypothesis n✝ is inaccessible: name it with `intro n` or `rename_i n`"] ms },
    { name := "TacticM.introFresh: the binder's name, made fresh, and returned", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := in3) \"in3\" : tactic\n" ++
          "def in3Tac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  p ← TacticM.introFresh g \"\";\n  q ← TacticM.introFresh p.2 \"\";\n  r ← TacticM.introFresh q.2 \"\";\n  s ← TacticM.introFresh r.2 \"n\";\n" ++
          "  u ← TacticM.trace (String.append p.1 (String.append \" \" (String.append q.1 (String.append \" \" (String.append r.1 (String.append \" \" s.1))))));\n" ++
          "  TacticM.replaceMainGoal (.cons s.2 .nil)\nattribute [tactic tactic.in3] in3Tac\n" ++
          "def k : (n : Nat) → (n : Nat) → (1 = 1) → Bool → Nat := by\n  in3\n  trace_state\n  exact n1")
          ["n n1 h n2", "n : Nat\nn1 : Nat\nh : True\nn2 : Bool\n⊢ Nat"] },
    { name := "a hole solved under a binder keeps the binder's name (not x0)", run := fun _ =>
        okLib ("import Prelude\ndef ap0 {B : Nat → Type} (f : (k : Nat) → B k) : B 0 := f 0\ndef g0 (n : Nat) : List Nat := .nil\n#check ap0 g0\n" ++
          "def Ex {A : Type} (P : A → Prop) : Prop := (R : Prop) → ((a : A) → P a → R) → R\n" ++
          "def Ex.elim {A : Type} {P : A → Prop} (R : Prop) (e : Ex P) (k : (a : A) → P a → R) : R := e R k\n" ++
          "def t (e : Ex (fun (n : Nat) => n = 0)) : Ex (fun (m : Nat) => m = 0) := by\n  apply Ex.elim _ e\n  intros\n  trace_state\n" ++
          "  rename_i w, h\n  exact (fun R k => k w h)")
          ["ap0 (fun k => List Nat) g0 : List Nat", "e : Ex Nat (fun n => n = 0)\na✝ : Nat\nh✝ : a✝ = 0\n⊢ Ex Nat (fun m => m = 0)"] },
    -- unfolding and rewriting (docs/stages/06-macros.md, 6f)
    { name := "unfold: a definition once, its match computed, the recursive call folded back", run := fun _ =>
        okLib (unfoldPrelude ++
          "def t2 (x : Nat) (L : List Nat) (p : Nat) : Ent (MList (.cons x L) p) (MList (.cons x L) p) := by\n  unfold MList\n  trace_state\n  unfold Ent\n  intros\n  assumption\n" ++
          "def t (x : Nat) (xs : List Nat) : Wrap (len (.cons x xs)) := by\n  unfold len\n  trace_state\n  unfold Wrap\n  rfl")
          ["x : Nat\nL : List Nat\np : Nat\n⊢ Ent (ex (fun n => star (cell p x n) (MList L n))) (ex (fun n => star (cell p x n) (MList L n)))",
           "x : Nat\nxs : List Nat\n⊢ Wrap (.succ (len xs))"] },
    { name := "unfold: several names; it fails when nothing changes (stuck, or absent); not a definition", run := fun _ => do
        okLib (unfoldPrelude ++
          "def t3 (L : List Nat) (p : Nat) : Ent (star (MList L p) (MList L p)) (MList L p) := by\n  unfold Ent, star\n  trace_state\n  intros\n  rename_i h, a\n  exact (a _ (fun x y => x))")
          ["L : List Nat\np : Nat\n⊢ (h : Nat) → And' (MList L p h) (MList L p h) → MList L p h"]
        failsLib (unfoldPrelude ++ "def t3 (L : List Nat) (p : Nat) : Ent (MList L p) (MList L p) := by\n  unfold MList\n  unfold Ent\n  intros\n  assumption")
          "unfold: nothing to unfold: the goal has no application of MList that computes"
        failsLib (unfoldPrelude ++ "def t3 (L : List Nat) (p : Nat) : Ent (MList L p) (MList L p) := by\n  unfold Ent, star\n  intros\n  assumption")
          "unfold: nothing to unfold: the goal has no application of star that computes"
        okLib (unfoldPrelude ++ "syntax (name := tryUnfold) \"try_unfold\" : tactic\n" ++
          "def tryUnfoldTac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  ty ← TacticM.goalType g;\n  ty' ← TacticM.unfold g \"MList\" ty;\n" ++
          "  s ← TacticM.ppExpr g ty';\n  TacticM.trace s\nattribute [tactic tactic.tryUnfold] tryUnfoldTac\n" ++
          "def t3 (L : List Nat) (p : Nat) : Ent (MList L p) (MList L p) := by\n  try_unfold\n  unfold Ent\n  intros\n  assumption")
          ["Ent (MList L p) (MList L p)"]
        failsLib "import Prelude\ndef t : Nat := by\n  unfold List.cons\n  exact 0" "unfold: List.cons is not a definition"
        failsLib "import Prelude\ndef t : Nat := by\n  unfold nope\n  exact 0" "unfold: unknown constant nope" },
    { name := "unfold: a definition by cases applied to a numeral computes its match (a lazy eliminator is forced)", run := fun _ =>
        okLib ("import Prelude\ndef w2 (a0 a1 : Bool) (i : Nat) : Bool := match i with\n  | .zero => a0\n  | _ => a1\n" ++
          "def t (a b : Bool) (h : b = .true) : w2 a b 1 = .true := by\n  unfold w2\n  trace_state\n  exact h")
          ["a : Bool\nb : Bool\nh : b = .true\n⊢ b = .true"] },
    { name := "whnf computes the goal's head; change restates it (checked by conversion)", run := fun _ => do
        okLib (unfoldPrelude ++
          "def t4 (x : Nat) (L : List Nat) (p : Nat) : Ent (MList (.cons x L) p) (MList (.cons x L) p) := by\n  whnf\n  trace_state\n" ++
          "  change Ent (MList (.cons x L) p) (ex (fun n => star (cell p x n) (MList L n)))\n  trace_state\n  unfold Ent\n  intros\n  assumption")
          ["x : Nat\nL : List Nat\np : Nat\n⊢ (h : Nat) → MList (.cons x L) p h → MList (.cons x L) p h",
           "x : Nat\nL : List Nat\np : Nat\n⊢ Ent (MList (.cons x L) p) (ex (fun n => star (cell p x n) (MList L n)))"]
        failsLib "import Prelude\ndef t : Nat := by\n  change Bool\n  exact 0" "change: the new goal is not convertible with the old one" },
    { name := "rw: rewrite with an equation, left to right and back; the kernel checks the cast", run := fun _ => do
        okLib ("import Prelude\ndef r (a b : Nat) (h : a = b) (P : Nat → Prop) (pb : P b) : P a := by\n  rw h\n  trace_state\n  exact pb\n" ++
          "def r2 (a b : Nat) (h : a = b) (P : Nat → Type) (pa : P a) : P b := by\n  rw ← h\n  exact pa\n" ++
          "def r3 (f : Nat → Nat) (a b : Nat) (h : f a = b) (Q : Nat → Nat → Prop) (q : Q b b) : Q (f a) (f a) := by\n  rw h\n  exact q\n" ++
          "#check r2")
          ["a : Nat\nb : Nat\nh : a = b\nP : Nat → Prop\npb : P b\n⊢ P b",
           "r2 : (a : Nat) → (b : Nat) → a = b → (P : Nat → Type) → P a → P b"]
        failsLib "import Prelude\ndef r (a b c : Nat) (h : a = b) (P : Nat → Prop) (pc : P c) : P c := by\n  rw h\n  exact pc" "rewrite: the goal does not mention a"
        failsLib "import Prelude\ndef r (a : Nat) (P : Nat → Prop) (pa : P a) : P a := by\n  rw pa\n  exact pa" "rewrite: not an equation" },
    -- typed reflection (docs/stages/06-macros.md, 6g)
    { name := "constructor applications are reflected by name, with the type's parameters", run := fun _ =>
        okLib (reflectPrelude ++
          "def t1 (x : Nat) (L : List Nat) : P (.cons x (.cons (Nat.succ x) L)) := by\n  dump\n  exact ()\n" ++
          "def t2 : P (.cons 3 .nil) := by\n  dump\n  exact ()\n" ++
          "def t3 (b : Bool) : V (Vec.cons b (Vec.cons .true Vec.nil)) := by\n  dump\n  exact ()\n" ++
          "def t4 (p : Nat) : Q (Prog.get p (fun v => Prog.ret (Nat.succ v))) := by\n  dump\n  exact ()")
          [" (P (List.cons Nat # (List.cons Nat (Nat.succ #) #)))",
           " (P (List.cons Nat lit (List.nil Nat)))",
           " (V (Nat.succ (Nat.succ lit)) (Vec.cons Bool (Nat.succ lit) # (Vec.cons Bool lit Bool.true (Vec.nil Bool))))",
           " (Q (Prog.get # (λv. (Prog.ret (Nat.succ #)))))"] },
    { name := "a reflected goal reifies to the same goal; two reflections are syntactically equal", run := fun _ =>
        okLib (reflectPrelude ++ "syntax (name := again) \"again\" : tactic\n" ++
          "def againTac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  ty ← TacticM.goalType g;\n  ty2 ← TacticM.goalType g;\n" ++
          "  u ← TacticM.trace (match Expr.beq ty ty2 with\n    | .true => \"equal\"\n    | .false => \"different\");\n" ++
          "  g' ← TacticM.change g ty;\n  TacticM.replaceMainGoal (.cons g' .nil)\nattribute [tactic tactic.again] againTac\n" ++
          "def t (b : Bool) (x : Nat) : (V (Vec.cons b Vec.nil) → P (.cons x .nil)) := by\n  again\n  trace_state\n  intros\n  exact ()")
          ["equal", "b : Bool\nx : Nat\n⊢ V 1 (.cons 0 b .nil) → P (.cons x .nil)"] },
    { name := "whnf, then the constructor: a program is read off by its head (no unification)", run := fun _ =>
        okLib (reflectPrelude ++ "syntax (name := shape) \"shape\" : tactic\n" ++
          "def shapeArg : List Expr → TacticM Unit\n  | .cons c _ => do\n    g ← TacticM.mainGoal;\n    c' ← TacticM.whnf g c;\n    r ← TacticM.ctorApp c';\n" ++
          "    (match r with\n    | .some p => do\n      i ← TacticM.ctorInfo p.1;\n      TacticM.trace (String.append p.1 (String.append \" with fields\" (Expr.dumpL 100 p.2)))\n    | .none => TacticM.trace \"not a constructor\")\n" ++
          "  | .nil => TacticM.fail \"no argument\"\n" ++
          "def shapeTac : Tactic := fun _ => do\n  g ← TacticM.mainGoal;\n  ty ← TacticM.goalType g;\n  match Expr.appOf \"Q\" ty with\n  | .some args => shapeArg args\n  | .none => TacticM.fail \"not Q\"\n" ++
          "attribute [tactic tactic.shape] shapeTac\n" ++
          "def t (p : Nat) : Q (swap p) := by\n  shape\n  exact ()\n" ++
          "def t' (c : Prog) : Q c := by\n  shape\n  exact ()")
          ["Prog.get with fields # (λv. (Prog.ret #))", "not a constructor"] },
    { name := "traces reach the language server (a diagnostic) and the infoview (wiz/plainGoal)", run := fun _ => do
        let src := "import Prelude\ndef k : Nat → Nat := by\n  intro n\n  trace_state\n  exact n\n"
        let (srv, out) ← tacticLsp src
        let ds := match LSP.get? out[0]! ["params", "diagnostics"] with
          | some (.arr ds) => ds.toList
          | _ => []
        checkEq ["3: n : Nat\n⊢ Nat"] (ds.map fun d => s!"{LSP.getNat d ["severity"]}: {LSP.getStr d ["message"]}")
        checkEq [3] (ds.map fun d => LSP.getNat d ["range", "start", "line"])
        let (_, r) := LSP.handle srv ((Lean.Json.parse "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"wiz/plainGoal\",\"params\":{\"textDocument\":{\"uri\":\"file:///t.wiz\"},\"position\":{\"line\":3,\"character\":5}}}").toOption.get!)
        checkEq "```wiz\nn : Nat\n⊢ Nat\n```\n\nn : Nat\n⊢ Nat" (LSP.getStr r[0]! ["result", "rendered"])
        checkEq "[\"n : Nat\\n⊢ Nat\"]" (((LSP.get? r[0]! ["result", "messages"]).map (·.compress)).getD "") }
  ]

builtin_initialize registerGroup tacticGroup

end Tests.Elab
