import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## Regions: borrow checking as typing (lib/Region.wiz, Feral RD12) -/

def regionsPush : String :=
  "def push1 {ρ : Region} (1 v : Uniq ρ (List Nat)) : Result1 Unit (Uniq ρ (List Nat)) :=\n  let 1 (xs, v) := Uniq.peek v;\n  .ok () (Uniq.write v (List.cons 1 xs))\n"

def regionsLongest : String :=
  "def longest {ρa ρb : Region} (0 h : Outlives ρa ρb) (x : Shr ρa Nat) (y : Shr ρb Nat) : Result (Shr ρb Nat) :=\n" ++
  "  match Nat.lt x.val y.val with\n  | .true => .ok y\n  | .false => .ok (Shr.weaken h x)\n"

/-- `swap` through two `&mut`, called on two locals borrowed in nested scopes. -/
def regionsSwap : String := r#"def swap {ρ₁ ρ₂ : Region} {A : Type} (1 x : Uniq ρ₁ A) (1 y : Uniq ρ₂ A) : Result1 Unit ((1 _ : Uniq ρ₁ A) × Uniq ρ₂ A) :=
  let 1 (t, x) := Uniq.peek x;
  let 1 (u, y) := Uniq.peek y;
  .ok () (Uniq.write x u, Uniq.write y t)
"#

/-- A linked list through `&mut`: recursion on reborrows of the tails, and a cursor. -/
def regionsList : String := r#"partial def incrAll {ρ : Region} (1 l : Uniq ρ (List Nat)) : Result1 Unit (Uniq ρ (List Nat)) :=
  Uniq.reborrow l (fun ρ' h l r =>
    let 1 (v, r) := Uniq.peek r;
    match v with
    | .nil => .ok () r
    | .cons x tail => (match Uniq.borrow ρ' tail (fun ρt ht tail rt => incrAll rt) with
      | .ok q => let (u, tail) := q; .ok () (Uniq.write r (List.cons (Nat.succ x) tail))
      | .err e => .err e r))
partial def pushBack.loop {ρ : Region} (x : Nat) (1 cur : Mut ρ (List Nat) (List Nat)) : Mut ρ (List Nat) (List Nat) :=
  let 1 (v, cur) := Mut.peek cur;
  match v with
  | .cons y next => pushBack.loop x (Mut.comp cur (fun (_ : List Nat) => (next, fun (n : List Nat) => List.cons y n)))
  | .nil => Mut.set cur (List.cons x List.nil)
def pushBack {ρ : Region} (1 l : Uniq ρ (List Nat)) (x : Nat) : Result1 Unit (Uniq ρ (List Nat)) :=
  .ok () (Mut.release (pushBack.loop x (Mut.whole l)))
def listMain (xs : List Nat) : Result (List Nat) :=
  match Uniq.borrow Region.static xs (fun ρ h xs r =>
    match incrAll r with
    | .ok u r => pushBack r 7
    | .err e r => .err e r) with
  | .ok p => let (u, xs) := p; .ok xs
  | .err e => .err e
"#

/-- Returning one of two `&mut` borrows: `'a : 'b` is the evidence for `Mut.weaken`; the
lender not returned rides along in the backward function (`Mut.alongside`). -/
def regionsPick (bound : Bool := true) : String :=
  let (hb, hx) := if bound then ("(0 h : Outlives ρa ρb) ", "Mut.weaken h (Mut.ofUniq x)") else ("", "Mut.ofUniq x")
  s!"def pick \{ρa ρb : Region} {hb}(c : Bool) (1 x : Uniq ρa Nat) (1 y : Uniq ρb Nat) :
    Borrowed (Mut ρb Nat ((1 _ : Uniq ρa Nat) × Uniq ρb Nat)) ((1 _ : Uniq ρa Nat) × Uniq ρb Nat) :=
  match c with
  | .true => .ok (Mut.alongside ({hx}) y (fun (x : Uniq ρa Nat) (y : Uniq ρb Nat) => (x, y)))
  | .false => .ok (Mut.alongside (Mut.ofUniq y) x (fun (y : Uniq ρb Nat) (x : Uniq ρa Nat) => (x, y)))
"

def regionsSetPick : String :=
  "def setPick {ρa ρb : Region} (0 h : Outlives ρa ρb) (c : Bool) (1 x : Uniq ρa Nat) (1 y : Uniq ρb Nat) : Result1 Unit ((1 _ : Uniq ρa Nat) × Uniq ρb Nat) :=\n" ++
  "  match pick h c x y with\n  | .ok m => .ok () (Mut.finish (Mut.set m 10))\n  | .err e q => .err e q\n"

/-- Two locals `a := 1` and `b := 2`, borrowed in nested scopes (`outer` first; the outer
handle is threaded through the inner scope), and `body` on the borrows `ra`, `rb`
(evidence `ha`, `hb`); `body` hands back `(ra, rb)` in a `Result1`. -/
def regionsTwo (name outer body : String) : String :=
  let (o, i) := if outer == "a" then ("a", "b") else ("b", "a")
  s!"def {name} : Result (Nat × Nat) :=
  match Uniq.borrow Region.static {if o == "a" then 1 else 2} (fun ρ{o} h{o} {o} r{o} =>
    match Uniq.borrowIn ρ{o} {if i == "a" then 1 else 2} r{o} (fun ρ{i} h{i} {i} r{o} r{i} =>
      match {body} with
      | .ok u q => let 1 (ra, rb) := q; .ok () (r{o}, r{i})
      | .err e q => let 1 (ra, rb) := q; .err e (r{o}, r{i})) with
    | .ok q r => let (u, x) := q; .ok x r
    | .err e r => .err e r) with
  | .ok p => let (x, y) := p; .ok {if o == "a" then "(y, x)" else "(x, y)"}
  | .err e => .err e
"

/-- The front end's state for `src`, with every library importable. -/
def libsState (src : String) (unbox : Bool := false) : IO (CommandState ZeroOneMany) := do
  let s := runFrontend (R := ZeroOneMany) src
    { trustedModule := Tests.libModule, loader := ← libLoader, globals := { unboxStructs := unbox } }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure s

/-- The optimised IR of the program computing `n`: `n` and the functions lifted from it. -/
def libsIR (s : CommandState ZeroOneMany) (n : Name) : IO (List String) := do
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      IR.lowerProgram code (.global n) : Except String (Array IR.Decl)) with
  | .ok decls =>
    pure ((decls.filter (·.name.startsWith n)).toList.map (·.optimize.toString))
  | .error e => throw (IO.userError e)

/-- The objects allocated computing `n` on the checked heap (a leak is an error). -/
def libsAllocs (s : CommandState ZeroOneMany) (n : Name) : IO Nat := do
  match (do
      let code ← (compileReachable s.globals s.builtins [n]).mapError toString
      let decls ← IR.lowerProgram code (.global n)
      let (_, a) ← IR.runProgram (decls.map (·.optimize))
      pure a : Except String Nat) with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{n}: {e}")

def regionsGroup : Group where
  name := "regions"
  exercise := "lib/Region.wiz (Feral lifetimes)"
  cases := [
    { name := "handles in different regions are different types; regions are inferred", run := fun _ => do
        okLibs ("import Region\ndef same {ρ : Region} (m : Mut ρ Nat (List Nat)) : Mut ρ Nat (List Nat) := m\n" ++
          "def get {ρ : Region} (x : Shr ρ Nat) : Nat := x.val\n#eval Shr.borrow Region.static 4 (fun ρ h x => .ok (get x))") [".ok 4"]
        failsLibs "import Region\ndef bad {ρ ρ' : Region} (m : Mut ρ Nat (List Nat)) : Mut ρ' Nat (List Nat) := m" "mismatch"
        failsLibs "import Region\ndef bad {ρ ρ' : Region} (x : Shr ρ Nat) : Shr ρ' Nat := x" "mismatch" },
    { name := "a mutable borrow scope hands the lender back", run := fun _ =>
        okLibs ("import Region\n" ++ regionsPush ++
          "#eval Uniq.borrow Region.static List.nil (fun ρ h v r => push1 r)") [".ok ((), .cons 1 .nil)"] },
    { name := "outlives evidence from nested scopes lets a reference flow outward", run := fun _ =>
        okLibs ("import Region\n" ++ regionsLongest ++
          "#eval Shr.borrow Region.static 3 (fun ρa ha a => Shr.borrow ρa 5 (fun ρb hb b =>\n" ++
          "  match longest hb a b with\n  | .ok r => .ok r.val\n  | .err e => .err e))") [".ok 5"] },
    { name := "without the bound, a &'a is not a &'b", run := fun _ =>
        failsLibs ("import Region\ndef longest {ρa ρb : Region} (x : Shr ρa Nat) (y : Shr ρb Nat) : Result (Shr ρb Nat) :=\n" ++
          "  match Nat.lt x.val y.val with\n  | .true => .ok y\n  | .false => .ok x") "mismatch" },
    { name := "returning a borrow of a local is a type error (E0515)", run := fun _ =>
        failsLibs ("import Region\ndef bad {ρ : Region} (x : Shr ρ Nat) : Result (Shr ρ Nat) :=\n" ++
          "  Shr.borrow ρ 5 (fun ρy hy y => .ok y)") "mismatch" },
    { name := "a borrow can't outlive its scope (E0597)", run := fun _ =>
        failsLibs ("import Region\n" ++ regionsLongest ++
          "def bad : Result Nat := Shr.borrow Region.static 3 (fun ρa ha a =>\n" ++
          "  match Shr.borrow ρa 5 (fun ρb hb b => longest hb a b) with\n  | .ok r => .ok r.val\n  | .err e => .err e)")
          "escapes the scope" },
    { name := "using the lender while it is mutably borrowed is a type error (E0499/E0502)", run := fun _ => do
        failsLibs ("import Region\n" ++ regionsPush ++
          "def bad : Result (Nat × List Nat) := Uniq.borrow Region.static List.nil (fun ρ h v r =>\n" ++
          "  match push1 r with\n  | .ok u r => .ok (List.length v) r\n  | .err e r => .err e r)") "mismatch"
        failsLibs ("import Region\n" ++ regionsPush ++
          "def bad : Result (Unit × List Nat) := Uniq.borrow Region.static List.nil (fun ρ1 h1 v r1 =>\n" ++
          "  match Uniq.borrowIn ρ1 v r1 (fun ρ2 h2 v r1 r2 => match push1 r2 with\n" ++
          "    | .ok u r2 => .ok () (r1, r2)\n    | .err e r2 => .err e (r1, r2)) with\n" ++
          "  | .ok q r1 => .ok () r1\n  | .err e r1 => .err e r1)") "mismatch" },
    { name := "swap through two &mut, each borrow in its own region", run := fun _ =>
        okLibs ("import Region\n" ++ regionsSwap ++ regionsTwo "t" "a" "swap ra rb" ++ "#eval t") [".ok (2, 1)"] },
    { name := "a linked list through &mut: recursion on reborrows of the tails, and a cursor", run := fun _ =>
        okLibs ("import Region\n" ++ regionsList ++ "#eval listMain (List.cons 1 (List.cons 2 List.nil))")
          [".ok (.cons 2 (.cons 3 (.cons 7 .nil)))"] },
    { name := "returning one of two &mut borrows needs 'a : 'b (Mut.weaken)", run := fun _ => do
        okLibs ("import Region\n" ++ regionsPick ++ regionsSetPick ++
          regionsTwo "t1" "a" "setPick hb .true ra rb" ++ regionsTwo "t2" "a" "setPick hb .false ra rb" ++ "#eval t1\n#eval t2")
          [".ok (10, 2)", ".ok (1, 10)"]
        failsLibs ("import Region\n" ++ regionsPick (bound := false)) "mismatch"
        -- the bound pointing the wrong way: b is borrowed first, so only 'b : 'a is known
        failsLibs ("import Region\n" ++ regionsPick ++ regionsSetPick ++ regionsTwo "t" "b" "setPick ha .true ra rb") "mismatch" },
    { name := "a borrow is shortened, never lengthened, and a local's &mut can't be returned (E0515)", run := fun _ => do
        failsLibs ("import Region\ndef bad {σ : Region} (1 v : Uniq σ Nat) : Result1 Unit (Uniq σ Nat) :=\n" ++
          "  Uniq.reborrow v (fun ρ h v r => .ok () (Mut.finish (Mut.weaken h (Mut.ofUniq r))))") "mismatch"
        -- (the borrow of `l` would have to leave in the result and be handed back too)
        failsLibs ("import Region\ndef bad {ρ : Region} (1 v : Uniq ρ Nat) : Borrowed (Mut ρ Nat (Uniq ρ Nat)) (Uniq ρ Nat) :=\n" ++
          "  match Uniq.borrow ρ 5 (fun ρl hl l rl => .ok (Mut.ofUniq rl) rl) with\n" ++
          "  | .ok p => let (m, n) := p; .ok m\n  | .err e => .err e v") "escapes the scope" },
    { name := "two borrows of different regions are not interchangeable", run := fun _ =>
        failsLibs ("import Region\ndef same {ρ : Region} (1 x : Uniq ρ Nat) (1 y : Uniq ρ Nat) : Result1 Unit ((1 _ : Uniq ρ Nat) × Uniq ρ Nat) := .ok () (x, y)\n" ++
          regionsTwo "t" "a" "same ra rb") "mismatch" },
    { name := "linear handles: a scope's handle is used once and handed back on every path (formerly KNOWN GAPs 1 and 3)", run := fun _ => do
        okLibs ("import Region\n" ++
          "def swap {ρa ρb : Region} (1 x : Uniq ρa Nat) (1 y : Uniq ρb Nat) : Result1 Unit ((1 _ : Uniq ρa Nat) × Uniq ρb Nat) :=\n" ++
          "  Uniq.read x (fun a x => Uniq.read y (fun b y => Result1.ok () (Uniq.write x b, Uniq.write y a)))\n" ++
          "-- `let mut a := 1; let mut b := 2; swap (&mut a) (&mut b); (a, b)`\n" ++
          "def main : Result (Nat × Nat) :=\n" ++
          "  match Uniq.borrow Region.static 1 (fun ρa ha la x =>\n" ++
          "    match Uniq.borrowIn Region.static 2 x (fun ρb hb lb x y => swap x y) with\n" ++
          "    | .ok ub x => .ok ub.2 x\n" ++
          "    | .err e x => .err e x) with\n" ++
          "  | .ok p => .ok (p.2, p.1)\n" ++
          "  | .err e => .err e\n" ++
          "#eval main\n") [".ok (2, 1)"]
        -- E0499 by linearity: one &mut passed twice
        failsLibs ("import Region\n" ++
          "def swap {ρa ρb : Region} (1 x : Uniq ρa Nat) (1 y : Uniq ρb Nat) : Result1 Unit ((1 _ : Uniq ρa Nat) × Uniq ρb Nat) :=\n" ++
          "  Uniq.read x (fun a x => Uniq.read y (fun b y => Result1.ok () (Uniq.write x b, Uniq.write y a)))\n" ++
          "-- E0499: one &mut passed twice\n" ++
          "def dup : Result (Unit × Nat) := Uniq.borrow Region.static 1 (fun ρ h l r =>\n" ++
          "  match swap r r with\n" ++
          "  | .ok u q => let 1 (r1, r2) := q; .ok () r1\n" ++
          "  | .err e q => let 1 (r1, r2) := q; .err e r1)\n") "quantity 1"
        -- no escape: a handle packed with its region can't also be handed back
        failsLibs ("import Region\n" ++
          "-- a handle packed with its region leaves the scope (and is also handed back)\n" ++
          "def esc (v : List Nat) : Result (((0 r : Region) × Uniq r (List Nat)) × List Nat) :=\n" ++
          "  Uniq.borrow Region.static v (fun ρ h l r => .ok (ρ, r) r)\n") "quantity 1"
        -- not forgeable
        failsLibs "import Region\ndef forge {ρ : Region} (s : List Nat) : Uniq ρ (List Nat) := Uniq.mk s" "private"
        -- KNOWN GAP (pinned; needs linear lenders and Copy, K3): the lender is an ω value,
        -- so a body that names the Lent token differently still reads it while it is lent (E0502)
        okLibs ("import Region\ndef lender (v : List Nat) : Result (Nat × List Nat) := Uniq.borrow Region.static v (fun ρ h tok r =>\n" ++
          "  .ok (List.length v) (Uniq.write r List.nil))\n#eval lender (List.cons 1 List.nil)") [".ok (1, .nil)"] },
    { name := "handles can't be forged outside lib/Region.wiz (private constructors, 13b)", run := fun _ => do
        failsLibs "import Region\ndef forge {ρ : Region} : Shr ρ Nat := Shr.mk 5" "'Shr.mk' is private to module Region"
        failsLibs "import Region\ndef forge {ρ : Region} (s : List Nat) : Uniq ρ (List Nat) := Uniq.mk s" "private"
        failsLibs "import Region\ndef forge {ρ : Region} : Lent ρ Nat := .mk ()" "Lent"
        failsLibs "import Region\ndef forge {ρ : Region} : Shr ρ Nat := (5, ())" "Shr"
        failsLibs ("import Region\nstructure MyShr (ρ : Region) (A : Type) where\n  val : A\n" ++
          "def forge {ρ : Region} : Shr ρ Nat := MyShr.mk 5") "mismatch"
        -- nor through an equation with a look-alike (the kernel compares by shape; `rfl`
        -- compares in the elaborator's view)
        failsLibs ("import Region\nstructure MyShr (ρ : Region) (A : Type) where\n  val : A\n" ++
          "def forge {ρ : Region} (x : Nat) : Shr ρ Nat := cast rfl (MyShr.mk x : MyShr ρ Nat)") "not definitionally equal" },
    { name := "with --unbox-structs a shared handle is its value at run time and its scope is its body run in place (22i); a linear &mut scope is its body run in place, but for the handle's cell", run := fun _ => do
        let s ← libsState ("import Region\n" ++ regionsPush ++
          "def get {ρ : Region} (x : Shr ρ Nat) : Nat := x.val\n" ++
          "def scoped (xs : List Nat) : Result (Unit × List Nat) := Uniq.borrow Region.static xs (fun ρ h v r => push1 r)\n" ++
          "def direct (xs : List Nat) : Result (Unit × List Nat) := .ok ((), List.cons 1 xs)\n" ++
          "def nested (a b : List Nat) : Result (List Nat × List Nat) :=\n" ++
          "  match Uniq.borrow Region.static a (fun ρa ha a ra =>\n" ++
          "    match Uniq.borrowIn ρa b ra (fun ρb hb b ra rb =>\n" ++
          "      match push1 rb with\n      | .ok u rb => .ok () (ra, rb)\n      | .err e rb => .err e (ra, rb)) with\n" ++
          "    | .ok q ra => .ok q.2 ra\n    | .err e ra => .err e ra) with\n" ++
          "  | .ok p => .ok (p.2, p.1)\n  | .err e => .err e\n" ++
          "def t1 : Result (Unit × List Nat) := scoped List.nil\n" ++
          "def t0 : Result (Unit × List Nat) := direct List.nil\n" ++
          "def t2 : Result (List Nat × List Nat) := nested List.nil List.nil\n#run t1\n#eval t1\n#run t2\n" ++
          "def shared (xs : List Nat) : Result Nat := Shr.borrow Region.static xs (fun ρ h x => .ok (List.length x.val))\n" ++
          "#run Shr.borrow Region.static 4 (fun ρ h x => .ok (get x))") (unbox := true)
        let msgs := s.messages.toList.map (·.text)
        checkEq [".ok ((), .cons 1 .nil)", ".ok ((), .cons 1 .nil)", ".ok (.nil, .cons 1 .nil)", ".ok 4"] msgs
        -- `x.val` is `x`: no projection
        let getIR ← libsIR s "get"
        check (getIR.all fun d => (d.splitOn "proj").length == 1) s!"a projection:\n{"\n".intercalate getIR}"
        -- a shared borrow's scope is its body run in place: no closure, nothing lifted
        let shIR ← libsIR s "shared"
        check (shIR.length == 1 && shIR.all fun d => (d.splitOn "pap").length == 1)
          s!"shared: a closure:\n{"\n".intercalate shIR}"
        -- a linear `&mut` scope is its body run in place too: the `match`es on the handle
        -- (`T.casesOn1`) are unfolded and their known tags simplified (`simpKnown`), so
        -- nothing is lifted. KNOWN COST (/workspace/wiz-notes/linear-scope-cost.md): the
        -- handle `Uniq` is still a cell (an inductive, not unboxed like a structure).
        -- Objects allocated without the scope / with one / with two nested (before: 3 15
        -- 29), and lifted decls (before: 8 23).
        checkEq "3 4 6" s!"{← libsAllocs s "t0"} {← libsAllocs s "t1"} {← libsAllocs s "t2"}"
        checkEq "1 1" s!"{(← libsIR s "scoped").length} {(← libsIR s "nested").length}" }
  ]

builtin_initialize registerGroup regionsGroup

end Tests.Elab
