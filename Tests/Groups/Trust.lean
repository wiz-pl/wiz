import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Messages of `input` (with `lib/` importable), without positions, errors marked. -/
def messagesLib (input : String) : IO (List String) := do
  let loader ← preludeLoader
  let s := runFrontend (R := ZeroOneMany) input { loader, trustedModule := Tests.libModule }
  pure (s.messages.toList.map fun m => (match m.severity with
    | .error => "error: " | .warning => "warning: " | .info => "") ++ m.text)

/-- Some error mentions `fragment` (others may follow from it). -/
def failsWith (input : String) (fragment : String) : IO Unit := do
  let errs := errors input
  unless errs.any (fun e => (e.splitOn fragment).length > 1) do
    throw (IO.userError s!"no error mentions '{fragment}': {errs}")

def familyTF : String := "inductive B where\n  | t\n  | f\ninductive T : B → Type where\n  | mk : T .t\n"

/-- A type the witness search can't reach: its only value is five constructors deep. -/
def deepType : String :=
  "inductive A5 where\n  | mk\ninductive A4 where\n  | mk (x : A5)\ninductive A3 where\n  | mk (x : A4)\n" ++
  "inductive A2 where\n  | mk (x : A3)\ninductive A1 where\n  | mk (x : A2)\n"

/-- A number type of one's own, with an addition that disagrees with the native one. -/
def ownNat : String :=
  "inductive N where\n  | zero\n  | succ (n : N)\ndef K (a b : N) : N := a\nbuiltin nat := N\n" ++
  "builtin nat.zero := N.zero\nbuiltin nat.succ := N.succ\nbuiltin nat.add := K\n"

/-- Some error (with `lib/` importable) mentions `fragment`. -/
def failsWithLib (input : String) (fragment : String) : IO Unit := do
  let errs := (← messagesLib input).filter (·.startsWith "error: ")
  unless errs.any (fun e => (e.splitOn fragment).length > 1) do
    throw (IO.userError s!"no error mentions '{fragment}': {errs}")

/-- O3: a registration outside the library that disagrees with native addition. -/
def badAdd : String :=
  ownNat ++
  "def h (n : N) : K n 3 = n := refl n\ndef bad : False := absurd (h 2)\n#print axioms bad\n"

/-- Replace every call `f a` by `f (wrap a)` (t1-review's probes, `trustGroup`). -/
partial def wrapCalls (f : Name) (wrap : Term ZeroOneMany → Term ZeroOneMany) (t : Term ZeroOneMany) : Term ZeroOneMany :=
  match t with
  | .app (.const c us) a => if c == f then .app (.const c us) (wrap (wrapCalls f wrap a)) else .app (.const c us) (wrapCalls f wrap a)
  | t => Id.run (t.mapChildrenM pure fun _ c => pure (wrapCalls f wrap c))

/-- The trusted base: partial definitions need a kernel-checked witness (O2), and
`builtin` registrations outside the library are tracked axioms (O3). -/
def trustGroup : Group where
  name := "trust"
  exercise := "—"
  cases := [
    { name := "O2: a partial definition at an empty index is rejected", run := fun _ =>
        failsWith (familyTF ++ "partial def bad : T .f := bad\ndef boom : False := match bad with\n  | .mk => absurd ()\n")
          "no witness found" },
    { name := "O2: a partial function into an empty index is rejected", run := fun _ =>
        fails (familyTF ++ "partial def bad : T .t → T .f := bad\n") "no witness found" },
    { name := "O2: a wrong witness is rejected", run := fun _ =>
        fails (familyTF ++ "partial (default := T.mk) def bad : T .f := bad\n") "type mismatch" },
    { name := "partial definitions with inferred witnesses", run := fun _ =>
        ok (familyTF ++ "inductive Nat where\n  | zero\n  | succ (n : Nat)\n" ++
            "inductive List (A : Type) where\n  | nil\n  | cons (x : A) (xs : List A)\n" ++
            "partial def p1 : T .t := p1\npartial def p2 (b : B) (x : T b) : T b := p2 b x\n" ++
            "partial def p3 : Nat → List Nat := p3\npartial def p4 : (A : Type) × A := p4\n" ++
            "partial def p5 (A : Type) : A → Unit × A := p5 A\npartial def p6 : Type := p6\n" ++
            "axiom World : Type\naxiom w0 : World\npartial def p7 : World × B := p7\n" ++
            "mutual\ndef ev : Nat → B\n  | .zero => .t\n  | .succ n => od n\ndef od : Nat → B\n  | .zero => .f\n  | .succ n => ev n\nend\n" ++
            "#print axioms p2\n#print axioms p7\n")
          ["'p2' does not depend on any axioms", "'p7' depends on axioms: [w0, World]"] },
    { name := "a witness the search can't find, given with `default`", run := fun _ => do
        fails (deepType ++ "partial def f : Unit → A1 := f\n") "no witness found"
        ok (deepType ++ "partial (default := fun _ => A1.mk (A2.mk (A3.mk (A4.mk A5.mk)))) def f : Unit → A1 := f\n" ++
            "mutual\npartial (default := A1.mk (A2.mk (A3.mk (A4.mk A5.mk)))) def g : A1 := h ()\ndef h (u : Unit) : A1 := g\nend\n") },
    { name := "the kernel checks a partial definition's witness", run := fun _ => do
        let ty : Term ZeroOneMany := .unit 1
        let bad : Term ZeroOneMany := .empty 1
        check ((addPartialDecl (R := ZeroOneMany) {} { name := "f", type := ty, value := none }) matches .error _)
          "no witness accepted"
        check ((addPartialDecl (R := ZeroOneMany) {} { name := "f", type := .empty 1, value := none, witness := some .tt }) matches .error _)
          "ill-typed witness accepted"
        check ((addPartialDecl (R := ZeroOneMany) {} { name := "f", type := ty, value := none, witness := some .tt }) matches .ok _)
          "good witness rejected"
        check ((addDecl (R := ZeroOneMany) {} { name := "f", type := ty, value := none }) >>= (addPartialImpl · "f" .tt) matches .error _)
          "an axiom took an implementation"
        let _ := bad },
    { name := "the kernel checks a definition's implementation for the compiler (Decl.impl)", run := fun _ => do
        -- `f : Unit := tt`, with the term compiled code runs given by hand
        let ty : Term ZeroOneMany := .unit 1
        let f (impl : Term ZeroOneMany) (levelParams : List Name := []) : Decl ZeroOneMany :=
          { name := "f", levelParams, type := ty, value := some .tt, impl := some impl }
        let rejected (d : Decl ZeroOneMany) (fragment : String) : Bool :=
          match addDecl {} d with
          | .error e => ((toString e).splitOn fragment).length > 1
          | .ok _ => false
        check ((addDecl {} (f .tt)) matches .ok _) "a good implementation was rejected"
        -- one that calls the definition must be its value with the calls on fields (derived):
        -- `f` itself is not (compiled code would loop: t1-review M1), though `f ≡ tt`
        check ((addDecl {} (f (.const "f" []))) matches .error _) "an implementation that is the definition itself was accepted"
        check (rejected (f (.const "g" [])) "implementation of f") "an implementation with an unknown constant was accepted"
        -- ill-typed, and well-typed at another type
        check (rejected (f (.app .tt .tt)) "implementation of f") "an ill-typed implementation was accepted"
        check (rejected (f (.unit 1)) "implementation of f") "an implementation of another type was accepted"
        check (rejected (f (.pair .tt .tt)) "implementation of f") "an implementation of another type was accepted"
        -- a `Π` whose codomain is noted to be in a sort it is not in (erasure reads the
        -- sorts): `let T : Type := Π… in tt`; and one without its sorts (mandatory sorts)
        let piNoted (s : BinderSorts) : Term ZeroOneMany :=
          .letE "T" (.qlit .zero) (.sort 1) (.pi "_" .default (.qlit .many) (.unit 1) (.unit 1) s) .tt
        check (rejected (f (piNoted .hole)) "without its sort") "an implementation without its sorts was accepted"
        check ((addDecl {} (f (piNoted ⟨1, 1⟩))) matches .ok _) "right sorts were rejected"
        check (rejected (f (piNoted ⟨1, 0⟩)) "marked as in Sort") "a wrong sort in an implementation was accepted"
        check (rejected { f .tt with value := some (piNoted ⟨1, 0⟩), impl := none } "marked as in Sort")
          "a wrong sort in a value was accepted"
        -- quantities: a linear variable used twice
        let lin (body : Term ZeroOneMany) : Decl ZeroOneMany :=
          { name := "f", type := .pi "x" .default (.qlit .one) ty (.sigma "_" (.qlit .one) ty ty ⟨1, 1⟩) ⟨1, 1⟩,
            value := some (.lam "x" (.pair (.var 0) .tt)), impl := some (.lam "x" body) }
        check ((addDecl {} (lin (.pair .tt (.var 0)))) matches .ok _) "a linear implementation was rejected"
        check (rejected (lin (.pair (.var 0) (.var 0))) "implementation of f") "an implementation using a linear variable twice was accepted"
        -- universe level parameters
        check (rejected (f (.ann .tt (.unit (.param "u")))) "unknown universe level parameter u")
          "an implementation with an undeclared level parameter was accepted"
        -- `attribute [implemented_by g] f` goes through the kernel too (`setImpl`)
        let g ← match addDecls (R := ZeroOneMany) {} [{ name := "f", type := ty, value := some .tt },
            { name := "g", type := ty, value := some .tt }, { name := "h", type := .sort 2, value := some (.sort 1) }] with
          | .ok g => pure g
          | .error e => throw (IO.userError s!"setup rejected: {e}")
        check ((setImpl g "f" (.const "g" [])) matches .ok _) "a native implementation of the same type was rejected"
        check ((setImpl g "f" (.const "h" [])) matches .error _) "a native implementation of another type was accepted" },
    { name := "recursive definitions: the compiled equations are kernel-checked terms", run := fun _ => do
        let src := "inductive N where\n  | z\n  | s (n : N)\n" ++
          "def add : N → N → N\n  | .z, m => m\n  | .s n, m => .s (add n m)\n" ++
          "def double : N → N\n  | .z => .z\n  | .s n => .s (.s (double n))\n" ++
          "inductive V (A : Type) : N → Type where\n  | nil : V A .z\n  | cons {n : N} (x : A) (xs : V A n) : V A (.s n)\n" ++
          "def vlen {A : Type} {0 n : N} : V A n → N\n  | .nil => .z\n  | .cons _ xs => .s (vlen xs)\n" ++
          "#eval double (add (.s .z) (.s .z))\n"
        let s := runFrontend (R := ZeroOneMany) src
        check (s.messages.all (·.severity != .error)) s!"errors: {s.messages.toList.map (·.text)}"
        for n in ["add", "double", "vlen"] do
          let some d := s.globals.find? n | throw (IO.userError s!"{n} is missing")
          let some impl := d.impl | throw (IO.userError s!"{n} has no implementation")
          -- what `addDecl` did: the implementation checks at the declared type, with `n` declared
          let ctx : Ctx ZeroOneMany := { globals := s.globals }
          check ((Wiz.check ctx impl (ctx.eval d.type)) matches .ok _) s!"{n}'s implementation does not check"
          -- and the declaration can't be re-added with a broken one
          let g0 : Globals ZeroOneMany := { s.globals with decls := s.globals.decls.erase n }
          check ((addDecl g0 d) matches .ok _) s!"{n} is rejected when added again"
          check ((addDecl g0 { d with impl := some .tt }) matches .error _)
            s!"{n} was accepted with an implementation of another type" },
    { name := "recursive definitions: a local variable named like the definition is an error", run := fun _ => do
        -- `f n` inside `f`'s equations is the recursive call; with a local `f` in scope that
        -- was ambiguous (the compiled equations once called the local: `f 2 = 0` was proved
        -- and `#eval f 2` printed `3`), so it is rejected with a hint to rename
        let n := "inductive N where\n  | z\n  | s (n : N)\n"
        let msg := "a local variable named f shadows the recursive definition f"
        fails (n ++ "def f : N → N\n  | .z => .z\n  | .s n => (fun (f : N → N) => f n) (fun x => .s (.s x))\n") msg
        fails (n ++ "def f : N → N\n  | .z => .z\n  | .s n => let f : N → N := fun x => .s (.s x); f n\n") msg
        -- a pattern variable, a parameter
        fails (n ++ "def f : N → (N → N) → N\n  | .z, _ => .z\n  | .s n, f => f n (fun x => .s x)\n") msg
        fails (n ++ "def f (f : N) : N → N\n  | .z => f\n  | .s n => f n\n") "rename a local variable called f"
        -- renamed, it is the recursive call
        ok (n ++ "def f : N → N\n  | .z => .z\n  | .s n => (fun (g : N → N) => f n) (fun x => .s (.s x))\n" ++
            "def fThm : f (.s (.s .z)) = .z := refl N.z\n#eval f (.s (.s .z))\n#run f (.s (.s .z))\n")
          [".z", ".z"] },
    { name := "recursive definitions: compiled equations derived from the value agree with it, with and without moving calls out of nested splits", run := fun _ => do
        -- nested patterns revert the hypotheses into an inner split (`last`, `leftmost`), a
        -- structural argument after another (`findT`), a mutual family's mode-B match
        -- (`Nat.lt` in the Prelude), an infinitary field (`wd`), an indexed family (`vsum`)
        let src := "import Prelude\nimport Vec\ninductive Tr where\n  | tip\n  | node (l : Tr) (x : Nat) (r : Tr)\n" ++
          "def build : Nat → Tr\n  | .zero => .tip\n  | .succ n => .node (build n) n (build n)\n" ++
          "def leftmost : Tr → Nat\n  | .tip => 0\n  | .node .tip x _ => x\n  | .node l _ _ => leftmost l\n" ++
          "def last : List Nat → Nat\n  | .nil => 0\n  | .cons a .nil => a\n  | .cons _ t => last t\n" ++
          "def findT (h : Nat) : Nat → Tr → Nat\n  | _, .tip => 0\n  | .zero, .node _ x _ => x\n" ++
          "  | .succ d, .node l _ r => match Nat.beq h d with\n    | .true => findT h d r\n    | .false => findT h d l\n" ++
          "inductive W where\n  | sup (f : Nat → W) (n : Nat)\n  | z\n" ++
          "def wd : W → Nat → Nat\n  | .z, _ => 0\n  | .sup f n, k => wd (f k) k + n\n" ++
          "def vsum {0 n : Nat} : Vec Nat n → Nat\n  | .nil => 0\n  | .cons x xs => x + vsum xs\n" ++
          "def l5 : List Nat := .cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))\n" ++
          "#run leftmost (build 4)\n#run last l5\n#run findT 1 3 (build 3)\n" ++
          "#run wd (.sup (fun i => .sup (fun _ => .z) i) 10) 5\n#run vsum (.cons 1 (.cons 2 .nil))\n#run Nat.lt 3 5\n" ++
          "def t1 : leftmost (build 4) = 0 := refl 0\ndef t2 : last l5 = 5 := refl 5\n" ++
          "def t4 : findT 1 3 (build 3) = 0 := refl 0\ndef t5 : wd (.sup (fun i => .sup (fun _ => .z) i) 10) 5 = 15 := refl 15\n"
        let ms ← Module.loadAll ["lib"]
        let loader := fun m => (ms[m]?).map (·.2)
        let run (push : Bool) : IO (List String) := do
          let s := runFrontend (R := ZeroOneMany) src
            { loader, trustedModule := Tests.libModule, globals := { pushCalls := push } }
          let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
          unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
          -- every derived implementation passes the kernel's agreement check
          for (n, d) in s.globals.decls.toList do
            if d.derivedEquations then
              unless (checkImplAgrees s.globals d d.value.get! d.impl.get!) matches .ok _ do
                throw (IO.userError s!"{n}: the compiled equations do not agree")
          pure (s.messages.toList.map (·.text))
        let expect := ["0", "5", "0", "15", "3", ".true"]
        checkEq (repr expect).pretty (repr (← run true)).pretty
        checkEq (repr expect).pretty (repr (← run false)).pretty },
    { name := "recursive definitions: the kernel rejects compiled equations that compute something else", run := fun _ => do
        -- `g`'s compiled equations, well typed at `f`'s type, given to `f`: `f 0 = 0` but
        -- `g 0 = 1`, so the agreement check (one conversion per constructor) fails
        let src := "inductive N where\n  | z\n  | s (n : N)\n" ++
          "def f : N → N\n  | .z => .z\n  | .s n => f n\n" ++
          "def g : N → N\n  | .z => .s .z\n  | .s n => g n\n"
        let s := runFrontend (R := ZeroOneMany) src {}
        let (some f, some g) := (s.globals.find? "f", s.globals.find? "g")
          | throw (IO.userError "f or g is missing")
        let g0 : Globals ZeroOneMany := { s.globals with decls := s.globals.decls.erase "f" }
        check ((addDecl g0 f) matches .ok _) "f is rejected when added again"
        match addDecl g0 { f with impl := g.impl } with
        | .ok _ => throw (IO.userError "f was accepted with g's compiled equations")
        | .error e => check (((toString e).splitOn "do not agree").length > 1) s!"unexpected error: {e}" },
    { name := "recursive definitions: the agreement check on a mutual family (index unification), and its shortcuts", run := fun _ => do
        let src := "inductive N where\n  | z\n  | s (n : N)\n" ++
          "mutual\ninductive A where\n  | a0\n  | a1 (b : B)\ninductive B where\n  | b0\n" ++
          "  | b1 (k : N) (r : B)\n  | b2 (a : A)\nend\n" ++
          "def shB : B → B\n  | .b0 => .b0\n  | .b1 k r => .b1 (.s k) (shB r)\n  | .b2 a => .b2 a\n" ++
          "def idB : B → B\n  | .b0 => .b0\n  | .b1 k r => .b1 k (idB r)\n  | .b2 a => .b2 a\n" ++
          "def sh : N → N\n  | .z => .z\n  | .s n => .s (sh n)\n"
        let s := runFrontend (R := ZeroOneMany) src {}
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
        let (some shB, some idB, some sh) := (s.globals.find? "shB", s.globals.find? "idB", s.globals.find? "sh")
          | throw (IO.userError "a definition is missing")
        -- another definition's equations are rejected (the calls are compared as calls)
        let g0 : Globals ZeroOneMany := { s.globals with decls := s.globals.decls.erase "shB" }
        check ((addDecl g0 shB) matches .ok _) "shB is rejected when added again"
        let idImpl := replaceConstTo "idB" "shB" idB.impl.get!
        check ((addDecl g0 { shB with impl := some idImpl }) matches .error _) "shB was accepted with idB's equations"
        -- the bridge by shape: the value as derived, and two values that only look like it
        let v := sh.value.get!
        check (bridgeByShape s.globals v 1 0 [] [] true 0) "the derived value has the shape"
        let .lam x body := v | throw (IO.userError "sh's value is not a λ")
        check (!bridgeByShape s.globals (.lam x (.letE "z" (.qlit 1) (.unit 1) .tt (body.lift 1 0))) 1 0 [] [] true 0)
          "a value under a let has the shape"
        let (h, args) := body.spine
        let motiveWithColumn := args.set 0 (.var 0)  -- (N has no parameters: the motive is first)
        check (!bridgeByShape s.globals (.lam x (motiveWithColumn.foldl .app h)) 1 0 [] [] true 0)
          "a motive that mentions the column passes as the shape" },
    { name := "groundEqDesc: one closed description at two levels is not identified", run := fun _ => do
        let s := runFrontend (R := ZeroOneMany) "inductive Box.{u} : Type (u+1) where\n  | mk (T : Type u)\n" {}
        let g := s.globals
        let atL (u : Level) : Val ZeroOneMany := eval g [] (.const "Box.desc" [u])
        let I : Val ZeroOneMany := .unit (.succ .zero)
        check (groundEqDesc g 0 I (atL .zero) (atL .zero)) "Box.desc.{0} is not itself"
        check (!groundEqDesc g 0 I (atL .zero) (atL (.succ .zero))) "Box.desc.{0} and Box.desc.{1} were identified" },
    { name := "recursive definitions: a local variable named like the definition doesn't capture its calls in compiled code", run := fun _ =>
        -- (#82's regression test.) `f n` is a recursive call (the kernel's definition
        -- recurses, so `f 2 = 0`); the compiled equations called the local `f`, and `#eval f 2`
        -- was `3`. Such a local is an error now (the previous case), so the same programs
        -- with the locals renamed: compiled code still computes what `refl` proves
        ok ("inductive N where\n  | z\n  | s (n : N)\n" ++
            "def f : N → N\n  | .z => .z\n  | .s n => (fun (f2 : N → N) => f n) (fun x => .s (.s x))\n" ++
            "def fThm : f (.s (.s .z)) = .z := refl N.z\n#eval f (.s (.s .z))\n#run f (.s (.s .z))\n" ++
            "def g : N → N\n  | .z => .z\n  | .s n => let g2 : N → N := fun x => .s (.s x); g n\n" ++
            "def gThm : g (.s (.s .z)) = .z := refl N.z\n#eval g (.s (.s .z))\n" ++
            "def h : N → (N → N) → N\n  | .z, _ => .z\n  | .s n, h2 => h n (fun x => .s x)\n" ++
            "def hThm : h (.s (.s .z)) (fun x => .s x) = .z := refl N.z\n#eval h (.s (.s .z)) (fun x => .s x)\n")
          [".z", ".z", ".z", ".z"] },
    { name := "recursive definitions: compiled code keeps an outer index that a method mentions", run := fun _ =>
        -- the value's hypothesis keeps the outer `n` (3 + 3 + 3); the compiled equations
        -- passed the field's index (3 + 2 + 1, `#eval` printed 6). With an erased index in the
        -- constructor, the compiled equations used it at ω and the definition was rejected.
        okLib ("import Prelude\ninductive V : Nat → Type where\n  | nil : V 0\n" ++
            "  | cons {ω n : Nat} (x : Nat) (xs : V n) : V (Nat.succ n)\n" ++
            "def g {ω n : Nat} : V n → Nat\n  | .nil => 0\n  | .cons _ xs => n + g xs\n" ++
            "def v3 : V 3 := .cons 1 (.cons 2 (.cons 3 .nil))\n" ++
            "def thm : g v3 = 9 := refl 9\n#eval g v3\n#run g v3\n" ++
            "inductive W : Nat → Type where\n  | nil : W 0\n" ++
            "  | cons {0 n : Nat} (x : Nat) (xs : W n) : W (Nat.succ n)\n" ++
            "def h {ω n : Nat} : W n → Nat\n  | .nil => 0\n  | .cons _ xs => n + h xs\n" ++
            "def w3 : W 3 := .cons 1 (.cons 2 (.cons 3 .nil))\n" ++
            "def thmW : h w3 = 9 := refl 9\n#eval h w3\n#run h w3\n")
          ["9", "9", "9", "9"] },
    { name := "recursive definitions: compiled equations whose calls are not on fields are rejected (t1-review M1)", run := fun _ => do
        -- probes t1-191-kernel / t1-191-unit: each of these agrees with the value where the
        -- kernel looks (or at a type where every two values are equal) but compiled code
        -- would loop; each derived one is accepted
        let src := "inductive N where\n  | z\n  | s (n : N)\n" ++
          "def f : N → N\n  | .z => .z\n  | .s n => f n\n" ++
          "inductive W where\n  | sup (g : N → W)\n  | z\n" ++
          "def wd : W → N\n  | .z => .z\n  | .sup g => wd (g .z)\n" ++
          "inductive W2 where\n  | node (l : W2) (g : N → W2)\n  | z\n" ++
          "def w2 : W2 → N\n  | .z => .z\n  | .node l g => w2 l\n" ++
          "def u : N → Unit\n  | .z => ()\n  | .s n => u n\n"
        let s := runFrontend (R := ZeroOneMany) src {}
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
        let verdict (nm : Name) (impl : Term ZeroOneMany → Term ZeroOneMany) : IO Bool := do
          let some d := s.globals.find? nm | throw (IO.userError s!"no {nm}")
          let g0 : Globals ZeroOneMany := { s.globals with decls := s.globals.decls.erase nm }
          pure ((addDecl g0 { d with impl := some (impl d.impl.get!) }) matches .ok _)
        for nm in ["f", "wd", "w2", "u"] do
          check (← verdict nm id) s!"{nm}'s derived equations were rejected"
        check (!(← verdict "f" (wrapCalls "f" (fun a => .app (.const "N.s" []) a)))) "f with f (.s n) was accepted"
        check (!(← verdict "f" (wrapCalls "f" (fun a => .app (.const "f" []) a)))) "f with f (f n) was accepted"
        check (!(← verdict "f" fun _ => .lam "x" (.app (.const "f" []) (.var 0)))) "f with λ x. f x was accepted"
        check (!(← verdict "f" fun _ => .const "f" [])) "f with f itself was accepted"
        check (!(← verdict "wd" (wrapCalls "wd" (fun a => .app (.const "W.sup" []) (.lam "_" (a.lift 1)))))) "wd with wd (sup (λ _. g z)) was accepted"
        check (!(← verdict "w2" (wrapCalls "w2" (fun a => .app (.app (.const "W2.node" []) a) (.lam "_" (a.lift 1)))))) "w2 with w2 (node l (λ _. l)) was accepted"
        check (!(← verdict "u" (wrapCalls "u" (fun a => .app (.const "N.s" []) a)))) "u with u (.s n) was accepted (a call at Unit)"
        -- t1-192-scrutinee / t1-192-run (M1c): a top split of `N.s x` instead of `x`, whose
        -- "field" is then `x` itself, with the real split inside
        let splitOfSucc (nm : Name) (impl : Term ZeroOneMany) : Term ZeroOneMany :=
          match impl with
          | .lam xn body =>
            match body.spine with
            | (h, [mot, mz, _, _]) =>
              let inner := [mot.lift 1, mz.lift 1, .lam "m" (.app (.const nm []) (.var 1)), .var 1].foldl .app h
              .lam xn ([mot, mz, .lam "n" inner, .app (.const "N.s" []) (.var 0)].foldl .app h)
            | _ => impl
          | _ => impl
        check (!(← verdict "u" (splitOfSucc "u"))) "u with a split of (.s x) was accepted"
        check (!(← verdict "f" (splitOfSucc "f"))) "f with a split of (.s x) was accepted" },
    { name := "O3: an unchecked registration is an axiom", run := fun _ => do
        let msgs ← messagesLib badAdd
        let expect := ["warning: builtin nat := N is not checked: it is an axiom of every declaration that depends on N (see `#print axioms`)",
          "warning: builtin nat.zero := N.zero is not checked: it is an axiom of every declaration that depends on N.zero (see `#print axioms`)",
          "warning: builtin nat.succ := N.succ is not checked: it is an axiom of every declaration that depends on N.succ (see `#print axioms`)",
          "warning: builtin nat.add := K is not checked: it is an axiom of every declaration that depends on K (see `#print axioms`)",
          "'bad' depends on axioms: [builtin nat.add := K, builtin nat := N, builtin nat.zero := N.zero, builtin nat.succ := N.succ]"]
        checkEq (repr expect).pretty (repr msgs).pretty },
    { name := "O3: numerals at a registered empty type are an error, not a crash", run := fun _ => do
        failsWith "def E : Type := Empty\nbuiltin nat := E\ndef bad : False := absurd (0 : E)\n" "inductive type"
        fails "inductive E where\n  | z\nbuiltin nat := E\ndef x : E := 0\n" "numerals need"
        fails "inductive N where\n  | z\naxiom Z : N\nbuiltin nat := N\nbuiltin nat.zero := Z\n" "must be a definition"
        fails "inductive N where\n  | z\ndef f (a : N) : N := a\nbuiltin nat := N\nbuiltin nat.add := f\n" "2 arguments" },
    { name := "O3: a registration in a module from an -I directory is an axiom", run := fun _ => do
        let dir : System.FilePath := s!"/tmp/wiz-trust-{← IO.monoNanosNow}"
        IO.FS.createDirAll dir
        IO.FS.writeFile (dir / "Mine.wiz") ownNat
        -- a `Prelude` in the directory doesn't replace the library's
        IO.FS.writeFile (dir / "Prelude.wiz") "builtin nat := Nat\n"
        let roots : List System.FilePath := ["lib", dir]
        let cl ← Wiz.Module.loadClosure roots "import Prelude\nimport Mine\n"
        let own := Wiz.Module.fromFirstRoot roots cl
        check (own.contains "Prelude" && !own.contains "Mine") s!"trusted modules: {own}"
        let init : CommandState ZeroOneMany := { loader := fun m => (cl.get? m).map (·.2), trustedModule := own.contains }
        let s := runFrontend (R := ZeroOneMany) "import Mine\ndef x : N := K 1 2\n#print axioms x\n" init
        let warns := (s.messages.toList.filter (·.severity == .warning)).map (·.text)
        let infos := (s.messages.toList.filter (·.severity == .info)).map (·.text)
        check (s.messages.all (·.severity != .error)) s!"errors: {s.messages.toList.map (·.text)}"
        checkEq 4 warns.length
        check (warns.all (·.startsWith "module Mine: ")) s!"warnings: {warns}"
        checkEq 1 infos.length
        for r in ["builtin nat.add := K", "builtin nat := N", "builtin nat.zero := N.zero", "builtin nat.succ := N.succ"] do
          check (infos.any fun l => (l.splitOn r).length > 1) s!"{r} is not listed: {infos}"
        -- the module and the Prelude both register `nat`: an error at the import, also
        -- when the module's commands are replayed from the cache
        let both := "import Prelude\nimport Mine\n"
        let once (s : CommandState ZeroOneMany) : Bool :=
          s.messages.any fun m => m.severity == .error && (m.text.splitOn "already registered").length > 1
        check (once (runFrontend (R := ZeroOneMany) both init)) "the frontend took a second `builtin nat`"
        let cache ← IO.FS.createTempDir
        for _ in [0:2] do
          let (s, _) ← Cache.elaborateCached (some cache) [] both init 0
          check (once s) s!"the cache took a second `builtin nat`: {s.messages.toList.map (·.text)}"
          check (s.globals.builtins.lookup "nat" == some "Nat") "`nat` was redirected"
        IO.FS.removeDirAll dir },
    { name := "a builtin key is registered once (soundness audit T14)", run := fun _ => do
        -- the probe: a second `nat.add` redirected how the Prelude's `Nat.add` unfolds, and
        -- `boom : False` showed no axioms
        failsWithLib ("import Prelude\ndef K (a b : Nat) : Nat := a\nbuiltin nat.add := K\n" ++
          "def h (n : Nat) : Nat.add n 1 = n := refl n\ndef boom : False := absurd (h 0)\n") "builtin nat.add is already registered (as Nat.add)"
        -- the same for the numerals' constructors and type
        failsWithLib "import Prelude\ndef Z : Nat := 1\nbuiltin nat.zero := Z\n" "builtin nat.zero is already registered"
        failsWithLib "import Prelude\ndef S (n : Nat) : Nat := n\nbuiltin nat.succ := S\n" "builtin nat.succ is already registered"
        failsWithLib "import Prelude\ninductive M where\n  | z\nbuiltin nat := M\n" "builtin nat is already registered"
        -- one key per constant too
        failsWith (ownNat ++ "builtin nat.sub := K\n") "K is already registered as builtin nat.add"
        -- numerals unfold through `nat.zero` and `nat.succ`: constructors only
        failsWith ("inductive N where\n  | zero\n  | succ (n : N)\ndef S (n : N) : N := .zero\n" ++
          "builtin nat := N\nbuiltin nat.zero := N.zero\nbuiltin nat.succ := S\n") "must be a constructor of N"
        failsWith ("inductive N where\n  | zero\n  | succ (n : N)\ndef Z : N := .succ .zero\n" ++
          "builtin nat := N\nbuiltin nat.zero := Z\n") "must be a constructor of N" },
    { name := "a registered operation depends on the numerals' registrations", run := fun _ => do
        -- `P z z` is the numeral `1` (0 ^ 0) with no literal in the term: it unfolds
        -- through `nat.succ`
        let msgs ← messagesLib ("inductive N where\n  | zero\n  | succ (n : N)\ndef P (a b : N) : N := a\n" ++
          "builtin nat := N\nbuiltin nat.zero := N.zero\nbuiltin nat.succ := N.succ\nbuiltin nat.pow := P\n" ++
          "def x : N := P .zero .zero\n#print axioms x\n")
        let some l := msgs.getLast? | throw (IO.userError "no output")
        for r in ["builtin nat.pow := P", "builtin nat := N", "builtin nat.zero := N.zero", "builtin nat.succ := N.succ"] do
          check ((l.splitOn r).length > 1) s!"{r} is not listed: {l}" },
    { name := "Prelude registrations are trusted and compute natively", run := fun _ =>
        okLib "import Prelude\ndef t : 2 + 2 = 4 := refl 4\n#print axioms t\n#eval 3 * 7 + Nat.pow 2 10\n"
          ["'t' does not depend on any axioms", "1045"] },
    { name := "#print axioms: the Prelude's castRefl", run := fun _ =>
        okLib ("import Prelude\n#print axioms castRefl\n" ++
            "def r (A : Type) (e : A = A) (a : A) : (cast e a : A) = a := castRefl e a\n#print axioms r\n")
          ["'castRefl' depends on axioms: [castRefl]", "'r' depends on axioms: [castRefl]"] },
    { name := "#print axioms lists native implementations (implemented_by)", run := fun _ => do
        let note := "\n(native: an implementation that compiled code runs, trusted to agree with its definition)"
        okLib ("import Prelude\ndef slow (n : Nat) : Nat := n + 0\ndef fast (n : Nat) : Nat := n\n" ++
            "attribute [implemented_by fast] slow\ndef use (n : Nat) : Nat := slow n\n" ++
            "#print axioms use\n#print axioms fast\n" ++
            -- a recursive definition's compiled equations (checked to agree with its value, T1)
            -- and a partial one's body (checked) are not listed
            "def len : List Nat → Nat\n  | .nil => 0\n  | .cons _ t => len t + 1\n#print axioms len\n" ++
            "partial def spin (n : Nat) : Nat := fast n\n#print axioms spin\n")
          ["'use' depends on axioms: [native slow := fast]" ++ note, "'fast' does not depend on any axioms",
           "'len' does not depend on any axioms", "'spin' does not depend on any axioms"]
        -- the library's are listed too: words run natively, in a native representation
        okLib ("import Prelude\nimport Word\ndef idW (x : UIntN 8) : UIntN 8 := x\n#print axioms idW\n" ++
            "def w : UIntN 8 := UIntN.add (UIntN.ofNat 8 3) (UIntN.ofNat 8 4)\n#print axioms w\n")
          ["'idW' depends on axioms: [native UIntN := UIntN.ofBits/UIntN.toBits, UIntN.seal✝]" ++ note,
           "'w' depends on axioms: [native UIntN.ofNat := UIntN.ofNatNative, native UIntN := UIntN.ofBits/UIntN.toBits, UIntN.seal✝, " ++
             "native UIntN.add := UIntN.addNative, native UIntN.toNat := UIntN.toBits]" ++ note] },
    { name := "#print axioms follows a whole implemented_by chain (t1-review L2)", run := fun _ => do
        let note := "\n(native: an implementation that compiled code runs, trusted to agree with its definition)"
        okLib ("import Prelude\naxiom secret : Nat\naxiom ext (n : Nat) : Nat\naxiom fx (n : Nat) : Nat\n" ++
            -- a1 → a2 → a3, and a3 uses an axiom: compiled code runs a3
            "def a3 (n : Nat) : Nat := n + secret\ndef a2 (n : Nat) : Nat := n + 1\ndef a1 (n : Nat) : Nat := n\n" ++
            "attribute [implemented_by a3] a2\nattribute [implemented_by a2] a1\n" ++
            "def useA (n : Nat) : Nat := a1 n\n#print axioms useA\n#print axioms a3\n" ++
            -- through a partial definition: its body runs, so what the body uses is listed
            "partial def p (n : Nat) : Nat := ext n\ndef b (n : Nat) : Nat := n\n" ++
            "attribute [implemented_by p] b\ndef useB (n : Nat) : Nat := b n\n#print axioms useB\n" ++
            -- reached through types and values alone, a partial body is still not listed
            "#print axioms p\n" ++
            -- an implementation with no value (here an axiom) is named once, by the native line
            "def c (n : Nat) : Nat := n\nattribute [implemented_by fx] c\n#print axioms c\n")
          ["'useA' depends on axioms: [native a1 := a2, native a2 := a3, secret]" ++ note,
           "'a3' depends on axioms: [secret]",
           "'useB' depends on axioms: [native b := p, ext]" ++ note,
           "'p' does not depend on any axioms",
           "'c' depends on axioms: [native c := fx]" ++ note] },
    { name := "O2 in the self-hosted frontend", run := fun _ =>
        selfhostCheckFile (familyTF ++ "inductive Nat where\n  | zero\n  | succ (n : Nat)\n" ++
            "partial def bad : T .f := bad\npartial def bad2 : T .t → T .f := bad2\n" ++
            "partial def ok1 : T .t := ok1\npartial def ok2 (n : Nat) : Nat := ok2 n\n" ++
            "partial (default := T.mk) def ok3 : T .t := ok3\npartial (default := T.mk) def bad3 : T .f := bad3\n")
          ("B : U0\nT : (x0 : B) → U0\nNat : U0\n" ++
           "error: partial definition bad: no witness found for its type; give one with `partial (default := w) def`\n" ++
           "error: partial definition bad2: no witness found for its type; give one with `partial (default := w) def`\n" ++
           "ok1 : (T B.t)\nok2 : (x0 : Nat) → Nat\nok3 : (T B.t)\nerror: type mismatch: expected (T B.f), got (T B.t)\n") }
  ]

builtin_initialize registerGroup trustGroup

end Tests.Elab
