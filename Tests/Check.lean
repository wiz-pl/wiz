import Wiz
import Tests.Harness

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Wiz Raw ZeroOneMany

namespace Tests.Check

/-- `addDecl` after the elaborator's sorts pass (mandatory sorts): `Raw` terms are built
with holes for the `Π`/`Σ` sorts, which the pass fills (`Decl.withSorts`). -/
def addDeclS {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R] (g : Globals R) (d : Decl R) : TCM (Globals R) :=
  addDecl g (Decl.withSorts g d)

def addDeclsS {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R] (g : Globals R) (ds : List (Decl R)) : TCM (Globals R) :=
  ds.foldlM addDeclS g

/-- Expect a list of declarations to check. -/
def accepts {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R] (ds : List (Decl R)) : IO Unit :=
  match addDeclsS {} ds with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"rejected: {e}")

/-- Expect the *last* declaration to be rejected, with an error satisfying `p`.
All earlier declarations must check. -/
def rejects {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]
    (ds : List (Decl R)) (p : TypeError → Bool) (what : String) : IO Unit := do
  let g ← match addDeclsS {} ds.dropLast with
    | .ok g => pure g
    | .error e => throw (IO.userError s!"setup declaration rejected: {e}")
  match addDeclS g ds.getLast! with
  | .ok _ => throw (IO.userError s!"accepted, but expected {what}")
  | .error e => unless p e do throw (IO.userError s!"expected {what}, got: {e}")

def isMismatch : TypeError → Bool | .typeMismatch .. => true | _ => false
def isQty : TypeError → Bool | .quantityMismatch .. => true | _ => false
/-- The projection rule's own error (R1). -/
def isProj : TypeError → Bool
  | .other m => (m.splitOn "a projection needs an unrestricted pair").length > 1
  | _ => false

/-! ## Plain dependent types (`Unit` rig) -/

/-- `Nat = (A : Type) → (A → A) → A → A`. Lives in `Type 1`. -/
def natTy : Raw Unit := pi' "A" () ty (arr () (arr () "A" "A") (arr () "A" "A"))
def church (n : Nat) : Raw Unit :=
  lams ["A", "s", "z"] ((List.range n).foldl (fun acc _ => .app "s" acc) "z")

def churchDecls : List (Decl Unit) := [
  Raw.defn "Nat" (.sort 1) natTy,
  Raw.defn "zero" "Nat" (church 0),
  Raw.defn "succ" (arr () "Nat" "Nat")
    (lams ["n", "A", "s", "z"] (.app "s" (apps "n" ["A", "s", "z"]))),
  Raw.defn "add" (arr () "Nat" (arr () "Nat" "Nat"))
    (lams ["m", "n", "A", "s", "z"] (apps "m" ["A", "s", apps "n" ["A", "s", "z"]])),
  Raw.defn "two" "Nat" (apps "succ" [apps "succ" ["zero"]]),
  Raw.defn "four" "Nat" (church 4)
]

/-- `Eq` à la Leibniz, so we can state `2 + 2 = 4` and prove it by `refl`:
type checking it requires `add two two` and `four` to be convertible. -/
def leibnizDecls : List (Decl Unit) := [
  Raw.defn "Eq" (arr () "Nat" (arr () "Nat" (.sort 2)))
    (lams ["x", "y"] (pi' "P" () (arr () "Nat" (.sort 1)) (arr () (.app "P" "x") (.app "P" "y")))),
  Raw.defn "refl" (pi' "x" () "Nat" (apps "Eq" ["x", "x"])) (lams ["x", "P", "px"] "px")
]

def mlttGroup : Group where
  name := "check: dependent types"
  parallel := true
  exercise := "Exercises 1.5–1.7"
  cases := [
    { name := "id : (A : Type) → A → A",
      run := fun _ => accepts [Raw.defn "id" (pi' "A" () ty (arr () "A" "A")) (lams ["A", "x"] "x")] },
    { name := "compose",
      run := fun _ => accepts [Raw.defn "comp"
        (pi' "A" () ty (pi' "B" () ty (pi' "C" () ty
          (arr () (arr () "B" "C") (arr () (arr () "A" "B") (arr () "A" "C"))))))
        (lams ["A", "B", "C", "g", "f", "x"] (.app "g" (.app "f" "x")))] },
    { name := "Church numerals", run := fun _ => accepts churchDecls },
    -- (audit 2) an index beyond the context used to panic and go on with `Sort 0`, as the
    -- variable's type and as its value: a term `Prop : Prop`
    { name := "a variable out of scope is rejected",
      run := fun _ => do
        let outOfScope : TypeError → Bool
          | .other m => (m.splitOn "out of scope").length > 1
          | _ => false
        let d (ty : Term Unit) (v : Option (Term Unit)) : Decl Unit := { name := "d", type := ty, value := v }
        let fnTy : Term Unit := Term.pi "x" .default (.qlit ()) (.sort 1) (.sort 0) ⟨2, 1⟩
        rejects [d (.sort 0) (some (.var 0))] outOfScope "an out-of-scope variable"
        rejects [d fnTy (some (.lam "x" (.var 3)))] outOfScope "an out-of-scope variable"
        rejects [d (.var 2) none] outOfScope "an out-of-scope variable" },
    { name := "refl : 2 + 2 = 4 (needs conversion)",
      run := fun _ => accepts (churchDecls ++ leibnizDecls ++
        [Raw.defn "twoPlusTwo" (apps "Eq" [apps "add" ["two", "two"], "four"]) (.app "refl" "four")]) },
    { name := "refl : 2 + 2 = 2 is rejected",
      run := fun _ => rejects (churchDecls ++ leibnizDecls ++
        [Raw.defn "bad" (apps "Eq" [apps "add" ["two", "two"], "two"]) (.app "refl" "two")])
        isMismatch "a type mismatch" },
    { name := "let in check mode",
      run := fun _ => accepts [Raw.defn "k" (pi' "A" () ty (arr () "A" "A"))
        (lams ["A", "x"] (.letE "y" () "A" "x" "y"))] },
    { name := "annotation lets a lambda be applied",
      run := fun _ => accepts [Raw.defn "t" (arr () ty ty)
        (lams ["A"] (.app (.ann (lams ["B"] "B") (arr () ty ty)) "A"))] },
    { name := "Type : Type is rejected",
      run := fun _ => rejects (R := Unit) [Raw.defn "girard" ty ty] isMismatch "a type mismatch" },
    { name := "wrong body type is rejected",
      run := fun _ => rejects [Raw.defn "bad" (pi' "A" () ty (arr () "A" "A")) (lams ["A", "x"] "A")]
        isMismatch "a type mismatch" },
    { name := "unbound global is reported",
      run := fun _ => rejects (R := Unit) [Raw.defn "bad" ty "Nope"]
        (· == .unboundGlobal "Nope") "unboundGlobal" },
    { name := "applying a non-function is rejected",
      run := fun _ => rejects [Raw.defn "bad" (pi' "A" () ty (arr () "A" "A"))
        (lams ["A", "x"] (.app "x" "x"))] (fun | .notAFunction .. => true | _ => false)
        "notAFunction" },
    { name := "bare lambda cannot be inferred",
      run := fun _ => rejects (R := Unit) [Raw.defn "bad" ty (.app (lams ["x"] "x") ty)]
        (fun | .cannotInfer .. => true | _ => false) "cannotInfer" }
  ]

/-! ## Methods in a rig without ω (Q2) -/

/-- In the `Nat` rig (exact counting) there is no unrestricted quantity, so a method of
an eliminator, which runs once per node, may not use a runtime variable. Here `coit`'s
step uses `y`: `bad` declares `y` linear (rejected: each `out` reruns the step), `good`
declares it erased and the step only passes it to an erased argument. -/
def natRigCoit (q : Nat) (name : Name) : List (Decl Nat) :=
  let pi (x : Name) (q : Nat) (a b : Term Nat) : Term Nat := .pi x .default (.qlit q) a b .hole
  let U : Term Nat := .unit 1
  let D : Term Nat := .dret .tt
  -- a global state family: `fun _ => Unit` would drop its linear argument
  let S : Term Nat := .const s!"{name}S" []
  -- ⟦ret tt⟧ S i = (0 _ : tt = i) × Unit
  let stepTy := pi "i" 1 U (pi "s" 1 (.app S (.var 0)) (pi "y" q U (.sigma "_" (.qlit 0) (.eq U .tt (.var 2)) (.unit 1) .hole)))
  [{ name := s!"{name}S", type := pi "i" 1 U (.sort 1), value := none },
   { name := s!"{name}S0", type := .app S .tt, value := none },
   { name := s!"{name}Step", type := stepTy, value := none },
   { name, type := pi "y" q U (.nu 0 U D .tt .szInf none),
     value := some (.lam "y" (.coit 0 U D S
       (.lam "i" (.lam "s" (.app (.app (.app (.const s!"{name}Step" []) (.var 1)) (.var 0)) (.var 2)))) .tt (.const s!"{name}S0" []))) }]

/-! ## Quantities (`ZeroOneMany` rig) -/

abbrev Q := ZeroOneMany

/-- `(A :0 Type) → body` -/
def forallA (body : Raw Q) : Raw Q := pi' "A" zero ty body

def qttGroup : Group where
  name := "check: quantities"
  parallel := true
  exercise := "Exercises 0.1, 1.5–1.7"
  cases := [
    { name := "linear identity: (A :0 Type) → (x :1 A) → A",
      run := fun _ => accepts [Raw.defn "id" (forallA (arr one "A" "A")) (lams ["A", "x"] "x")] },
    { name := "erased variable used in a type only",
      run := fun _ => accepts [Raw.defn "id" (forallA (pi' "x" one "A" "A")) (lams ["A", "x"] "x")] },
    { name := "erased variable used at runtime is rejected",
      run := fun _ => rejects [Raw.defn "bad" (forallA (arr zero "A" "A")) (lams ["A", "x"] "x")]
        isQty "a quantity error" },
    { name := "linear variable used twice is rejected",
      run := fun _ => rejects [Raw.defn "dup"
        (forallA (arr many (arr many "A" (arr many "A" "A")) (arr one "A" "A")))
        (lams ["A", "f", "x"] (apps "f" ["x", "x"]))] isQty "a quantity error" },
    { name := "linear variable dropped is rejected",
      run := fun _ => rejects [Raw.defn "drop" (forallA (arr one "A" (arr one "A" "A")))
        (lams ["A", "x", "y"] "x")] isQty "a quantity error" },
    { name := "ω variable used once is fine",
      run := fun _ => accepts [Raw.defn "app1" (forallA (arr one (arr one "A" "A") (arr many "A" "A")))
        (lams ["A", "f", "x"] (.app "f" "x"))] },
    { name := "ω variable used twice is fine",
      run := fun _ => accepts [Raw.defn "twice" (forallA (arr one (arr many "A" (arr many "A" "A")) (arr many "A" "A")))
        (lams ["A", "f", "x"] (apps "f" ["x", "x"]))] },
    { name := "passing a linear var to an ω argument is rejected (scaling)",
      run := fun _ => rejects [Raw.defn "bad" (forallA (arr one (arr many "A" "A") (arr one "A" "A")))
        (lams ["A", "f", "x"] (.app "f" "x"))] isQty "a quantity error" },
    { name := "passing a linear var to an erased argument drops it",
      run := fun _ => rejects [Raw.defn "bad" (forallA (arr many (arr zero "A" "A") (arr one "A" "A")))
        (lams ["A", "f", "x"] (.app "f" "x"))] isQty "a quantity error" },
    { name := "erased var can be passed to an erased argument",
      run := fun _ => accepts [Raw.defn "ok" (forallA (arr one (arr zero "A" "A") (arr zero "A" "A")))
        (lams ["A", "f", "x"] (.app "f" "x"))] },
    { name := "linear let",
      run := fun _ => accepts [Raw.defn "l" (forallA (arr one "A" "A"))
        (lams ["A", "x"] (.letE "y" one "A" "x" "y"))] },
    { name := "unused linear let is rejected",
      run := fun _ => rejects [Raw.defn "l" (forallA (arr one "A" (arr one "A" "A")))
        (lams ["A", "x", "z"] (.letE "y" one "A" "x" "z"))] isQty "a quantity error" },
    { name := "erased let feeding a type",
      run := fun _ => accepts [Raw.defn "l" (forallA (arr one "A" "A"))
        (lams ["A", "x"] (.letE "B" zero ty "A" (.ann "x" "B")))] },
    { name := "Nat rig: a method may use an erased variable", run := fun _ => accepts (natRigCoit 0 "good") },
    { name := "Nat rig: a method may not use a linear variable, it runs any number of times (Q2)", run := fun _ =>
        rejects (natRigCoit 1 "bad") (fun | .other .. => true | _ => false) "a method usage error" }
  ]

/-! ## Structural types -/

/-! ## The index type's level in the eliminators (audit F3) -/

/-- The five eliminators that name the index type, with index type `Unit.{k}` and the data
type at level `l`, on the descriptions `ret tt` (and `rec tt (ret tt)` for `ν`). They are
well typed exactly when `k = l+1`. The surface language can't write the others (the
elaborator builds the eliminator from a checked type), so these are core terms. -/
def elimsAt (l k : Nat) : List (String × Term Q) :=
  let l' : Level := Level.ofNat l
  let I : Term Q := .unit (Level.ofNat k)
  let uD : Term Q := .dret .tt
  let sD : Term Q := .drec (.qlit .many) .tt (.dret .tt)
  let x : Term Q := .con (.pair .tt .tt)
  let lams (xs : List Name) (b : Term Q) : Term Q := xs.foldr .lam b
  let P := lams ["i", "x"] (.unit 1)
  let S := lams ["i"] (.unit (Level.ofNat (l + 1)))
  [("ind", .ind l' I uD 1 P (lams ["i", "xs", "ih"] .tt) .tt x),
   ("sfix", .sfix l' I uD 1 P (lams ["s", "rec", "i", "x"] .tt) .szInf .tt x),
   ("scase", .scase l' (.qlit .many) I uD 1 P (lams ["j", "i", "xs"] .tt) .szInf .tt x),
   ("coit", .coit l' I sD S (lams ["i", "s"] (.pair .tt (.pair .tt .tt))) .tt .tt),
   ("scofix", .scofix l' I sD S
      (lams ["s", "rec", "i", "a"] (.cocon (.pair (.app (.app (.var 2) (.var 1)) (.var 0)) (.pair .tt .tt)))) .szInf .tt .tt)]

/-- Every eliminator of `elimsAt l k` is rejected with the index-level error. -/
def elimsRejected (l k : Nat) : IO Unit :=
  for (n, t) in elimsAt l k do
    match infer (R := Q) { globals := {} } t with
    | .ok _ => throw (IO.userError s!"{n} at level {l} with an index type in Sort {k} was accepted")
    | .error e =>
      let frag := s!"an index type must be in the data type's universe: Sort {l + 1}, not Sort {k}"
      unless ((toString e).splitOn frag).length > 1 do
        throw (IO.userError s!"{n}: expected the index-level error, got: {e}")

def elimsAccepted (l : Nat) : IO Unit :=
  for (n, t) in elimsAt l (l + 1) do
    match infer (R := Q) { globals := {} } t with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"{n} at level {l} with its index type in Sort {l + 1} was rejected: {e}")

/-- The hint of a `μ`/`ν` type is checked before `eval` runs it: raw core terms whose hint
would make the evaluator panic or loop, or instantiate a constant at the wrong number of
levels, are rejected (both formers); well-typed hints are accepted. -/
def hintCase : IO Unit := do
  let pi (a b : Term Q) : Term Q := .pi "x" .default (.qlit .many) a b ⟨1, 2⟩  -- (`Unit → Type`)
  let g ← match addDecls (R := Q) {} [{ name := "T", type := pi (.unit 1) (.sort 1), value := none },
      { name := "P", levelParams := ["u"], type := pi (.unit 1) (.sort 1), value := none }] with
    | .ok g => pure g
    | .error e => throw (IO.userError s!"setup rejected: {e}")
  let ty (former : Bool) (h : Name × List Level × List (Term Q)) : Term Q :=
    if former then .mu 0 (.unit 1) (.dret .tt) .tt .szInf (some h) else .nu 0 (.unit 1) (.dret .tt) .tt .szInf (some h)
  let omega : Term Q := .app (.lam "x" (.app (.var 0) (.var 0))) (.lam "x" (.app (.var 0) (.var 0)))
  let bad : List (String × (Name × List Level × List (Term Q))) := [
    ("an application of tt (the evaluator would panic)", ("T", [], [.app .tt .tt])),
    ("a projection of tt, undeclared name", ("Nope", [], [.fst .tt])),
    ("a looping term", ("T", [], [omega])),
    ("a looping term, undeclared name", ("Nope", [], [omega])),
    ("an argument of the wrong type", ("T", [], [.sort 0])),
    ("too many arguments", ("T", [], [.tt, .tt])),
    ("a constant at too few levels", ("P", [], [.tt])),
    ("a constant at too few levels in an argument", ("Nope", [], [.const "P" []]))]
  for former in [true, false] do
    for (what, h) in bad do
      if let .ok _ := infer (R := Q) { globals := g } (ty former h) then
        throw (IO.userError s!"a hint with {what} was accepted")
    for h in [("T", [], [.tt]), ("T", [], []), ("P", [Level.ofNat 1], [.tt]), ("Nope", [], [.unit 1, .const "T" []])] do
      if let .error e := infer (R := Q) { globals := g } (ty former h) then
        throw (IO.userError s!"a well-typed hint was rejected: {e}")

/-- `t` with every occurrence of the closed subterm `target` replaced by `c`. -/
partial def replaceClosed (target c : Term Q) (t : Term Q) : Term Q :=
  if t == target then c else Id.run (t.mapChildrenM pure fun _ x => pure (replaceClosed target c x))

/-- (Mandatory sorts; review F3) The description templates (`Templates.lean`) carry
hand-written component sorts, which the kernel trusts when it evaluates them: kernel-check
each template term against its type, at closed levels and at level parameters, so that a
wrong leaf is caught mechanically (the kernel checks every written sort of a term). -/
def templatesCheck : IO Unit := do
  let ω : Term Q := .qlit .many
  let v (i : Nat) : Term Q := .var i
  let pi (a b : Term Q) : Term Q := .pi "x" .default ω a b .hole
  let apps (f : Term Q) (as : List (Term Q)) : Term Q := as.foldl .app f
  for (l, w, ps) in [(Level.ofNat 0, Level.ofNat 0, []), (Level.ofNat 0, Level.ofNat 1, []), (Level.ofNat 1, Level.ofNat 2, []),
                     (Level.ofNat 2, Level.ofNat 0, []), (Level.param "u", Level.param "v", ["u", "v"])] do
    let l1 : Level := .succ l
    -- (the templates applied inside the types are constants declared first: the sorts pass
    -- types the `Π`s it fills, and a bare template is an unannotated `λ`)
    let us : List Level := ps.map .param
    let interp (I D X i : Term Q) : Term Q := apps (.const "interpTm" us) [I, D, X, i]
    -- I : Sort (l+1), D : Desc I, X : I → Sort (l+1)
    let pre (rest : Term Q) : Term Q := pi (.sort l1) (pi (.desc l (v 0)) (pi (pi (v 1) (.sort l1)) rest))
    let interpTy := pre (pi (v 2) (.sort l1))
    -- P : (i : I) → X i → Sort w (ctx X0 D1 I2)
    let Pty : Term Q := pi (v 2) (pi (.app (v 1) (v 0)) (.sort w))
    let allTy := pre (pi Pty (pi (v 3) (pi (interp (v 4) (v 3) (v 2) (v 0)) (.sort (.max l1 w)))))
    -- f : (i : I) → (x : X i) → P i x (ctx P0 X1 D2 I3)
    let fTy : Term Q := pi (v 3) (pi (.app (v 2) (v 0)) (apps (v 2) [v 1, v 0]))
    let hypsTy := pre (pi Pty (pi fTy (pi (v 4) (pi (interp (v 5) (v 4) (v 3) (v 0))
      (apps (.const "allTm" us) [v 6, v 5, v 4, v 3, v 1, v 0])))))
    -- Y : I → Sort (l+1) (ctx X0 D1 I2); f : (i : I) → X i → Y i (ctx Y0 X1 D2 I3)
    let mapTy := pre (pi (pi (v 2) (.sort l1)) (pi (pi (v 3) (pi (.app (v 2) (v 0)) (.app (v 2) (v 1))))
      (pi (v 4) (pi (interp (v 5) (v 4) (v 3) (v 0)) (interp (v 6) (v 5) (v 3) (v 1))))))
    let mut g : Globals Q := {}
    -- (a template applies the ones before it as closed `λ`s, which the kernel can't infer
    -- a type for: they are replaced by the constants just checked)
    let byName (t : Term Q) : Term Q :=
      replaceClosed (Templates.interpTm l) (.const "interpTm" us) (replaceClosed (Templates.allTm l w) (.const "allTm" us) t)
    let allBody := replaceClosed (Templates.interpTm l) (.const "interpTm" us) (Templates.allTm l w)
    for (n, ty, t) in [("interpTm", interpTy, Templates.interpTm l), ("allTm", allTy, allBody),
                       ("hypsTm", hypsTy, byName (Templates.hypsTm l w)), ("mapTm", mapTy, byName (Templates.mapTm l))] do
      -- (checked in an erased position: a template's quantities are variables, `q`, so its
      -- projections are of pairs at quantity `q`; then inserted, for the next)
      let d := Decl.withSorts g { name := n, levelParams := ps, type := ty, value := some t }
      let ctx : Ctx Q := { globals := g, erased := true }
      let r : TCM Unit := do
        let _ ← Wiz.checkType ctx d.type
        -- (with the proof markers the kernel requires at `v = 0`: the pass adds them)
        let _ ← Wiz.check ctx ((d.withMarks g).value.getD .tt) (ctx.eval d.type)
      if let .error e := r then throw (IO.userError s!"{n} at l = {l}, v = {w}: {e}")
      -- (inserted unchecked, with its value: it was just checked, erased)
      g := g.insert d

def structGroup : Group where
  name := "check: structural types"
  parallel := true
  exercise := "Exercise 4.7"
  cases := [
    { name := "mandatory sorts: every description template is a well-typed term of its type, its written sorts included", run := fun _ => templatesCheck },
    -- (`Globals.sortHolesOk` is for elaboration-time checks only: the declaration check
    -- rejects a hole whatever the flag says, `checkHeader`)
    { name := "mandatory sorts: a declaration with a sort hole is rejected, even with sortHolesOk set", run := fun _ => do
        let holed : Term Q := .pi "x" .default (.qlit .many) (.unit 1) (.unit 1) .hole
        for flag in [false, true] do
          let g : Globals Q := { sortHolesOk := flag }
          for d in [({ name := "a", type := holed, value := none } : Decl Q),
                    { name := "b", type := .sort 1, value := some holed },
                    { name := "c", type := .unit 1, value := some .tt, impl := some (.letE "T" (.qlit .zero) (.sort 1) holed .tt) }] do
            match addDecl g d with
            | .ok _ => throw (IO.userError s!"{d.name} (sortHolesOk := {flag}): accepted with a hole")
            | .error e => unless ((toString e).splitOn "without its sort").length > 1 do
                throw (IO.userError s!"{d.name}: {e}") },
    { name := "the hint of μ/ν is checked before it is evaluated (a panicking or a looping hint is rejected)", run := fun _ => hintCase },
    { name := "transp at a proposition is rejected, at a type accepted (as eq and refl)", run := fun _ => do
        let P : Term Q := .lam "b" (.lam "e" (.unit 0))
        let at' (A : Term Q) : Term Q := .transp A .tt P .tt .tt .tt
        match infer (R := Q) { globals := {} } (at' (.unit 0)) with
        | .ok _ => throw (IO.userError "transp at True was accepted")
        | .error e => unless ((toString e).splitOn "transp is for types in Type u, not propositions").length > 1 do
            throw (IO.userError s!"expected the transp error, got: {e}")
        match infer (R := Q) { globals := {} } (at' (.unit 1)) with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"transp at Unit was rejected: {e}") },
    { name := "F3: ind, sfix, scase, coit, scofix accept an index type in Sort (l+1)", run := fun _ => do
        elimsAccepted 0; elimsAccepted 1 },
    { name := "F3: ind, sfix, scase, coit, scofix reject an index type one level too high", run := fun _ => do
        elimsRejected 0 2; elimsRejected 1 3 },
    { name := "F3: ind, sfix, scase, coit, scofix reject an index type one level too low", run := fun _ => do
        elimsRejected 1 1; elimsRejected 2 1 },
    { name := "swap with projections", run := fun _ =>
        accepts [Raw.defn "swap" (pi' "A" () ty (pi' "B" () ty (arr () (.sigma "_" () "A" "B") (.sigma "_" () "B" "A"))))
          (lams ["A", "B", "p"] (.pair (.snd "p") (.fst "p")))] },
    { name := "Σ lives in the larger universe", run := fun _ =>
        accepts [Raw.defn "S" (.sort 1) (.sigma "A" () ty "A")] },
    { name := "linear swap with let (x, y) := p", run := fun _ =>
        accepts [Raw.defn "swap" (forallA (pi' "B" zero ty (arr one (.sigma "x" one "A" "B") (.sigma "y" one "B" "A"))))
          (lams ["A", "B", "p"] (.split one "p" "z" (.sigma "y" one "B" "A") "x" "y" (.pair "y" "x")))] },
    { name := "linear pair projected twice is rejected", run := fun _ =>
        rejects [Raw.defn "swap" (forallA (pi' "B" zero ty (arr one (.sigma "x" one "A" "B") (.sigma "y" one "B" "A"))))
          (lams ["A", "B", "p"] (.pair (.snd "p") (.fst "p")))]
          (fun e => isQty e || match e with | .other .. => true | _ => false) "a quantity or projection error" },
    { name := "erased field cannot be projected", run := fun _ =>
        rejects [Raw.defn "bad" (forallA (pi' "B" zero ty (arr many (.sigma "x" zero "A" "B") "A")))
          (lams ["A", "B", "p"] (.fst "p"))] (fun | .other .. => true | _ => false) "a projection error" },
    -- (R1) projections are available only on unrestricted pairs, whatever the components
    { name := "p.2 on a linear pair is rejected, whatever the first field's quantity (R1)", run := fun _ => do
        for q in [one, many, zero] do
          rejects [Raw.defn "drop" (forallA (pi' "B" zero ty (arr one (.sigma "x" q "A" "B") "B")))
            (lams ["A", "B", "p"] (.snd "p"))] isProj "a projection error" },
    { name := "p.1 on a linear pair is rejected: it would drop the bare second component (R1)", run := fun _ => do
        for q in [one, many] do
          rejects [Raw.defn "drop" (forallA (pi' "B" zero ty (arr one (.sigma "x" q "A" "B") "A")))
            (lams ["A", "B", "p"] (.fst "p"))] isProj "a projection error" },
    { name := "an unrestricted pair has both projections, whatever its fields' quantities", run := fun _ =>
        accepts [Raw.defn "dropMany" (forallA (pi' "B" zero ty (arr many (.sigma "x" one "A" "B") "B")))
            (lams ["A", "B", "p"] (.snd "p")),
          Raw.defn "dropFstMany" (forallA (pi' "B" zero ty (arr many (.sigma "x" many "A" (.sigma "y" one "B" "B")) "A")))
            (lams ["A", "B", "p"] (.fst "p")),
          Raw.defn "mid" (forallA (pi' "B" zero ty (arr many (.sigma "x" many "A" (.sigma "y" one "B" (.sigma "z" one "B" "B"))) "B")))
            (lams ["A", "B", "p"] (.fst (.snd "p")))] },
    { name := "projecting out of the middle of a linear tuple is rejected (R1)", run := fun _ =>
        rejects [Raw.defn "mid" (forallA (pi' "B" zero ty (arr one (.sigma "x" many "A" (.sigma "y" one "B" (.sigma "z" one "B" "B"))) "B")))
          (lams ["A", "B", "p"] (.fst (.snd "p")))] isProj "a projection error" },
    { name := "a projection of an expression uses the expression ω times (R1)", run := fun _ => do
        -- `(f w).1` with `w` linear: rejected; with `w` unrestricted: accepted
        let tyOf (q : ZeroOneMany) := forallA (pi' "B" zero ty (arr many (arr one "B" (.sigma "x" many "A" "B")) (arr q "B" "A")))
        rejects [Raw.defn "bad" (tyOf one) (lams ["A", "B", "f", "w"] (.fst (.app "f" "w")))] isProj "a projection error"
        accepts [Raw.defn "ok" (tyOf many) (lams ["A", "B", "f", "w"] (.fst (.app "f" "w")))] },
    { name := "a linear pair is consumed by a split at 1, and a split at ω is not enough", run := fun _ => do
        -- (the bare second component `y : B` is held at 1: it goes into a field at 1)
        let tyOf := forallA (pi' "B" zero ty (arr one (.sigma "x" many "A" "B") (.sigma "y" one "B" "A")))
        accepts [Raw.defn "swap" tyOf
          (lams ["A", "B", "p"] (.split one "p" "z" (.sigma "y" one "B" "A") "x" "y" (.pair "y" "x")))]
        rejects [Raw.defn "swap" tyOf
          (lams ["A", "B", "p"] (.split many "p" "z" (.sigma "y" one "B" "A") "x" "y" (.pair "y" "x")))] isQty "a quantity error"
        -- and the split may not drop the bare second component either
        rejects [Raw.defn "drop" (forallA (pi' "B" zero ty (arr one (.sigma "x" many "A" "B") "A")))
          (lams ["A", "B", "p"] (.split one "p" "z" "A" "x" "y" "x"))] isQty "a quantity error" },
    { name := "erased positions project freely: a 0 argument, a let at 0, a 0 field (R1)", run := fun _ => do
        let P : Raw ZeroOneMany := .sigma "x" many "A" "B"
        -- `g p.1 p`: the 0 argument reads the linear pair without using it
        accepts [Raw.defn "arg" (forallA (pi' "B" zero ty (arr many (arr zero "A" (arr one P P)) (arr one P P))))
          (lams ["A", "B", "g", "p"] (.app (.app "g" (.fst "p")) "p"))]
        accepts [Raw.defn "let0" (forallA (pi' "B" zero ty (arr one P P)))
          (lams ["A", "B", "p"] (.letE "a" zero "A" (.fst "p") "p"))]
        accepts [Raw.defn "field0" (forallA (pi' "B" zero ty (arr one P (.sigma "a" zero "A" P))))
          (lams ["A", "B", "p"] (.pair (.fst "p") "p"))]
        -- an erased field may be read there too (as in an argument to a 0 binder)
        accepts [Raw.defn "let0e" (forallA (pi' "B" zero ty (arr many (.sigma "x" zero "A" "B") "B")))
          (lams ["A", "B", "p"] (.letE "a" zero "A" (.fst "p") (.snd "p")))]
        -- but what is bound at 0 can't be used at runtime
        rejects [Raw.defn "use0" (forallA (pi' "B" zero ty (arr one P "A")))
          (lams ["A", "B", "p"] (.letE "a" zero "A" (.fst "p") "a"))] (fun _ => true) "an error"
        -- and a let at 1 or ω is not an erased position
        rejects [Raw.defn "let1" (forallA (pi' "B" zero ty (arr one P "A")))
          (lams ["A", "B", "p"] (.letE "a" one "A" (.fst "p") "a"))] isProj "a projection error" },
    { name := "the second projection reads past an erased first field of an unrestricted pair", run := fun _ =>
        accepts [Raw.defn "drop0" (forallA (pi' "B" zero ty (arr many (.sigma "x" zero "A" "B") "B")))
            (lams ["A", "B", "p"] (.snd "p"))] },
    { name := "erased field can be bound by split and ignored", run := fun _ =>
        accepts [Raw.defn "ok" (forallA (pi' "B" zero ty (arr one (.sigma "x" zero "A" "B") "B")))
          (lams ["A", "B", "p"] (.split one "p" "z" "B" "x" "y" "y"))] },
    { name := "unit η: P () → P u", run := fun _ =>
        accepts (R := Unit) [Raw.defn "eta"
          (pi' "u" () (.unit 1) (pi' "P" () (arr () (.unit 1) ty) (arr () (.app "P" .tt) (.app "P" "u"))))
          (lams ["u", "P", "x"] "x")] },
    { name := "ex falso", run := fun _ =>
        accepts (R := Unit) [Raw.defn "efq" (pi' "A" () ty (arr () (.empty 1) "A"))
          (lams ["A", "e"] (.absurd "A" "e"))] },
    { name := "() only checks against Unit", run := fun _ =>
        rejects (R := Unit) [Raw.defn "bad" (.empty 1) .tt] (fun _ => true) "an error" }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  mlttGroup ::
  qttGroup ::
  structGroup ::
  []

end Tests.Check
