import Wiz.Compiler.NativeRun
import Wiz.Elab.Mark

/-!
# `native_refl`: deciding a closed equation by running it (stage 27a)

`def X : a = b := native_refl` (with `--trust-native`) is accepted when running `a` and
`b` gives the same value. The command elaborator calls `decideNative`, then adds the
axiom `X.native✝ : a = b` and `X := X.native✝` (`Command.lean`).

1. Erase `a` and `b` and the definitions they reach (`compileReachableE`, as `#eval`
   does, with foreign functions' models), and refuse if a definition can't be erased or
   is a partial definition (its implementation is unchecked and may diverge).
2. Run both (`NativeRun`: `#eval`'s interpreter with fuel and errors instead of panics).
3. Read each result back **strictly** as a closed term of `T` (`nativeReadback`): only
   first-order data is accepted, and anything that is not a value of `T`'s shape is an
   error (not a default).
4. The kernel checks each read-back term against `T` and decides `conv` between them
   (two normal forms of first-order data: cheap).

What it trusts: see `wiz-notes/native-refl.md` and docs/Status.md ("Trusted base").
-/

namespace Wiz.Native

open Wiz

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

private def isZeroQ (q : Val R) : Bool := match q.toPoly? with
  | some p => p.isErased
  | none => false

/-- The inhabitant of an erased function into `Unit` (`erasedFunTy`): `fun _ … _ => ()`. -/
partial def unitFun (g : Globals R) (ty : VTy R) (lvl : Nat) : Term R :=
  match whnf ty with
  | .pi x _ _ _ cod _ => .lam x (unitFun g (Closure.inst g cod (.var lvl)) (lvl + 1))
  | _ => .tt

/-- A runtime value as a closed term of type `ty`, for first-order data only: inductive
data (through its description), enumerations, `Unit`, pairs, numbers of the registered
`nat` type (as literals), native representations (as the model's constructor), and the
erased functions into `Unit` of phantom tails. A function, codata, a type, a field of
quantity 0 or a proof is refused, and so is a value whose shape is not the type's. -/
partial def nativeReadback (g : Globals R) (builtins : List (Name × Name)) (ty : VTy R) (v : RVal)
    (fuel : Nat := 100000000) : Except String (Term R) := do
  if fuel == 0 then throw "the value is too deep"
  let rb (t : VTy R) (x : RVal) (f : Nat) := nativeReadback g builtins t x f
  let fuel := fuel - 1
  match whnf ty with
  | .mu l I D i _ hint =>
    if isNatTy { g with builtins := builtins } ty && hint.map (·.1) == builtins.lookup "nat" && hint.isSome then
      match v with
      | .nat n => return .natLit n
      | v => match v.toNat? with
        | some n => return .natLit n
        | none => throw "a number was expected"
    -- a native value (stage 22d): the model's object around it
    let v := match v, hint.bind fun (T, _, _) => reprOf? builtins T with
      | .nat n, some ri => RVal.obj ri.tag ((List.range ri.nfields).toArray.map fun k =>
          if k == ri.r then .nat n else .erased)
      | v, _ => v
    let v ← match v with
      | .nat n => if isNatTy { g with builtins := builtins } ty then pure (RVal.natView n) else throw "a number where data was expected"
      | .obj .. => unflat D v
      | _ => throw "data was expected"
    return .con (← rb (vInterp g l I D (muFamily l I D) i) v fuel)
  | .sigma _ q A B _ =>
    if unboxedSigma g 1000000 ty then
      let a' ← rb A v fuel
      return .pair a' (unitFun g (Closure.inst g B (eval g [] a')) 1000000)
    if erasedFunTy g A 1000000 then
      let a' := unitFun g A 1000000
      return .pair a' (← rb (Closure.inst g B (eval g [] a')) (v.field 1) fuel)
    if isZeroQ q then
      -- (only the index equation of a constructor's payload, `⟦ret i⟧ X j = (0 _ : i = j) × Unit`:
      -- a data field of quantity 0 was refused by `unflat`)
      unless irrelevant A 100 do throw s!"a field of quantity 0 (erased at run time) that is not a proof, of type {(quote g 0 A).pretty}"
      let p ← proof A 100
      return .pair p (← rb (Closure.inst g B (eval g [] p)) (v.field 1) fuel)
    let .obj _ fs := v | throw "a pair was expected"
    unless fs.size == 2 do throw "a pair was expected"
    let a' ← rb A fs[0]! fuel
    return .pair a' (← rb (Closure.inst g B (eval g [] a')) fs[1]! fuel)
  | .enum ls =>
    let t ← match v with
      | .obj t #[] => pure t
      | .nat t => pure t
      | _ => throw "a tag was expected"
    unless t < ls.length do throw "a tag out of range"
    return .tag ls t
  | .unit _ => return .tt
  | .ulift _ _ A => return .up (← rb A v fuel)
  -- the last component of a constructor's payload: its index equation, a proof
  | .neutral (.eq A a b) #[] =>
    if conv g #[] A a b then return .refl (quote g 0 A) (quote g 0 a)
    throw "an index equation that does not hold"
  | .pi .. => if erasedFunTy g ty 1000000 then return unitFun g ty 1000000 else throw "a function (not first-order data)"
  | .nu .. => throw "codata (not first-order data)"
  | .sort _ => throw "a type (not first-order data)"
  | t => throw s!"a value of a type that is not first-order data ({(quote g 0 t).pretty})"
where
  /-- Is `A` a proposition (or a lifted one)? Conversion ignores its proofs (proof
  irrelevance, and η at `ULift` of a proposition), so building any proof of it is as good
  as the erased one; at any other type an erased field could hold different values on the
  two sides, and is refused. -/
  irrelevant (A : VTy R) (fuel : Nat) : Bool :=
    match fuel, whnf A with
    | 0, _ => false
    | fuel + 1, .ulift _ _ B => irrelevant B fuel
    | _, t => propSort? t == some true
  /-- A proof of a closed proposition that holds by computation (an index equation, a
  range proof `Nat.lt n m = .true`, …), which the kernel then checks with the rest. -/
  proof (A : VTy R) (fuel : Nat) : Except String (Term R) := do
    if fuel == 0 then throw "a proof too deep"
    match whnf A with
    | .unit _ => return .tt
    | .ulift _ _ B => return .up (← proof B (fuel - 1))
    | .neutral (.eq X a b) #[] =>
      if conv g #[] X a b then return .refl (quote g 0 X) (quote g 0 a)
      throw "an index equation that does not hold"
    | .sigma _ _ P Q _ =>
      let p ← proof P (fuel - 1)
      return .pair p (← proof (Closure.inst g Q (eval g [] p)) (fuel - 1))
    | t => throw s!"a proof of {(quote g 0 t).pretty} (not first-order data)"
  /-- The payload of a flat value, walking the description (as a value). -/
  unflat (D : Val R) (v : RVal) : Except String RVal := do
    let .obj tag fs := v | throw "data was expected"
    let field (n : Nat) : Except String RVal := match fs[n]? with
      | some f => pure f
      | none => throw "a field is missing"
    let rec rest (d : Val R) (n : Nat) (fuel : Nat) : Except String RVal := do
      match fuel with
      | 0 => throw "the description is too long"
      | fuel + 1 =>
      match whnf d with
      | .darg q S F =>
        if isZeroQ q then
          -- an erased proof field (a word's range proof): built, not read (it is `◾`)
          unless irrelevant S 100 do
            throw s!"a constructor field of quantity 0 (erased at run time), of type {(quote g 0 S).pretty}"
          let p ← proof S 100
          return .obj 0 #[.erased, ← rest (vApp g F (eval g [] p)) (n + 1) fuel]
        let f ← field n
        let s ← nativeReadback g builtins S f
        return .obj 0 #[f, ← rest (vApp g F (eval g [] s)) (n + 1) fuel]
      | .drec q _ D' =>
        if isZeroQ q then throw "a recursive field of quantity 0"
        return .obj 0 #[← field n, ← rest D' (n + 1) fuel]
      | .dhrec .. => throw "an infinitely branching field (a function, not first-order data)"
      | .dret _ =>
        unless n == fs.size do throw "too many fields"
        return .obj 0 #[.erased, .erased]
      | _ => throw "not a description"
    match whnf D with
    | .darg _ S F =>
      match tagField? S with
      | some (ls, lifted) =>
        unless tag < ls.length do throw "a constructor tag out of range"
        return .obj 0 #[.obj tag #[], ← rest (vApp g F (if lifted then .up (.tag ls tag) else .tag ls tag)) 0 10000]
      | none => rest D 0 10000
    | _ => rest D 0 10000

/-- What `decideNative` found. -/
structure Verdict (R : Type) where
  /-- both sides, read back -/
  lhs : Term R
  rhs : Term R
  /-- interpreter steps used -/
  steps : Nat
  /-- the native implementations the run can reach (`implemented_by` targets), which
  the definition mentions so that `#print axioms` walks them too -/
  natives : List Name

/-- Decide the closed equation `a = b` at `A` by running both sides (see the module
docstring). `.ok` only when the kernel finds the two results convertible. -/
def decideNative (g : Globals R) (builtins : List (Name × Name)) (A a b : Term R) (fuel : Nat) :
    Except String (Verdict R) := do
  let ctx : Ctx R := { globals := g }
  let vA := ctx.eval A
  match whnf vA with
  | .pi .. | .nu .. | .sort _ =>
    throw s!"native_refl compares first-order data; {(quote g 0 vA).pretty} is not (a function, codata or a type)"
  | _ => pure ()
  let ea ← (eraseTop ctx a vA).mapError (s!"cannot erase the left-hand side: {·}")
  let eb ← (eraseTop ctx b vA).mapError (s!"cannot erase the right-hand side: {·}")
  let (code, failed) ← (compileReachableE g builtins (ea.globals ++ eb.globals).toList (externImpls := false)).mapError toString
  if let (n, err) :: _ := failed then throw s!"cannot erase {n}: {err}"
  let mut natives : List Name := []
  for (n, _) in code.toList do
    if let some d := g.find? n then
      if d.witness.isSome then
        throw s!"the computation reaches the partial definition {n}, whose implementation the kernel does not check against anything"
      -- (an implementation that is a foreign function does not run here: its model does)
      if let some m := d.nativeImpl? then
        unless builtins.any (fun (k, x) => x == m && k.startsWith "extern:") do natives := m :: natives
  let (va, sa) ← NativeRun.runWith code ea fuel
  let (vb, sb) ← NativeRun.runWith code eb (fuel - sa)
  let ta ← (nativeReadback g builtins vA va).mapError (s!"the left-hand side's value is not first-order data: {·}")
  let tb ← (nativeReadback g builtins vA vb).mapError (s!"the right-hand side's value is not first-order data: {·}")
  -- (P2) the proofs the read-back built (index equations, a word's range proof) get the
  -- markers the kernel requires, as every declaration does (`Mark`, untrusted)
  let ta := Mark.check ctx ta vA
  let tb := Mark.check ctx tb vA
  -- (the kernel checks the values it is given: a malformed result is not a value of `A`)
  let _ ← (check ctx ta vA).mapError (s!"internal error: the left-hand side's value is ill-typed: {·}")
  let _ ← (check ctx tb vA).mapError (s!"internal error: the right-hand side's value is ill-typed: {·}")
  unless conv g #[] vA (ctx.eval ta) (ctx.eval tb) do
    throw s!"native evaluation refutes it: the left-hand side is {ta.pretty}, the right-hand side {tb.pretty}"
  pure { lhs := ta, rhs := tb, steps := sa + sb, natives := natives.eraseDups }

end Wiz.Native
