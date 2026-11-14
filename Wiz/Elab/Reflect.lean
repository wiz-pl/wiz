import Wiz.Elab.Tactic
import Wiz.Core.Pretty
import Wiz.Parser.Builtin
import Wiz.Parser.Interp

/-!
# Reflection for macros (HD8)

A macro may ask about the environment (`MacroM.getInductive`, `MacroM.getType` in the
prelude). The answers are runtime values of the prelude's types:

    inductive BinderKind where | default | implicit | instImplicit
    inductive ParamView where | mk (name : String) (kind : BinderKind) (type : Syntax)
    inductive FieldView where
      | mk (name : String) (kind : BinderKind) (type : Syntax) (recursive : Bool) (proof : Bool)
    inductive CtorView where | mk (name : String) (fields : List FieldView) (indices : List Syntax)
    inductive IndView where
      | mk (name : String) (levelParams : List String) (params : List ParamView)
           (indices : List ParamView) (ctors : List CtorView) (isStructure : Bool)

**Types are syntax.** Wiz terms use de Bruijn indices; a macro wants to splice types
into the code it writes. So each type is printed (`Term.prettyPrec`, whose output is
surface syntax) with the names of the binders in scope (the parameters, then the
earlier fields) and parsed back as a `term`. The printer shows constants by name and
never uses notation, so the built-in grammar suffices. A form that does not print back
(rare in declarations) becomes a hole `_`.

**Where the facts come from.** Everything is read off the kernel's declarations, so
it works for declarations replayed from the cache too:

* an `inductive T` has `T.desc : Δ → Desc …`, whose binders are the parameters and
  whose body starts with an `Enum` of the constructor names; `T`'s remaining binders
  are the indices; each `T.c : {Δ} → fields → T Δ ξ` gives the fields and the indices
  `ξ` of its result.
* a `structure S` (or `class`) has no description: `S : Δ → Sort …` is a Σ-type and
  `S.mk : {Δ} → fields → S Δ` is its only constructor.
-/

namespace Wiz.Elab

variable {R : Type} [QRig R] [DecidableEq R] [QuantitySyntax R]

def encodeOption : Option RVal → RVal
  | none => mkCon 0 []
  | some v => mkCon 1 [v]

def encodeBinderKind : BinderInfo → RVal
  | .default => mkCon 0 []
  | .implicit => mkCon 1 []
  | .instImplicit => mkCon 2 []

/-- A term as syntax, given the names of the variables in scope (innermost first). -/
def termSyntax (names : List Name) (t : Term R) : Syntax :=
  match parseCategory Builtin.tables "term" (t.prettyPrec names 0) with
  | .ok stx => stx
  | .error _ => .node {} "term.hole" #[.atom {} "_"]

/-- Binder names, made distinct (with primes) so that printing by name is unambiguous. -/
def distinctName (scope : List Name) (x : Name) : Name :=
  let x := if x == "_" || x.isEmpty then "x" else x
  go (scope.length + 1) x
where
  go : Nat → Name → Name
    | 0, y => y
    | n + 1, y => if scope.contains y then go n (y ++ "'") else y

/-- Binders of a telescope as `(name, kind, type)`, each type printed in the scope of
the binders before it; returns the scope after all of them (innermost first). -/
def telescopeSyntax (scope : List Name) (bs : List (Name × BinderInfo × Term R)) :
    List (Name × BinderInfo × Syntax) × List Name :=
  bs.foldl (fun (acc, sc) (x, bi, A) =>
    let x' := distinctName sc x
    (acc ++ [(x', bi, termSyntax sc A)], x' :: sc)) ([], scope)

private def piBinders : Term R → List (Name × BinderInfo × Term R) × Term R
  | .pi x bi _ A b _ => let (bs, r) := piBinders b; ((x, bi, A) :: bs, r)
  | t => ([], t)

/-- For each binder of a telescope, whether its type is a proposition (a proof field:
derivers skip it, since all its inhabitants are equal and none is shown). -/
private def propBinders (g : Globals R) : Array (VTy R) → Env R → List (Name × BinderInfo × Term R) → List Bool
  | _, _, [] => []
  | tys, env, (_, _, A) :: bs =>
    let v := eval g env A
    isProp g tys v :: propBinders g (tys.push v) (Val.var tys.size :: env) bs

private def encodeParam (p : Name × BinderInfo × Syntax) : RVal :=
  mkCon 0 [encodeString p.1, encodeBinderKind p.2.1, encodeSyntax p.2.2]

/-- The view of the inductive type or structure `T` (an `IndView` value), if `T` is one. -/
def inductiveView (g : Globals R) (T : Name) : Option RVal := do
  let Td ← g.find? T
  let (tBinders, _) := piBinders Td.type
  -- the parameters, the constructors, and whether `T` is a structure
  let (nΔ, ctors, isStructure) ← match g.find? (T ++ ".desc") with
    | some descD =>
      let nΔ := (piBinders descD.type).1.length
      let body := (List.range nΔ).foldl (fun t _ => match t with
        | .lam _ b => b
        | t => t) (descD.value.getD .tt)
      match body.descTag? with
      | some (ls, _, _) => some (nΔ, ls, false)
      | none => none
    | none =>
      let isSigma := match (Td.value.map fun v => (List.range tBinders.length).foldl (fun t _ => match t with
          | .lam _ b => b
          | t => t) v) with
        | some (.sigma ..) | some (.unit _) => true
        | _ => false
      if isSigma && g.contains (T ++ ".mk") then some (tBinders.length, ["mk"], true) else none
  let (params, scopeΔ) := telescopeSyntax [] (tBinders.take nΔ)
  let (indices, _) := telescopeSyntax scopeΔ (tBinders.drop nΔ)
  let ctorViews ← ctors.mapM fun c => do
    let cd ← g.find? (ctorConst T c)
    let (bs, res) := piBinders cd.type
    -- the constructor's own names for the parameters (usually the same as `T`'s)
    let (_, scope) := telescopeSyntax [] (bs.take nΔ)
    let fieldBs := bs.drop nΔ
    let (fields, scope') := telescopeSyntax scope fieldBs
    let recursive := fieldBs.map fun (_, _, A) => match (Term.spine A).1 with
      | .const n _ => n == T
      | _ => false
    let proofs := (propBinders g #[] [] bs).drop nΔ
    let idx := ((Term.spine res).2.drop nΔ).map (termSyntax scope')
    pure (mkCon 0 [encodeString c,
      encodeList (((fields.zip recursive).zip proofs).map fun (((x, bi, A), r), pr) =>
        mkCon 0 [encodeString x, encodeBinderKind bi, encodeSyntax A, encodeBool r, encodeBool pr]),
      encodeList (idx.map encodeSyntax)])
  pure (mkCon 0 [encodeString T, encodeList (Td.levelParams.map encodeString),
    encodeList (params.map encodeParam), encodeList (indices.map encodeParam),
    encodeList ctorViews, encodeBool isStructure])

/-- The type of the declaration `n`, as syntax. -/
def declTypeSyntax (g : Globals R) (n : Name) : Option RVal :=
  (g.find? n).map fun d => encodeSyntax (termSyntax [] d.type)

/-- What macros may ask about, for the globals `g`. -/
def macroEnv (g : Globals R) : MacroEnv where
  inductive? := inductiveView g
  declType? := declTypeSyntax g

end Wiz.Elab
