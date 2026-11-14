import WizMeta
import Tests.Elab

/-!
# The reference checker of `WizMeta` as a third voter

`WizMeta/Checker.lean` is a small checker written from the spec's rules
(`WizMeta/Spec/`). Here it votes on the terms of the differential test
(`Tests/Elab.lean`, "the Wiz kernel agrees with the Lean kernel"): the same samples and
the same 400 generated terms. That case compares `Kernel.wiz` with the Lean kernel; this
group compares the reference checker with the Lean kernel, in process, on the terms that
are in its fragment.
-/

open Wiz

namespace Tests.Meta
open Tests.Elab (MTm leanGlobals)
open WizMeta (Tm Lvl Sig Opts Err)

/-- The rules as today's kernels have them, where the spec differs on purpose: a `Π`/`Σ`
may come without its sort, and equations are formed only above `Prop`. -/
def kernelOpts : Opts := { sortsOptional := true, kernelEqFormation := true, payload := .kernel }

def has (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- The globals of the differential test, in the reference checker. -/
def refSig (opts : Opts := kernelOpts) : Except String Sig :=
  MTm.globalDefs.foldlM (init := []) fun sg (n, ps, v, ty) => do
    let some d := WizMeta.ofDecl { name := n, levelParams := ps, type := ty.toTerm, value := v.map MTm.toTerm }
      | throw s!"global {n} is outside the fragment"
    match WizMeta.addDecl sg d opts with
    | .ok sg => pure sg
    | .error e => throw s!"global {n}: {e}"

inductive Outcome where
  /-- the term is outside the fragment: no vote -/
  | outside
  /-- both accept, and the reference checker finds the two types convertible -/
  | accept
  /-- both accept; the kernel's type is outside the fragment, so it was not compared -/
  | acceptUncompared
  | reject
  /-- the kernel rejects for a usage (quantity) reason, which the reference checker does
  not look at, and the reference checker accepts -/
  | usage
  | fuel
  | disagree (what : String)
  deriving Repr, BEq

/-- The Lean kernel on a raw term, with the proof markers it requires (P2) from the
marking pass, as the elaborator gives them and as the differential tests do (`leanVerdict`):
the term is marked only if it is well typed without the requirement (the pass checks
nothing), else the kernel's answer is that check's. The reference checker needs no
markers: it does not evaluate terms through the kernel's evaluator. -/
def kernelInfer (g : Globals ZeroOneMany) (t0 : Term ZeroOneMany) : TCM (VTy ZeroOneMany × Usage ZeroOneMany) :=
  -- (mandatory sorts: the holes `MTm` writes are filled by the sorts pass first)
  -- (the pre-check first, holes allowed: the sorts pass evaluates, so only on a well-typed term)
  match infer (R := ZeroOneMany) { globals := { g with lazyProofs := false, sortHolesOk := true } } t0 with
  | .error e => .error e
  | .ok _ =>
    let t := (Mark.infer (R := ZeroOneMany) { globals := g, sortsOnly := true } t0).1
    infer (R := ZeroOneMany) { globals := g } (Mark.infer (R := ZeroOneMany) { globals := g } t).1

/-- One term: the Lean kernel's verdict against the reference checker's. -/
def vote (g : Globals ZeroOneMany) (sg : Sig) (t : MTm) (opts : Opts := kernelOpts) : Outcome :=
  match WizMeta.ofTerm [] t.toTerm with
  | none => .outside
  | some tm =>
    let k := kernelInfer g t.toTerm
    let r := WizMeta.inferClosed sg tm opts
    match k, r with
    | _, .error .fuel => .fuel
    | .ok (ty, _), .ok T =>
      match WizMeta.ofTerm [] (quote g 0 ty) with
      | none => .acceptUncompared
      | some kT =>
        match WizMeta.convTy { sig := sg, opts } WizMeta.defaultFuel [] T kT with
        | .ok true => .accept
        | .ok false => .disagree "both accept, with types that are not convertible"
        | .error .fuel => .fuel
        | .error (.fail m) => .disagree s!"both accept; comparing the types failed: {m}"
    | .ok _, .error (.fail m) => .disagree s!"the kernel accepts, the reference checker rejects: {m}"
    | .error e, .ok _ =>
      let m := toString e
      if has m "declared with quantity" || has m "cannot project the field" || has m "cannot discard" ||
          has m "a projection needs an unrestricted pair" then .usage
      else .disagree s!"the reference checker accepts, the kernel rejects: {m}"
    | .error _, .error (.fail _) => .reject

/-- The terms of the differential test (`Tests/Elab.lean`): the samples, then 400
generated ones. Keep in step with that case. -/
def diffTerms (n : Nat := 400) : Array MTm := Id.run do
  let mut terms : Array MTm := MTm.samples.toArray
  let mut seed := 42
  for i in [0:n] do
    let (t, s) := MTm.gen seed (2 + i % 3) 0
    terms := terms.push t
    seed := s
  terms

structure Tally where
  outside : Nat := 0
  accept : Nat := 0
  acceptUncompared : Nat := 0
  reject : Nat := 0
  usage : Nat := 0
  fuel : Nat := 0
  disagree : List (Nat × String × String) := []

def Tally.summary (t : Tally) : String :=
  s!"accept {t.accept} (+{t.acceptUncompared} with the type not compared), reject {t.reject}, " ++
  s!"usage-only {t.usage}, out of fuel {t.fuel}, outside the fragment {t.outside}, disagree {t.disagree.length}"

def tally (terms : Array MTm) (opts : Opts := kernelOpts) : Except String Tally := do
  let sg ← refSig opts
  let g := leanGlobals ()
  let mut t : Tally := {}
  let mut i := 0
  for tm in terms do
    match vote g sg tm opts with
    | .outside => t := { t with outside := t.outside + 1 }
    | .accept => t := { t with accept := t.accept + 1 }
    | .acceptUncompared => t := { t with acceptUncompared := t.acceptUncompared + 1 }
    | .reject => t := { t with reject := t.reject + 1 }
    | .usage => t := { t with usage := t.usage + 1 }
    | .fuel => t := { t with fuel := t.fuel + 1 }
    | .disagree w => t := { t with disagree := t.disagree ++ [(i, w, tm.pretty 0)] }
    i := i + 1
  pure t

/-! ## The cases -/

open Tests.Elab.MTm

def kernelAccepts (t : MTm) (g : Globals ZeroOneMany := leanGlobals ()) : Bool :=
  (kernelInfer g t.toTerm).isOk

/-- The reference checker's verdict on a term: `ok`, `fuel`, `outside`, or the rejection. -/
def refVerdict (t : MTm) (opts : Opts := kernelOpts) (sg : Option Sig := none) : String :=
  match sg.map Except.ok |>.getD (refSig opts) with
  | .error e => s!"signature: {e}"
  | .ok sg =>
    match WizMeta.ofTerm [] t.toTerm with
    | none => "outside"
    | some tm =>
      match WizMeta.inferClosed sg tm opts with
      | .ok _ => "ok"
      | .error .fuel => "fuel"
      | .error (.fail m) => s!"rejected: {m}"

def accepts (t : MTm) (opts : Opts := kernelOpts) (sg : Option Sig := none) : IO Unit :=
  checkEq "ok" (refVerdict t opts sg)
def rejects (t : MTm) (opts : Opts := kernelOpts) (sg : Option Sig := none) : IO Unit :=
  check ((refVerdict t opts sg).startsWith "rejected") s!"expected a rejection, got {refVerdict t opts sg}: {t.pretty 0}"

/-- A term in an erased position (the argument of a `0`-binder), so that the kernel's
usage check does not get in the way of what is being probed. -/
def erased (t T : MTm) : MTm := app (ann (lam star) (piq .zero T (unit 0))) (ann t T)

/-- A level of the differential test, in the spec's syntax (`u`, `v` are parameters 0, 1). -/
def ofMLvl (l : Tests.Elab.MLvl) : WizMeta.Lvl := (WizMeta.ofLevel ["u", "v"] l.toLevel).getD 0

-- audit W1: a constant at two universe instances
def w1Decl : Decl ZeroOneMany :=
  { name := "d", levelParams := ["u"], type := prop.toTerm,
    value := some (pi (sortParam "u") (pi (var 0) (pi (var 1) (pi (pi (var 2) prop) (pi (app (var 0) (var 2)) (app (var 1) (var 2))))))).toTerm }
def w1 (a b : Nat) : MTm :=
  ann (lam (lam (var 0))) (pi (enum 1) (pi (ecase prop (var 0) [const "d" [a]]) (ecase prop (var 1) [const "d" [b]])))

-- model-memo E5b: a payload equation at a field whose type is a variable
def wrapTy (A : MTm) : MTm := mu 0 (unit 0) (darg A (lam (dret star))) star
def wrap (A a : MTm) : MTm := ann (con (pair a (pair star star))) (wrapTy A)
def e5bTy : MTm :=
  pi (univ 0) (pi (var 0) (pi (var 1) (pi (eq (wrapTy (var 2)) (wrap (var 2) (var 1)) (wrap (var 2) (var 0))) (eq (var 3) (var 2) (var 1)))))
def e5b : MTm := erased (lam (lam (lam (lam (fst (var 0)))))) e5bTy

-- model-memo T4: an equation between two Π types whose domains are in different universes
def crossLevel : MTm :=
  let A1 := sorted 0 1 (pi pfalse (enum 2))
  let A2 := sorted 0 2 (pi pfalse (univ 0))
  let no := lam (exfalso pfalse (var 0))
  erased (pair (pair (pair no no) no) (lam star)) (eqTy (sorted 1 2 (pi A1 (univ 0))) (sorted 2 2 (pi A2 (univ 0))))


-- PR #40 (CoreSpec §8.4b): equality at `Desc`, `μ ≡ μ` by codes, casts at `Desc` and `μ`
namespace DescEq
def U : MTm := unit 0
def DU : MTm := desc 0 U
def dRet : MTm := dret star
def dArg1 : MTm := darg (enum 1) (lam (dret star))
def dRec : MTm := drec star (dret star)
def M1 : MTm := mu 0 U dRet star
def M2 : MTm := mu 0 U dArg1 star
def Bool' : MTm := mu 0 U (darg (enum 2) (lam (dret star))) star
def tagged (B : MTm) (k : Nat) : MTm := ann (con (pair (tag 2 k) (pair star star))) B
/-- two constructors with a field at a type variable `A` (at index `k`): not inert -/
def W (k : Nat) : MTm := mu 0 U (darg (enum 2) (lam (darg (var (k + 1)) (lam (dret star))))) star
def wcon (k t : Nat) (x : MTm) : MTm := ann (con (pair (tag 2 t) (pair x (pair star star)))) (W k)
/-- `(name, term, the kernel and the reference checker both accept)` -/
def terms : List (String × MTm × Bool) := [
  ("μ ≡ μ by codes: different descriptions give False (eqTyMu, Σ rule, cast at Desc, eqCtors)",
    erased (lam (exfalso pfalse (fst (snd (var 0))))) (pi (eqTy M1 M2) pfalse), true),
  ("equality at Desc: different constructors are False",
    erased (lam (exfalso pfalse (var 0))) (pi (eq DU dRet dArg1) pfalse), true),
  ("equality at Desc: arg = arg gives the field types' equation first",
    erased (lam (fst (var 0))) (pi (eq DU dArg1 dArg1) (eqTy (enum 1) (enum 1))), true),
  ("equality at Desc: ret = ret is the index equation (True), not False",
    erased (lam (exfalso pfalse (var 0))) (pi (eq DU dRet dRet) pfalse), false),
  ("a cast at Desc computes on arg",
    erased (lam (lam (exfalso pfalse (var 0)))) (pi (eqTy DU DU) (pi (eq DU (cast DU DU (var 0) dArg1) dRet) pfalse)), true),
  ("a cast at Desc computes on rec",
    erased (lam (lam (exfalso pfalse (var 0)))) (pi (eqTy DU DU) (pi (eq DU (cast DU DU (var 0) dRec) dRet) pfalse)), true),
  ("a cast at an inert μ on a constructor, then the tags differ",
    erased (lam (lam (exfalso pfalse (fst (var 0)))))
      (pi (eqTy Bool' Bool') (pi (eq Bool' (cast Bool' Bool' (var 0) (tagged Bool' 0)) (tagged Bool' 1)) pfalse)), true),
  ("a cast at a non-inert μ (a field at a type variable) on a constructor, then the tags differ",
    erased (lam (lam (lam (lam (exfalso pfalse (fst (var 0)))))))
      (pi (univ 0) (pi (var 0) (pi (eqTy (W 1) (W 1))
        (pi (eq (W 2) (cast (W 2) (W 2) (var 0) (wcon 2 0 (var 1))) (wcon 2 1 (var 1))) pfalse)))), true),
  ("a cast at a non-inert μ, same tags: no False",
    erased (lam (lam (lam (lam (exfalso pfalse (fst (var 0)))))))
      (pi (univ 0) (pi (var 0) (pi (eqTy (W 1) (W 1))
        (pi (eq (W 2) (cast (W 2) (W 2) (var 0) (wcon 2 0 (var 1))) (wcon 2 0 (var 1))) pfalse)))), false),
  ("μ ≡ μ by codes, the same family: the index types' equation first",
    erased (lam (fst (var 0))) (pi (eqTy M1 M1) (eqTy U U)), true)
]
end DescEq

-- PR #123 (CoreSpec §8.2, wiz-notes/nu-transp.md): an equation at a proposition is `True`;
-- the Σ rule at a proof first component proves `B a.1 ≡ B b.1` by `reflTy`, not `transp`
namespace NuTransp
/-- `(x : Enum 2) × x = x` (closed): a proof second component -/
def sub (_ : Nat) : MTm := sigma (enum 2) (eq (enum 2) (var 0) (var 0))
/-- `(0 _ : True) × B` in a context of `k` variables, `B` the outermost: a proof first component -/
def prf (k : Nat) : MTm := sigmaq .zero ptrue (var k)
/-- `fun pres… p q (h : p = q) => let h2 : T := h.2; ()`, with `p q : S k` (`S k` the Σ in a
context of `k` variables); `T` is over `pres, p, q, h`. The elaborator let-binds `h.2` at the
type the kernel inferred, quoted, and the kernel checks it again: this is that path. -/
def letSnd (pres : List MTm) (S : Nat → MTm) (T : MTm) : MTm :=
  let n := pres.length
  let body := lam (lam (lam (letE T (snd (var 0)) star)))
  let ty := pi (S n) (pi (S (n + 1)) (pi (eq (S (n + 2)) (var 1) (var 0)) ptrue))
  ann (pres.foldr (fun _ t => lam t) body) (pres.foldr (fun A t => pi A t) ty)
/-- f1 of #123's test: `h.2 : True` at a subtype (the kernel's type, quoted) -/
def f1 : MTm := letSnd [] sub ptrue
/-- f2 of #123's test: `h.2 : cast (reflTy B) p.2 = q.2` at `(0 k : True) × B` (the kernel's type, quoted) -/
def f2 : MTm := letSnd [univ 0] prf (eq (var 3) (cast (var 3) (var 3) (reflTy (var 3)) (snd (var 2))) (snd (var 1)))
/-- f2 at the type the kernel quoted before #123: `transp` along `True` -/
def f2old : MTm := letSnd [univ 0] prf
  (eq (var 3) (cast (var 3) (var 3)
    (transp ptrue (fst (var 2)) (lam (lam (eqTy (var 5) (var 5)))) (reflTy (var 3)) (fst (var 1)) (fst (var 0)))
    (snd (var 2))) (snd (var 1)))
/-- f1 at the type before #123: an equation at the proposition `q.1 = q.1` -/
def f1old : MTm :=
  let x1 (i : Nat) : MTm := eq (enum 2) (fst (var i)) (fst (var i))
  letSnd [] sub
    (eq (x1 1) (cast (x1 2) (x1 1)
      (transp (enum 2) (fst (var 2)) (lam (lam (eqTy (x1 4) (eq (enum 2) (var 1) (var 1))))) (reflTy (x1 2)) (fst (var 1)) (fst (var 0)))
      (snd (var 2))) (snd (var 1)))
/-- `Unit × True` -/
def UT : MTm := sigma (unit 0) ptrue
/-- `((), f ()) = ((), ())` at `Unit × True`, `f : Unit → True` the variable 0 -/
def pfEq : MTm := eq UT (ann (pair star (app (var 0) star)) UT) (ann (pair star star) UT)
/-- `(name, term, the kernel and the reference checker both accept)` -/
def terms : List (String × MTm × Bool) := [
  ("f1: an equation at a subtype, h.2 : True", f1, true),
  ("f2: an equation at (0 k : True) × B, h.2 : cast (reflTy B) p.2 = q.2", f2, true),
  ("f2 at the type quoted before #123 (transp along True): rejected", f2old, false),
  ("f1 at the type quoted before #123 (an equation at q.1 = q.1): rejected", f1old, false),
  ("an equation at a proposition is True: ((), f ()) = ((), ()) at Unit × True is proved by ((), ())",
    ann (lam (pair star star)) (pi (pi (unit 0) ptrue) pfEq), true),
  ("… and is not False",
    ann (lam (lam (snd (var 0)))) (pi (pi (unit 0) ptrue) (pi pfEq pfalse)), false)
]
/-- A context of the reference checker from types written outermost first. -/
def ctxOf (tys : List MTm) : Except String WizMeta.Ctx :=
  tys.foldlM (init := []) fun Γ A => do
    let some A' := WizMeta.ofTerm [] A.toTerm | throw s!"outside the fragment: {A.pretty 0}"
    pure (A' :: Γ)
/-- The context `pres, p q : S, h : p = q` of `letSnd`. -/
def letSndCtx (pres : List MTm) (S : Nat → MTm) : List MTm :=
  let n := pres.length
  pres ++ [S n, S (n + 1), eq (S (n + 2)) (var 1) (var 0)]
def run {α : Type} (r : WizMeta.M α) : Except String α :=
  match r with
  | .ok a => pure a
  | .error e => throw (toString e)
/-- The reference checker's own type of `h.2` in `f1`/`f2` (in the context of `letSnd`), in
weak-head normal form, is well formed under the kernels' formation rules (`kernelOpts`):
what the elaborator path above asks of the third voter. -/
def sndTyWellFormed (sg : Sig) (pres : List MTm) (S : Nat → MTm) : Except String Unit := do
  let Γ ← ctxOf (letSndCtx pres S)
  let E : WizMeta.Env := { sig := sg, opts := kernelOpts }
  let F := WizMeta.defaultFuel
  run do
    let T ← WizMeta.infer E F Γ (.snd (.var 0))
    let T' ← WizMeta.whnf E F Γ T
    let _ ← WizMeta.inferSort E F Γ T'
    pure ()
end NuTransp

/-! ## The second reading (meta-review): defects found, and presupposition properties

Terms here are written in the spec's own syntax (`WizMeta.Tm`), most of them in a context. -/

namespace Review

def F : Nat := WizMeta.defaultFuel
def env (o : Opts := {}) (sg : Sig := []) : WizMeta.Env := { sig := sg, opts := o }
def piT (s : WizMeta.Lvl) (A B : Tm) : Tm := .pi .many (some s) A B
def sgT (s : WizMeta.Lvl) (A B : Tm) : Tm := .sigma .many (some s) A B

def okOr {α : Type} (what : String) : WizMeta.M α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-- Subject reduction at one term: its weak-head normal form checks against its type
(unless the type is a proposition: proofs are not reduced). -/
def subjRed (o : Opts) (sg : Sig) (Γ : WizMeta.Ctx) (t : Tm) : WizMeta.M Bool := do
  let E := env o sg
  let T ← WizMeta.infer E F Γ t
  if (← WizMeta.propOf E F Γ (← WizMeta.whnf E F Γ T)) == some true then return false
  let t' ← WizMeta.whnf E F Γ t
  WizMeta.check E F Γ t' T
  pure true

/-- A cast between `X` and `Y` given `e : X ≡ Y` and `t : X` in the context. -/
def castIn (X Y : Tm) : WizMeta.Ctx × Tm := ([X, .eqTy X Y], .cast X Y (.var 1) (.var 0))

/-- Closed types with their sorts, for the template properties. -/
def typePool : List (Tm × WizMeta.Lvl) :=
  [(Tm.True', 0), (.unit 1, 1), (.enum 2, 1), (.sort 0, 1), (.unit 2, 2), (.sort 1, 2),
   (piT 1 (.enum 2) (.unit 1), 1), (sgT 2 (.sort 1) (.unit 1), 2), (.ulift 3 (.enum 2), 3)]

/-- Index types `I : Sort (l+1)` with an element, and fields of that level. -/
def indexPool : List (WizMeta.Lvl × Tm × Tm) :=
  [(0, .unit 1, .tt), (0, .enum 2, .tag 2 1), (1, .unit 2, .tt), (0, .sort 0, Tm.True'), (1, .sort 1, .enum 2)]

/-- Kernel subterms with the number of binders they are under. -/
partial def subterms (t : Term ZeroOneMany) (d : Nat := 0) : List (Term ZeroOneMany × Nat) :=
  let kids : StateM (List (Term ZeroOneMany × Nat)) (Term ZeroOneMany) :=
    t.mapChildrenM pure fun k c => do modify (· ++ subterms c (d + k)); pure c
  (t, d) :: (kids.run []).2

end Review

open Review in
def group : Group where
  name := "meta"
  parallel := true
  exercise := "WizMeta (metatheory-plan M1c): the reference checker"
  cases := [
    { name := "the reference checker agrees with the Lean kernel on the differential test's terms (samples + 400 generated)", run := fun _ => do
        match tally (diffTerms 400) with
        | .error e => throw (IO.userError e)
        | .ok t =>
          IO.println s!"    {t.summary}"
          unless t.disagree.isEmpty do
            throw (IO.userError ("\n".intercalate (t.disagree.map fun (i, w, tm) => s!"#{i}: {w}\n    {tm}")))
          check (t.fuel == 0) "a term ran out of fuel"
          check (t.accept ≥ 200) s!"too few accepted terms: {t.accept}"
          check (t.reject ≥ 100) s!"too few rejected terms: {t.reject}"
          check (t.acceptUncompared ≤ 10) s!"too many types not compared: {t.acceptUncompared}" },
    { name := "the same with the levelled rule for Π ≡ Π (the corpus does not tell the variants apart)", run := fun _ => do
        match tally (diffTerms 400) { kernelOpts with eqTyLevelled := true } with
        | .error e => throw (IO.userError e)
        | .ok t =>
          unless t.disagree.isEmpty do
            throw (IO.userError ("\n".intercalate (t.disagree.map fun (i, w, tm) => s!"#{i}: {w}\n    {tm}"))) },
    { name := "PR #40 (CoreSpec 8.4b): equality at Desc, μ ≡ μ by codes, casts at Desc and μ: the reference checker agrees with the Lean kernel", run := fun _ => do
        let sg ← match refSig with | .ok sg => pure sg | .error e => throw (IO.userError e)
        let g := leanGlobals ()
        for (what, t, ok) in DescEq.terms do
          check (kernelAccepts t g == ok) s!"{what}: the kernel {if ok then "rejects" else "accepts"} {t.pretty 0}"
          match vote g sg t with
          | .accept | .acceptUncompared => check ok s!"{what}: both accept"
          | .reject => check (!ok) s!"{what}: both reject"
          | o => throw (IO.userError s!"{what}: {repr o}\n    {t.pretty 0}")
          -- the spec's own options, in each payload variant
          for p in [WizMeta.PayloadRule.kernel, .stuck, .uniform] do
            let r := refVerdict t { kernelOpts with payload := p }
            check ((r == "ok") == ok) s!"{what}, payload {repr p}: {r}" },
    { name := "PR #123 (CoreSpec 8.2): equations at propositions are True, the Σ rule at a proof component uses reflTy: the reference checker agrees with the Lean kernel", run := fun _ => do
        let sg ← match refSig with | .ok sg => pure sg | .error e => throw (IO.userError e)
        let g := leanGlobals ()
        for (what, t, ok) in NuTransp.terms do
          check (kernelAccepts t g == ok) s!"{what}: the kernel {if ok then "rejects" else "accepts"} {t.pretty 0}"
          match vote g sg t with
          | .accept | .acceptUncompared => check ok s!"{what}: both accept"
          | .reject => check (!ok) s!"{what}: both reject"
          | o => throw (IO.userError s!"{what}: {repr o}\n    {t.pretty 0}")
        -- the checker's own type of `h.2`, as the elaborator would quote it, is well formed
        -- for the kernels (before #123 it was a `transp` along `True`)
        for (what, pres, S) in [("f1", ([] : List MTm), NuTransp.sub), ("f2", [univ 0], NuTransp.prf)] do
          match NuTransp.sndTyWellFormed sg pres S with
          | .ok () => pure ()
          | .error e => throw (IO.userError s!"{what}: the type of h.2 is not well formed for the kernels: {e}")
        -- the rule before #123: its proof, in the context of f2 and `e : p.1 = q.1`, is
        -- `transp` along `True`, which the kernels' formation rules reject
        let Γ ← match NuTransp.ctxOf ([univ 0, NuTransp.prf 1, NuTransp.prf 2]) with
          | .ok Γ => pure Γ | .error e => throw (IO.userError e)
        let Γe := Tm.eq Tm.True' (.fst (.var 1)) (.fst (.var 0)) :: Γ
        let E : WizMeta.Env := { sig := sg, opts := kernelOpts }
        check (match WizMeta.infer E WizMeta.defaultFuel Γe (Tm.eqSigmaTransport Tm.True' (.var 3) (.var 1) (.var 0)) with
          | .error (.fail m) => has m "may be a proposition" | _ => false)
          "transp along True is formed by the kernels' rules"
        -- the new reduct is well formed by the spec's rules (its first component is an
        -- equation at `True`, which only the spec forms; the kernels compute it to `True`)
        check (match WizMeta.infer { E with opts := { kernelOpts with kernelEqFormation := false } } WizMeta.defaultFuel Γ (Tm.eqSigmaProof Tm.True' (.var 3) (.var 1) (.var 0)) with
          | .ok _ => true | _ => false)
          "the reduct of Sigma.eqProof is not well formed"
        -- known gap of both kernels (pinned in 'observational equality'): at a neutral
        -- proposition `P q.1` the kernels do not see a proposition, the reference checker
        -- (which computes sorts) does: it accepts `h.2 : True`, the kernel rejects it.
        -- Mandatory sorts closes the gap; then this flips to agreement.
        let g1 := NuTransp.letSnd [univ 0, pi (var 0) prop] (fun k => sigma (var (k - 1)) (app (var (k - 1)) (var 0))) ptrue
        check (!kernelAccepts g1 g) "the kernel accepts g1 (the neutral-proposition gap is closed): make it a corpus term"
        check (refVerdict g1 == "ok") "the reference checker rejects g1" },
    { name := "declarations at symbolic levels: the reference checker agrees with the Lean kernel (216)", run := fun _ => do
        let sg ← match refSig with | .ok sg => pure sg | .error e => throw (IO.userError e)
        let decls := MTm.declSamples ++ MTm.levelPuzzles 200
        let mut oks := 0
        for d in decls do
          let (ps, v, ty) := d
          let k := Tests.Elab.leanDeclVerdict d
          let r := match WizMeta.ofDecl { name := "test", levelParams := ps, type := ty.toTerm, value := v.map MTm.toTerm } with
            | none => "outside"
            | some dd => match WizMeta.addDecl sg dd kernelOpts with
              | .ok _ => "ok"
              | .error .fuel => "fuel"
              | .error _ => "error"
          unless k == r do
            throw (IO.userError s!"kernel {k}, reference checker {r}: {ty.pretty 0} := {v.map (·.pretty 0)}")
          if k == "ok" then oks := oks + 1
        check (oks ≥ 60 && decls.length - oks ≥ 30) s!"unbalanced: {oks} of {decls.length} accepted" },
    { name := "levels: the decision procedure agrees with evaluation (generated pairs, parameters in 0..3)", run := fun _ => do
        let mut s := 11
        let mut equal := 0
        for _ in [0:600] do
          let (a, s1) := Tests.Elab.MLvl.gen s 2
          let (b, s2) := if s1 % 3 == 0 then Tests.Elab.MLvl.rewrite s1 a else Tests.Elab.MLvl.gen s1 2
          s := s2
          let (a, b) := (ofMLvl a, ofMLvl b)
          let grid := (List.range 4).flatMap fun x => (List.range 4).map fun y => (fun i => if i == 0 then x else y : Nat → Nat)
          let same := grid.all fun ρ => a.eval ρ == b.eval ρ
          unless a.equiv b == same do throw (IO.userError s!"equiv {a.pretty} {b.pretty}: {a.equiv b}, by evaluation {same}")
          unless a.neverZero == grid.all (fun ρ => a.eval ρ != 0) do throw (IO.userError s!"neverZero {a.pretty}")
          unless a.isZero == grid.all (fun ρ => a.eval ρ == 0) do throw (IO.userError s!"isZero {a.pretty}")
          if same then equal := equal + 1
        check (equal ≥ 100 && equal ≤ 500) s!"unbalanced: {equal} of 600 equal" },
    { name := "the spec's own rules: a Π/Σ carries its sort, and it is checked", run := fun _ => do
        let spec : Opts := {}
        rejects (ann (lam (lam (var 0))) (pi (univ 0) (pi (var 0) (var 1)))) spec (some [])
        accepts (ann (lam (lam (var 0))) (sorted 2 1 (pi (univ 0) (sorted 1 1 (pi (var 0) (var 1)))))) spec (some [])
        rejects (ann (lam (lam (var 0))) (sorted 1 1 (pi (univ 0) (sorted 1 1 (pi (var 0) (var 1)))))) spec (some [])
        -- impredicativity: a Π into Prop is in Prop
        accepts (sorted 2 0 (pi (univ 0) ptrue)) spec (some [])
        rejects (sorted 2 2 (pi (univ 0) ptrue)) spec (some [])
        accepts (sorted 2 0 (sigma (univ 0) ptrue)) spec (some []) },
    { name := "the spec's own rules: equations are formed at every sort, and are True at a proposition", run := fun _ => do
        let spec : Opts := {}
        let eqP := eq ptrue star star
        rejects eqP
        check (!kernelAccepts eqP) "the kernel forms an equation at a proposition"
        accepts eqP spec (some [])
        accepts (ann star eqP) spec (some [])
        -- between a proposition and a type that is not one: formed in the spec, and False
        rejects (eqTy ptrue (enum 2))
        accepts (ann (lam (var 0)) (sorted 0 0 (pi (eqTy ptrue (enum 2)) pfalse))) spec (some []) },
    { name := "T0 against T1: a cast between convertible inert types is its argument only with InReg", run := fun _ => do
        let nat := const "Nat"
        let t := ann (lam (lam (refl nat (var 0)))) (pi (eqTy nat nat) (pi nat (eq nat (cast nat nat (var 1) (var 0)) (var 0))))
        accepts t
        rejects t { kernelOpts with inertReg := false }
        -- a non-inert type (a function type): the cast computes structurally instead; no rule identifies
        -- a cast at a neutral type with its argument
        let v := ann (lam (lam (lam (refl (var 2) (var 0))))) (pi (univ 0) (pi (eqTy (var 0) (var 0)) (pi (var 1) (eq (var 2) (cast (var 2) (var 2) (var 1) (var 0)) (var 0)))))
        rejects v
        check (!kernelAccepts v) "the kernel has regularity at a type variable" },
    { name := "the level premise of ind (audit F3): the index type is in Sort (l+1)", run := fun _ => do
        -- `ind.{1}` at an index type in `Sort 1`; `D` and the scrutinee are checked against values
        -- the rule builds, so no former sees the level (the Lean kernel at a143052 accepts this)
        let bad := ind 1 (unit 0) (dret star) 1 (lam (lam (enum 2))) (lam (lam (lam (tag 2 0)))) star (con (pair star star))
        rejects bad
        accepts (ind 0 (unit 0) (dret star) 1 (lam (lam (enum 2))) (lam (lam (lam (tag 2 0)))) star (con (pair star star)))
        rejects (desc 1 (unit 0))
        accepts (desc 0 (unit 0)) },
    { name := "audit probes in the fragment: K6 (a variable out of scope), Y4 (a name declared twice), W1 (a constant at two levels)", run := fun _ => do
        -- K6: the Lean kernel on master types an out-of-scope variable as Prop : Prop (not run here: it panics)
        rejects (var 0)
        rejects (ann (var 3) (var 3))
        rejects (ann (lam (var 1)) (pi (univ 0) (univ 0)))
        let sg ← match refSig with | .ok sg => pure sg | .error e => throw (IO.userError e)
        let some d := WizMeta.ofDecl w1Decl | throw (IO.userError "d is outside the fragment")
        let sg1 ← match WizMeta.addDecl sg d kernelOpts with | .ok sg => pure sg | .error e => throw (IO.userError s!"d: {e}")
        -- Y4
        check (match WizMeta.addDecl sg1 d kernelOpts with | .error (.fail m) => has m "already declared" | _ => false)
          "a second declaration of a name is accepted"
        -- W1: `d.{0}` and `d.{1}` under a stuck case are different
        rejects (w1 0 1) kernelOpts (some sg1)
        accepts (w1 1 1) kernelOpts (some sg1)
        let g1 ← match addDecl (leanGlobals ()) (Decl.withMarks (leanGlobals ()) w1Decl) with | .ok g => pure g | .error e => throw (IO.userError s!"{e}")
        check (!kernelAccepts (w1 0 1) g1 && kernelAccepts (w1 1 1) g1) "the Lean kernel's verdicts on W1 changed" },
    { name := "E5b: a payload equation at a neutral field type, in the three variants (the kernels' rule is not stable under substitution)", run := fun _ => do
        let stuck := { kernelOpts with payload := .stuck }
        let uniform := { kernelOpts with payload := .uniform }
        -- the instance of `e5b` at `A := Enum 2`, `a = b = #0`, and `e5b` applied to them
        let two := enum 2
        let inst := erased (lam (fst (var 0))) (pi (eq (wrapTy two) (wrap two (tag 2 0)) (wrap two (tag 2 0))) (eq two (tag 2 0) (tag 2 0)))
        -- the kernels' rule: the generic term is accepted and its instance is not
        accepts e5b
        rejects inst
        check (kernelAccepts e5b && !kernelAccepts inst) "the Lean kernel's verdicts on E5b changed: update the note"
        -- stuck at a neutral field type: the generic term is rejected
        rejects e5b stuck
        rejects inst stuck
        -- no shortcut: both accepted
        accepts e5b uniform
        accepts inst uniform
        -- at a canonical field type that is not a tag type, all three take the Σ rule
        let F := pi (enum 2) (enum 2)
        let idf := ann (lam (var 0)) F
        let t := erased (lam (fst (var 0))) (pi (eq (wrapTy F) (wrap F idf) (wrap F idf)) (eq F idf idf))
        accepts t
        accepts t stuck
        accepts t uniform
        check (kernelAccepts t) "the kernel rejects the Σ rule at a canonical field" },
    { name := "T4: an equation between Π types with domains in different universes (accepted by the kernels' rule, stuck with the levelled one)", run := fun _ => do
        accepts crossLevel
        rejects crossLevel { kernelOpts with eqTyLevelled := true }
        check (kernelAccepts crossLevel) "the Lean kernel no longer decomposes across levels: update the note" },
    { name := "review: a structural cast whose components are in different sorts is stuck (its reduct would cast across universes)", run := fun _ => do
        -- (Unit₁ → Unit₂) and (Unit₂ → Unit₂) are both in Sort 2; so are the Σs and the lifts
        let pairs : List (String × Tm × Tm) :=
          [("Π", piT 2 (.unit 1) (.unit 2), piT 2 (.unit 2) (.unit 2)),
           ("Σ", sgT 2 (.unit 1) (.unit 2), sgT 2 (.unit 2) (.unit 2)),
           ("ULift", .ulift 1 Tm.True', .ulift 1 (.unit 1))]
        for o in [({} : Opts), { eqTyLevelled := true }] do
          for (what, X, Y) in pairs do
            let (Γ, t) := castIn X Y
            let _ ← okOr s!"{what}: subject reduction (levelled {o.eqTyLevelled})" (subjRed o [] Γ t)
            let t' ← okOr what (WizMeta.whnf (env o) F Γ t)
            check (match t' with | .cast .. => true | _ => false) s!"{what}: the cast computed: {repr t'}"
        -- control: components in one sort, the cast computes and its reduct has the type
        for (what, X, Y) in [("Π", piT 2 (.unit 2) (.unit 1), piT 2 (.unit 2) (.enum 2)),
                             ("Σ", sgT 2 (.unit 2) (.unit 1), sgT 2 (.unit 2) (.enum 2))] do
          let (Γ, t) := castIn X Y
          let _ ← okOr s!"{what} control" (subjRed {} [] Γ t)
          let t' ← okOr what (WizMeta.whnf (env) F Γ t)
          check (match t' with | .cast .. => false | _ => true) s!"{what}: the control cast is stuck" },
    { name := "review: transp's motive type is a type at every level (it was annotated Sort 1)", run := fun _ => do
        for (A, l) in typePool ++ [(.sort (.param 0), (WizMeta.Lvl.param 0).succ)] do
          let Γ : WizMeta.Ctx := [A]
          let k ← okOr s!"motive type at {repr A}" (WizMeta.inferSort (env) F Γ (Tm.transpMotiveTy l A.shift (.var 0)))
          check (k.equiv (.imax l 1)) s!"sort {k.pretty}"
        let t : Tm := .transp (.sort 1) (.enum 2) (.lam (.lam Tm.True')) .tt (.enum 2) (.refl (.sort 1) (.enum 2))
        let _ ← okOr "transp at Sort 2" (WizMeta.infer (env { checkTemplates := true }) F [] t) },
    { name := "review: in the levelled variant A ≡ B is formed only at one sort", run := fun _ => do
        let t : Tm := .eqTy Tm.True' (.enum 2)
        let _ ← okOr "cross" (WizMeta.infer (env) F [] t)
        check (match WizMeta.infer (env { eqTyLevelled := true }) F [] t with | .error (.fail _) => true | _ => false)
          "levelled: formed across sorts" },
    { name := "review: All and hyps compute at a field only when its quantity is a literal", run := fun _ => do
        let I : Tm := .unit 1
        let X : Tm := .lam (.unit 1)
        let P : Tm := .lam (.lam Tm.True')
        -- context: q : Qty, xs : ⟦arg q (Enum 2) (λ_. ret tt)⟧ X tt
        for (qv, ok) in [((Tm.var 1, Tm.var 0), false), ((.qlit .many, .qlit .many), true)] do
          let Γ : WizMeta.Ctx := [.interp 0 I (.darg qv.2 (.enum 2) (.lam (.dret .tt))) X .tt, .qty]
          let t : Tm := .ann .tt (.dall 0 0 I (.darg qv.1 (.enum 2) (.lam (.dret .tt))) X P .tt (.var 0))
          let r := WizMeta.infer (env) F Γ t
          check ((match r with | .ok _ => true | _ => false) == ok) s!"tt : All … at quantity {repr qv.1}: {repr (r.toOption)}" },
    { name := "review: the description templates are types (presupposition), at every index type and motive level", run := fun _ => do
        let E := env
        let mut n := 0
        for (l, I, i) in indexPool do
          let descs : List Tm := [.dret i, .drec (.qlit .one) i (.dret i),
            .darg (.qlit .many) I (.lam (.dret i.shift)),
            .dhrec (.qlit .many) I (.lam (.var 0)) (.dret i)]
          let _ ← okOr "Tm.familyTy" (WizMeta.inferSort E F [] (Tm.familyTy l I))
          for S in [Tm.enum 2, I] do
            if (← okOr "field" (WizMeta.inferSort E F [] S)).equiv l.succ then
              let _ ← okOr "Tm.argContTy" (WizMeta.inferSort E F [] (Tm.argContTy l I S))
              let _ ← okOr "Tm.hrecIndexTy" (WizMeta.inferSort E F [] (Tm.hrecIndexTy l I S))
          for v in [(0 : WizMeta.Lvl), 1, 2] do
            let k ← okOr "Tm.delimMotiveTy" (WizMeta.inferSort E F [] (Tm.delimMotiveTy l v I))
            check (k.equiv (.imax l.succ.succ v.succ)) s!"Tm.delimMotiveTy sort {k.pretty}"
            let ΓP : WizMeta.Ctx := [Tm.delimMotiveTy l v I]
            let (a, b, c, h) := Tm.delimMethodTys l v I.shift (.var 0)
            for T in [a, b, c, h] do
              let _ ← okOr s!"Tm.delimMethodTys l={l.pretty} v={v.pretty}" (WizMeta.inferSort E F ΓP T)
            for D in descs do
              let _ ← okOr "a sample description" (WizMeta.check E F [] D (.desc l I))
              let _ ← okOr "Tm.indMotiveTy" (WizMeta.inferSort E F [] (Tm.indMotiveTy l v I D))
              let Γm : WizMeta.Ctx := [Tm.indMotiveTy l v I D]
              let _ ← okOr s!"Tm.indMethodTy l={l.pretty} v={v.pretty}" (WizMeta.inferSort E F Γm (Tm.indMethodTy l v I.shift D.shift (.var 0)))
              -- at a variable family (a λ such as `muFamily` makes β-redexes, which `infer` does not type)
              let ΓX : WizMeta.Ctx := [Tm.familyTy l I]
              let _ ← okOr "predTy" (WizMeta.inferSort E F ΓX (Tm.predTy l v I.shift (.var 0)))
              let _ ← okOr "sectionTy" (WizMeta.inferSort E F (Tm.predTy l v I.shift (.var 0) :: ΓX) (Tm.sectionTy l v (I.shiftN 2) (.var 1) (.var 0)))
              n := n + 1
        check (n == 60) s!"{n} instances" },
    { name := "review: the corpus with every built type checked to be a type, and subject reduction on it", run := fun _ => do
        match tally (diffTerms 400) { kernelOpts with checkTemplates := true } with
        | .error e => throw (IO.userError e)
        | .ok t =>
          unless t.disagree.isEmpty do
            throw (IO.userError ("\n".intercalate (t.disagree.map fun (i, w, tm) => s!"#{i}: {w}\n    {tm}")))
        let sg ← match refSig with | .ok sg => pure sg | .error e => throw (IO.userError e)
        let mut reduced := 0
        let mut uninferable := 0
        for tm in diffTerms 400 do
          let some t := WizMeta.ofTerm [] tm.toTerm | continue
          match WizMeta.inferClosed sg t kernelOpts with
          | .ok _ =>
            match subjRed kernelOpts sg [] t with
            | .ok true => reduced := reduced + 1
            | .ok false => pure ()
            -- a reduct with a β- or projection redex on a constructor (`(x, y).2` in an
            -- equation's reduct) is typable by the rules but not inferable by a bidirectional
            -- checker: not a counterexample, counted apart
            | .error (.fail "cannot infer a type for this term") => uninferable := uninferable + 1
            | .error e => throw (IO.userError s!"subject reduction fails ({e}): {tm.pretty 0}")
          | .error _ => pure ()
        IO.println s!"    {reduced} accepted relevant terms reduced to a weak-head normal form of their type ({uninferable} reducts not inferable)"
        check (reduced ≥ 50) s!"too few: {reduced}" },
    { name := "review: weakening and substitution commute with the translation (every subterm of the corpus)", run := fun _ => do
        let s : Term ZeroOneMany := MTm.toTerm (enum 2)
        let some s' := WizMeta.ofTerm [] s | throw (IO.userError "enum")
        let mut n := 0
        for tm in diffTerms 400 do
          for (u, _) in subterms tm.toTerm do
            let some u' := WizMeta.ofTerm [] u | continue
            for cut in [0, 1] do
              let ρ : Nat → Nat := fun i => if i ≥ cut then i + 1 else i
              check (WizMeta.ofTerm [] (u.lift 1 cut) == some (u'.ren ρ)) s!"lift 1 {cut}: {repr u}"
            check (WizMeta.ofTerm [] (u.instantiateAt 0 s) == some (u'.inst s')) s!"instantiate 0: {repr u}"
            let σ : Nat → Tm := fun i => if i == 0 then .var 0 else if i == 1 then s' else .var (i - 1)
            check (WizMeta.ofTerm [] (u.instantiateAt 1 s) == some (u'.sub σ)) s!"instantiate 1: {repr u}"
            n := n + 1
        IO.println s!"    {n} subterms"
        check (n ≥ 5000) s!"too few subterms: {n}" }
  ]

def groups : List Group :=
  group ::
  []

end Tests.Meta
