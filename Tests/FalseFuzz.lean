import Tests.Groups.Prop

/-!
# A `False` fuzzer for the two kernels

`Tests/Prop.lean` checks laws on samples that are well typed by construction.  This module
is the other half: it generates *closed* terms that claim to inhabit `Empty`, for the
shapes the property harness reaches thinly (descriptions with a parameter, `ν`, sizes,
`let ()`, `scase` at a quantity, mutual families, casts at a `Σ`, a stuck `Desc.elim`),
and asks both kernels for a verdict.  A kernel that accepts one has proved `Empty`
inhabited; a verdict or normal-form difference between the kernels is a `P5` finding.

The oracle is uniform.  For a generated type `T` and value `v : T`, the candidate is

  `cast T (Empty l) (reflTy T) v : Empty l`

where `l` is `T`'s sort (`Empty l` has no constructor at any `l`).  It is accepted exactly
when the kernel's conversion believes `T ≡ Empty l`; every shape is therefore a question
about one conversion (or `vCast`) rule.  A *well-typed* candidate is a soundness bug in
that kernel, on a closed term.

The module also asks each kernel for the normal form of the equation `T = Empty l`, so a
run compares verdicts *and* normal forms even when neither kernel accepts anything.

`tests --false-fuzz N SEED` runs the campaign; `tests --false-fuzz-replay SHAPE C…` runs
one sample again.  See `/workspace/wiz-notes/false-fuzz.md`.
-/

set_option compiler.extract_closed false

open Wiz
open Tests.Elab (MTm)
open Tests.Prop

namespace Tests.FalseFuzz

abbrev Tm := Tests.Prop.Tm

/-- The world both kernels share (`Tests/Prop.lean`): the differential test's globals. -/
def world : World := sharedWorld ()

def cx0 : Cx := mkCx world #[]

/-- A term of `T`, drawn from the property harness's generator in the empty context. -/
def leaf (T : Tm) (fuel : Nat := 1) : Gen Tm := genTm cx0 T fuel

/-! ## Small closed terms -/

def tEmpty (l : Level := 0) : Tm := .empty l
def tUnit0 : Tm := .unit 0
def tUnit1 : Tm := .unit 1
def tEnum2 : Tm := .enum (MTm.labels 2)
def tEnum1 : Tm := .enum (MTm.labels 1)
def tAxTy : Tm := .const "A" []
def tAx : Tm := .const "a" []
def tNat : Tm := .const "Nat" []
def qMany : Tm := .qlit .many
def qZero : Tm := .qlit .zero
def qOne : Tm := .qlit .one

def tag2 (i : Nat) : Tm := .tag (MTm.labels 2) i
def tag1 (i : Nat) : Tm := .tag (MTm.labels 1) i

/-- The payload of a `ret`: the index equation's proof (`tt`, at the matching index) and
the unit.  `interp (ret j) … i = (0 _ : j = i) × Unit`. -/
def retPayload : Tm := .pair .tt .tt

/-- `Nat` as a description over `Unit` (`MTm.natD` in `Tests/Elab.lean`). -/
def natD : Tm :=
  .darg qMany tEnum2
      (.lam "t" (.ecase "z" (.desc 0 tUnit1) (.var 0) [.dret .tt, .drec qMany .tt (.dret .tt)]))

def natAt (s : Tm) : Tm := .mu 0 tUnit1 natD .tt s none

def natZero : Tm := .con (.pair (tag2 0) retPayload)
def natSucc (n : Tm) : Tm := .con (.pair (tag2 1) (.pair n retPayload))

/-- A two-member mutual family, over the tag index `Enum 2`:

* `A0 : Fam 0` (no fields), `A1 : Fam 0` (no fields, a second constructor of the same
  member), and `B : Fam 1` with one field of type `Fam 0`;
* so `Fam 1`'s constructor mentions the other member: a genuine mutual family, encoded as
  one description over the tag (`Elab/Command.lean`, `mutualInductive`). -/
def mutualD : Tm :=
  .darg qMany tEnum2
    (.lam "t" (.ecase "z" (.desc 0 tEnum2) (.var 0) [
      .dret (tag2 0),
      .darg qMany tEnum2
        (.lam "u" (.ecase "z" (.desc 0 tEnum2) (.var 0) [
          .dret (tag2 0),
          .drec qMany (tag2 0) (.dret (tag2 1))]))]))

def mutualAt (i : Nat) (s : Tm := .szInf) : Tm := .mu 0 tEnum2 mutualD (tag2 i) s none

def mutualA0 : Tm := .con (.pair (tag2 0) retPayload)
def mutualA1 : Tm := .con (.pair (tag2 1) (.pair (tag2 0) retPayload))
def mutualB (a : Tm) : Tm := .con (.pair (tag2 1) (.pair (tag2 1) (.pair a retPayload)))

/-- `Stream` over `Unit`: one field of the same type. -/
def streamD : Tm := .darg qMany tEnum2 (.lam "t" (.drec qMany .tt (.dret .tt)))
def streamAt (s : Tm) : Tm := .nu 0 tUnit1 streamD .tt s none

/-! ## The shapes -/

inductive Shape where
  /-- a `μ` over a description with a (λ-bound or axiom) parameter -/
  | descParam
  /-- a `ν`, its `cocon`/`out`/`coit`/`scofix` terms -/
  | nu
  /-- sizes: `μ`/`ν` at `↑∞`, `Size`, `Size< ∞`, `scase`/`sfix` at `∞` -/
  | sizes
  /-- `let () := u; b` at unit and at a non-unit type -/
  | letUnit
  /-- `scase` at a quantity (0, 1, ω), with a constant motive -/
  | scaseQ
  /-- a family over a tag whose recursive fields land at another member -/
  | mutual
  /-- casts at a `Σ`, including a `Σ ⟶ Σ` cast and a stuck equation -/
  | castSigma
  /-- `Desc.elim` with a description that is not a code (a decision: an ill-typed
  argument the kernel must reject) -/
  | stuckDelim
  deriving Repr, BEq, Inhabited

def Shape.label : Shape → String
  | .descParam => "desc-param"
  | .nu => "nu"
  | .sizes => "sizes"
  | .letUnit => "let-unit"
  | .scaseQ => "scase-q"
  | .mutual => "mutual"
  | .castSigma => "cast-sigma"
  | .stuckDelim => "stuck-delim"

def Shape.all : List Shape :=
  [.descParam, .nu, .sizes, .letUnit, .scaseQ, .mutual, .castSigma, .stuckDelim]

def Shape.ofString? (s : String) : Option Shape :=
  Shape.all.find? (·.label == s)

/-- A generated sample: the claim `T`, a value `v` of `T` (well typed when the generator
can manage it), and extra observations for the shape. -/
structure Fuzz where
  shape : Shape
  T : Tm
  v : Tm
  extra : Array (String × Tm) := #[]
  /-- the choice sequence that produced it -/
  seq : Array Nat := #[]
  /-- the core cannot be well typed (a shape that needs a kernel decision) -/
  decision : Bool := false
  /-- further terms that claim `Empty` (deliberate near misses: a kernel decision) -/
  decisions : Array (String × Tm) := #[]

/-! ### The generators -/

def genDescParam : Gen (Tm × Tm) := do
  let A ← pick #[pure tUnit1, pure tEnum2, pure tAxTy, pure tNat, pure (tEmpty 1)] (pure tUnit1)
  if (← choose 2) == 0 then
    -- a description with a λ-bound type parameter:
    -- `(fun (A : Type) (a : A) => μ (arg A (ret ())) ()) A₀ a₀`
    let b ← pick #[pure tUnit1, pure tEnum2, pure tNat, pure tAxTy] (pure tUnit1)
    let D0 : Tm := .darg qMany (.var 1) (.lam "x" (.dret .tt))
    let T0 : Tm := .mu 0 tUnit1 D0 .tt .szInf none
    let body : Tm := .con (.pair (.var 0) retPayload)
    let fnTy : Tm := .pi "A" .default qMany (.sort 1)
      (.pi "a" .default qMany (.var 0) T0 none) none
    let fn : Tm := .ann (.lam "A" (.lam "a" body)) fnTy
    let D : Tm := .darg qMany b (.lam "x" (.dret .tt))
    let T : Tm := .mu 0 tUnit1 D .tt .szInf none
    let a ← leaf b 0
    pure (T, .app (.app fn b) a)
  else
    let D : Tm := .darg qMany A (.lam "a" (.dret .tt))
    let T : Tm := .mu 0 tUnit1 D .tt .szInf none
    let a ← leaf A 1
    pure (T, .con (.pair a retPayload))

def genNu : Gen (Tm × Tm) := do
  let T := streamAt .szInf
  let v ← leaf T 2
  pure (T, v)

def genSizes : Gen (Tm × Tm) := do
  match ← choose 5 with
  | 0 => pure (natAt (.szSuc .szInf), natZero)
  | 1 => pure (natAt .szInf, natSucc natZero)
  | 2 => do
      let T := streamAt (.szSuc .szInf)
      pure (T, ← leaf T 1)
  | 3 => pure (.size, .szInf)
  | _ => pure (.sizeLt .szInf, .szSuc .szInf)

def genLetUnit : Gen (Tm × Tm) := do
  let U ← pick #[pure tUnit0, pure tUnit1] (pure tUnit0)
  let b ← leaf U 1
  let u ← if (← choose 3) == 0 then leaf tNat 0 else leaf U 0
  pure (U, .letUnit u b)

def genScaseQ : Gen (Tm × Tm) := do
  let (dt, idx) ← pick #[pure (tNat, Term.tt), pure (mutualAt 0, tag2 0),
    pure (mutualAt 1, tag2 1)] (pure (tNat, Term.tt))
  match cx0.whq dt with
  | .mu ld I D _ _ _ =>
    let T ← pick #[pure tUnit0, pure tUnit1, pure tNat, pure tEnum2] (pure tUnit1)
    let some vT := cx0.lvlOf T | pure (T, .tt)
    let P : Tm := .lam "i" (.lam "x" (liftT 2 T))
    let vP := cx0.k.eval P
    let q ← pick #[pure qZero, pure qOne, pure qMany] (pure qMany)
    let qq : ZeroOneMany ←
      if q == qZero then pure .zero else if q == qOne then pure .one else pure .many
    let sz ← pick #[pure (.szInf : Tm), pure (.szSuc .szInf)] (pure .szInf)
    let mTy := quote world.g cx0.k.lvl
      (scaseMethodTy world.g ld (cx0.k.eval I) (cx0.k.eval D) vP (cx0.k.eval sz) (cx0.k.eval (.qlit qq)))
    let m ← leaf mTy 1
    let x ← leaf dt 1
    pure (T, .scase ld (.qlit qq) I D vT P m sz idx x)
  | _ => pure (tUnit1, .tt)

def genMutual : Gen (Tm × Tm) := do
  match ← choose 3 with
  | 0 => pure (mutualAt 0, mutualA0)
  | 1 => pure (mutualAt 0, mutualA1)
  | _ => pure (mutualAt 1, mutualB mutualA0)

/-- `Σ` types with the quantity and the sort annotation varied; the value is a pair. -/
def genCastSigma : Gen (Tm × Tm) := do
  let A ← pick #[pure tUnit0, pure tUnit1, pure tEnum2, pure tNat, pure tAxTy] (pure tUnit1)
  let B ← pick #[pure tUnit0, pure tUnit1, pure tEnum2] (pure tUnit0)
  let q ← pick #[pure qMany, pure qZero, pure qOne] (pure qMany)
  let sx ← pick #[pure (none : Option Level),
    (do let some la := cx0.lvlOf A | pure none
        let some lb := cx0.lvlOf (liftT 1 B) | pure none
        pure (some (Level.max la lb)))] (pure none)
  let S : Tm := .sigma "x" q A (liftT 1 B) sx
  pure (S, ← leaf S 1)

def genStuckDelim : Gen (Tm × Tm) := do
  let T ← pick #[pure tUnit0, pure tUnit1, pure tNat, pure tEnum2] (pure tUnit1)
  let D ← pick #[
    pure (.dret .tt),
    pure (.dret .tt),
    -- an axiom `a : A` used as a `Desc`: rejected by the annotation (a decision)
    pure (.ann tAx (.desc 0 tUnit1)),
    -- a cast from `A` to `Desc`: the equation is stuck, the cast must be rejected
    pure (.cast tAxTy (.desc 0 tUnit1) (.reflTy tAxTy) tAx),
    -- a case on a tag that is itself an ill-typed cast
    pure (.ecase "z" (.desc 0 tUnit1)
      (mkInf (.cast tAxTy tEnum2 (.reflTy tAxTy) tAx) tEnum2) [.dret .tt, .dret .tt])]
    (pure (.dret .tt))
  let P : Tm := .lam "D" (liftT 1 T)
  let some lT := cx0.lvlOf T | pure (T, .tt)
  let vP := cx0.k.eval P
  let (ta, tb, tc, th) := delimMethodTys world.g 0 (cx0.k.eval tUnit1) vP .many
  let q (x : Val Q) : Tm := quote world.g cx0.k.lvl x
  let a ← leaf (q ta) 1
  let b ← leaf (q tb) 1
  let c ← leaf (q tc) 1
  let h ← leaf (q th) 1
  pure (T, .delim lT P a b c h (.ann D (.desc 0 tUnit1)))

/-- `T`'s sort, from the kernel (the empty type at that sort is the oracle's target). -/
def sortOf (T : Tm) : Level := (cx0.lvlOf T).getD 0

/-- `cast T (Empty l) (reflTy T) v : Empty l` — accepted exactly when `T ≡ Empty l`. -/
def falseCast (T v : Tm) : Tm :=
  let l := sortOf T
  .ann (.cast T (.empty l) (.reflTy T) v) (.empty l)

def genShape (s : Shape) : Gen (Tm × Tm) :=
  match s with
  | .descParam => genDescParam
  | .nu => genNu
  | .sizes => genSizes
  | .letUnit => genLetUnit
  | .scaseQ => genScaseQ
  | .mutual => genMutual
  | .castSigma => genCastSigma
  | .stuckDelim => genStuckDelim

/-- The generator, retried until the core `v : T` is well typed (a sample whose core the
kernel rejects is asking about that error, not about the shape's rule).  `stuck-delim`
has no well-typed closed instance (`Desc.elim` needs a *neutral* description, and a closed
term cannot be neutral without an axiom of that type): it is generated as it is, and
marked as a decision. -/
partial def genSample (s : Shape) (fuel : Nat := 20) : Gen (Tm × Tm × Bool) := do
  -- (the generator's step budget is per attempt: `tick` counts across retries otherwise,
  -- and a late attempt gets nothing but `tt`)
  let steps0 := (← get).steps
  let p ← genShape s
  let inFragment := (toM (falseCast p.1 p.2)).isSome
  let retry : Gen (Tm × Tm × Bool) := do
    modify fun st => { st with steps := steps0 }
    genSample s (fuel - 1)
  if s == .stuckDelim then
    if fuel == 0 || inFragment then return (p.1, p.2, !accepts world.g (.ann p.2 p.1))
    retry
  else
    if fuel == 0 || (inFragment && accepts world.g (.ann p.2 p.1)) then
      return (p.1, p.2, false)
    retry

/-- Extra observations of a sample (the conversion rules the shape is about). -/
def Fuzz.observations (f : Fuzz) : Array (String × Tm) :=
  f.extra ++ match f.shape with
  | .castSigma =>
    let S := f.T
    let annotated := match S with
      | .sigma x q A B _ => .sigma x q A B (some ((cx0.lvlOf S).getD 0))
      | _ => S
    let dropped := stripSorts S
    let flip := (flipQ S).getD S
    #[("Σ → Σ (with the sort)", .cast S annotated (.reflTy S) f.v),
      ("Σ → Σ (sorts dropped)", .cast S dropped (.reflTy S) f.v),
      ("Σ → Σ (quantity changed, K1)", .cast S flip (.reflTy S) f.v)].filter fun (_, t) => t != .cast S S (.reflTy S) f.v
  | .scaseQ => #[("the scase at ω", f.v)]
  | _ => #[]

/-! ## One sample, checked by the Lean kernel -/

def Fuzz.candidate (f : Fuzz) : Tm := falseCast f.T f.v

/-- What one sample asks the kernels. -/
structure Query where
  shape : Shape
  role : String
  /-- the sample's replay sequence -/
  seq : Array Nat
  /-- the term, in `Kernel.wiz`'s calculus -/
  m : MTm
  /-- ask for a normal form (otherwise the verdict) -/
  nf : Bool
  /-- the Lean kernel's answer: `"ok"`/`"error"` for a verdict, the printed term for a
  normal form -/
  lean : String
  /-- a human-readable rendering of the term and its type -/
  render : String
  /-- the term claims `Empty`: acceptance by either kernel is a soundness bug -/
  falseClaim : Bool

def verdictString (b : Bool) : String := if b then "ok" else "error"

/-- The Lean kernel's normal form, printed as `Kernel.wiz` prints. -/
def leanNormal (m : MTm) : String := wizNormal world.g m

/-- The queries for one sample: the candidate's verdict, the equation's normal form, and
the shape's extra observations (verdicts only). -/
def Fuzz.queries (f : Fuzz) : Array Query := Id.run do
  let l := sortOf f.T
  let cand := f.candidate
  let mut out : Array Query := #[]
  match toM cand with
  | some m =>
    out := out.push (Query.mk f.shape "the candidate" f.seq m false
      (verdictString (accepts world.g cand)) s!"{cand.pretty []} : {(tEmpty l).pretty []}" true)
  | none => pure ()
  let eq := .eqTy f.T (.empty l)
  match toM eq with
  | some m =>
    let lean := if accepts world.g eq then leanNormal m else "error"
    out := out.push (Query.mk f.shape "the equation" f.seq m true lean s!"{eq.pretty []}" false)
  | none => pure ()
  for (role, t) in f.observations do
    match toM t with
    | some m =>
      out := out.push (Query.mk f.shape role f.seq m false
        (verdictString (accepts world.g t)) s!"{t.pretty []}" false)
    | none => pure ()
  for (role, t) in f.decisions do
    match toM t with
    | some m =>
      out := out.push (Query.mk f.shape role f.seq m false
        (verdictString (accepts world.g t)) s!"{t.pretty []}" true)
    | none => pure ()
  return out

/-! ## Coverage: the constructs a sample contains -/

partial def feats (t : Tm) : List String := Id.run do
  let (_, a) := (go t).run #[]
  return a.toList.eraseDups
where
  go (t : Tm) : StateM (Array String) Unit := do
    let add (s : String) : StateM (Array String) Unit := modify (·.push s)
    match t with
    | .letUnit .. => add "letUnit"
    | .scase _ (.qlit .zero) .. => add "scase at quantity 0"
    | .scase _ (.qlit .one) .. => add "scase at quantity 1"
    | .scase _ (.qlit .many) .. => add "scase at quantity ω"
    | .scase _ _ .. => add "scase at a quantity variable"
    | .cocon _ => add "cocon"
    | .coit .. => add "coit"
    | .scofix .. => add "scofix"
    | .out _ => add "out"
    | .sfix _ _ _ _ _ _ s _ _ => add (if s == .szInf then "sfix at ∞" else "sfix at a size")
    | .mu _ _ _ _ s _ => add (if s == .szInf then "μ at ∞" else "μ at a size")
    | .nu _ _ _ _ s _ => add (if s == .szInf then "ν at ∞" else "ν at a size")
    | .size => add "Size"
    | .sizeLt _ => add "Size<"
    | .darg _ (.var _) _ => add "description with a variable parameter"
    | .drec _ (.tag _ _) _ => add "a recursive field at a tag (mutual or indexed)"
    | .dhrec .. => add "higher recursive field"
    | .delim .. => add "Desc.elim"
    | .cast _ _ _ _ => add "cast"
    | .absurd .. => add "absurd"
    | _ => pure ()
    let _ ← mapKidsM (m := StateM (Array String)) pure
      (fun _ c => do go c; pure c) t
    pure ()

/-! ## Running the campaign -/

structure Stats where
  generated : Std.HashMap String Nat := {}
  skipped : Std.HashMap String Nat := {}
  /-- a kernel accepted a closed `Empty` -/
  hits : Array (String × Query) := #[]
  /-- the two kernels disagree on a verdict -/
  verdictDiffs : Array (String × String × Query) := #[]
  /-- a known difference (K1: a quantity at a proposition Σ) -/
  knownDiffs : Array (String × String × Query) := #[]
  /-- both accept, and the normal forms print differently -/
  nfDiffs : Array (String × String × Query × String) := #[]
  /-- samples whose core `v : T` the Lean kernel accepts (the shape actually reached) -/
  coreOK : Std.HashMap String Nat := {}
  /-- the first reason a core was rejected, per shape -/
  coreWhy : Std.HashMap String String := {}
  /-- a Lean acceptance of the candidate, even outside Kernel.wiz's fragment -/
  leanHits : Array (String × Fuzz) := #[]
  /-- the constructs the samples contain (the shape's coverage) -/
  features : Std.HashMap String Nat := {}
  checked : Nat := 0

abbrev SM := StateM Stats

def bump (k : String) : SM Unit := modify fun s => { s with generated := s.generated.insert k (s.generated.getD k 0 + 1) }

def bumpSkip (k : String) : SM Unit := modify fun s => { s with skipped := s.skipped.insert k (s.skipped.getD k 0 + 1) }

def bumpCore (k : String) : SM Unit := modify fun s => { s with coreOK := s.coreOK.insert k (s.coreOK.getD k 0 + 1) }

def bumpFeature (k : String) : SM Unit := modify fun s => { s with features := s.features.insert k (s.features.getD k 0 + 1) }

/-- Generate `n` samples of one shape, seeded, and collect their queries. -/
def campaign (sh : Shape) (n : Nat) (seed0 : Nat) : SM (Array Query) := do
  let mut seed := seed0
  let mut qs : Array Query := #[]
  for _ in [0:n] do
    seed := lcg seed
    let (triple, gs) := runGen #[] (some seed) (genSample sh)
    let seq := gs.log.map (·.1)
    let f : Fuzz := { shape := sh, T := triple.1, v := triple.2.1, seq, decision := triple.2.2 }
    bump sh.label
    if accepts world.g (.ann f.v f.T) then bumpCore sh.label
    else
      let j : Jd := { ctx := #[], t := f.v, T := f.T }
      modify fun s => if s.coreWhy.contains sh.label then s
        else { s with coreWhy := s.coreWhy.insert sh.label (why world.g j) }
    if accepts world.g f.candidate then
      modify fun s => { s with leanHits := s.leanHits.push (sh.label, f) }
    for k in feats f.v ++ feats f.T ++ feats (f.candidate) do bumpFeature k
    let fq := f.queries
    -- (a sample whose terms are outside the fragment is still reported: it is the
    -- generator's business, not the kernels')
    if fq.isEmpty then bumpSkip sh.label
    qs := qs ++ fq
  return qs

/-- The `Kernel.wiz` program: the kernel, a verdict and a normal form for every query,
then one line per query.  A query that the Lean kernel accepts gets its proof markers
first (the kernel requires them); a term the pre-P2 kernel rejects is `error`. -/
def wizProgram (kernel : String) (qs : Array Query) : String :=
  let header :=
    "def rawVerdict (t : Tm) : String := match infer empty t with\n  | .ok ty _ => show .nil 0 (quote 0 ty)\n  | .err _ => \"error\"\n" ++
    "def markedVerdict (t : Tm) : String := rawVerdict (MR.tm (markInfer (TCtx.relevant empty) t))\n" ++
    "def verdict (t : Tm) : String := match infer (TCtx.noMarkers empty) t with\n  | .err _ => \"error\"\n  | .ok _ _ => markedVerdict t\n" ++
    "def markedNormalize (t : Tm) : String := show .nil 0 (quote 0 (eval .nil (MR.tm (markInfer (TCtx.relevant empty) t))))\n" ++
    "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
  let defs := String.join ((List.range qs.size).zip qs.toList |>.map fun (i, q) =>
    s!"def q{i} (u : Unit) : String := {if q.nf then "markedNormalize" else "verdict"} {q.m.toWiz}\n")
  let calls := (List.range qs.size).map fun i => s!"(q{i} ())"
  kernel ++ "\n" ++ header ++ defs ++ s!"def main : IO Unit := printAll {Elab.wizList calls}\n"

/-- The Wiz output with the one expected spelling difference collapsed (`↑∞` against
`∞`, PH-K1). -/
def norm (x : String) : String := (x.replace "↑(∞)" "∞").replace ", ∞)" ")"

/-- One `Kernel.wiz` program for a batch of queries.  `wizRun`'s build timeout is 900 s;
one campaign can be too large for a single program (the frontend elaborates every query
as a definition), so `runKernel` batches. -/
def runKernelChunk (qs : Array Query) : IO (Array (Query × String)) := do
  if qs.isEmpty then return #[]
  let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
  let prog := wizProgram kernel qs
  match ← wizRun prog with
  | none => return #[]
  | some out =>
    let got := (out.splitOn "\n").take qs.size
    if got.length != qs.size then
      throw (IO.userError s!"false-fuzz: {got.length} answers for {qs.size} queries")
    return qs.zip got.toArray

/-- `KERNEL_CHUNK` queries per program (about two minutes of frontend at 1200). -/
def chunkSize : Nat := 1200

def runKernel (qs : Array Query) : IO (Array (Query × String)) := do
  let mut out : Array (Query × String) := #[]
  let mut i := 0
  while i < qs.size do
    let j := min (i + chunkSize) qs.size
    let chunk := qs.extract i j
    if qs.size > chunkSize then
      IO.println s!"  (Kernel.wiz: queries {i}..{j} of {qs.size})"
    let ans ← runKernelChunk chunk
    if ans.isEmpty && !chunk.isEmpty then return #[]
    out := out ++ ans
    i := j
  return out

/-- Compare the answers; any acceptance of the candidate is a hit. -/
def checkAnswers (_qs : Array Query) (ans : Array (Query × String)) : SM Unit := do
  for (q, got) in ans do
    if q.nf then
      if q.lean != "error" && norm q.lean != norm got then
        modify fun s => { s with nfDiffs := s.nfDiffs.push (q.shape.label, q.role, q, got) }
    else
      let leanAcc := q.lean == "ok"
      let wizAcc := got != "error"
      if q.falseClaim && (leanAcc || wizAcc) then
        modify fun s => { s with hits := s.hits.push (q.shape.label ++ " / " ++ q.role, q) }
      if leanAcc != wizAcc then
        if q.role == "Σ → Σ (quantity changed, K1)" then
          modify fun s => { s with knownDiffs := s.knownDiffs.push (q.shape.label, q.role, q) }
        else
          modify fun s => { s with verdictDiffs := s.verdictDiffs.push (q.shape.label, q.role, q) }
  modify fun s => { s with checked := s.checked + ans.size }

/-- Print one sample and both kernels' answers (the replay command's body). -/
def replayOne (sh : Shape) (seq : Array Nat) : IO UInt32 := do
  let (triple, _) := runGen seq none (genSample sh)
  let f : Fuzz := { shape := sh, T := triple.1, v := triple.2.1, seq, decision := triple.2.2 }
  IO.println s!"shape {sh.label}, choices {seq.toList}"
  IO.println s!"  T := {f.T.pretty []}"
  IO.println s!"  v := {f.v.pretty []}"
  IO.println s!"  candidate := {f.candidate.pretty []} : Empty {sortOf f.T}"
  IO.println s!"  core v : T is {if accepts world.g (.ann f.v f.T) then "well typed" else "ILL TYPED"}{if f.decision then " (a decision)" else ""}"
  let qs := f.queries
  match ← runKernel qs with
  | #[] =>
    for q in qs do
      IO.println s!"  [{q.role}] {if q.nf then "normal form" else "verdict"} asked: {q.m.toWiz}"
      IO.println s!"    Lean: {q.lean}"
    IO.println "  (Kernel.wiz not run: no toolchain)"
  | ans =>
    for (q, got) in ans do
      IO.println s!"  [{q.role}] {if q.nf then "normal form" else "verdict"} asked: {q.m.toWiz}"
      IO.println s!"    Lean: {q.lean}\n    Wiz:  {got}"
  pure 0

/-- `tests --false-fuzz-check SHAPE [N] [SEED]`: the Lean side only — generate, report
whether each core is well typed and why not (no `Kernel.wiz` compile). -/
def checkMain (args : List String) : IO UInt32 := do
  let sh := (args[0]? >>= Shape.ofString?).getD .descParam
  let n := (args[1]? >>= String.toNat?).getD 5
  let seed0 := (args[2]? >>= String.toNat?).getD 1
  let mut seed := seed0
  for _ in [0:n] do
    seed := lcg seed
    let (triple, gs) := runGen #[] (some seed) (genSample sh)
    let f : Fuzz := { shape := sh, T := triple.1, v := triple.2.1, seq := gs.log.map (·.1), decision := triple.2.2 }
    let ok := accepts world.g (.ann f.v f.T)
    IO.println s!"{sh.label}: core {if ok then "ok" else "ILL TYPED"} choices {f.seq.toList}"
    IO.println s!"  T := {f.T.pretty []}\n  v := {f.v.pretty []}"
    unless ok do
      let j : Jd := { ctx := #[], t := f.v, T := f.T }
      IO.println s!"  the kernel: {why world.g j}"
    IO.println s!"  candidate: Lean {verdictString (accepts world.g f.candidate)}"
    IO.println s!"  queries: {f.queries.size} ({", ".intercalate (f.queries.toList.map (·.role))})"
    IO.println s!"  toM candidate: {(toM f.candidate).isSome}, toM equation: {(toM (.eqTy f.T (.empty (sortOf f.T)))).isSome}"
  pure 0

def replayMain (args : List String) : IO UInt32 := do
  match args with
  | sh :: choices =>
    let some sh := Shape.ofString? sh | do IO.eprintln s!"unknown shape {sh}"; pure 2
    replayOne sh (choices.filterMap String.toNat?).toArray
  | _ => do IO.eprintln "usage: --false-fuzz-replay SHAPE CHOICE…"; pure 2

/-- The campaign: `N` samples per shape, one `Kernel.wiz` program. -/
def main (args : List String) : IO UInt32 := do
  let n := (args[0]? >>= String.toNat?).getD 200
  let seed := (args[1]? >>= String.toNat?).getD 20261114
  IO.println s!"false-fuzz: {n} samples per shape, seed {seed}; shapes: {", ".intercalate (Shape.all.map Shape.label)}"
  let (qss, st) := (Shape.all.mapM fun sh => campaign sh n seed).run {}
  let qs : Array Query := qss.foldl (fun acc a => acc ++ a) #[]
  IO.println s!"  {qs.size} queries"
  let ans ← runKernel qs
  if ans.isEmpty then
    IO.println "  (Kernel.wiz was not run: no C toolchain; the campaign is inconclusive)"
    return 2
  let (_, st) := (checkAnswers qs ans).run st
  IO.println s!"  {st.checked} answers"
  IO.println "\n  coverage (samples containing the construct):"
  for (k, v) in st.features.toList do IO.println s!"    {k}: {v}"
  let byShape := qs.foldl (fun (m : Std.HashMap String Nat) q =>
    m.insert q.shape.label (m.getD q.shape.label 0 + 1)) {}
  for (k, v) in byShape.toList do IO.println s!"    {k}: {v} queries"
  for (k, v) in st.generated.toList do
    IO.println s!"  {k}: {v} samples ({st.coreOK.getD k 0} with a well-typed core), {st.skipped.getD k 0} outside Kernel.wiz's fragment"
    if let some e := st.coreWhy.get? k then IO.println s!"    first core rejected: {e.take 200}"
    if k == "stuck-delim" then IO.println "    (a decision: the generated description is not a code)"
  unless st.leanHits.isEmpty do
    IO.println "\n✗ the Lean kernel accepted a closed term of Empty"
    for (role, f) in st.leanHits do
      IO.println s!"  {role}: {f.candidate.pretty []}\n    replay: tests --false-fuzz-replay {f.shape.label} {" ".intercalate (f.seq.toList.map toString)}"
  unless st.hits.isEmpty do
    IO.println "\n✗ a kernel accepted a closed term of Empty"
    for (role, q) in st.hits do
      IO.println s!"  {role}: {q.render}\n    replay: tests --false-fuzz-replay {q.shape.label} {" ".intercalate (q.seq.toList.map toString)}"
  unless st.verdictDiffs.isEmpty do
    IO.println s!"\n✗ {st.verdictDiffs.size} verdict differences"
    for (k, role, q) in st.verdictDiffs.take 20 do
      IO.println s!"  {k} / {role}: Lean {q.lean}, Wiz differs\n    {q.render}\n    replay: tests --false-fuzz-replay {q.shape.label} {" ".intercalate (q.seq.toList.map toString)}"
  unless st.knownDiffs.isEmpty do
    IO.println s!"\n(known: K1 is not gated) {st.knownDiffs.size} differences on quantity-only Σ pairs"
    for (k, role, q) in st.knownDiffs.take 3 do
      IO.println s!"  {k} / {role}: Lean {q.lean}, Wiz differs\n    {q.render}\n    replay: tests --false-fuzz-replay {q.shape.label} {" ".intercalate (q.seq.toList.map toString)}"
  unless st.nfDiffs.isEmpty do
    IO.println s!"\n(not gated) {st.nfDiffs.size} normal forms differ"
    for (k, role, q, got) in st.nfDiffs.take 10 do
      IO.println s!"  {k} / {role}\n    Lean: {q.lean}\n    Wiz:  {got}"
  if st.hits.isEmpty && st.leanHits.isEmpty && st.verdictDiffs.isEmpty then IO.println "\n✓ no hit, no verdict difference"
  IO.println s!"\nfalse-fuzz: {st.hits.size} hits, {st.verdictDiffs.size} verdict differences, {st.nfDiffs.size} normal-form differences on {st.checked} answers"
  return (if st.hits.isEmpty && st.leanHits.isEmpty && st.verdictDiffs.isEmpty then 0 else 1)

/-! ## The test group -/

/-- The bounded campaign as a test: every shape generates, every shape but `stuck-delim`
has well-typed cores, and neither kernel accepts a closed `Empty` nor do the kernels
disagree.  (Normal-form differences are printed by `--false-fuzz`, not gated: the
property harness treats them the same way.) -/
def caseRun (n : Nat) (seed : Nat) : IO Unit := do
  let (qss, st) := (Shape.all.mapM fun sh => campaign sh n seed).run {}
  let qs : Array Query := qss.foldl (fun acc a => acc ++ a) #[]
  let ans ← runKernel qs
  if ans.isEmpty then throw (IO.userError "false-fuzz: Kernel.wiz was not run (no toolchain)")
  let (_, st) := (checkAnswers qs ans).run st
  IO.println s!"  {qs.size} queries, {st.checked} answers"
  for sh in Shape.all do
    let k := sh.label
    unless st.generated.getD k 0 > 0 do
      throw (IO.userError s!"false-fuzz: no sample for shape {k}")
    if sh != .stuckDelim && st.coreOK.getD k 0 == 0 then
      throw (IO.userError s!"false-fuzz: no well-typed core for shape {k}")
  unless st.hits.isEmpty do
    throw (IO.userError s!"false-fuzz: a kernel accepted a closed Empty ({st.hits.size} queries)")
  unless st.leanHits.isEmpty do
    throw (IO.userError s!"false-fuzz: the Lean kernel accepted a closed Empty ({st.leanHits.size} samples)")
  unless st.verdictDiffs.isEmpty do
    throw (IO.userError s!"false-fuzz: {st.verdictDiffs.size} verdict differences between the kernels")
  IO.println s!"  ({st.hits.size} hits, {st.verdictDiffs.size} verdict differences, {st.knownDiffs.size} known K1, {st.nfDiffs.size} normal-form differences)"

def group : Group where
  name := "false-fuzz"
  exercise := "a False fuzzer for the two kernels (property harness)"
  cases := [
    { name := "closed Empty candidates for eight shapes; no hit, no verdict difference",
      run := fun _ => caseRun 20 20261114 }]

end Tests.FalseFuzz
