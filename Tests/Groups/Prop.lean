import Wiz
import Tests.Harness
import Tests.Elab

/-!
# A property harness for the kernels: substitution laws

The laws tested (`wiz-notes/metatheory-plan.md` §5.1 M1b; `wiz-notes/prop-harness.md`):

* **P1** typing is stable under substitution, for term, quantity and level variables;
* **P2** conversion is an equivalence on the sample and stable under substitution;
* **P3** evaluation commutes with substitution, up to conversion;
* **P4** a type (or term) equation that computes to `False` stays `False` under every
  instance, and the two sides are then never convertible (F6);
* **P5** the Lean kernel and `selfhost/Kernel.wiz` give the same verdict;
* **P6** `quote ∘ eval` is the identity up to conversion and normal forms are well typed.

The kernel's P2 makes the marker `prf` part of every well-typed core term: a raw term the
generator builds is the coarse syntax, and what reaches the kernel is the *marked* term
(the elaborator's pass, `Wiz/Elab/Mark.lean`). Every check here is of the marked term, and
the marking pass runs only on a term the kernel already accepted without the requirement
(the pre-P2 mode, `lazyProofs := false`), as `Tests/Elab` does: the pass checks nothing and
may loop on an ill-typed term.

Terms are generated type-directed, as a function of a **choice sequence**: the same
generator enumerates small terms (every sequence with at most `d` non-default choices)
and samples large ones (random choices), and a failure is shrunk by shrinking its
sequence. Every generated judgment is validated by the kernel before it is used.

`lake test -- '=prop'` is the default run; `.lake/build/bin/tests --prop-long [N] [SEED]`
the long one.
-/

set_option compiler.extract_closed false

open Wiz

namespace Tests.Prop

open Tests.Elab (MTm)

abbrev Q := ZeroOneMany
abbrev Tm := Term Q
abbrev Gl := Globals Q

/-! ## The harness's own traversal

Not `Term.mapChildrenM`: a hole in the kernel's traversal (S1) must not be a hole in the
test. Every constructor is listed, with no wildcard arm, so a new constructor does not
compile until it is added here (and to `ctorName`). -/

@[specialize] def mapKidsM {m : Type → Type} [Monad m] (fl : Level → m Level)
    (f : Nat → Tm → m Tm) : Tm → m Tm
  | .var i => pure (.var i)
  | .const n ls => return .const n (← ls.mapM fl)
  | .sort l => return .sort (← fl l)
  | .pi x bi q a b σ => return .pi x bi (← f 0 q) (← f 0 a) (← f 1 b) (← σ.mapM fl)
  | .lam x b => return .lam x (← f 1 b)
  | .app a b => return .app (← f 0 a) (← f 0 b)
  | .letE x q t v b => return .letE x (← f 0 q) (← f 0 t) (← f 0 v) (← f 1 b)
  | .letUnit u b => return .letUnit (← f 0 u) (← f 0 b)
  | .ann a b => return .ann (← f 0 a) (← f 0 b)
  | .mvar i => pure (.mvar i)
  | .sigma x q a b σ => return .sigma x (← f 0 q) (← f 0 a) (← f 1 b) (← σ.mapM fl)
  | .pair a b => return .pair (← f 0 a) (← f 0 b)
  | .fst t => return .fst (← f 0 t)
  | .snd t => return .snd (← f 0 t)
  | .split q s z m x y b => return .split (← f 0 q) (← f 0 s) z (← f 1 m) x y (← f 2 b)
  | .unit l => return .unit (← fl l)
  | .tt => pure .tt
  | .empty l => return .empty (← fl l)
  | .absurd a b => return .absurd (← f 0 a) (← f 0 b)
  | .eq A a b => return .eq (← f 0 A) (← f 0 a) (← f 0 b)
  | .eqTy A B => return .eqTy (← f 0 A) (← f 0 B)
  | .refl A a => return .refl (← f 0 A) (← f 0 a)
  | .reflTy X => return .reflTy (← f 0 X)
  | .cast A B e t => return .cast (← f 0 A) (← f 0 B) (← f 0 e) (← f 0 t)
  | .prf l t => return .prf (← fl l) (← f 0 t)
  | .transp A a P p b e =>
    return .transp (← f 0 A) (← f 0 a) (← f 0 P) (← f 0 p) (← f 0 b) (← f 0 e)
  | .qty => pure .qty
  | .qlit r => pure (.qlit r)
  | .enum ls => pure (.enum ls)
  | .tag ls i => pure (.tag ls i)
  | .ecase z mo s bs => return .ecase z (← f 1 mo) (← f 0 s) (← bs.mapM (f 0))
  | .desc l I => return .desc (← fl l) (← f 0 I)
  | .dret i => return .dret (← f 0 i)
  | .darg q S D => return .darg (← f 0 q) (← f 0 S) (← f 0 D)
  | .drec q j D => return .drec (← f 0 q) (← f 0 j) (← f 0 D)
  | .dhrec q H j D => return .dhrec (← f 0 q) (← f 0 H) (← f 0 j) (← f 0 D)
  | .delim v P a b c h D =>
    return .delim (← fl v) (← f 0 P) (← f 0 a) (← f 0 b) (← f 0 c) (← f 0 h) (← f 0 D)
  | .mu l I D i s h => return .mu (← fl l) (← f 0 I) (← f 0 D) (← f 0 i) (← f 0 s) (← h.mapM hint)
  | .con x => return .con (← f 0 x)
  | .ind l I D v P mt i x =>
    return .ind (← fl l) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 mt) (← f 0 i) (← f 0 x)
  | .nu l I D i s h => return .nu (← fl l) (← f 0 I) (← f 0 D) (← f 0 i) (← f 0 s) (← h.mapM hint)
  | .out x => return .out (← f 0 x)
  | .size => pure .size
  | .szInf => pure .szInf
  | .szSuc s => return .szSuc (← f 0 s)
  | .sizeLt s => return .sizeLt (← f 0 s)
  | .sfix l I D v P g s i x =>
    return .sfix (← fl l) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 g) (← f 0 s) (← f 0 i) (← f 0 x)
  | .scase l q I D v P m s i x =>
    return .scase (← fl l) (← f 0 q) (← f 0 I) (← f 0 D) (← fl v) (← f 0 P) (← f 0 m) (← f 0 s) (← f 0 i) (← f 0 x)
  | .cocon x => return .cocon (← f 0 x)
  | .scofix l I D A g s i a =>
    return .scofix (← fl l) (← f 0 I) (← f 0 D) (← f 0 A) (← f 0 g) (← f 0 s) (← f 0 i) (← f 0 a)
  | .coit l I D S st i s =>
    return .coit (← fl l) (← f 0 I) (← f 0 D) (← f 0 S) (← f 0 st) (← f 0 i) (← f 0 s)
  | .natLit n => pure (.natLit n)
  | .natOp op args => return .natOp op (← args.mapM (f 0))
  | .ulift k l A => return .ulift (← fl k) (← fl l) (← f 0 A)
  | .up a => return .up (← f 0 a)
  | .down t => return .down (← f 0 t)
where
  hint : Name × List Level × List Tm → m (Name × List Level × List Tm)
    | (n, us, as) => return (n, ← us.mapM fl, ← as.mapM (f 0))

def mapKids (fl : Level → Level) (f : Nat → Tm → Tm) (t : Tm) : Tm :=
  Id.run <| mapKidsM (m := Id) (fun l => pure (fl l)) (fun d c => pure (f d c)) t

def ctorName : Tm → String
  | .var _ => "var" | .const .. => "const" | .sort _ => "sort" | .pi .. => "pi" | .lam .. => "lam"
  | .app .. => "app" | .letE .. => "letE" | .letUnit .. => "letUnit" | .ann .. => "ann" | .mvar _ => "mvar" | .sigma .. => "sigma"
  | .pair .. => "pair" | .fst _ => "fst" | .snd _ => "snd" | .split .. => "split" | .unit _ => "unit"
  | .tt => "tt" | .empty _ => "empty" | .absurd .. => "absurd" | .eq .. => "eq" | .eqTy .. => "eqTy"
  | .refl .. => "refl" | .reflTy _ => "reflTy" | .cast .. => "cast" | .transp .. => "transp"
  | .qty => "qty" | .qlit _ => "qlit" | .enum _ => "enum" | .tag .. => "tag" | .ecase .. => "ecase"
  | .desc .. => "desc" | .dret _ => "dret" | .darg .. => "darg" | .drec .. => "drec" | .dhrec .. => "dhrec"
  | .delim .. => "delim" | .mu .. => "mu" | .con _ => "con" | .ind .. => "ind" | .nu .. => "nu"
  | .out _ => "out" | .size => "size" | .szInf => "szInf" | .szSuc _ => "szSuc" | .sizeLt _ => "sizeLt"
  | .sfix .. => "sfix" | .scase .. => "scase" | .cocon _ => "cocon" | .scofix .. => "scofix"
  | .coit .. => "coit" | .natLit _ => "natLit" | .natOp .. => "natOp" | .ulift .. => "ulift"
  | .up _ => "up" | .down _ => "down" | .prf .. => "prf"

/-- A structural hash of a term: its constructor, the parts that are not subterms (names,
the tag index, the quantity literal, …) and its children's hashes. It only picks a memo
bucket — an equal key decides a hit — so a collision costs a comparison. (A fold, with no
list built per node: the memo hashes a term on every lookup.) -/
partial def hashTm : Tm → UInt64
  | .var i => h 1 (hash i)
  | .const n ls => h 2 (h (hash n) (hash ls))
  | .sort l => h 3 (hash l)
  | .pi x bi q a b σ => h 4 (h (hash x) (h (biHash bi) (h (hashTm q) (h (hashTm a) (h (hashTm b) (sortsHash σ))))))
  | .lam x b => h 5 (h (hash x) (hashTm b))
  | .app a b => h 6 (h (hashTm a) (hashTm b))
  | .letE x q t v b => h 7 (h (hash x) (h (hashTm q) (h (hashTm t) (h (hashTm v) (hashTm b)))))
  | .letUnit u b => h 8 (h (hashTm u) (hashTm b))
  | .ann a b => h 9 (h (hashTm a) (hashTm b))
  | .mvar i => h 10 (hash i)
  | .sigma x q a b σ => h 11 (h (hash x) (h (hashTm q) (h (hashTm a) (h (hashTm b) (sortsHash σ)))))
  | .pair a b => h 12 (h (hashTm a) (hashTm b))
  | .fst t => h 13 (hashTm t)
  | .snd t => h 14 (hashTm t)
  | .split q s z m x y b =>
    h 15 (h (hashTm q) (h (hashTm s) (h (hash z) (h (hashTm m) (h (hash x) (h (hash y) (hashTm b)))))))
  | .unit l => h 16 (hash l)
  | .tt => h 17 0
  | .empty l => h 18 (hash l)
  | .absurd a b => h 19 (h (hashTm a) (hashTm b))
  | .eq A a b => h 20 (h (hashTm A) (h (hashTm a) (hashTm b)))
  | .eqTy A B => h 21 (h (hashTm A) (hashTm B))
  | .refl A a => h 22 (h (hashTm A) (hashTm a))
  | .reflTy X => h 23 (hashTm X)
  | .cast A B e t => h 24 (h (hashTm A) (h (hashTm B) (h (hashTm e) (hashTm t))))
  | .transp A a P p b e =>
    h 25 (h (hashTm A) (h (hashTm a) (h (hashTm P) (h (hashTm p) (h (hashTm b) (hashTm e))))))
  | .qty => h 26 0
  | .qlit r => h 27 (qHash r)
  | .enum ls => h 28 (hash ls)
  | .tag ls i => h 29 (h (hash ls) (hash i))
  | .ecase z mo s bs => h 30 (h (hash z) (h (hashTm mo) (h (hashTm s) (hs bs))))
  | .desc l I => h 31 (h (hash l) (hashTm I))
  | .dret i => h 32 (hashTm i)
  | .darg q S D => h 33 (h (hashTm q) (h (hashTm S) (hashTm D)))
  | .drec q j D => h 34 (h (hashTm q) (h (hashTm j) (hashTm D)))
  | .dhrec q H j D => h 35 (h (hashTm q) (h (hashTm H) (h (hashTm j) (hashTm D))))
  | .delim v P a b c e D =>
    h 36 (h (hash v) (h (hashTm P) (h (hashTm a) (h (hashTm b) (h (hashTm c) (h (hashTm e) (hashTm D)))))))
  | .mu l I D i sz hh =>
    h 37 (h (hash l) (h (hashTm I) (h (hashTm D) (h (hashTm i) (h (hashTm sz) (hintHash hh))))))
  | .con x => h 38 (hashTm x)
  | .ind l I D v P m i x =>
    h 39 (h (hash l) (h (hashTm I) (h (hashTm D) (h (hash v) (h (hashTm P) (h (hashTm m) (h (hashTm i) (hashTm x))))))))
  | .nu l I D i sz hh =>
    h 40 (h (hash l) (h (hashTm I) (h (hashTm D) (h (hashTm i) (h (hashTm sz) (hintHash hh))))))
  | .out x => h 41 (hashTm x)
  | .size => h 42 0
  | .szInf => h 43 0
  | .szSuc s => h 44 (hashTm s)
  | .sizeLt s => h 45 (hashTm s)
  | .sfix l I D v P g s i x =>
    h 46 (h (hash l) (h (hashTm I) (h (hashTm D) (h (hash v) (h (hashTm P) (h (hashTm g) (h (hashTm s) (h (hashTm i) (hashTm x)))))))))
  | .scase l q I D v P m s i x =>
    h 47 (h (hash l) (h (hashTm q) (h (hashTm I) (h (hashTm D) (h (hash v) (h (hashTm P) (h (hashTm m) (h (hashTm s) (h (hashTm i) (hashTm x))))))))))
  | .cocon x => h 48 (hashTm x)
  | .scofix l I D A f s i a =>
    h 49 (h (hash l) (h (hashTm I) (h (hashTm D) (h (hashTm A) (h (hashTm f) (h (hashTm s) (h (hashTm i) (hashTm a))))))))
  | .coit l I D S st i s =>
    h 50 (h (hash l) (h (hashTm I) (h (hashTm D) (h (hashTm S) (h (hashTm st) (h (hashTm i) (hashTm s)))))))
  | .natLit n => h 51 (hash n)
  | .natOp op args => h 52 (h (hash op) (ha args))
  | .ulift k l A => h 53 (h (lvHash k) (h (hash l) (hashTm A)))
  | .up a => h 54 (hashTm a)
  | .down t => h 55 (hashTm t)
  | .prf l t => h 56 (h (hash l) (hashTm t))
where
  /-- Mix one field into a node's hash. -/
  h (a b : UInt64) : UInt64 := mixHash (mixHash 0x9e3779b97f4a7c15 a) b
  /-- Mix a list of terms (a description's branches). -/
  hs (ts : List Tm) : UInt64 := ts.foldl (fun acc t => h acc (hashTm t)) 0
  /-- Mix an array of terms (a native operation's arguments). -/
  ha (ts : Array Tm) : UInt64 := ts.foldl (fun acc t => h acc (hashTm t)) 0
  biHash : BinderInfo → UInt64
    | .default => 1
    | .implicit => 2
    | .instImplicit => 3
  lvHash (l : Level) : UInt64 := mixHash 0x5bd1e995 (hash l)
  /-- A `Π`/`Σ`'s two component sorts. -/
  sortsHash : BinderSorts → UInt64
    | σ => h (lvHash σ.dom) (lvHash σ.cod)
  qHash : Q → UInt64
    | .zero => 1
    | .one => 2
    | .many => 3
  hintHash : Option (Name × List Level × List Tm) → UInt64
    | none => 0
    | some (n, us, ts) => h (h (hash n) (hash us)) (hs ts)

/-- Every constructor of `Term`, by name. (`ctorName` is exhaustive; a name it returns
that is missing here fails the coverage gate as "unknown".) -/
def allCtors : List String :=
  ["var", "const", "sort", "pi", "lam", "app", "letE", "letUnit", "ann", "mvar", "sigma", "pair", "fst", "snd",
   "split", "unit", "tt", "empty", "absurd", "eq", "eqTy", "refl", "reflTy", "cast", "transp", "qty",
   "qlit", "enum", "tag", "ecase", "desc", "dret", "darg", "drec", "dhrec", "delim", "mu", "con", "ind",
   "nu", "out", "size", "szInf", "szSuc", "sizeLt", "sfix", "scase", "cocon", "scofix", "coit",
   "natLit", "natOp", "ulift", "up", "down", "prf"]

/-- Constructors no checked term contains: the kernel rejects `mvar`, and `natOp` is made
only by `eval` (its coverage is the feature rows `native: …`). -/
def exemptCtors : List String := ["mvar", "natOp"]

partial def liftT (k : Nat) (t : Tm) (cut : Nat := 0) : Tm :=
  match t with
  | .var i => if i ≥ cut then .var (i + k) else .var i
  | t => mapKids id (fun d c => liftT k c (cut + d)) t

/-- Substitute `s` for variable `k`, removing it. `s` lives in the context without `k`. -/
partial def substT (t : Tm) (k : Nat) (s : Tm) (depth : Nat := 0) : Tm :=
  match t with
  | .var i =>
    if i < k + depth then .var i
    else if i == k + depth then liftT depth s
    else .var (i - 1)
  | t => mapKids id (fun d c => substT c k s (depth + d)) t

/-- Replace variable `k` by `s`, keeping it in the context (`s` lives in the same context). -/
partial def replT (t : Tm) (k : Nat) (s : Tm) (depth : Nat := 0) : Tm :=
  match t with
  | .var i => if i == k + depth then liftT depth s else .var i
  | t => mapKids id (fun d c => replT c k s (depth + d)) t

partial def hasVarT (t : Tm) (k : Nat) : Bool :=
  match t with
  | .var i => i == k
  | t => ((mapKidsM (m := StateM Bool) pure (fun d c => do
      if hasVarT c (k + d) then set true
      pure c) t).run false).2

partial def instLv (ps : List String) (us : List Level) (t : Tm) : Tm :=
  mapKids (fun l => l.instParams ps us) (fun _ c => instLv ps us c) t

partial def lvParams (t : Tm) : List String :=
  ((go t).run []).2.eraseDups
where
  go (t : Tm) : StateM (List String) Unit := do
    let _ ← mapKidsM (fun l => do modify (l.params ++ ·); pure l) (fun _ c => do go c; pure c) t

/-- Drop the sorts of every `Π`/`Σ` (to holes: the sorts pass fills them again, from the
components' types). -/
partial def stripSorts (t : Tm) : Tm :=
  match mapKids id (fun _ c => stripSorts c) t with
  | .pi x bi q a b _ => .pi x bi q a b .hole
  | .sigma x q a b _ => .sigma x q a b .hole
  | t => t

/-- Does the term mention a size, or a primitive of the sized fragment? -/
partial def mentionsSize (t : Tm) : Bool :=
  match t with
  | .size | .szSuc _ | .sizeLt _ | .sfix .. | .scase .. | .scofix .. | .cocon _ => true
  | .mu _ _ _ _ s _ | .nu _ _ _ _ s _ => s != .szInf ||
    ((mapKidsM (m := StateM Bool) pure (fun _ c => do
      if mentionsSize c then set true
      pure c) t).run false).2
  | t => ((mapKidsM (m := StateM Bool) pure (fun _ c => do
      if mentionsSize c then set true
      pure c) t).run false).2

partial def sizeT (t : Tm) : Nat :=
  ((mapKidsM (m := StateM Nat) pure (fun _ c => do modify (· + sizeT c); pure c) t).run 1).2

/-! ## A memo for the marking pass

Under P2 every term is marked before it is checked (`Wiz/Elab/Mark.lean`), and the same
raw term is marked again and again — and soon: the judgment's term once for the coverage
table and again in `lawsOn`; a type at each `tyPair` of a sample and again in `genTm`; a
candidate argument each time the generator rebuilds it for the next choice sequence; a
query's normal form right after its verdict. The pass is a pure function of the term and
the context it is run in, so the harness keeps its answers. (This is only a memo: the pass,
and what the harness checks, are untouched.)

The key is **structural** — the entry point, the world (a tag for its globals), the context
(its raw types, which `Cx.k` is `eval` of), the raw term, and for `Mark.check` the written
type — never an address. A lookup compares the stored key with the requested one (`BEq` on
`Term` is structural), so a hash collision costs a comparison and cannot change an answer.

The cell is mutable behind a pure interface (`unsafeBaseIO`, as `Budget` in
`Wiz/Core/Term.lean` and the module cache in `Wiz/Frontend/Frontend.lean`): the compiled
test driver uses it, and the interpreter (and the kernel) sees a miss, so a cached answer
can only ever save work. It keeps a rolling window of `PROP_MEMO_CAP` answers (2000: the
measured best; see `memoCapRef`), starting again from empty when full, so a run that marks
millions of candidates keeps bounded memory. A world's name means the same globals only
within one case, so each case starts from an empty memo (`memoReset`). `PROP_MEMO_STATS=1`
prints the counts; `PROP_NO_MEMO=1` turns the memo off (an A/B in one build). -/

/-- A marking call, as the memo keys it. `kind` is the entry point (a `chk` never gets an
`accepts`' answer); `world` tags the globals; `ctx` is the context a term is marked in (its
raw types, innermost first — the level follows their number); `ty` is the written type, for
`Mark.check`. `h` is the key's hash, computed once when the key is made (a lookup and its
insert both use it). -/
structure MKey where
  kind : UInt64
  world : UInt64
  ctx : List Tm := []
  t : Tm
  ty : Option Tm := none
  h : UInt64 := 0
  deriving BEq

/-- A memo's answer; the key's `kind` says which field is meaningful. (Only what a second
call can reuse is kept: a closed term's marked form never repeated — 3 hits in a run — and
keeping those terms is what a run cannot afford, so `accepts` keeps its verdict alone, and
`chk` — which repeats — is the entry point that carries `markAt`.) -/
structure Ans where
  /-- the marked term (`markKnown`) -/
  term : Option Tm := none
  /-- the level of a marked type (`lvlOf`) -/
  level : Option Level := none
  /-- a verdict (`chk`, `accepts`) -/
  verdict : Bool := false
  /-- a `Kernel.wiz` query's answer (`wizVerdict`, `wizNormal`) -/
  text : String := ""
  deriving Inhabited

structure MemoState where
  map : Std.HashMap UInt64 (Array (MKey × Ans)) := {}
  calls : Nat := 0
  hits : Nat := 0
  inserts : Nat := 0
  /-- lookups and hits of each entry point (`kind`) -/
  byKind : Array (Nat × Nat) := Array.replicate 9 (0, 0)
  /-- nanoseconds spent inside lookups and inserts -/
  lookupNs : Nat := 0
  insertNs : Nat := 0
  deriving Inhabited, Nonempty

structure Memo where
  ref : IO.Ref MemoState

/-- A key with its hash. -/
def mkeyOf (kind world : UInt64) (ctx : List Tm) (t : Tm) (ty : Option Tm := none) : MKey :=
  let h := ctx.foldl (fun h A => mixHash h (hashTm A))
    (mixHash (mixHash 0x243f6a8885a308d3 kind) world)
  let h := mixHash h (hashTm t)
  let h := match ty with
    | none => h
    | some T => mixHash (mixHash h 0x9e3779b97f4a7c15) (hashTm T)
  { kind, world, ctx, t, ty, h }

def MKey.hash (k : MKey) : UInt64 := k.h

initialize memoRef : IO.Ref MemoState ← IO.mkRef {}

/-- `PROP_NO_MEMO=1` turns the memo off (every lookup misses, nothing is kept): an A/B
of the memo in one build. -/
initialize memoOffRef : IO.Ref Bool ← do
  pure (← IO.mkRef (← IO.getEnv "PROP_NO_MEMO").isSome)

/-- `PROP_MEMO_STATS=1`: count the memo's lookups, hits and time (off, so that a run
measures the harness and not the counters). -/
initialize memoStatsOnRef : IO.Ref Bool ← do
  pure (← IO.mkRef (← IO.getEnv "PROP_MEMO_STATS").isSome)

/-- How many answers the memo keeps (`PROP_MEMO_CAP`, default 2000: measured fastest, and a
bigger window only costs memory). A full memo starts again from empty, so it keeps the
most recent window: a run that marks millions of generated candidates keeps bounded
memory, and the answers the harness asks for again soon (a sample's term in `lawsOn` right
after the coverage table, a type at the next `tyPair`, a candidate the generator rebuilds
for the next choice sequence) are still there. -/
initialize memoCapRef : IO.Ref Nat ← do
  let n := ((← IO.getEnv "PROP_MEMO_CAP").bind String.toNat?).getD 2000
  pure (← IO.mkRef n)

/-- This run's memo. -/
def memo : Memo := ⟨memoRef⟩

private unsafe def memoFindImpl (m : Memo) (k : MKey) : Option Ans :=
  unsafeBaseIO do
    if ← memoOffRef.get then pure none else
    let stats ← memoStatsOnRef.get
    let t0 ← if stats then IO.monoNanosNow else pure 0
    let s ← m.ref.get
    let found := (s.map.getD k.hash #[]).find? (fun (k', _) => k' == k)
    if stats then
      let i := k.kind.toNat
      let byKind :=
        if i < s.byKind.size then
          let (c, n) := s.byKind.getD i (0, 0)
          s.byKind.set! i (c + 1, n + (if found.isSome then 1 else 0))
        else s.byKind
      m.ref.set { s with calls := s.calls + 1, hits := s.hits + (if found.isSome then 1 else 0), byKind,
                         lookupNs := s.lookupNs + ((← IO.monoNanosNow) - t0) }
    pure (found.map (·.2))

/-- The memo's answer for `k`, if it has one. (Compiled code reads the cell; the
interpreter misses.) -/
@[implemented_by memoFindImpl]
opaque memoFind (m : Memo) (k : MKey) : Option Ans

private unsafe def memoPutImpl (m : Memo) (k : MKey) (a : Ans) : Ans :=
  unsafeBaseIO do
    if ← memoOffRef.get then pure a else
    let stats ← memoStatsOnRef.get
    let t0 ← if stats then IO.monoNanosNow else pure 0
    let cap ← memoCapRef.get
    let s ← m.ref.get
    let s := if s.map.size ≥ cap then { s with map := {} } else s
    let bucket := s.map.getD k.hash #[]
    let s :=
      if bucket.any (fun (k', _) => k' == k) then s else
      { s with map := s.map.insert k.hash (bucket.push (k, a)), inserts := s.inserts + 1 }
    if stats then
      m.ref.set { s with insertNs := s.insertNs + ((← IO.monoNanosNow) - t0) }
    else m.ref.set s
    pure a

/-- Keep `a` under `k`; returns it (so the write cannot be dropped). -/
@[implemented_by memoPutImpl]
opaque memoPut (m : Memo) (k : MKey) (a : Ans) : Ans

/-- Start a case from an empty memo. -/
def memoReset : IO Unit := memo.ref.set {}

/-- The name of an entry point, for the memo's table. -/
def kindName : Nat → String
  | 3 => "markKnown" | 4 => "lvlOf" | 5 => "chk" | 6 => "accepts"
  | 7 => "wizVerdict" | 8 => "wizNormal" | k => s!"kind {k}"

/-- (`PROP_MEMO_STATS=1`) the memo's counts, on stdout and in `.scratch/mark-cache-stats.txt`
(the driver keeps a passing case's output to itself). -/
def memoStats (what : String) : IO Unit := do
  if (← IO.getEnv "PROP_MEMO_STATS").isSome then
    let s ← memo.ref.get
    let pct := if s.calls == 0 then 0 else s.hits * 100 / s.calls
    let secs (ns : Nat) : String := s!"{ns / 1000000} ms"
    let nodes := s.map.toList.foldl (fun n (_, b) => b.foldl (fun n (k, _) => n + sizeT k.t) n) 0
    let mut out := s!"{what}: {s.calls} lookups, {s.hits} hits ({pct}%), {s.inserts} kept, {s.map.size} keys, {nodes} terms; {secs s.lookupNs} in lookups, {secs s.insertNs} in inserts\n"
    for ((c, n), kind) in s.byKind.zipIdx do
      unless c == 0 && n == 0 do out := out ++ s!"  {kindName kind}: {c} lookups, {n} hits\n"
    IO.print out
    if ← System.FilePath.isDir ".scratch" then
      let f := ".scratch/mark-cache-stats.txt"
      let old ← if ← System.FilePath.pathExists f then IO.FS.readFile f else pure ""
      IO.FS.writeFile f (old ++ out)

private def kMarkKnown : UInt64 := 3
private def kLvlOf : UInt64 := 4
private def kChk : UInt64 := 5
private def kAccepts : UInt64 := 6
private def kWizVerdict : UInt64 := 7
private def kWizNormal : UInt64 := 8

/-- The tag of the globals `wizCase` asks `Kernel.wiz`'s queries with (`Elab.leanGlobals`). -/
private def wizTag : UInt64 := hash "prop.wiz-case"

def inferable : Tm → Bool
  | .lam .. | .pair .. | .tt | .con _ | .cocon _ | .up _ | .dret _ | .darg .. | .drec .. | .dhrec ..
  | .natOp .. => false
  -- (P2: a marker is transparent; the underlying term decides)
  | .prf _ t => inferable t
  | .letE _ _ _ _ b => inferable b
  | .letUnit _ b => inferable b
  | _ => true

def mkInf (t T : Tm) : Tm := if inferable t then t else .ann t T

/-! ## Into the calculus of `Kernel.wiz`

Like `MTm.ofTerm`, but a `Π`/`Σ` keeps its sort annotation (`sorted`). `none` outside the
fragment: quantity variables, symbolic levels, `split`, numerals, native operations. -/

partial def toM : Tm → Option MTm
  | .var i => some (.var i)
  | .sort l => match l.toNat? with
    | some (n + 1) => some (.univ n)
    | some 0 => some .prop
    | _ => none
  | .pi _ _ q a b σ => do
    let core ← match q with
      | .qlit .many => pure (MTm.pi (← toM a) (← toM b))
      | .qlit r => pure (MTm.piq r (← toM a) (← toM b))
      | _ => none
    match σ.dom.toNat?, σ.cod.toNat? with
    | some i, some j => pure (.sorted i j core)
    | _, _ => pure core
  | .sigma _ q a b σ => do
    let core ← match q with
      | .qlit .many => pure (MTm.sigma (← toM a) (← toM b))
      | .qlit r => pure (MTm.sigmaq r (← toM a) (← toM b))
      | _ => none
    match σ.dom.toNat?, σ.cod.toNat? with
    | some i, some j => pure (.sorted i j core)
    | _, _ => pure core
  | .lam _ b => return .lam (← toM b)
  | .app f a => return .app (← toM f) (← toM a)
  | .letE _ (.qlit .many) t v b => return .letE (← toM t) (← toM v) (← toM b)
  | .letE _ (.qlit q) t v b => return .letq q (← toM t) (← toM v) (← toM b)
  | .letUnit u b => return .letUnit (← toM u) (← toM b)
  | .ann t ty => return .ann (← toM t) (← toM ty)
  | .pair a b => return .pair (← toM a) (← toM b)
  | .fst p => return .fst (← toM p)
  | .snd p => return .snd (← toM p)
  | .unit l => match l.toNat? with
    | some (n + 1) => some (.unit n)
    | some 0 => some .ptrue
    | _ => none
  | .tt => some .star
  | .empty l => match l.toNat? with
    | some (n + 1) => some (.empty n)
    | some 0 => some .pfalse
    | _ => none
  | .absurd m t => return .exfalso (← toM m) (← toM t)
  | .enum ls => some (.enum ls.length)
  | .tag ls i => some (.tag ls.length i)
  | .ecase _ m s bs => return .ecase (← toM m) (← toM s) (← bs.mapM toM)
  | .eq A a b => return .eq (← toM A) (← toM a) (← toM b)
  | .eqTy A B => return .eqTy (← toM A) (← toM B)
  | .refl A a => return .refl (← toM A) (← toM a)
  | .reflTy X => return .reflTy (← toM X)
  | .cast A B e t => return .cast (← toM A) (← toM B) (← toM e) (← toM t)
  | .transp A a P p b e => return .transp (← toM A) (← toM a) (← toM P) (← toM p) (← toM b) (← toM e)
  | .desc l I => return .desc (← l.toNat?) (← toM I)
  | .dret i => return .dret (← toM i)
  | .darg (.qlit .many) S E => return .darg (← toM S) (← toM E)
  | .drec (.qlit .many) j E => return .drec (← toM j) (← toM E)
  | .dhrec (.qlit .many) H j E => return .dhrec (← toM H) (← toM j) (← toM E)
  | .delim v P a b c h D =>
    return .delim (← v.toNat?) (← toM P) (← toM a) (← toM b) (← toM c) (← toM h) (← toM D)
  | .mu l I D i .szInf _ => return .mu (← l.toNat?) (← toM I) (← toM D) (← toM i)
  | .mu l I D i s _ => return .mus (← l.toNat?) (← toM I) (← toM D) (← toM i) (← toM s)
  | .nu l I D i s _ => return .nu (← l.toNat?) (← toM I) (← toM D) (← toM i) (← toM s)
  | .out x => return .out (← toM x)
  | .cocon x => return .cocon (← toM x)
  | .con x => return .con (← toM x)
  | .ind l I D v P m i x =>
    return .ind (← l.toNat?) (← toM I) (← toM D) (← v.toNat?) (← toM P) (← toM m) (← toM i) (← toM x)
  | .scofix l I D A f s i a =>
    return .scofix (← l.toNat?) (← toM I) (← toM D) (← toM A) (← toM f) (← toM s) (← toM i) (← toM a)
  | .coit l I D S st i s =>
    return .coit (← l.toNat?) (← toM I) (← toM D) (← toM S) (← toM st) (← toM i) (← toM s)
  | .sfix l I D v P f s i x =>
    return .sfix (← l.toNat?) (← toM I) (← toM D) (← v.toNat?) (← toM P) (← toM f) (← toM s) (← toM i) (← toM x)
  | .scase l (.qlit .many) I D v P m s i x =>
    return .scase (← l.toNat?) (← toM I) (← toM D) (← v.toNat?) (← toM P) (← toM m) (← toM s) (← toM i) (← toM x)
  | .scase l (.qlit q) I D v P m s i x =>
    return .scaseq q (← l.toNat?) (← toM I) (← toM D) (← v.toNat?) (← toM P) (← toM m) (← toM s) (← toM i) (← toM x)
  | .size => some .size
  | .szInf => some .szInf
  | .szSuc s => return .szSuc (← toM s)
  | .sizeLt s => return .sizeLt (← toM s)
  | .const n us => do
    if MTm.globalDefs.any (·.1 == n) then return .const n (← us.mapM Level.toNat?) else none
  | .ulift k l A => return .ulift (← k.toNat?) (← l.toNat?) (← toM A)
  | .up a => return .up (← toM a)
  | .down t => return .down (← toM t)
  | .prf l t => do return .prf (.num (← l.toNat?)) (← toM t)
  | _ => none

/-! ## Worlds: the signatures terms are generated over -/

structure World where
  name : String
  g : Gl
  /-- the type of numbers -/
  nat : Tm
  /-- constants applied type-directed, to any number of arguments (so `Nat.add x` too) -/
  heads : List Tm
  /-- closed terms used as leaves, with their types (computed by the kernel) -/
  gadgets : List (Tm × Tm) := []
  /-- closed data types to eliminate from -/
  dataTys : List Tm := []
  /-- has `idP.{u}` -/
  idP : Bool := false
  /-- the terms are in `Kernel.wiz`'s calculus, over `MTm.globalDefs` -/
  wiz : Bool := false
  /-- contexts for the enumeration -/
  fixed : List (Array Tm) := []
  /-- every generated `Π`/`Σ` carries its sort, and no rewrite drops one: the theory with
  mandatory sorts (N2 of the plan). A finding that goes away under it is an instance of
  U5 (`p1-stable.md`): the optional annotation decides `vEqType`/`vCast`. -/
  strict : Bool := false
  /-- `Size` and `Size< s` as ordinary types (to cast and equate). Off: conversion at
  them is not reflexive on a stuck size (finding Sz1, `prop-harness.md`). -/
  sizeTypes : Bool := false
  /-- sizes at all: size variables, `μ`/`ν` at a size, `scase`, `sfix`, `scofix`
  (`tests --prop-no-sizes` turns them off: Sz1, Sz2) -/
  sizes : Bool := true
  /-- the types of the gadgets, with their sorts: leaves of the type generator -/
  gadgetTys : List (Tm × Tm) := []

/-- (P2) The term as the elaborator delivers it: the marking pass over `t`, and `none`
when the pre-P2 kernel (the marker's requirement off) rejects it — the pass checks
nothing, and a random term can be ill-typed. -/
def markInf (g : Gl) (t : Tm) : Option Tm :=
  -- (mandatory sorts: the pre-check tolerates the holes the generator writes, which the
  -- pass then fills — `leanVerdict` does the same)
  let ctx : Ctx Q := { globals := { g with lazyProofs := false, sortHolesOk := true } }
  match infer (R := Q) ctx t with
  | .error _ => none
  | .ok _ => some (Mark.infer { globals := g } t).1

def accepts (g : Gl) (t : Tm) : Bool :=
  match markInf g t with
  | none => false
  | some t' =>
    match infer (R := Q) { globals := g } t' with
    | .ok _ => true
    | .error _ => false

def typeOfClosed (g : Gl) (t : Tm) : Option Tm :=
  match markInf g t with
  | none => none
  | some t' =>
    match infer (R := Q) { globals := g } t' with
    | .ok (ty, _) => some (quote g 0 ty)
    | .error _ => none

/-- (memo) `accepts`, for a world whose tag is `tag`: a closed term is checked once, and
the same closed term is a law's term in one law and the same judgment's term in another. -/
def acceptsC (tag : UInt64) (g : Gl) (t : Tm) : Bool :=
  let k := mkeyOf kAccepts tag [] t
  match memoFind memo k with
  | some a => a.verdict
  | none =>
    let b := match markInf g t with
      | none => false
      | some t' =>
        match infer (R := Q) { globals := g } t' with
        | .ok _ => true
        | .error _ => false
    (memoPut memo k { verdict := b }).verdict

def withGadgets (w : World) (ts : List Tm) : World :=
  let gadgets := ts.filterMap fun t => (typeOfClosed w.g t).map (t, ·)
  let tys := (gadgets.map (·.2)).eraseDups.filterMap fun ty => (typeOfClosed w.g ty).map (ty, ·)
  { w with gadgets, gadgetTys := tys }

def E2 : Tm := .enum (MTm.labels 2)
def piW (a b : Tm) : Tm := .pi "x" .default (.qlit .many) a b .hole
/-- A `Π` with its components' sorts written (`i` the domain's, `j` the codomain's). -/
def piS (a b : Tm) (i j : Level) : Tm := .pi "x" .default (.qlit .many) a b ⟨i, j⟩

/-- The world both kernels share: the globals of the differential test. -/
def sharedWorld (_ : Unit) : World :=
  let g := Elab.leanGlobals ()
  let nat : Tm := .const "Nat" []
  let m (t : MTm) : Tm := t.toTerm
  let w : World :=
    { name := "shared", g, nat, idP := true, wiz := true
      heads := [.const "idU" [], .const "twice" [], .const "constP" [1, 1],
        -- (a case on its argument, glued: coverage of stuck cases on a global)
        .const "caseF" [],
        -- families over sizes
        m (.ann (.lam (MTm.natAt (.var 0))) (.pi .size (.univ 0))),
        m (.ann (.lam (MTm.streamAt (.szSuc (.var 0)))) (.pi .size (.univ 0)))]
      dataTys := [nat]
      fixed := [#[], #[.qty, .qty], #[nat, nat], #[.sort 1, .sort 0, .var 1, .var 1],
        #[E2, piS E2 (.sort 1) 1 2], #[.sort 1, .sort 1, .eqTy (.var 1) (.var 0), .var 2],
        #[.size, .sizeLt (.var 0)], #[.empty 0, .sort 1]] }
  withGadgets w [.const "zero" [], .const "one" [], .const "a" [], .const "A" [], .const "polyK" [0], .const "dLv" [0],
    m MTm.alt, m MTm.zeros, m (MTm.shead MTm.alt), m (MTm.stail MTm.alt), m MTm.natZero,
    m (MTm.natSucc MTm.natZero), .ann (m MTm.natD) (.desc 0 (.unit 1))]

def nativeSrc : String :=
  "import Prelude\n" ++
  "def IsZ (n : Nat) : Type := match n with\n  | .zero => Unit\n  | .succ _ => Empty\n" ++
  "def TF (f : Nat → Nat) : Type := IsZ (f 0)\n"

/-- The world of the Lean kernel alone: the Prelude's numbers with their native
operations, a family over numbers and one over functions on numbers. -/
def nativeWorld : IO World := do
  let loader ← Elab.preludeLoader
  let s := runFrontend (R := Q) nativeSrc { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render nativeSrc
  unless errs.isEmpty do throw (IO.userError s!"prop: unexpected errors:\n{"\n".intercalate errs.toList}")
  let nat : Tm := .const "Nat" []
  let w : World :=
    { name := "native", g := s.globals, nat
      heads := [.const "Nat.succ" [], .const "Nat.add" [], .const "Nat.mul" [], .const "Nat.sub" [],
        .const "IsZ" [], .const "TF" []]
      dataTys := [nat]
      fixed := [#[nat, nat], #[nat, piS nat nat 1 1], #[.qty, nat]] }
  pure (withGadgets w [.natLit 0, .natLit 1, .natLit 2])

/-! ## Choice sequences -/

structure GS where
  /-- the prescribed choices; past them, a choice is random (`rnd`) or the default `0` -/
  pre : Array Nat
  pos : Nat := 0
  /-- the choices made, with their arities -/
  log : Array (Nat × Nat) := #[]
  rnd : Option Nat := none
  steps : Nat := 0

abbrev Gen := StateM GS

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def choose (k : Nat) : Gen Nat := do
  if k ≤ 1 then return 0
  let st ← get
  let (c, rnd) : Nat × Option Nat :=
    if h : st.pos < st.pre.size then (st.pre[st.pos] % k, st.rnd) else
    match st.rnd with
    | some r => let r := lcg r; ((r >>> 33) % k, some r)
    | none => (0, none)
  set { st with pos := st.pos + 1, log := st.log.push (c, k), rnd }
  return c

/-- A node of the generated term: `false` when the sample has grown too large. -/
def tick : Gen Bool := do
  modify fun st => { st with steps := st.steps + 1 }
  return (← get).steps < 400

def pick {α : Type} (alts : Array (Gen α)) (dflt : Gen α) : Gen α := do
  if alts.isEmpty then dflt else
  let i ← choose alts.size
  alts.getD i dflt

def runGen {α : Type} (pre : Array Nat) (rnd : Option Nat) (x : Gen α) : α × GS :=
  x.run { pre, rnd }

/-! ## The generator -/

/-- A context: its types as terms (innermost first), and the kernel's context. -/
structure Cx where
  w : World
  tys : List Tm := []
  k : Ctx Q
  /-- level parameters the sample may use -/
  lps : List String := []

namespace Cx

def g (cx : Cx) : Gl := cx.w.g
def size (cx : Cx) : Nat := cx.tys.length

def push (cx : Cx) (A : Tm) : Cx :=
  { cx with tys := A :: cx.tys, k := cx.k.bind s!"x{cx.tys.length}" (QPoly.const .many) (cx.k.eval A) }

def nf (cx : Cx) (t : Tm) : Tm := quote cx.g cx.k.lvl (cx.k.eval t)
/-- weak head normal form of a type (its parts are normal) -/
def whq (cx : Cx) (t : Tm) : Tm := quote cx.g cx.k.lvl (whnf (cx.k.eval t))
def convTy (cx : Cx) (A B : Tm) : Bool := Wiz.convTy cx.g cx.k.tys (cx.k.eval A) (cx.k.eval B)

/-- (memo) the key of a marking call made in this context. -/
def mkey (cx : Cx) (kind : UInt64) (t : Tm) (ty : Option Tm := none) : MKey :=
  mkeyOf kind (hash cx.w.name) cx.tys t ty

def lvlOf (cx : Cx) (A : Tm) : Option Level :=
  let k := cx.mkey kLvlOf A
  match memoFind memo k with
  | some a => a.level
  | none =>
    -- (mandatory sorts: the pre-check tolerates the generator's holes, as `markAt` does)
    let ctx0 := { cx.k with globals := { cx.g with lazyProofs := false, sortHolesOk := true } }
    let l := match checkType ctx0 A with
      | .error _ => none
      | .ok _ => match checkType cx.k (Mark.type cx.k A).1 with
        | .ok l => some l
        | .error _ => none
    (memoPut memo k { level := l }).level

/-- (P2) `t : T` marked, or `none` when the pre-P2 kernel rejects it. -/
def markAt (cx : Cx) (t T : Tm) : Option Tm :=
  -- (mandatory sorts: the generator writes `Π`/`Σ` holes, which the sorts pass fills; the
  -- pre-check runs before it and must tolerate them, as `leanVerdict`/`markInf` do)
  let ctx0 := { cx.k with globals := { cx.g with lazyProofs := false, sortHolesOk := true } }
  match Wiz.check ctx0 t (ctx0.eval T) with
  | .error _ => none
  | .ok _ => some (Mark.check cx.k t (cx.k.eval T))

/-- (P2) `t : T` marked, for a term the kernel already accepted (`V`): the pass checks
nothing, so it is run only on a term that kernel accepted. -/
def markKnown (cx : Cx) (t T : Tm) : Tm :=
  let k := cx.mkey kMarkKnown t (some T)
  match (memoFind memo k).bind (·.term) with
  | some t' => t'
  | none =>
    let t' := Mark.check cx.k t (cx.k.eval T)
    (memoPut memo k { term := some t' }).term.getD t'

def chk (cx : Cx) (t T : Tm) : Bool :=
  let k := cx.mkey kChk t (some T)
  match memoFind memo k with
  | some a => a.verdict
  | none =>
    let b := match markAt cx t T with
      | none => false
      | some t' =>
        match Wiz.check cx.k t' (cx.k.eval T) with
        | .ok _ => true
        | .error _ => false
    (memoPut memo k { verdict := b }).verdict

/-- the variables whose type is convertible with `T` -/
def varsOfTy (cx : Cx) (T : Tm) : Array Tm :=
  let vT := cx.k.eval T
  ((List.range cx.size).filter fun i => Wiz.convTy cx.g cx.k.tys cx.k.types[i]! vT).toArray.map Term.var

/-- the type of variable `i`, as written, in this context -/
def rawTy (cx : Cx) (i : Nat) : Tm := liftT (i + 1) cx.tys[i]!

def names (cx : Cx) : List Name := cx.k.names

end Cx

def mkCx (w : World) (ctx : Array Tm) (lps : List String := []) : Cx :=
  ctx.foldl (fun cx A => cx.push A) { w, k := { globals := w.g }, lps }

def genQ (cx : Cx) : Gen Tm := do
  let alts : Array Tm := #[.qlit .many, .qlit .zero, .qlit .one] ++ cx.varsOfTy .qty
  return alts.getD (← choose alts.size) (.qlit .many)

def levelIs (l : Level) (n : Nat) : Bool := l.toNat? == some n

/-- How many arguments (at least one) `h : (x₁ : A₁) → … → B` takes to give a `T`.
(Decided with placeholders for the arguments: exact when the telescope is not dependent.) -/
partial def fitDepth (cx : Cx) (ty : Val Q) (vT : Val Q) (n : Nat) (lvl : Nat) (k : Nat := 0) : Option Nat :=
  if k > 0 && Wiz.convTy cx.g cx.k.tys ty vT then some k
  else if n == 0 then none
  else match whnf ty with
    | .pi _ _ _ _ cod _ => fitDepth cx (Closure.inst cx.g cod (Val.var lvl)) vT (n - 1) (lvl + 1) (k + 1)
    | _ => none

/-- The outermost binder's quantity literal changed (`ω ↦ 1 ↦ 0 ↦ ω`): two types that
differ in a quantity only. -/
def flipQ : Tm → Option Tm
  | .pi x bi (.qlit q) a b σ => some (.pi x bi (.qlit (nextQ q)) a b σ)
  | .sigma x (.qlit q) a b σ => some (.sigma x (.qlit (nextQ q)) a b σ)
  | _ => none
where
  nextQ : Q → Q
    | .many => .one
    | .one => .zero
    | .zero => .many

/-- Every constant's levels raised by one: a polymorphic constant at two instances (the
result is well typed only when the constant's type does not depend on the level). -/
partial def bumpLevels (t : Tm) : Tm :=
  match t with
  | .const n ls => .const n (ls.map .succ)
  | t => mapKids id (fun _ c => bumpLevels c) t

def hasBinder (t : Tm) : Bool := stripSorts t != t || (match t with | .pi .. | .sigma .. => true | _ => false)

/-- Fill in the sort of every `Π`/`Σ` of a type's skeleton that lacks one (the kernel
computes it): the types the kernel builds itself (the methods of the eliminators) carry
none. -/
partial def annotate (cx : Cx) (t : Tm) : Tm :=
  match t with
  | .pi x bi q A B σ =>
    let A' := annotate cx A
    let cx' := cx.push A'
    let B' := annotate cx' B
    let σ' := match σ.hasHole, cx.lvlOf A', cx'.lvlOf B' with
      | true, some i, some j => ⟨i, j⟩
      | _, _, _ => σ
    .pi x bi q A' B' σ'
  | .sigma x q A B σ =>
    let A' := annotate cx A
    let cx' := cx.push A'
    let B' := annotate cx' B
    let σ' := match σ.hasHole, cx.lvlOf A', cx'.lvlOf B' with
      | true, some i, some j => ⟨i, j⟩
      | _, _, _ => σ
    .sigma x q A' B' σ'
  | t => t

mutual

/-- A type in `Sort l`. -/
partial def genTy (cx : Cx) (l : Level) (fuel : Nat) : Gen Tm := do
  unless ← tick do return .unit l
  let w := cx.w
  let mut alts : Array (Gen Tm) := #[]
  let leaf (t : Tm) : Gen Tm := pure t
  if levelIs l 1 then
    alts := alts ++ #[leaf (.unit 1), leaf E2, leaf w.nat, leaf (.empty 1), leaf (.sort 0),
      leaf (.enum (MTm.labels 1)), leaf (.enum (MTm.labels 3))]
  else if levelIs l 0 then alts := alts ++ #[leaf (.unit 0), leaf (.empty 0)]
  else if levelIs l 2 then alts := alts ++ #[leaf (.sort 1), leaf (.desc 0 (.unit 1)), leaf (.unit 2)]
  else
    alts := alts ++ #[leaf (.unit l), leaf (.empty l)]
    if let .succ l' := l then alts := alts.push (leaf (.sort l'))
  alts := alts ++ (cx.varsOfTy (.sort l)).map leaf
  alts := alts ++ (w.gadgets.filter fun (_, ty) => ty == .sort l).toArray.map fun (t, _) => leaf t
  alts := alts ++ (w.gadgetTys.filter fun (ty, s) => s == .sort l && !alts.isEmpty && ty != w.nat).toArray.map fun (ty, _) => leaf ty
  if fuel > 0 then
    let f := fuel - 1
    -- the domain's level: `imax la l` and `max la l` must be `l`
    let doms : Array Level :=
      if levelIs l 0 then #[1, 0] else if levelIs l 1 then #[1, 0] else if levelIs l 2 then #[1, 2, 0]
      else #[l, 0]
    let binder (isPi : Bool) : Gen Tm := do
      let q ← genQ cx
      let la := doms.getD (← choose (if isPi || !levelIs l 0 then doms.size else 1)) 0
      let la := if !isPi && levelIs l 0 then 0 else la
      let A ← genTy cx la f
      let B ← genTy (cx.push A) l f
      -- (mandatory sorts: the components are the domain's level and the codomain's,
      -- which the generator knows; a hole in the variants that leave it to the pass)
      let σ : BinderSorts := if (← choose 2) == 0 || w.strict then ⟨la, l⟩ else .hole
      return if isPi then .pi "x" .default q A B σ else .sigma "x" q A B σ
    alts := alts ++ #[binder true, binder false]
    if levelIs l 0 then
      alts := alts ++ #[
        (do let A ← genTy cx 1 f
            let a ← genTm cx A f
            let b ← variantTm cx A a f
            return .eq A a b),
        (do let lv : Level := if (← choose 2) == 0 then 1 else 2
            let A ← genTy cx lv f
            let B ← variantTy cx lv A f
            return .eqTy A B)]
    -- data: `μ`/`ν` over a small code, at a size
    if let .succ l' := l then
      let data (isMu : Bool) : Gen Tm := do
        -- (indexed by a tag when the context has one: the index is then a variable, and
        -- casts between two instances go by the constructor rule)
        let tagFirst := !(cx.varsOfTy E2).isEmpty
        let other := levelIs l 1 && (← choose 2) == 1
        let I : Tm := if levelIs l 1 && (other != tagFirst) then E2 else .unit l
        let D ← genDesc cx l' I f
        let i ← genTm cx I 0
        let sizes : Array Tm := if !w.sizes then #[.szInf] else #[.szInf, .szSuc .szInf] ++
          cx.varsOfTy .size ++ (cx.varsOfTy .size).map .szSuc
        let s := sizes.getD (← choose sizes.size) .szInf
        return if isMu then .mu l' I D i s none else .nu l' I D i s none
      alts := alts ++ #[data true, data false]
    -- lifting (also a proposition, to `Prop`)
    if levelIs l 0 then alts := alts.push (do return .ulift 0 0 (← genTy cx 0 f))
    if l.isNeverZero then
      alts := alts.push (do
        let la : Level := if Level.le 1 l && (← choose 2) == 1 then 1 else 0
        let A ← genTy cx la f
        return .ulift la l A)
    -- large elimination on a tag
    alts := alts.push (do
      let s ← genTm cx E2 f
      let a ← genTy cx l f
      let b ← genTy cx l f
      return .ecase "z" (.sort l) (mkInf s E2) [a, b])
    -- a stuck case whose environment holds a type: `(fun T => ecase s [T, T]) G` (compared
    -- with its variants, the two environments are compared: W1 of the kernel lint)
    if levelIs l 1 || levelIs l 0 then
      alts := alts.push (do
        let s ← genTm cx E2 0
        let G ← genTy cx l 0
        return .app (.ann (.lam "T" (.ecase "z" (.sort l) (liftT 1 (mkInf s E2)) [.var 0, .var 0]))
          (.pi "T" .default (.qlit .many) (.sort l) (.sort l) ⟨.succ l, .succ l⟩)) G)
    alts := alts ++ (← headAlts cx (.sort l) f)
    if levelIs l 1 then alts := alts.push (leaf .qty)
    if levelIs l 1 && w.sizeTypes then alts := alts ++ #[leaf .size, leaf (.sizeLt .szInf)]
  let A ← pick alts (pure (.unit l))
  -- (the generator evaluates the types it makes: an ill-typed one is replaced)
  return if fuel == 0 || (cx.lvlOf A).isSome then A else .unit l

/-- Another type of the same sort to compare `A` with: `A` itself, `A` with a variable
renamed or a quantity variable instantiated (two instances of one schema), `A` without its
sort annotations, or a fresh type. -/
partial def variantTy (cx : Cx) (l : Level) (A : Tm) (fuel : Nat) : Gen Tm := do
  let mut alts : Array (Gen Tm) := #[pure A, genTy cx l fuel]
  let n := cx.size
  for i in [0:n] do
    if hasVarT A i then
      for j in [0:n] do
        if i != j && cx.convTy (cx.rawTy i) (cx.rawTy j) then alts := alts.push (pure (replT A i (.var j)))
      if cx.whq (cx.rawTy i) == .qty then
        alts := alts ++ #[pure (replT A i (.qlit .one)), pure (replT A i (.qlit .many))]
  if hasBinder A then alts := alts.push (pure A)
  if let some B := flipQ A then alts := alts.push (pure B)
  if bumpLevels A != A then alts := alts.push (pure (bumpLevels A))
  pick alts (pure A)

partial def variantTm (cx : Cx) (T : Tm) (t : Tm) (fuel : Nat) : Gen Tm := do
  let mut alts : Array (Gen Tm) := #[pure t, genTm cx T fuel]
  let n := cx.size
  for i in [0:n] do
    if hasVarT t i && !hasVarT T i then
      for j in [0:n] do
        if i != j && cx.convTy (cx.rawTy i) (cx.rawTy j) then alts := alts.push (pure (replT t i (.var j)))
  pick alts (pure t)

/-- A description in `Desc.{l} I`. -/
partial def genDesc (cx : Cx) (l : Level) (I : Tm) (fuel : Nat) : Gen Tm := do
  unless ← tick do return .dret .tt
  let ret : Gen Tm := do return .dret (← genTm cx I 0)
  let mut alts : Array (Gen Tm) := #[ret]
  alts := alts ++ (cx.varsOfTy (.desc l I)).map pure
  if fuel > 0 then
    let f := fuel - 1
    alts := alts ++ #[
      (do let q ← genQ cx
          let j ← genTm cx I 0
          return .drec q j (← genDesc cx l I f)),
      (do let q ← genQ cx
          let S ← genTy cx (.succ l) f
          let D ← genDesc (cx.push S) l (liftT 1 I) f
          return .darg q S (.lam "s" D)),
      (do let q ← genQ cx
          let cx' := cx.push E2
          let a ← genDesc cx' l (liftT 1 I) f
          let b ← genDesc cx' l (liftT 1 I) f
          return .darg q E2 (.lam "t" (.ecase "z" (.desc l (liftT 2 I)) (.var 0) [a, b]))),
      (do let q ← genQ cx
          let H ← genTy cx (.succ l) f
          let j ← genTm (cx.push H) (liftT 1 I) 0
          return .dhrec q H (.lam "h" j) (← genDesc cx l I f))]
  pick alts ret

/-- Applications of a head (a constant of the signature, or a variable of a function
type) to as many generated arguments as it takes to reach the type `T`. -/
partial def headAlts (cx : Cx) (T : Tm) (fuel : Nat) : Gen (Array (Gen Tm)) := do
  let vT := cx.k.eval T
  let fnVars : List Tm := (List.range cx.size).filterMap fun i =>
    match whnf cx.k.types[i]! with
    | .pi .. => some (.var i)
    | _ => none
  let mut alts : Array (Gen Tm) := #[]
  for h in cx.w.heads ++ fnVars do
    let .ok (hty, _) := infer cx.k h | continue
    if let some k := fitDepth cx hty vT 3 cx.k.lvl then
      alts := alts.push (apply h hty k)
  return alts
where
  apply (acc : Tm) (ty : Val Q) (n : Nat) : Gen Tm := do
    if n == 0 then return acc else
    match whnf ty with
    | .pi _ _ _ dom cod _ =>
      let domT := quote cx.g cx.k.lvl dom
      let a ← genTm cx domT fuel
      let dependent := match cod with
        | .mk _ body => body.hasVar 0
      -- (the codomain is evaluated at the argument: only at a well-typed one)
      if dependent && !cx.chk a domT then return .app acc a else
      apply (.app acc a) (cx.k.instArg cod a) (n - 1)
    | _ => return acc

/-- A term of type `T`. -/
partial def genTm (cx : Cx) (T : Tm) (fuel : Nat) : Gen Tm := do
  unless ← tick do return .tt
  let w := cx.w
  let g := cx.g
  let T := if w.strict then annotate cx T else T
  let Tw := cx.whq T
  let vars := cx.varsOfTy T
  let vT := cx.k.eval T
  let gadgets : Array Tm := (w.gadgets.filter fun (_, ty) =>
    Wiz.convTy g cx.k.tys (eval g [] ty) vT).toArray.map (·.1)
  let leaves : Array (Gen Tm) := (vars ++ gadgets).map pure
  let f := fuel - 1
  -- introduction forms, by the shape of the type
  let intro : Array (Gen Tm) := match Tw with
    | .pi x _ _ A B _ => #[do return .lam x (← genTm (cx.push A) B fuel)]
    | .sigma _ _ A B _ => #[do
        let a ← genTm cx A fuel
        -- (the second type is evaluated at the first component: only at a well-typed one)
        if hasVarT B 0 && !cx.chk a A then return .pair a .tt else
        let b ← genTm cx (substT B 0 a) fuel
        return .pair a b]
    | .unit _ => #[pure .tt]
    | .enum ls => (List.range ls.length).toArray.map fun i => pure (Term.tag ls i)
    | .ulift _ _ A => #[do return .up (← genTm cx A fuel)]
    | .sort l => #[genTy cx l fuel]
    | .qty => #[genQ cx]
    | .size => #[pure .szInf, pure (.szSuc .szInf)]
    | .desc l I => #[genDesc cx l I fuel]
    | .eq A a _ => #[pure (.refl A a)]
    | .eqTy A _ => #[pure (.reflTy A)]
    | .mu l I D i s _ =>
      if fuel == 0 && !leaves.isEmpty then #[] else
      match sizePred? (cx.k.eval s) with
      | some s' =>
        let vI := cx.k.eval I
        let vD := cx.k.eval D
        let P := quote g cx.k.lvl (vInterp g l vI vD (muFamilyAt l vI vD s') (cx.k.eval i))
        #[do return .con (← genTm cx P f)]
      | none => #[]
    | .nu l I D i s _ =>
      if fuel == 0 && !leaves.isEmpty then #[] else
      let vI := cx.k.eval I
      let vD := cx.k.eval D
      let unitS : Tm := .lam "i" (.unit (.succ l))
      let vS := cx.k.eval unitS
      let viaCoit : Array (Gen Tm) := #[do
        let st ← genTm cx (quote g cx.k.lvl (coitStepTy g l vI vD vS .many)) f
        return .ann (.coit l I D unitS st i .tt) Tw]
      let viaScofix : Array (Gen Tm) := #[do
        let fn ← genTm cx (quote g cx.k.lvl (scofixFunTy g l vI vD vS .many)) f
        return .scofix l I D unitS fn s i .tt]
      (match sizePred? (cx.k.eval s) with
       | some s' =>
         let P := quote g cx.k.lvl (vInterp g l vI vD (nuFamilyAt l vI vD s') (cx.k.eval i))
         #[do return .cocon (← genTm cx P f)]
       | none => #[]) ++ (if fuel > 0 then viaCoit ++ (if w.sizes then viaScofix else #[]) else #[])
    | _ => #[]
  -- (at data and tags a variable comes first: open terms by default)
  let mut alts : Array (Gen Tm) := match Tw with
    | .mu .. | .nu .. | .enum _ => leaves ++ intro
    | _ => intro ++ leaves
  -- (a size is a variable, `∞` or `↑s`: conversion at `Size` knows no other stuck size, Sz1)
  let elims := match Tw with
    | .size | .sizeLt _ => w.sizeTypes
    | _ => true
  if fuel > 0 && elims then
    let lT := cx.lvlOf T
    alts := alts ++ #[
      (do return .ann (← genTm cx T f) T),
      -- a β-redex
      (do let A ← genTy cx 1 f
          let q : Tm := if (← choose 3) == 1 then .qlit .zero else .qlit .many
          let body ← genTm (cx.push A) (liftT 1 T) f
          let arg ← genTm cx A f
          return .app (.ann (.lam "x" body) (.pi "x" .default q A (liftT 1 T) .hole)) arg),
      -- a linear identity
      (do let t ← genTm cx T f
          return .app (.ann (.lam "x" (.var 0)) (.pi "x" .default (.qlit .one) T (liftT 1 T) .hole)) t),
      (do let A ← genTy cx 1 f
          let v ← genTm cx A f
          let body ← genTm (cx.push A) (liftT 1 T) f
          return .letE "x" (.qlit .many) A v body),
      -- `let () := u; b` (1-elimination at a unit type; computes to `b`)
      (do let l ← if (← choose 2) == 1 then pure (1 : Level) else pure 0
          let u ← genTm cx (.unit l) f
          let body ← genTm cx T f
          return .letUnit u body),
      -- projections of an annotated pair
      (do let B ← genTy cx 1 f
          let t ← genTm cx T f
          let u ← genTm cx B f
          let q ← genQ cx
          return if (← choose 2) == 0 then .fst (.ann (.pair t u) (.sigma "x" (.qlit .many) T (liftT 1 B) .hole))
            else .snd (.ann (.pair u t) (.sigma "x" q B (liftT 1 T) .hole))),
      (do let s ← genTm cx E2 f
          let a ← genTm cx T f
          let b ← genTm cx T f
          return .ecase "z" (liftT 1 T) (mkInf s E2) [a, b]),
      (do return .cast T T (.reflTy T) (← genTm cx T f)),
      -- a pair taken apart
      (do let A ← genTy cx 1 f
          let B ← genTy cx 1 f
          let S : Tm := .sigma "x" (.qlit .many) A (liftT 1 B) .hole
          let p ← genTm cx S f
          let body ← genTm ((cx.push A).push (liftT 1 B)) (liftT 2 T) f
          return .split (.qlit .many) (mkInf p S) "z" (liftT 1 T) "x" "y" body)]
    -- a cast along a hypothesis `e : A = T`
    for i in [0:cx.size] do
      if let .eqTy A B := cx.rawTy i then
        if cx.convTy B T then
          alts := alts.push (do return .cast A B (.var i) (← genTm cx A f))
    -- from an empty hypothesis
    for i in [0:cx.size] do
      if let .empty _ := whnf cx.k.types[i]! then alts := alts.push (pure (.absurd T (.var i)))
    if let some l := lT then
      -- a cast from a variant of the type, along a generated proof
      alts := alts.push (do
        let A ← variantTy cx l T f
        let e ← genTm cx (.eqTy A T) f
        let t ← genTm cx A f
        return .cast A T e t)
      alts := alts.push (do return .down (.ann (.up (← genTm cx T f)) (.ulift l l T)))
      if w.idP then
        if let some n := l.toNat? then
          alts := alts.push (do return .app (.app (.const "idP" [Level.ofNat n]) T) (← genTm cx T f))
      -- transport, into a proposition
      if l.equiv 0 then
        alts := alts.push (do
          let A ← genTy cx 1 f
          let a ← genTm cx A f
          let b ← variantTm cx A a f
          let e ← genTm cx (.eq A a b) f
          let p ← genTm cx T f
          return .transp A a (.lam "b" (.lam "e" (liftT 2 T))) p b e)
      -- eliminators with a constant motive; the kernel gives the methods' types
      for dt in w.dataTys do
        if let .mu ld I D i _ _ := cx.whq dt then
          let vI := cx.k.eval I
          let vD := cx.k.eval D
          let P : Tm := .lam "i" (.lam "x" (liftT 2 T))
          let vP := cx.k.eval P
          alts := alts.push
            (do let m ← genTm cx (quote g cx.k.lvl (indMethodTy g ld l vI vD vP .many)) f
                let x ← genTm cx dt f
                return .ind ld I D l P m i x)
          if w.sizes then alts := alts ++ #[
            (do let m ← genTm cx (quote g cx.k.lvl (scaseMethodTy g ld l vI vD vP .szInf (.qlit .many))) f
                let x ← genTm cx dt f
                return .scase ld (.qlit .many) I D l P m .szInf i x),
            (do let fn ← genTm cx (quote g cx.k.lvl (sfixFunTy g ld l vI vD vP .many)) f
                let x ← genTm cx dt f
                return .sfix ld I D l P fn .szInf i x)]
      -- `Desc.elim` with a constant motive
      alts := alts.push (do
        let I : Tm := .unit 1
        let D ← genDesc cx 0 I f
        let P : Tm := .lam "D" (liftT 1 T)
        let (ta, tb, tc, th) := delimMethodTys g 0 l (cx.k.eval I) (cx.k.eval P) .many
        let q (v : Val Q) : Tm := quote g cx.k.lvl v
        let a ← genTm cx (q ta) f
        let b ← genTm cx (q tb) f
        let c ← genTm cx (q tc) f
        let h ← genTm cx (q th) f
        return .delim l P a b c h (.ann D (.desc 0 I)))
    alts := alts ++ (← headAlts cx T f)
  pick alts (pure .tt)

end

/-! ## Samples -/

structure Sample where
  w : World
  /-- outermost first; each type in the context of the ones before it -/
  ctx : Array Tm
  /-- two types of `Sort l` and a term of the first (`T` is `Sort l`), or two terms of `T` -/
  types : Bool
  T : Tm
  t : Tm
  u : Tm
  x : Tm := .tt

def levelAlts : Array Level := #[1, 0, 2, .param "u", .succ (.param "u")]

def genCtx (w : World) (fuel : Nat) : Gen (Array Tm) := do
  let n ← choose 5
  let mut ctx : Array Tm := #[]
  for _ in [0:n] do
    let cx := mkCx w ctx ["u"]
    let alts : Array (Gen Tm) := #[pure w.nat, pure .qty, pure (.sort 1), pure E2, pure (.sort 0),
      genTy cx 1 fuel, genTy cx 0 fuel, genTy cx 2 fuel] ++ (if w.sizes then #[pure .size] else #[])
    let A ← pick alts (pure w.nat)
    ctx := ctx.push (if (cx.lvlOf A).isSome then A else .unit 1)
  return ctx

def genSample (w : World) (fixed : Option (Array Tm)) (fuel : Nat) (mode : Option Bool := none) : Gen Sample := do
  let ctx ← match fixed with
    | some c => pure c
    | none => genCtx w fuel
  let cx := mkCx w ctx ["u"]
  let l := levelAlts.getD (← choose levelAlts.size) 1
  let types ← match mode with
    | some m => pure m
    | none => do pure ((← choose 2) == 0)
  if types then
    let A ← genTy cx l fuel
    let B ← variantTy cx l A fuel
    let x ← genTm cx A (fuel - 1)
    return { w, ctx, types := true, T := .sort l, t := A, u := B, x }
  else
    let T ← genTy cx l fuel
    let t ← genTm cx T fuel
    let u ← variantTm cx T t fuel
    return { w, ctx, types := false, T, t, u }

def Sample.show (s : Sample) : String := Id.run do
  let mut names : List Name := []
  let mut out := s!"world {s.w.name}\n"
  for A in s.ctx, i in [0:s.ctx.size] do
    out := out ++ s!"  x{i} : {A.pretty names}\n"
    names := s!"x{i}" :: names
  let (a, b) := if s.types then ("A", "B") else ("t", "u")
  out := out ++ s!"  ⊢ {a} := {s.t.pretty names}\n    {b} := {s.u.pretty names}\n    : {s.T.pretty names}\n"
  if s.types then out := out ++ s!"    x := {s.x.pretty names} : A\n"
  return out

/-! ## The checks -/

structure Acc where
  cov : Std.HashMap String Nat := {}
  findings : Array (String × String) := #[]
  /-- findings attributed to a known issue: the issue, the law, the instance -/
  known : Array (String × String × String) := #[]
  /-- queries for `Kernel.wiz`: the closed term, what it is, and whether its normal form
  is asked for (otherwise its verdict) -/
  wiz : Array (MTm × String × Bool) := #[]
  wizCap : Nat := 0
  /-- how many of the queries ask for a normal form -/
  wizNf : Nat := 0
  /-- queries are distinct (by hash); those about a pair of different types are always
  taken (up to half the cap), the others from one sample in `wizStride` -/
  wizSeen : Std.HashSet UInt64 := {}
  wizPairs : Nat := 0
  wizOn : Bool := false
  /-- the pair under test is a type against itself at other levels: always asked -/
  wizLv : Bool := false
  wizLvN : Nat := 0
  /-- the queries of the targeted generator (`levelPairs`, W1): always asked, apart from
  the caps (the generator is bounded) -/
  wizTargeted : Bool := false
  samples : Nat := 0

abbrev M := StateM Acc

def hit (k : String) (n : Nat := 1) : M Unit :=
  modify fun a => { a with cov := a.cov.insert k (a.cov.getD k 0 + n) }

def bad (p : String) (msg : Unit → String) : M Unit :=
  modify fun a => { a with findings := a.findings.push (p, msg ()) }

/-- A judgment `ctx ⊢ t ⇐ T`. -/
structure Jd where
  ctx : Array Tm
  t : Tm
  T : Tm

/-- `(fun x… => t : (x… : ctx) → T)`: the judgment as a closed term both kernels infer. -/
def close (ctx : Array Tm) (t T : Tm) : Tm :=
  let (t, T) := ctx.foldr (fun A (t, T) => (Term.lam "x" t, piW A T)) (t, T)
  .ann t T

/-- `a ≡ b : T` as a typing judgment: `fun P p => p : (P : T → Type) → P a → P b`. -/
def convJd (ctx : Array Tm) (T a b : Tm) : Tm :=
  close ctx (.lam "P" (.lam "p" (.var 0)))
    (piW (piW T (.sort 1)) (piW (.app (.var 0) (liftT 1 a)) (.app (.var 1) (liftT 2 b))))

def wq (w : World) (role : String) (closed : Tm) (nf : Bool := false) (pair : Bool := false) : M Unit := do
  let a ← get
  -- (a cap for each class: level pairs 300, other pairs half of `wizCap`, the rest half)
  let room := if a.wizTargeted then true
    else if pair && a.wizLv then a.wizLvN < 300
    else if pair then a.wizPairs * 2 < a.wizCap && a.samples % 3 == 0 else a.wizOn && (a.wiz.size - a.wizPairs) * 2 < a.wizCap
  if w.wiz && room && (!nf || a.wizNf * 8 < a.wizCap) then
    if let some m := toM closed then
      let h := hash (m.toWiz, nf)
      unless a.wizSeen.contains h do
        set { a with wiz := a.wiz.push (m, role, nf), wizNf := a.wizNf + (if nf then 1 else 0),
                     wizSeen := a.wizSeen.insert h,
                     wizPairs := a.wizPairs + (if pair && !a.wizLv && !a.wizTargeted then 1 else 0),
                     wizLvN := a.wizLvN + (if pair && a.wizLv && !a.wizTargeted then 1 else 0) }

def V (w : World) (role : String) (j : Jd) : M Bool := do
  let c := close j.ctx j.t j.T
  wq w role c
  return acceptsC (hash w.name) w.g c

def names (n : Nat) : List Name := (List.range n).reverse.map (s!"x{·}")

def Jd.show (j : Jd) : String := Id.run do
  let mut ns : List Name := []
  let mut out := ""
  for A in j.ctx, i in [0:j.ctx.size] do
    out := out ++ s!"x{i} : {A.pretty ns}, "
    ns := s!"x{i}" :: ns
  return s!"{out}⊢ {j.t.pretty ns} : {j.T.pretty ns}"

/-- Substitute `a` (a term over the first `k` entries) for the `k`-th entry. -/
def instTm (n k : Nat) (a : Tm) (t : Tm) : Tm := substT t (n - 1 - k) (liftT (n - 1 - k) a)

def instCtx (ctx : Array Tm) (k : Nat) (a : Tm) : Array Tm :=
  ctx.extract 0 k ++ (Array.range (ctx.size - k - 1)).map fun d => substT ctx[k + 1 + d]! d (liftT d a)

def instJ (j : Jd) (k : Nat) (a : Tm) : Jd :=
  { ctx := instCtx j.ctx k a, t := instTm j.ctx.size k a j.t, T := instTm j.ctx.size k a j.T }

/-- Why the Lean kernel rejects a judgment. (In the pre-P2 mode, so that the marker's
requirement does not hide the real error; the marks are the pass's job.) -/
def why (g : Gl) (j : Jd) : String :=
  match infer (R := Q) { globals := { g with lazyProofs := false } } (close j.ctx j.t j.T) with
  | .ok _ => "(accepted)"
  | .error e => (toString e).replace "\n" " "

def Jd.wiz (j : Jd) : String :=
  match toM (close j.ctx j.t j.T) with
  | some m => s!"\n  as a term of Kernel.wiz: {m.toWiz}"
  | none => ""

/-- Instances for the `k`-th variable: well-typed terms over the entries before it. A
quantity variable gets every literal; other variables get the first few terms the
generator enumerates, a random one, and the earlier variables of the type. -/
def instancesFor (w : World) (ctx : Array Tm) (k : Nat) (iseed : Nat) : List Tm :=
  let pfx := ctx.extract 0 k
  let A := ctx[k]!
  let cx := mkCx w pfx
  match cx.whq A with
  | .qty => (([.qlit .one, .qlit .zero, .qlit .many] : List Tm) ++ (cx.varsOfTy .qty).toList).take 4
  | _ =>
    let cands := (([#[], #[1], #[2], #[0, 1]] : List (Array Nat)).map fun pre => (runGen pre none (genTm cx A 1)).1) ++
      [(runGen #[] (some (iseed + k)) (genTm cx A 2)).1] ++ (cx.varsOfTy A).toList
    -- (annotated when it can only be checked: an instance lands in positions that infer;
    -- mandatory sorts: the instance is the *marked* term — the sorts pass fills its
    -- `Π`/`Σ` holes — so that substituting it keeps the judgment well typed)
    ((cands.eraseDups.filterMap fun a => (cx.markAt a A).map fun a' => mkInf a' A).take 3)

def subsFor (w : World) (ctx : Array Tm) (iseed : Nat) : List (Nat × Tm) :=
  (List.range ctx.size).flatMap fun k => (instancesFor w ctx k iseed).map (k, ·)

def vHead : Val Q → String
  | .neutral h _ => match h with
    | .local _ => "var" | .global .. => "axiom" | .mvar _ => "mvar" | .eq .. => "eq" | .eqTy .. => "eqTy"
    | .cast .. => "stuck-cast" | .refl .. => "refl" | .reflTy _ => "reflTy" | .transp .. => "transp"
    | .prf .. => "proof"
  | .sort _ => "Sort" | .pi .. => "Π" | .lam .. => "λ" | .sigma .. => "Σ" | .pair .. => "pair"
  | .unit _ => "Unit" | .tt => "tt" | .empty _ => "Empty" | .qty => "Qty" | .qlit _ => "qlit"
  | .enum _ => "Enum" | .tag .. => "tag" | .desc .. => "Desc" | .dret _ => "ret" | .darg .. => "arg"
  | .drec .. => "rec" | .dhrec .. => "hrec" | .mu .. => "μ" | .con _ => "con" | .nu .. => "ν"
  | .size => "Size" | .szInf => "∞" | .szSuc _ => "↑" | .sizeLt _ => "Size<" | .cocon _ => "cocon"
  | .scofix .. => "scofix" | .coit .. => "coit" | .natLit _ => "numeral" | .ulift .. => "ULift"
  | .up _ => "up" | .unfold .. => "glued" | .lazyInd .. => "lazyInd"

/-- The head of a type, with what the kernel knows of its sort (`propSort?`). -/
def tyHead (v : Val Q) : String :=
  let v := whnf v
  let p := match v with
    | .pi .. | .sigma .. | .unit _ | .empty _ | .ulift .. => match propSort? v with
      | some true => "ᵖ" | some false => "" | none => "?"
    | _ => ""
  vHead v ++ p

def eqKind (E : Val Q) : String :=
  match whnf E with
  | .unit _ => "True"
  | .empty _ => "False"
  | .neutral (.eq ..) _ | .neutral (.eqTy ..) _ => "stuck"
  | v => vHead v

/-- Coverage of the term constructors and of the features the bugs needed. -/
partial def countTm (g : Gl) (t : Tm) (applied : Nat := 0) : StateM (Array String) Unit := do
  let add (s : String) : StateM (Array String) Unit := modify (·.push s)
  add ("ctor " ++ ctorName t)
  let qf (what : String) (q : Tm) : StateM (Array String) Unit := match q with
    | .qlit .zero => add s!"feature {what} at quantity 0"
    | .qlit .one => add s!"feature {what} at quantity 1"
    | .qlit .many => add s!"feature {what} at quantity ω"
    | _ => add s!"feature {what} at a quantity variable"
  match t with
  | .pi _ _ q _ _ σ => do qf "Π" q; add (if σ.hasHole then "feature Π with the pass's sorts" else "feature Π with its sorts")
  | .sigma _ q _ _ σ => do qf "Σ" q; add (if σ.hasHole then "feature Σ with the pass's sorts" else "feature Σ with its sorts")
  | .letE _ q .. => qf "let" q
  | .darg q .. | .drec q .. | .dhrec q .. => qf "a description field" q
  | .const n _ =>
    match g.builtinKey? n with
    | some k =>
      if k.startsWith "nat." && natOpArity k == 2 then
        add (if applied == 0 then "feature native: operation unapplied"
          else if applied == 1 then "feature native: operation partially applied (Nat.add x)"
          else "feature native: operation fully applied")
      else add (if k == "nat" then "feature native: the builtin type of numbers" else "feature native: constructor or unary operation")
    | none => match g.find? n with
      | some { value := some _, .. } => add "feature global: glued definition"
      | _ => add "feature global: axiom"
  | .cast _ _ e _ => match e with
    | .reflTy _ => add "feature cast along reflTy"
    | .var _ => add "feature cast along a hypothesis"
    | _ => add "feature cast along a built proof (suspended)"
  | .transp .. => add "feature transp (suspended proofs)"
  | .mu _ _ _ _ s _ | .nu _ _ _ _ s _ => add (if s == .szInf then "feature data at size ∞" else "feature data at a size")
  | _ => pure ()
  let _ ← mapKidsM (m := StateM (Array String))
    (fun l => do
      if !l.params.isEmpty then add "feature level variable"
      pure l)
    (fun _ c => do
      countTm g c (match t, c with
        | .app f _, c' => if f == c' then applied + 1 else 0
        | _, _ => 0)
      pure c) t

def countAll (g : Gl) (ts : List Tm) : M Unit := do
  let keys := ((ts.forM (countTm g ·)).run #[]).2
  for k in keys do hit k

/-- Rewrites of `t : T` that the theory says have the type `T` (`must`), and are
convertible with `t` (`conv`). -/
def rewrites (cx : Cx) (t T : Tm) : List (String × Bool × Bool × Tm) :=
  let ti := mkInf t T
  let base : List (String × Bool × Bool × Tm) :=
    [("an annotation", true, true, .ann t T),
     ("a let", true, true, .letE "x" (.qlit .many) T t (.var 0)),
     ("a cast along reflTy", true, false, .cast T T (.reflTy T) t)]
  let byShape : List (String × Bool × Bool × Tm) := match cx.whq T with
    | .pi .. => [("η", true, true, .lam "x" (.app (liftT 1 ti) (.var 0)))]
    | .sigma .. => [("η for pairs", false, true, .pair (.fst ti) (.snd ti))]
    | .ulift .. => [("η for up", true, true, .up (.down ti))]
    | .sort _ =>
      -- (mandatory sorts: a `Π`/`Σ` without its sorts is a hole, which the kernel rejects,
      -- so "the same term with the sorts dropped" is not a rewrite to a well-typed term)
      []
    | _ => []
  let lifted : List (String × Bool × Bool × Tm) := match cx.lvlOf T with
    | some l => [("down (up t)", true, true, .down (.ann (.up t) (.ulift l l T)))]
    | none => []
  base ++ byShape ++ lifted

/-- The laws on one judgment: normal forms (P6), conversion as an equivalence on the
judgment's rewrites and `extra` (P2), `sameVal` (P6), and every substitution instance
(P1, P2, P3). `ps` are the level parameters the judgment mentions. -/
def lawsOn (w : World) (what : String) (j : Jd) (extra : List Tm) (subs : List (Nat × Tm))
    (ps : List String) (derived : Bool := false) : M Unit := do
  -- (a derived judgment, an equation or a cast: one instance for each variable)
  let subs := if !derived then subs else
    subs.filter fun (k, a) => (subs.find? (·.1 == k)).map (·.2) == some a
  let g := w.g
  let cx := mkCx w j.ctx
  let k := cx.k
  -- (P2, mandatory sorts) the judgment as the elaborator delivers it: the sorts pass
  -- fills the type too (a hole in it is a kernel error, and it is quoted as `nT` and as
  -- `close`'s codomain), then the marking pass the term. Everything below (evaluation,
  -- conversion, substitution, the rewrites) is about that judgment.
  let T := (Mark.infer cx.k j.T).1
  let j : Jd := { j with T, t := cx.markKnown j.t T }
  let n := j.ctx.size
  let vT := k.eval j.T
  let vt := k.eval j.t
  let nt := quote g k.lvl vt
  let nT := quote g k.lvl vT
  let lv := if ps.isEmpty then "" else s!" (level variables {ps})"
  let ctxOf (m : String) : Unit → String := fun _ => s!"{what}{lv}: {m}\n  {j.show}{j.wiz}"
  hit "law P6 normal forms"
  hit s!"value  {vHead vt}"
  hit s!"value  {vHead (whnf vt)}  (weak head normal)"
  unless ← V w "a normal form" { j with t := nt } do
    bad "P6 a normal form is ill typed" fun _ =>
      ctxOf s!"normal form {nt.pretty (names n)}\n  the kernel: {why g { j with t := nt }}" ()
  unless conv g k.tys vT vt (k.eval nt) do
    bad "P6 quote∘eval is not the identity" fun _ => ctxOf s!"normal form {nt.pretty (names n)}" ()
  unless Wiz.convTy g k.tys vT (k.eval nT) do
    bad "P6 quote∘eval is not the identity (type)" (ctxOf s!"normal form of the type {nT.pretty (names n)}")
  wq w "t ≡ its normal form" (convJd j.ctx j.T j.t nt)
  wq w "a normal form (of the judgment as a closed term)" (close j.ctx j.t j.T) (nf := true)
  -- the set conversion is tested on
  let mut set : Array (String × Tm) := #[("the term", j.t), ("its normal form", nt)]
  for (name, must, cv, r) in (if derived then [] else rewrites cx j.t j.T) do
    if ← V w name { j with t := r } then
      set := set.push (name, cx.markKnown r j.T)
      hit "law L3 rewrites"
      if cv && !conv g k.tys vT vt (k.eval r) then
        bad s!"L3 a term is not convertible with {name}" (ctxOf s!"rewrite {r.pretty (names n)}")
    else if must then
      bad s!"L3 {name} of a well-typed term is ill typed" fun _ =>
        ctxOf s!"rewrite {r.pretty (names n)}\n  the kernel: {why g { j with t := r }}" ()
  for e in extra do set := set.push ("the other term", cx.markKnown e j.T)
  let vals := set.map fun (_, a) => k.eval a
  let m := vals.size
  let rel : Array (Array Bool) := vals.map fun a => vals.map fun b => conv g k.tys vT a b
  let pr (i : Nat) : String := s!"{set[i]!.1} {set[i]!.2.pretty (names n)}"
  let ge : Gl := { g with quoteErasesProofs := true }
  let syn := vals.map fun a => quote ge k.lvl a
  for i in [0:m] do
    hit "law P2 reflexive"
    unless rel[i]![i]! do bad "P2 conversion is not reflexive" (ctxOf (pr i))
    for i' in [i+1:m] do
      hit "law P2 symmetric"
      unless rel[i]![i']! == rel[i']![i]! do
        bad "P2 conversion is not symmetric" (ctxOf s!"{pr i}\n  and {pr i'}")
      hit "law P6 sameVal"
      -- (P2: `sameVal` is gone. The kernel's remaining value comparison is `convGlued`'s
      -- shortcut: erase-mode read-back and `==` (`syn`, above). So the law is that this
      -- comparison never identifies inconvertible values; the read-back's faithfulness is
      -- what makes it true, and S1 was an instance of it failing.)
      let sv := syn[i]! == syn[i']!
      if sv && !rel[i]![i']! then
        bad "P6 the kernel's erase-mode comparison identifies inconvertible values"
          (ctxOf s!"{pr i}\n  and {pr i'}")
    for i' in [0:m] do
      for i'' in [0:m] do
        hit "law P2 transitive"
        if rel[i]![i']! && rel[i']![i'']! && !rel[i]![i'']! then
          bad "P2 conversion is not transitive" (ctxOf s!"{pr i}\n  ≡ {pr i'}\n  ≡ {pr i''}")
  -- substitution instances
  for (kk, a) in subs do
    let j' := instJ j kk a
    let isQ := cx.whq (liftT (n - kk) j.ctx[kk]!) == .qty
    let which := if isQ then "a quantity variable" else "a term variable"
    let inst : Unit → String := fun _ =>
      ctxOf s!"x{kk} := {a.pretty (names kk)}\n  instance: {j'.show}\n  the kernel, of the instance: {why g j'}{j'.wiz}" ()
    hit s!"law P1 substitution for {which}"
    unless ← V w "a substitution instance" j' do
      bad s!"P1 typing is not stable under substitution for {which}" inst
      continue
    unless ← V w "a substitution instance, at the normal form of the type" { j' with T := instTm n kk a nT } do
      bad s!"P1 typing at the type's normal form is not stable under substitution for {which}" inst
      continue
    let cx' := mkCx w j'.ctx
    let k' := cx'.k
    let vT' := k'.eval j'.T
    let set' := set.map fun (_, x) => instTm n kk a x
    -- (the rewrites and the other term are well typed after the substitution, by P1 again;
    -- checked, for the term's normal form, the other term and two rewrites)
    let ok' := (set'.zip (Array.range m)).map fun (x, i) =>
      (i < 4 || i + extra.length ≥ m) && cx'.chk x j'.T
    let vals' := (set'.zip ok').map fun (x, ok) => if ok then k'.eval x else .tt
    hit "law P3 evaluation commutes with substitution"
    unless ok'[1]! do
      bad "P3 the instance of a normal form is ill typed" fun _ =>
        inst () ++ s!"\n  the kernel, of the normal form's instance: {why g { j' with t := set'[1]! }}"
      continue
    unless conv g k'.tys vT' vals'[0]! vals'[1]! do
      bad "P3 evaluation does not commute with substitution" fun _ =>
        inst () ++ s!"\n  normal form before: {nt.pretty (names n)}\n  its instance: {set'[1]!.pretty (names (n - 1))}\n  normal form after: {(cx'.nf j'.t).pretty (names (n - 1))}"
    unless Wiz.convTy g k'.tys vT' (k'.eval (instTm n kk a nT)) do
      bad "P3 evaluation does not commute with substitution (type)" inst
    wq w "the instance of the normal form ≡ the instance" (convJd j'.ctx j'.T j'.t set'[1]!)
    -- (against the term itself: the other pairs follow by symmetry and transitivity)
    for i in [0:1] do
      for i' in [i+1:m] do
        if rel[i]![i']! && ok'[i]! && ok'[i']! then
          hit "law P2 stable under substitution"
          unless conv g k'.tys vT' vals'[i]! vals'[i']! do
            bad "P2 conversion is not stable under substitution" fun _ =>
              inst () ++ s!"\n  {pr i}\n  ≡ {pr i'}\n  but not their instances"
  -- level instances
  unless ps.isEmpty do
    for l in ([0, 1, 2, .succ (.param "v")] : List Level) do
      let us := ps.map fun _ => l
      let jl : Jd := { ctx := j.ctx.map (instLv ps us), t := instLv ps us j.t, T := instLv ps us j.T }
      let inst : Unit → String := fun _ =>
        ctxOf s!"{ps} := {l}\n  instance: {jl.show}\n  the kernel, of the instance: {why g jl}" ()
      hit "law P1 substitution for a level variable"
      unless ← V w "a level instance" jl do
        bad "P1 typing is not stable under substitution for a level variable" inst
        continue
      let cxl := mkCx w jl.ctx
      let vTl := cxl.k.eval jl.T
      let ntl := instLv ps us nt
      unless cxl.chk ntl jl.T do
        bad "P3 the level instance of a normal form is ill typed" fun _ =>
          inst () ++ s!"\n  the kernel, of the normal form's instance: {why g { jl with t := ntl }}"
        continue
      unless conv g cxl.k.tys vTl (cxl.k.eval jl.t) (cxl.k.eval ntl) do
        bad "P3 evaluation does not commute with level substitution" inst

/-- A type equation `A = B` in `ctx`: the rule reached (coverage), `False` against
conversion, and `False`/`True` under every instance (P4). -/
def tyPair (w : World) (ctx : Array Tm) (A B : Tm) (subs : List (Nat × Tm)) (tag : String := "") : M Unit := do
  let g := w.g
  let cx := mkCx w ctx
  let k := cx.k
  let n := ctx.size
  let vA := k.eval A
  let vB := k.eval B
  let kind := eqKind (vEqType g vA vB)
  let back := eqKind (vEqType g vB vA)
  let c := Wiz.convTy g k.tys vA vB
  hit s!"type equality  {tyHead vA} = {tyHead vB}  ↦ {kind}"
  let pr : Unit → String := fun _ =>
    s!"{(Jd.mk ctx A (.sort 0)).show}\n  A := {A.pretty (names n)}\n  B := {B.pretty (names n)}"
  hit "law P4 type equations"
  if kind == "False" && c then bad "P4 convertible types whose equation computes to False" pr
  if (kind == "False") != (back == "False") then bad "P4 (A = B) is False but (B = A) is not" pr
  if kind == "True" && !c then bad "P4' the equation computes to True but the types are not convertible" pr
  hit "law P6 sameVal"
  -- (P2: as in `lawsOn` — the kernel's erase-mode read-back comparison, `convGlued`'s)
  let ge : Gl := { g with quoteErasesProofs := true }
  let sv := quote ge k.lvl vA == quote ge k.lvl vB
  if sv && !c then bad "P6 the kernel's erase-mode comparison identifies inconvertible values" pr
  -- (for `Kernel.wiz`: conversion of the two types, and the same two facts, as judgments)
  modify fun a => { a with wizLv := B == bumpLevels A && A != B }
  -- (not a pair that differs in a quantity only: at a proposition that is K1, pinned)
  if A != B && flipQ A != some B then
    if let some l := cx.lvlOf A then wq w (tag ++ "P2: A ≡ B (two types)") (convJd ctx (.sort l) A B) (pair := true)
    wq w (tag ++ "P4: does (A = B) compute to False?") (close ctx (.lam "e" (.var 0)) (piW (.eqTy A B) (.empty 0))) (pair := true)
    wq w (tag ++ "P4: does (A = B) compute to True?") (close ctx .tt (.eqTy A B)) (pair := true)
  for (kk, a) in subs do
    let ctx' := instCtx ctx kk a
    let A' := instTm n kk a A
    let B' := instTm n kk a B
    -- (instances of well-typed types: P1, checked on the judgment itself)
    let cx' := mkCx w ctx'
    unless (cx'.lvlOf A').isSome && (cx'.lvlOf B').isSome do continue
    let vA' := cx'.k.eval A'
    let vB' := cx'.k.eval B'
    let kind' := eqKind (vEqType g vA' vB')
    let c' := Wiz.convTy g cx'.k.tys vA' vB'
    let inst : Unit → String := fun _ =>
      pr () ++ s!"\n  x{kk} := {a.pretty (names kk)}\n  A' := {A'.pretty (names (n - 1))}\n  B' := {B'.pretty (names (n - 1))}\n  (A' = B') ↦ {kind'}"
    hit "law P4 type equations under substitution"
    if kind == "False" && c' then
      bad "P4 an equation computes to False, and an instance of its sides is convertible" inst
    else if kind == "False" && kind' != "False" then
      bad "P4 an equation computes to False, and an instance of it does not" inst
    if kind == "True" && kind' != "True" then
      bad "P4 an equation computes to True, and an instance of it does not" inst
    if c && !c' then bad "P2 conversion of types is not stable under substitution" inst

/-! ### A targeted generator: one constant at two levels (W1)

W1 (`wiz-notes/kernel-lint.md`, fixed by #76): `Kernel.wiz`'s `headSame` compared two
constants by name, so `d.{0}` and `d.{1}` in the spines of two glued values were "the
same", and two stuck cases whose environments differed only in a level instance were
convertible. The general generator does not build that shape (`prop-harness.md` §6a): it
needs a level-polymorphic constant as an argument of a glued global or of a variable, the
whole stuck, compared against itself at another level. This generator builds exactly that:
a proposition-valued polymorphic constant `c` (a gadget of the world whose type does not
depend on its level), at two levels, under up to two wrappers from

* `caseF · x` (a glued global, a case on its argument, stuck on a variable `x : Enum 1`),
* `P ·` (a variable `P : Prop → Prop`: a neutral spine),

in the fixed context `x0 : Enum 1, P : Prop → Prop, x2 : Enum 1`. Every choice sequence is
enumerated (`levelPairSeqs`); each pair goes to `tyPair` (the laws in the Lean kernel, and
its three queries for `Kernel.wiz`, always asked). -/

/-- the context of the targeted pairs -/
def lvCtx : Array Tm := #[.enum (MTm.labels 1), piW (.sort 0) (.sort 0), .enum (MTm.labels 1)]
/-- the two levels (a pair at one level is the same type twice, which `tyPair` does not
send: the controls are the general generator's) -/
def lvPairs : Array (Nat × Nat) := #[(0, 1), (1, 2), (2, 0)]

/-- the polymorphic propositions of a world: gadgets `c.{l}` of type `Prop` -/
def lvConsts (w : World) : Array Name :=
  (w.gadgets.filterMap fun (c, T) => match c, T with
    | .const n [_], .sort l => if levelIs l 0 then some n else none
    | _, _ => none).toArray

def genLvPair (w : World) : Gen (Option (Tm × Tm)) := do
  let cs := lvConsts w
  if cs.isEmpty then return none
  let n := cs[← choose cs.size]!
  let (l, l') := lvPairs[← choose lvPairs.size]!
  -- (in `lvCtx`: x0 = var 2, P = var 1, x2 = var 0)
  let wrappers : Array (Tm → Tm) :=
    #[fun e => .app (.app (.const "caseF" []) e) (.var 2),
      fun e => .app (.app (.const "caseF" []) e) (.var 0),
      fun e => .app (.var 1) e]
  let depth ← choose 3
  let mut ws : Array (Tm → Tm) := #[]
  for _ in [0:depth] do
    ws := ws.push wrappers[← choose wrappers.size]!
  let mkAt (u : Nat) : Tm := ws.foldl (fun e f => f e) (.const n [Level.ofNat u])
  return some (mkAt l, mkAt l')

/-- every choice sequence of `genLvPair` (a full enumeration: the tree is small) -/
partial def levelPairSeqs (w : World) (pre : Array Nat := #[]) : Array (Array Nat) :=
  let log := (runGen pre none (genLvPair w)).2.log
  if h : pre.size < log.size then
    let k := log[pre.size].2
    (List.range k).foldl (fun acc c => acc ++ levelPairSeqs w (pre.push c)) #[]
  else #[pre]

/-- The targeted pairs of a world, into the accumulator. -/
def levelPairs (w : World) (iseed : Nat) : M Unit := do
  unless w.wiz && (w.heads.contains (.const "caseF" [])) do return
  modify fun a => { a with wizTargeted := true }
  let subs := subsFor w lvCtx iseed
  let cx := mkCx w lvCtx
  for pre in levelPairSeqs w do
    let (some (A, B), _) := runGen pre none (genLvPair w) | continue
    -- (both sides must be types: every wrapper keeps `Prop`)
    unless (cx.lvlOf A).isSome && (cx.lvlOf B).isSome do
      bad "W1 generator: a generated side is ill typed" fun _ => s!"{A.pretty (names 3)}  /  {B.pretty (names 3)}"
      continue
    hit "W1 generator: a constant at two levels, in a stuck spine"
    tyPair w lvCtx A B subs (tag := "W1 pair: ")
  modify fun a => { a with wizTargeted := false, wizLv := false }

def castKind (g : Gl) (lvl : Nat) (x C : Val Q) : String :=
  match whnf C with
  | .neutral (.cast ..) _ => "stuck"
  | C' => if quote g lvl C' == quote g lvl (whnf x) then "the term itself" else vHead C'

/-- Everything checked on one sample. `iseed` seeds the random substitution instances. -/
def checkSample (s : Sample) (iseed : Nat) : M Unit := do
  let w := s.w
  let g := w.g
  let j : Jd := { ctx := s.ctx, t := s.t, T := s.T }
  hit "sample generated"
  unless ← V w "a generated judgment" j do
    hit "sample ill typed (discarded)"
    return
  hit (if s.types then "sample: two types" else "sample: two terms")
  let uOk ← V w "a generated judgment" { j with t := s.u }
  let cx := mkCx w s.ctx
  let k := cx.k
  let n := s.ctx.size
  let subs := subsFor w s.ctx iseed
  let ps := lvParams (close s.ctx (.pair s.t s.u) s.T)
  -- (P2: the coverage of `prf` is the pass's output on the judgment's term)
  let tM := cx.markKnown s.t s.T
  countAll g (s.ctx.toList ++ [s.T, tM] ++ (if uOk then [s.u] else []))
  lawsOn w "the judgment" j (if uOk && s.u != s.t then [s.u] else []) subs ps
  if s.types then
    -- instances of the type that stay in the context: two instances of one schema
    let kept : List Tm := subs.filterMap fun (kk, a) =>
      let B := replT s.t (n - 1 - kk) (liftT (n - kk) a)
      if B != s.t then some B else none
    let Bs := (if uOk then [s.u] else []) ++ kept.take 2
    for B in Bs, bi in [0:Bs.length] do
      tyPair w s.ctx s.t B subs
      -- the equation itself, as a judgment (its normal form is the kernel's own term: L4)
      lawsOn w "a type equation" { ctx := s.ctx, t := .eqTy s.t B, T := .sort 0 } [] subs ps (derived := true)
      -- a cast along a hypothetical proof
      if bi < 2 && cx.chk s.x s.t then
        let ctx2 := s.ctx.push (.eqTy s.t B)
        let jc : Jd := { ctx := ctx2, t := .cast (liftT 1 s.t) (liftT 1 B) (.var 0) (liftT 1 s.x), T := liftT 1 B }
        if ← V w "a cast along a hypothesis" jc then
          let cx2 := mkCx w ctx2
          let vx := cx2.k.eval (liftT 1 s.x)
          let vA := cx2.k.eval (liftT 1 s.t)
          let vB := cx2.k.eval (liftT 1 B)
          let C := vCast g vA vB (Val.var n) vx
          hit s!"cast  {tyHead vA} ⟶ {tyHead vB}  ↦ {castKind g (n + 1) vx C}"
          lawsOn w "a cast" jc [] (subsFor w ctx2 iseed) ps (derived := true)
        else bad "a cast between two types of one sort is ill typed" fun _ => s!"{jc.show}\n  the kernel: {why g jc}"
  else if uOk then
    -- the equation between the two terms
    if let some l := cx.lvlOf s.T then
      if l.isNeverZero then
        let vT := k.eval s.T
        let vt := k.eval s.t
        let vu := k.eval s.u
        let kind := eqKind (vEq g vT vt vu)
        let c := conv g k.tys vT vt vu
        hit s!"equality at  {tyHead vT}  ↦ {kind}"
        let je : Jd := { ctx := s.ctx, t := .eq s.T s.t s.u, T := .sort 0 }
        if kind == "False" && c then bad "P4 convertible terms whose equation computes to False" fun _ => je.show
        if kind == "True" && !c then
          bad "P4' the equation computes to True but the terms are not convertible" fun _ => je.show
        lawsOn w "an equation" je [] subs ps (derived := true)

/-! ## Running: enumeration, sampling, shrinking -/

structure Plan where
  w : World
  fixed : Option (Array Tm)
  fuel : Nat
  /-- two types (`true`), two terms (`false`), or chosen by the sequence -/
  mode : Option Bool := none

def Plan.gen (p : Plan) (pre : Array Nat) (rnd : Option Nat) : Sample × GS :=
  runGen pre rnd (genSample p.w p.fixed p.fuel p.mode)

def Plan.modeArg (p : Plan) : String := match p.mode with
  | some true => "types" | some false => "terms" | none => "any"

/-- The choice sequences one deviation further than `pfx`: at one later choice, an
alternative that is not the default (the generator is run to learn the arities). -/
def children (p : Plan) (pfx : Array Nat) : Array (Array Nat) := Id.run do
  let log := (p.gen pfx none).2.log
  let mut out := #[]
  for i in [pfx.size:log.size] do
    for v in [1:log[i]!.2] do
      out := out.push ((log.extract 0 i).map (·.1) |>.push v)
  return out

def sampleEvenly {α : Type} [Inhabited α] (xs : Array α) (n : Nat) : Array α :=
  if xs.size ≤ n then xs else (Array.range n).map fun i => xs[i * xs.size / n]!

/-- The enumeration: every sequence with at most one choice that is not the default,
and of those with `2 … d`, an even sample of `perLevel`. Also how many there were at
each depth. -/
def enumeration (p : Plan) (d perLevel : Nat) : Array (Array Nat) × List (Nat × Nat) := Id.run do
  let mut all : Array (Array Nat) := #[#[]]
  let mut level : Array (Array Nat) := #[#[]]
  let mut counts : List (Nat × Nat) := []
  for depth in [1:d + 1] do
    let next := level.flatMap (children p)
    level := if depth == 1 then next else sampleEvenly next perLevel
    counts := counts ++ [(level.size, next.size)]
    all := all ++ level
  return (all, counts)

def runSeq (p : Plan) (pre : Array Nat) (iseed : Nat) (acc : Acc) : Acc :=
  ((checkSample (p.gen pre none).1 iseed).run acc).2

def Plan.strict (p : Plan) : Plan := { p with w := { p.w with strict := true } }

/-- The findings of a sequence, each with the known issue it is attributed to (`""`:
none). **U5**: the law holds on the same sample when every `Π`/`Σ` carries its sort. -/
def findingsOf (p : Plan) (pre : Array Nat) (iseed : Nat) (fs : Array (String × String)) :
    Array (String × String × String) :=
  if fs.isEmpty then #[] else
  let strict := (runSeq p.strict pre iseed {}).findings.map (·.1)
  let has (msg frag : String) : Bool := (msg.splitOn frag).length > 1
  fs.map fun (law, msg) =>
    let illTyped := has law "ill typed"
    -- Sz2: `scase … ∞ i (con xs)` reduces to `m ∞ i xs`, and `∞` is not a `Size< ∞`
    let issue := if illTyped && has msg "is not below" then "Sz2"
      -- U5b: `vCast` computes at a Π/Σ whose sort depends on a level variable, where
      -- `vEqType` is stuck: the reduct projects a proof that has no Σ type
      else if illTyped && has msg "(level variables" then "U5b"
      else if !p.w.strict && !strict.contains law then "U5"
      else ""
    (issue, law, msg)

/-- Shrink a failing choice sequence: shorter, then smaller choices, while the same law
still fails (with the same attribution). -/
partial def shrink (p : Plan) (issue law : String) (iseed : Nat) (seq : Array Nat) (budget : Nat) : Array Nat := Id.run do
  let fails (s : Array Nat) : Bool :=
    (findingsOf p s iseed (runSeq p s iseed {}).findings).any fun (i, l, _) => i == issue && l == law
  let mut cur := seq
  let mut left := budget
  let mut progress := true
  while progress && left > 0 do
    progress := false
    -- drop a suffix, then single choices, then lower choices
    let mut cands : Array (Array Nat) := #[]
    for i in [0:cur.size] do cands := cands.push (cur.extract 0 i)
    for i in [0:cur.size] do cands := cands.push (cur.extract 0 i ++ cur.extract (i + 1) cur.size)
    for i in [0:cur.size] do
      if cur[i]! > 0 then
        cands := cands.push (cur.set! i 0)
        if cur[i]! > 1 then cands := cands.push (cur.set! i (cur[i]! - 1))
    for c in cands do
      if left == 0 then break
      left := left - 1
      if c != cur && fails c then
        cur := c
        progress := true
        break
  return cur

def strip0 (s : Array Nat) : Array Nat := Id.run do
  let mut s := s
  while s.size > 0 && s.back! == 0 do s := s.pop
  return s

structure Budget where
  /-- deviations enumerated per context, and the cap on samples per context at each
  number of deviations above one -/
  dev : Nat := 2
  perCtx : Nat := 1200
  /-- the same cap for the enumeration of pairs of terms -/
  termsPerCtx : Nat := 300
  /-- the fuel (depth of eliminations) of the enumerated samples -/
  enumFuel : Nat := 2
  /-- random samples per world, and their largest fuel -/
  random : Nat := 600
  fuel : Nat := 2
  seed : Nat := 20261110
  wizCap : Nat := 0

initialize startRef : IO.Ref Nat ← IO.mkRef 0
/-- `tests --prop-no-sizes`, `tests --prop-trace` -/
initialize noSizesRef : IO.Ref Bool ← IO.mkRef false
initialize traceRef : IO.Ref Bool ← IO.mkRef false

def Plan.ctxArg (p : Plan) : String := match p.fixed with
  | some c => toString ((p.w.fixed.findIdx? (· == c)).getD 0)
  | none => "-"

/-- Run one sequence; report (shrunk) the first finding of each law. -/
def runOne (p : Plan) (pre : Array Nat) (iseed : Nat) (acc : Acc) (seen : List String) : IO (Acc × List String) := do
  -- (`tests --prop-trace`: each sample before it is checked, to find the one that panics)
  if ← traceRef.get then
    IO.eprintln s!"@ tests --prop-replay {p.w.name} {p.ctxArg} {p.modeArg} {p.fuel} {iseed} {" ".intercalate (pre.toList.map toString)}"
    IO.eprintln (p.gen pre none).1.show
  let r := runSeq p pre iseed { acc with findings := #[], samples := acc.samples + 1, wizOn := acc.samples % 12 == 0 }
  let fs := findingsOf p pre iseed r.findings
  let mut seen := seen
  for (issue, law, _) in fs do
    if seen.contains (issue ++ law) then continue
    seen := (issue ++ law) :: seen
    let start ← IO.monoMsNow
    let small := strip0 (shrink p issue law iseed pre 500)
    let s := (p.gen small none).1
    let detail := ((runSeq p small iseed {}).findings.find? (·.1 == law)).map (·.2) |>.getD "?"
    let mark := if issue == "" then "✗" else s!"(known issue {issue})"
    IO.println s!"\n{mark} {law}\n  found {start - (← startRef.get)} ms into the run; shrunk in {(← IO.monoMsNow) - start} ms; replay: tests --prop-replay {p.w.name} {p.ctxArg} {p.modeArg} {p.fuel} {iseed} {" ".intercalate (small.toList.map toString)}\n{s.show}  {detail}"
  let real := fs.filter (·.1 == "")
  let known := fs.filter (·.1 != "")
  return ({ r with findings := acc.findings ++ real.map (·.2), known := acc.known ++ known }, seen)

/-- Run the harness on a world; the accumulated coverage, findings (shrunk) and queries. -/
def runWorld (w : World) (b : Budget) (acc : Acc) (seen : List String) : IO (Acc × List String) := do
  let mut acc := acc
  let mut seen := seen
  -- the targeted pairs (W1), before the caps of the general queries fill up
  acc := ((levelPairs w b.seed).run acc).2
  -- enumeration
  for ctx in w.fixed do
    for types in [true, false] do
      let p : Plan := { w, fixed := some ctx, fuel := b.enumFuel, mode := some types }
      let (all, counts) := enumeration p b.dev (if types then b.perCtx else b.termsPerCtx)
      IO.println s!"  ({w.name}, context of {ctx.size}, two {if types then "types" else "terms"}: {all.size} enumerated; taken/all at each number of deviations: {counts})"
      for pre in all do
        (acc, seen) ← runOne p pre b.seed acc seen
  -- random sampling, over generated contexts
  let mut seed := b.seed
  for i in [0:b.random] do
    seed := lcg seed
    let p : Plan := { w, fixed := none, fuel := 1 + i % b.fuel }
    let pre := (p.gen #[] (some seed)).2.log.map (·.1)
    (acc, seen) ← runOne p pre seed acc seen
  return (acc, seen)

/-- The rules of type equality and of casts that the default run must reach (from
`vEqType` and `vCast` in `Wiz/Core/Eval.lean`; `wiz-notes/prop-harness.md` lists the arms
that are not here, and why). -/
def requiredRules : List String :=
  (["Π = Π  ↦ Σ", "Π = Π  ↦ False", "Π = Π  ↦ stuck", "Σ = Σ  ↦ Σ", "Σ = Σ  ↦ False", "Σ = Σ  ↦ stuck",
    "Πᵖ = Πᵖ  ↦ Σ", "Π? = Π?  ↦ stuck", "Sort = Sort  ↦ True", "Unit = Unit  ↦ True",
    "Empty = Empty  ↦ True", "Enum = Enum  ↦ True", "Enum = Enum  ↦ False", "Desc = Desc  ↦ True",
    "ULift = ULift  ↦ Σ", "ULift = ULift  ↦ True", "ULiftᵖ = ULiftᵖ  ↦ Σ",
    -- (`μ = μ` computes to `True` or, with description equality (PR #40), to a Σ: not required)
    "μ = μ  ↦ stuck", "ν = ν  ↦ stuck", "Unit = Enum  ↦ False", "Unit = var  ↦ stuck"].map
      ("type equality  " ++ ·)) ++
  (["Π ⟶ Π  ↦ λ", "Π ⟶ Π  ↦ stuck", "Σ ⟶ Σ  ↦ pair", "Σ ⟶ Σ  ↦ stuck", "Sort ⟶ Sort  ↦ the term itself",
    "Unit ⟶ Unit  ↦ tt", "Enum ⟶ Enum  ↦ the term itself", "Enum ⟶ Enum  ↦ stuck", "ULift ⟶ ULift  ↦ up",
    "Unitᵖ ⟶ Unitᵖ  ↦ stuck", "μ ⟶ μ  ↦ the term itself", "μ ⟶ μ  ↦ con", "μ ⟶ μ  ↦ stuck",
    "ν ⟶ ν  ↦ cocon", "ν ⟶ ν  ↦ stuck", "Unit ⟶ Enum  ↦ stuck", "var ⟶ var  ↦ stuck"].map ("cast  " ++ ·)) ++
  ["feature Π at a quantity variable", "feature Σ at a quantity variable", "feature level variable",
   "feature native: operation partially applied (Nat.add x)", "feature global: glued definition",
   "feature cast along a built proof (suspended)", "feature transp (suspended proofs)",
   "feature cast along a hypothesis", "feature let at quantity ω", "feature data at a size",
   "W1 generator: a constant at two levels, in a stuck spine"]


def padRight (s : String) (n : Nat) : String := s ++ "".pushn ' ' (n - s.length)

/-- Print the coverage table; the rows that fail the gate. -/
def coverage (acc : Acc) (thin : Nat) (sizes : Bool := true) : IO (List String) := do
  let rows := acc.cov.toList.toArray.qsort (fun a b => a.1 < b.1)
  let mut failed : List String := []
  IO.println "\n── coverage"
  for (k, n) in rows do
    IO.println s!"  {padRight k 78} {n}{if n < thin then "   (thin)" else ""}"
  for c in allCtors do
    if exemptCtors.contains c || (!sizes && ["size", "szSuc", "sizeLt", "sfix", "scase", "scofix", "cocon"].contains c) then continue
    if acc.cov.getD ("ctor " ++ c) 0 == 0 then
      IO.println s!"  {padRight ("ctor " ++ c) 78} 0   ✗"
      failed := s!"constructor {c}" :: failed
  for (k, _) in rows do
    if k.startsWith "ctor " && !allCtors.contains (k.drop 5).toString then failed := s!"unknown {k}" :: failed
  -- (without sizes the rows that need sized data are not required: only the constructors)
  for r in (if sizes then requiredRules else []) do
    if acc.cov.getD r 0 == 0 then
      IO.println s!"  {padRight r 78} 0   ✗"
      failed := r :: failed
  return failed

def summarize (acc : Acc) : IO Unit := do
  let known := acc.known.toList.map (fun (i, l, _) => (i, l)) |>.eraseDups
  unless known.isEmpty do
    IO.println "\n── known issues (not gated)"
    for (i, l) in known do
      IO.println s!"  {(acc.known.filter fun (i', l', _) => i' == i && l' == l).size} × {i}: {l}"
  let laws := acc.findings.toList.map (·.1) |>.eraseDups
  unless laws.isEmpty do
    IO.println "\n── findings"
    for l in laws do
      IO.println s!"  {(acc.findings.filter (·.1 == l)).size} × {l}"

/-- Without sizes: no context, head or gadget that mentions one. -/
def World.noSizes (w : World) : World :=
  { w with
    sizes := false
    heads := w.heads.filter (!mentionsSize ·)
    gadgets := w.gadgets.filter fun (t, ty) => !mentionsSize t && !mentionsSize ty
    gadgetTys := w.gadgetTys.filter fun (ty, _) => !mentionsSize ty
    fixed := w.fixed.filter fun c => !c.any mentionsSize }

def sizedCtors : List String := ["size", "szSuc", "sizeLt", "sfix", "scase", "scofix", "cocon"]

def worlds : IO (List World) := do
  let ws := [sharedWorld (), ← nativeWorld]
  -- (`leanGlobals` skips a declaration the kernel rejects: a query about it would vanish)
  for (n, _, _, _) in MTm.globalDefs do
    unless (ws.head?.map (·.g.contains n)).getD false do
      throw (IO.userError s!"the differential test's global {n} is rejected by the Lean kernel")
  for w in ws do
    for h in w.heads do
      if (typeOfClosed w.g h).isNone then throw (IO.userError s!"world {w.name}: a head is ill typed: {h.pretty}")
  return if ← noSizesRef.get then ws.map World.noSizes else ws


def runLean (b : Budget) : IO Acc := do
  let mut acc : Acc := { wizCap := b.wizCap }
  let mut seen : List String := []
  startRef.set (← IO.monoMsNow)
  for w in ← worlds do
    let start ← IO.monoMsNow
    (acc, seen) ← runWorld w b acc seen
    IO.println s!"  (world {w.name}: {(← IO.monoMsNow) - start} ms)"
    memoStats s!"world {w.name}"
  return acc

/-- `tests --prop-replay WORLD CTX MODE FUEL ISEED CHOICE…`: one sample again, with
everything the harness finds on it (`CTX`: the number of an enumeration context, or `-`;
`MODE`: `types`, `terms` or `any`). -/
def replayMain (args : List String) : IO UInt32 := do
  match args with
  | wn :: ctx :: mode :: fuel :: iseed :: choices =>
    let some w := (← worlds).find? (·.name == wn) | do IO.eprintln s!"no world {wn}"; pure 2
    let m : Option Bool := if mode == "types" then some true else if mode == "terms" then some false else none
    let p : Plan := { w, fixed := ctx.toNat? >>= (w.fixed[·]?), fuel := fuel.toNat!, mode := m }
    let pre := (choices.filterMap String.toNat?).toArray
    let s := (p.gen pre none).1
    IO.println s.show
    let acc := runSeq p pre iseed.toNat! {}
    for (issue, law, msg) in findingsOf p pre iseed.toNat! acc.findings do
      IO.println s!"{if issue == "" then "✗" else s!"(known issue {issue})"} {law}\n  {msg}\n"
    IO.println s!"{acc.findings.size} findings"
    pure 0
  | _ => do IO.eprintln "usage: --prop-replay WORLD CTX MODE FUEL ISEED CHOICE…"; pure 2

def leanCase (b : Budget) : IO Unit := do
  memoReset
  let acc ← runLean b
  let failed ← coverage acc 10 (sizes := !(← noSizesRef.get))
  summarize acc
  unless acc.findings.isEmpty do
    throw (IO.userError s!"{(acc.findings.toList.map (·.1)).eraseDups.length} laws violated ({acc.findings.size} instances)")
  unless failed.isEmpty do
    throw (IO.userError s!"coverage gate: nothing generated reaches {failed}")

/-! ## `Kernel.wiz` -/

def wizVerdict (g : Gl) (t : MTm) : String :=
  -- (P2) each side marks with its own pass, as `Tests/Elab`'s differential test does
  let k := mkeyOf kWizVerdict wizTag [] t.toTerm
  match memoFind memo k with
  | some a => a.text
  | none =>
    let s := match markInf g t.toTerm with
      | none => "error"
      | some t' => match infer (R := Q) { globals := g } t' with
        | .ok (ty, _) => match MTm.ofTerm (quote g 0 ty) with
          | some m => m.pretty 0
          | none => "?"
        | .error _ => "error"
    (memoPut memo k { text := s }).text

/-- The Lean kernel's normal form of a closed term, printed as `Kernel.wiz` prints. -/
def wizNormal (g : Gl) (t : MTm) : String :=
  let k := mkeyOf kWizNormal wizTag [] t.toTerm
  match memoFind memo k with
  | some a => a.text
  | none =>
    let t' := (markInf g t.toTerm).getD t.toTerm
    let s := match MTm.ofTerm (quote g 0 (eval g [] t')) with
      | some m => m.pretty 0
      | none => "?"
    (memoPut memo k { text := s }).text

/-- Build and run a program with `main : IO Unit`; its output (`none`: no C toolchain). -/
def wizRun (src : String) : IO (Option String) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let effLib ← IO.FS.readFile "lib/Eff.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib else if m == "Eff" then some effLib
    else if m == "Std" then some stdLib else none
  let s := runFrontend (R := Q) src { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate (errs.toList.take 3)}")
  let dir ← IO.FS.createTempDir
  match ← Build.runGlobal (← toolchain) s "main" dir false (timeout := some 900) with
  | .ok v => pure (some v)
  | .error e =>
    let missing := ["gmp.h", "llc:", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then pure none else throw (IO.userError e)

/-- Pinned queries, asked first: what each probes, whether its normal form is asked, the
term, and whether the two kernels' answers **differ** today (after reading `↑∞` as `∞`).
The test fails when one flips: a fixed difference is then removed from here.

* W1 (kernel lint): `Kernel.wiz`'s `headSame` compared two constants without their levels,
  so two stuck cases whose environments hold one constant at two levels were convertible.
  Pinned as it must be (both reject): the case fails on a `Kernel.wiz` without the fix.
* PH-K1: `Kernel.wiz` keeps `↑∞` where a size variable under `↑` is instantiated with `∞`
  (the Lean kernel's `eval` gives `∞`), and its syntactic tests then see two sizes: it is
  stuck or stricter, never more permissive.
* K1 (first audit): quantities at a proposition Σ are ignored by the Lean kernel's
  conversion and compared by `Kernel.wiz`'s.
* PH-K3: under a stuck cast between propositions, `Kernel.wiz`'s normal form keeps a
  glued application that the Lean kernel's unfolds. -/
def pinned : List (String × Bool × MTm × Bool) :=
  let G : MTm := .ann (.lam (.mus 0 (.unit 0) MTm.natD .star (.szSuc (.var 0)))) (.pi .size (.univ 0))
  let Gi : MTm := .app G .szInf
  let N := MTm.natTy
  let SL : MTm := .app (.ann (.lam (.sizeLt (.szSuc (.var 0)))) (.pi .size (.univ 0))) .szInf
  let conv (T a b : MTm) : MTm :=
    .ann (.lam (.lam (.var 0))) (.pi (.pi T (.univ 0)) (.pi (.app (.var 0) a) (.app (.var 1) b)))
  let L : MTm := .ulift 0 1 .ptrue
  -- W1 (kernel lint): `F A x := ecase x [A]` at `polyK.{0}` and at `polyK.{1}`, stuck on `x`
  let F (a x : MTm) : MTm :=
    .app (.app (.ann (.lam (.lam (.ecase .prop (.var 0) [.var 1]))) (.pi .prop (.pi (.enum 1) .prop))) a) x
  let w1 (l l' : Nat) : MTm := .ann (.lam (.lam (.var 0)))
    (.pi (.enum 1) (.pi (F (.const "polyK" [l]) (.var 0)) (F (.const "polyK" [l']) (.var 1))))
  [("W1: (x : Enum 1) → F polyK.{0} x → F polyK.{1} x (both must reject)", false, w1 0 1, false),
   ("W1 control: (x : Enum 1) → F polyK.{0} x → F polyK.{0} x", false, w1 0 0, false),
   ("PH-K1: conversion of μ^(↑∞) with μ^∞ (under a variable's spine)", false, conv (.univ 0) Gi N, false),
   ("PH-K1: regularity, cast from μ^(↑∞) to μ^∞ of zero, normal form", true,
     .ann (.lam (.cast Gi N (.var 0) MTm.natZero)) (.pi (.eqTy Gi N) N), true),
   -- (these two differed at 76801e9 and agree at fd63740: Kernel.wiz's sizes changed in
   -- between, probably #40, desc-eq's "sizes compared as conversion does", dc4a32d)
   ("PH-K1: type equality μ^(↑∞) = μ^∞, normal form", true, .eqTy Gi N, false),
   ("PH-K1: () : μ^(↑∞) = μ^∞", false, .ann .star (.eqTy Gi N), false),
   ("PH-K1: ∞ : Size< ↑∞ (D2: rejected)", false, .ann .szInf SL, false),
   ("PH-K1: Size< ↑∞ ≤ Size< ∞", false, .ann (.lam (.var 0)) (.pi SL (.sizeLt .szInf)), false),
   ("PH-K1: Size< ∞ ≤ Size< ↑∞", false, .ann (.lam (.var 0)) (.pi (.sizeLt .szInf) SL), false),
   ("PH-K1: zero : μ^(↑∞)", false, .ann (.con (.pair (.tag 2 0) (.pair .star .star))) Gi, false),
   ("K1: (0 x : False) × False ≡ (x : False) × False", false,
     conv .prop (.sorted 0 0 (.sigmaq .zero .pfalse .pfalse)) (.sorted 0 0 (.sigma .pfalse .pfalse)), true),
   ("PH-K3: a glued application under a stuck cast between propositions, normal form", true,
     .ann (.lam (.cast L L (.var 0) (.app (.app (.const "idP" [1]) L) (.up .star)))) (.pi (.eqTy L L) L), true)]

/-- P5: `Kernel.wiz` gives the Lean kernel's verdict on every recorded query (the
judgments, their substitution instances, their normal forms, and conversions written as
judgments). With P1–P3 holding in the Lean kernel on the same queries, they hold in
`Kernel.wiz` on them too. -/
def wizCase (b : Budget) : IO Unit := do
  memoReset
  let acc ← runLean b
  -- (the pinned queries first)
  let acc := { acc with wiz := (pinned.map fun ((r, nf, m, _) : String × Bool × MTm × Bool) => (m, "pinned " ++ r, nf)).toArray ++ acc.wiz }
  let g := Elab.leanGlobals ()
  let qs := acc.wiz.toList
  -- (a normal form is asked only of a term the Lean kernel accepts)
  let qs := qs.filter fun (m, _, nf) => !nf || wizVerdict g m != "error"
  let expected := qs.map fun (m, _, nf) => if nf then wizNormal g m else wizVerdict g m
  let verdicts := (qs.zip expected).filter fun ((_, _, nf), _) => !nf
  let accepted := (verdicts.filter (·.2 != "error")).length
  IO.println s!"    ({qs.length} queries: {verdicts.length} verdicts, {accepted} accepted by the Lean kernel; {qs.length - verdicts.length} normal forms)"
  memoStats "prop-kernels: the queries"
  let w1 := qs.filter fun (m, _, _) => (m.toWiz.splitOn "polyK").length > 1
  let has (x frag : String) : Bool := (x.splitOn frag).length > 1
  let two := w1.filter fun (m, _, _) => has m.toWiz "(.lnum 1) .nil" && has m.toWiz "(.lnum 0) .nil"
  let w1Line := s!"{w1.length} queries mention polyK, {two.length} at two levels, {(two.filter fun (m, r, _) => has m.toWiz ".ecase" && !r.startsWith "pinned").length} of those generated with a case (W1's shape)"
  IO.println s!"    ({w1Line})"
  let roles := (qs.map (·.2.1)).eraseDups
  for r in roles do
    let mine := (qs.zip expected).filter (·.1.2.1 == r)
    IO.println s!"      {mine.length} × {r} ({(mine.filter (·.2 != "error")).length} not `error`)"
  let kernel ← IO.FS.readFile "selfhost/Kernel.wiz"
  let verdict :=
    "def rawVerdict (t : Tm) : String := match infer empty t with\n  | .ok ty _ => show .nil 0 (quote 0 ty)\n  | .err _ => \"error\"\n" ++
    "def markedVerdict (t : Tm) : String := rawVerdict (MR.tm (markInfer (TCtx.relevant empty) t))\n" ++
    -- (P2) every query gets its proof markers first (the kernel requires them); a term the
    -- pre-P2 kernel rejects is marked only when that kernel accepts it, as in `Tests/Elab`
    -- (mandatory sorts: the queries are `MTm` terms, whose `Π`/`Σ` sorts are holes until
    -- the sorts pass fills them; the kernel rejects a hole)
    "def verdict (t : Tm) : String := let u := sortsInfer t; match infer (TCtx.noMarkers empty) u with\n  | .err _ => \"error\"\n  | .ok _ _ => markedVerdict u\n" ++
    "def markedNormalize0 (t : Tm) : String := show .nil 0 (quote 0 (eval .nil (MR.tm (markInfer (TCtx.relevant empty) t))))\n" ++
    "def markedNormalize (t : Tm) : String := markedNormalize0 (sortsInfer t)\n"
  let printAll := "def printAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.println s;\n    printAll ss\n"
  let defs := String.join ((List.range qs.length).zip qs |>.map fun (i, (m, _, nf)) =>
    s!"def q{i} (u : Unit) : String := {if nf then "markedNormalize" else "verdict"} {m.toWiz}\n")
  let calls := (List.range qs.length).map fun i => s!"(q{i} ())"
  let prog := kernel ++ "\n" ++ verdict ++ printAll ++ defs ++ s!"def main : IO Unit := printAll {Elab.wizList calls}\n"
  let some out ← wizRun prog | IO.println "    (skipped: no toolchain)"
  let got := (out.splitOn "\n").take qs.length
  let norm (x : String) : String := (x.replace "↑(∞)" "∞").replace ", ∞)" ")"
  let mut verdictDiffs := 0
  let mut other := 0
  let mut phk1 := 0
  let mut flipped : List String := []
  let mut shown : List String := []
  -- (a passing case's output is not shown: the answers that matter are also kept in a file)
  let mut report := ""
  for (m, role, _) in qs, e in expected, o in got do
    if role.startsWith "pinned " then
      report := report ++ s!"{role}\n  Lean: {e}\n  Wiz:  {o}\n"
      IO.println s!"    {role}\n      Lean: {e}\n      Wiz:  {o}"
      let expectDiff := (pinned.find? fun (r, _, _, _) => "pinned " ++ r == role).map (·.2.2.2) |>.getD false
      if (norm e != norm o) != expectDiff then flipped := role :: flipped
      continue
    if (m.toWiz.splitOn "polyK").length > 1 then
      report := report ++ s!"(W1) {role}: Lean {e.take 60} / Wiz {o.take 60} / {(m.pretty 0).take 300}\n"
      IO.println s!"    (W1) {role}: Lean {e.take 60} / Wiz {o.take 60} / {(m.pretty 0).take 300}"
    if e != o then
      -- PH-K1: the answers differ only by `↑∞` against `∞`
      if norm o == norm e then
        phk1 := phk1 + 1
        continue
      let verdict := (e == "error") != (o == "error")
      if verdict then verdictDiffs := verdictDiffs + 1 else other := other + 1
      -- (one in full for each kind of query, the rest in brief)
      let key := s!"{role}/{verdict}"
      if !shown.contains key then
        shown := key :: shown
        IO.println s!"\n{if verdict then "✗ P5 one kernel accepts and the other rejects" else "(not gated) P5 the answers differ"}: {role}\n  Lean: {e}\n  Wiz:  {o}\n  term: {m.pretty 0}\n  as a term of Kernel.wiz: {m.toWiz}"
      else
        IO.println s!"{if verdict then "✗" else "(not gated)"} P5 {role}: Lean {e.take 80} / Wiz {o.take 80} / {(m.pretty 0).take 200}"
  IO.println s!"    ({phk1} answers differ only by ↑∞ against ∞ (PH-K1); {other} accepted by both with different normal forms or printed types (not gated: PH-K2, PH-K3); {verdictDiffs} accept/reject differences)"
  report := report ++ s!"{qs.length} queries; {phk1} PH-K1; {other} different normal forms; {verdictDiffs} accept/reject differences\n"
  -- (in the worktree's scratch directory, when there is one)
  if ← System.FilePath.isDir ".scratch" then
    IO.FS.writeFile ".scratch/prop-kernels-report.txt" (w1Line ++ "\n" ++ report)
  unless got.length == qs.length do throw (IO.userError s!"{got.length} answers for {qs.length} queries")
  unless flipped.isEmpty do throw (IO.userError s!"pinned differences changed (update `pinned`): {flipped}")
  unless verdictDiffs == 0 do throw (IO.userError s!"P5: one kernel accepts and the other rejects on {verdictDiffs} of {qs.length} queries")
  Tests.check (accepted * 4 ≥ verdicts.length) "too few accepted queries"

def group : Group where
  name := "prop"
  exercise := "property harness"
  cases := [
    { name := "substitution laws P1–P4, P6 in the Lean kernel (enumerated and sampled terms; coverage gate)",
      run := fun _ => leanCase {}}]

def kernelGroup : Group where
  name := "prop-kernels"
  exercise := "property harness"
  cases := [
    { name := "P5: Kernel.wiz agrees with the Lean kernel on judgments, substitution instances and conversions",
      run := fun _ => wizCase { random := 300, wizCap := 2000 } }]

/-- `tests --prop-long [SAMPLES] [SEED]`: the long run (no `Kernel.wiz`). -/
def longMain (args : List String) : IO UInt32 := do
  let n := (args[0]? >>= String.toNat?).getD 20000
  let seed := (args[1]? >>= String.toNat?).getD 1
  try
    leanCase { dev := 3, perCtx := n / 8, random := n, fuel := 3, seed }
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

/-- `tests --prop-no-sizes` (the default run without sizes) and `tests --prop-trace` (it
prints each sample before checking it; with `LEAN_ABORT_ON_PANIC=1`, the one that panics). -/
def flagMain (noSizes trace : Bool) : IO UInt32 := do
  noSizesRef.set noSizes
  traceRef.set trace
  try
    leanCase {}
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

builtin_initialize registerGroup group
builtin_initialize registerGroup kernelGroup

end Tests.Prop
