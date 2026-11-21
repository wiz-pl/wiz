/-!
# Hot-reload P0: the slot model

This file is the data half of the P0 prototype described in
`/workspace/wiz-notes/hot-reload.md` §12. It is a **model**, not the Wiz kernel:
`Ty` is a first-order toy type language, `Tm` is a de Bruijn term language, and a
generation is a list of slots. The point is the shape of the invariants, not
typechecking Wiz.

The four invariants this file makes representable:

* a slot has a stable surface name and slot id, and a fresh internal name
  `x@<revision>` for every body (no rebinding, §1.1/§11(b));
* a generation is immutable; a swap appends a new one (G6);
* a `Pinned` is an immutable generation id; a `read` is a projection of it (G2/G4);
* a slot's *check key* and its *revision* are different identities: the check key
  is generation-independent, the revision includes the slots the body reads
  (§6.3, §8.5, C7).
-/

namespace HotReload

/-- Stable slot identity. In the real system this comes from the program manifest;
here it is just a `Nat`. -/
abbrev SlotId := Nat

/-- The toy type language. It has enough formers to say what `Value A` accepts and
rejects; it is not Wiz's type theory. `observable` is the phantom surface type of a
slot descriptor; `pinned` is the snapshot index; the resource formers are here so
that the `Value` predicate can reject them. -/
inductive Ty where
  | nat
  | bool
  | unit
  | str
  | arr (dom cod : Ty)
  | list (elem : Ty)
  | option (elem : Ty)
  | prod (fst snd : Ty)
  | observable (elem : Ty)
  | pinned
  | subscription
  | region
  | world
  | uniq (reg elem : Ty)
  | chan (proto : Ty)
  | mut (reg elem : Ty)
  | io (result : Ty)
  | io1 (result : Ty)
  deriving DecidableEq, BEq, Repr

/-- A surface rendering, used for hashes and the `#check` line. -/
def Ty.render : Ty → String
  | .nat => "Nat"
  | .bool => "Bool"
  | .unit => "Unit"
  | .str => "String"
  | .arr a b => "(" ++ Ty.render a ++ " → " ++ Ty.render b ++ ")"
  | .list a => "List " ++ Ty.render a
  | .option a => "Option " ++ Ty.render a
  | .prod a b => "(" ++ Ty.render a ++ " × " ++ Ty.render b ++ ")"
  | .observable a => "Observable " ++ Ty.render a
  | .pinned => "Pinned"
  | .subscription => "Subscription"
  | .region => "Region"
  | .world => "World"
  | .uniq r a => "Uniq " ++ Ty.render r ++ " " ++ Ty.render a
  | .chan p => "Chan " ++ Ty.render p
  | .mut r a => "Mut " ++ Ty.render r ++ " " ++ Ty.render a
  | .io a => "IO " ++ Ty.render a
  | .io1 a => "IO1 " ++ Ty.render a

/-- The structural `Value A` side condition of §5.5: no `1`-quantity value, no
resource token, no `World`, no `Pinned`, no `Subscription`. A function is a value
only when both ends are, which is why `Pinned → A` is not a legal slot type while
`Nat → Nat` is. -/
def Ty.isValue : Ty → Bool
  | .nat | .bool | .unit | .str => true
  | .arr a b => Ty.isValue a && Ty.isValue b
  | .list a => Ty.isValue a
  | .option a => Ty.isValue a
  | .prod a b => Ty.isValue a && Ty.isValue b
  | .observable a => Ty.isValue a
  | .pinned | .subscription | .region | .world
  | .uniq _ _ | .chan _ | .mut _ _ | .io _ | .io1 _ => false

/-- De Bruijn terms. `read s` is the hidden-`self` form available inside a slot
body (`read self s`); `readAt p s` is the explicit-snapshot form available to pure
code. `const n` is a non-reloadable helper. `snapshot` is present so the checker
can reject it in pure code, not because it is a pure term. -/
inductive Tm where
  | unit
  | nat (n : Nat)
  | bool (b : Bool)
  | str (s : String)
  | var (i : Nat)
  | lam (body : Tm)
  | app (fn arg : Tm)
  | add (a b : Tm)
  | sub (a b : Tm)
  | mul (a b : Tm)
  | eq (a b : Tm)
  | ifE (c t e : Tm)
  | pair (a b : Tm)
  | fst (p : Tm)
  | snd (p : Tm)
  | nil (elem : Ty)
  | cons (head tail : Tm)
  | none (elem : Ty)
  | some (v : Tm)
  | read (slot : SlotId)
  | readAt (p : Tm) (slot : SlotId)
  | const (name : String)
  | snapshot
  deriving Repr

/-- A rendering. It is only used to derive a stable content hash for the model;
the real revision is a SHA-256 over the elaborated term, its type, its helper
environment and the kernel version (§6.3, §8.5). -/
def Tm.render : Tm → String
  | .unit => "()"
  | .nat n => toString n
  | .bool b => if b then "true" else "false"
  | .str s => "\"" ++ s ++ "\""
  | .var i => "#" ++ toString i
  | .lam b => "(fun => " ++ Tm.render b ++ ")"
  | .app f a => "(" ++ Tm.render f ++ " " ++ Tm.render a ++ ")"
  | .add a b => "(+ " ++ Tm.render a ++ " " ++ Tm.render b ++ ")"
  | .sub a b => "(- " ++ Tm.render a ++ " " ++ Tm.render b ++ ")"
  | .mul a b => "(* " ++ Tm.render a ++ " " ++ Tm.render b ++ ")"
  | .eq a b => "(= " ++ Tm.render a ++ " " ++ Tm.render b ++ ")"
  | .ifE c t e => "(if " ++ Tm.render c ++ " " ++ Tm.render t ++ " " ++ Tm.render e ++ ")"
  | .pair a b => "(" ++ Tm.render a ++ ", " ++ Tm.render b ++ ")"
  | .fst p => "(fst " ++ Tm.render p ++ ")"
  | .snd p => "(snd " ++ Tm.render p ++ ")"
  | .nil _ => "[]"
  | .cons h t => "(:: " ++ Tm.render h ++ " " ++ Tm.render t ++ ")"
  | .none _ => "none"
  | .some v => "(some " ++ Tm.render v ++ ")"
  | .read s => "(read " ++ toString s ++ ")"
  | .readAt p s => "(readAt " ++ Tm.render p ++ " " ++ toString s ++ ")"
  | .const n => n
  | .snapshot => "snapshot"

/-- The slots a body reads, either through the hidden `self` or an explicit
snapshot. These are **not** definitional dependencies: the kernel does not unfold
a slot body (§6.3). They are the dependencies whose revisions enter the content
revision (§8.5). -/
def Tm.slotIds : Tm → List SlotId
  | .read s => [s]
  | .readAt p s => Tm.slotIds p ++ [s]
  | .lam b => Tm.slotIds b
  | .app f a => Tm.slotIds f ++ Tm.slotIds a
  | .add a b | .sub a b | .mul a b | .eq a b => Tm.slotIds a ++ Tm.slotIds b
  | .ifE c t e => Tm.slotIds c ++ Tm.slotIds t ++ Tm.slotIds e
  | .pair a b => Tm.slotIds a ++ Tm.slotIds b
  | .fst p | .snd p => Tm.slotIds p
  | .cons h t => Tm.slotIds h ++ Tm.slotIds t
  | .some v => Tm.slotIds v
  | .unit | .nat _ | .bool _ | .str _ | .var _ | .nil _ | .none _ | .const _ | .snapshot => []

/-- The slots a body reads through the hidden `self` only. An explicit `readAt p`
reads a *different* snapshot, so it is not a dependency on this generation's other
slots; it is a cross-generation read (§4.4). These edges are the ones whose
revisions enter the memo revision. -/
def Tm.selfSlotIds : Tm → List SlotId
  | .read s => [s]
  | .readAt _ _ => []
  | .lam b => Tm.selfSlotIds b
  | .app f a => Tm.selfSlotIds f ++ Tm.selfSlotIds a
  | .add a b | .sub a b | .mul a b | .eq a b => Tm.selfSlotIds a ++ Tm.selfSlotIds b
  | .ifE c t e => Tm.selfSlotIds c ++ Tm.selfSlotIds t ++ Tm.selfSlotIds e
  | .pair a b => Tm.selfSlotIds a ++ Tm.selfSlotIds b
  | .fst p | .snd p => Tm.selfSlotIds p
  | .cons h t => Tm.selfSlotIds h ++ Tm.selfSlotIds t
  | .some v => Tm.selfSlotIds v
  | .unit | .nat _ | .bool _ | .str _ | .var _ | .nil _ | .none _ | .const _ | .snapshot => []

/-- A witness must be total and independent of every generation. In this model
that is "no `read`, no `readAt`, no `snapshot`". The note's witness rule is "a
checked term of its type"; see `README.md` roadblock 3 for why the stronger
restriction is needed. -/
def Tm.isReadFree : Tm → Bool
  | .read _ => false
  | .readAt _ _ => false
  | .snapshot => false
  | .unit | .nat _ | .bool _ | .str _ | .var _ | .nil _ | .none _ | .const _ => true
  | .lam b => Tm.isReadFree b
  | .app f a => Tm.isReadFree f && Tm.isReadFree a
  | .add a b | .sub a b | .mul a b | .eq a b => Tm.isReadFree a && Tm.isReadFree b
  | .ifE c t e => Tm.isReadFree c && Tm.isReadFree t && Tm.isReadFree e
  | .pair a b => Tm.isReadFree a && Tm.isReadFree b
  | .fst p | .snd p => Tm.isReadFree p
  | .cons h t => Tm.isReadFree h && Tm.isReadFree t
  | .some v => Tm.isReadFree v

/-- The non-reloadable helpers a term mentions, for the cache's helper-environment
hash. -/
def Tm.consts : Tm → List String
  | .const n => [n]
  | .unit | .nat _ | .bool _ | .str _ | .var _ | .nil _ | .none _ | .read _ | .snapshot => []
  | .readAt p _ => Tm.consts p
  | .lam b => Tm.consts b
  | .app f a => Tm.consts f ++ Tm.consts a
  | .add a b | .sub a b | .mul a b | .eq a b => Tm.consts a ++ Tm.consts b
  | .ifE c t e => Tm.consts c ++ Tm.consts t ++ Tm.consts e
  | .pair a b => Tm.consts a ++ Tm.consts b
  | .fst p | .snd p => Tm.consts p
  | .cons h t => Tm.consts h ++ Tm.consts t
  | .some v => Tm.consts v

/-- A non-reloadable helper. Its body is pure in this model; a helper that reads a
slot is the explicit-`Pinned` case and reads at its caller's generation. -/
structure Helper where
  name : String
  ty : Ty
  body : Tm
  deriving Repr

/-- A tiny FNV-1a. This is **not** the real content hash: `Wiz/Cache.lean` uses a
domain-separated SHA-256 for identity and a 64-bit hash only as an index. The model
only needs a deterministic string. -/
def fnv1a (s : String) : Nat :=
  s.toList.foldl
    (fun h c => (h * 1099511628211 + c.toNat) % 18446744073709551616)
    14695981039346656037

def shortHash (s : String) : String := "h" ++ toString (fnv1a s)

/-- The part of the helper environment a body actually mentions. A new unrelated
helper must not change the body's identity (or its cache key); a changed helper is
a *new name* (§6.3), so a body that mentions the old name keeps the old meaning. -/
def helperHashFor (helpers : List Helper) (t : Tm) : String :=
  shortHash (t.consts.foldl (fun acc n =>
    match helpers.find? (fun h => h.name == n) with
    | some h => acc ++ "|" ++ n ++ ":" ++ Ty.render h.ty ++ ":" ++ shortHash (Tm.render h.body)
    | none => acc ++ "|" ++ n ++ ":missing") "")

/-- A slot. `surface` is the stable name the user writes; `internal` is the
versioned name of this body (`x@<bodyRevision>`). A *different* body gets a
different `internal`; re-staging the same body keeps its old name, which is the
old meaning, not a rebinding. `version` is the generation-local counter;
`revision` is the memo/content identity (C7). -/
structure Slot where
  id : SlotId
  ty : Ty
  surface : String
  /-- `surface@bodyRevision`: the versioned name of the *body constant*. It is a
  function of `Pinned`, so its meaning is unchanged by a callee swap; a new body
  text gets a new body revision and so a new name. -/
  internal : String
  /-- The body's own content identity (type, body, mentioned helpers, witness,
  kernel). It is generation-independent while the body is unchanged. -/
  bodyRevision : String
  /-- The body revision mixed with the revisions of the slots the body reads
  through `self`. This is the key a runtime memo / `native_refl` / scry revision
  must use, because the body's *result* can change when a callee does (§8.5). -/
  revision : String
  body : Tm
  witness : Tm
  checked : Bool
  version : Nat
  /-- Definitional dependencies on staged items (new helpers/bodies) in the
  transaction that produced this slot. They are part of the revision, not the
  check key: a new helper's meaning is in the body's identity even though no
  kernel recheck of the consumer is needed. -/
  deps : List SlotId := []
  deriving Repr

/-- The checker's version is part of a body's identity: a changed checker must
not reuse an old verdict or an old internal name. -/
def kernelVersion : String := "hot-reload-p0-model-1"

/-- The body's own revision: type, body, the helper meanings it mentions, the
witness and the kernel. No callees, so it is stable while the body text is. This
is also the cache's `baseRevision` and the `x@<...>` internal name. -/
def bodyRevisionOf (ty : Ty) (body witness : Tm) (helpers : String) : String :=
  shortHash ("check|" ++ Ty.render ty ++ "|" ++ Tm.render body ++ "|" ++ helpers ++
    "|" ++ Tm.render witness ++ "|" ++ kernelVersion)

/-- Mix the body revision with the revisions of its `self`-read callees. -/
def revisionFor (bodyRevision : String) (deps : List String) : String :=
  shortHash (bodyRevision ++ "|deps|" ++ deps.foldl (fun acc d => acc ++ "|" ++ d) "")

/-- Build a fresh slot. The caller supplies the id and surface name; the internal
name is derived from the body revision, never from the surface name alone. -/
def Slot.make (id : SlotId) (surface : String) (ty : Ty) (body witness : Tm)
    (version : Nat := 0) (helpers : List Helper := []) : Slot :=
  let bodyRevision := bodyRevisionOf ty body witness (helperHashFor helpers body)
  { id := id
    ty := ty
    surface := surface
    internal := surface ++ "@" ++ bodyRevision
    bodyRevision := bodyRevision
    revision := revisionFor bodyRevision []
    body := body
    witness := witness
    checked := true
    version := version }

/-- The revisions a slot's body reads through `self`, in the candidate generation,
plus its definitional (`deps`) edges. -/
def depRevs (slots : List Slot) (s : Slot) : List String :=
  (s.deps ++ Tm.selfSlotIds s.body).map fun d =>
    match slots.find? (fun x => x.id == d) with
    | some x => x.revision
    | none => "missing"

/-- Recompute every slot's memo revision to a fixed point. A body that reads a
changed callee gets a new revision even though its text is unchanged; this is what
§8.5 requires. If the `self`-read graph is cyclic the fixed point may not exist
(the mutual meanings are genuinely recursive), so after `fuel` rounds the whole
generation is keyed conservatively by its id, exactly the note's fallback. The
check cache is untouched: only the revision changes, not the kernel verdict. -/
def refreshRevisions (fuel : Nat) (genId : Nat) (slots : List Slot) : List Slot :=
  match fuel with
  | 0 => slots.map (fun s =>
      { s with revision := shortHash (s.bodyRevision ++ "|gen|" ++ toString genId) })
  | n + 1 =>
    let slots' := slots.map fun s =>
      { s with revision := revisionFor s.bodyRevision (depRevs slots s) }
    if slots'.map (fun s => s.revision) == slots.map (fun s => s.revision) then slots'
    else refreshRevisions n genId slots'

/-- An immutable generation. `names` is every internal body name used in the
history: it is the audit trail (a body name is a function of the body's own
content, so a different body cannot reuse it). `envHash` is the non-reloadable
environment's identity (helpers); a change to it is a new image or a
re-elaboration, not a silent slot swap. -/
structure Gen where
  id : Nat
  parent : Option Nat
  slots : List Slot
  names : List String
  envHash : String
  ledger : List String
  deriving Repr

def Gen.findSlot (g : Gen) (s : SlotId) : Option Slot :=
  g.slots.find? (fun x => x.id == s)

/-- A runtime value. A function slot is a closure that stores the generation it
was built in, not a code pointer: `read` returns that closure, so a nested
reloadable call uses the pinned generation and not the global current one (§4.4). -/
inductive Val where
  | unit
  | nat (n : Nat)
  | bool (b : Bool)
  | str (s : String)
  | pinned (g : Nat)
  | clos (gen : Nat) (env : List Val) (body : Tm)
  | pair (a b : Val)
  | nil
  | cons (head tail : Val)
  | none
  | some (v : Val)
  | helper (name : String)
  deriving Repr

def Val.render : Val → String
  | .unit => "()"
  | .nat n => toString n
  | .bool b => if b then "true" else "false"
  | .str s => s
  | .pinned g => "<pinned " ++ toString g ++ ">"
  | .clos g _ _ => "<closure@" ++ toString g ++ ">"
  | .pair a b => "(" ++ Val.render a ++ ", " ++ Val.render b ++ ")"
  | .nil => "[]"
  | .cons h t => Val.render h ++ "::" ++ Val.render t
  | .none => "none"
  | .some v => "some " ++ Val.render v
  | .helper n => "<helper " ++ n ++ ">"

/-- Equality used only by the model's tests. Closures compare by generation tag,
not by code; the real runtime does not need value equality. -/
def Val.beq (a b : Val) : Bool := Val.render a == Val.render b

/-- The memo table: `(generation, slot) → value`. A memo entry for a reloadable
slot is keyed by the generation, never by the slot alone; a swap does not
invalidate old entries, it makes new ones under a new key (§8.5). -/
abbrev Memo := List ((Nat × SlotId) × Val)

def memoFind (m : Memo) (g : Nat) (s : SlotId) : Option Val :=
  match m.find? (fun p => match p with | ((g', s'), _) => g' == g && s' == s) with
  | some (_, v) => some v
  | none => none

/-- The generation-independent part of a checked body's cache key (the "check
key"): type, body, helper environment, witness, kernel version. This is the key of
§6.3. The content revision adds the callees' revisions and is computed separately.
-/
structure CacheKey where
  slotTy : String
  body : String
  helpers : String
  witness : String
  kernel : String
  deriving DecidableEq, BEq, Repr

def CacheKey.render (k : CacheKey) : String :=
  k.slotTy ++ "|" ++ k.body ++ "|" ++ k.helpers ++ "|" ++ k.witness ++ "|" ++ k.kernel

structure CacheEntry where
  key : CacheKey
  /-- The body revision (`bodyRevisionOf`): the generation-independent verdict's
  content identity. The memo revision mixes this with the callees' revisions. -/
  baseRevision : String
  deriving Repr

structure Cache where
  entries : List CacheEntry := []
  hits : Nat := 0
  misses : Nat := 0
  deriving Repr

def Cache.lookup (c : Cache) (k : CacheKey) : Option CacheEntry :=
  c.entries.find? (fun e => e.key == k)

def Cache.insert (c : Cache) (e : CacheEntry) : Cache :=
  { c with entries := e :: c.entries, misses := c.misses + 1 }

def Cache.recordHit (c : Cache) : Cache :=
  { c with hits := c.hits + 1 }

/-- The whole P0 runtime state. `gens` is the immutable history in ascending id
order; the last element is the current generation. Old generations are never
removed in P0 (§7.4 item 3). -/
structure Runtime where
  gens : List Gen
  helpers : List Helper := []
  cache : Cache := { entries := [], hits := 0, misses := 0 }
  memo : Memo := []
  /-- Re-entrant forcing marks, so a data slot that reads itself fails instead of
  looping (§7.2). -/
  forcing : List (Nat × SlotId) := []
  deriving Repr

def Runtime.current? (rt : Runtime) : Option Gen := rt.gens.reverse.head?

def Runtime.findGen (rt : Runtime) (g : Nat) : Option Gen :=
  rt.gens.find? (fun x => x.id == g)

/-- The initial generation, id 0, with the fixed shape's slots. The model trusts
the initial slot list (a real image checks it); it still normalises each slot's
body revision against the helper environment and seeds the cache with the checked
initial bodies, so a later re-stage of an unchanged initial body is a hit. -/
def Runtime.initial (helpers : List Helper) (slots : List Slot) : Runtime :=
  let slots := slots.map fun s =>
    let helperRev := helperHashFor helpers s.body
    let bodyRev := bodyRevisionOf s.ty s.body s.witness helperRev
    { s with bodyRevision := bodyRev
             internal := s.surface ++ "@" ++ bodyRev
             revision := revisionFor bodyRev s.deps }
  let slots := refreshRevisions (slots.length + 2) 0 slots
  let g : Gen :=
    { id := 0
      parent := none
      slots := slots
      names := slots.map (fun s => s.internal)
      envHash := shortHash "p0-env-0"
      ledger := [] }
  let entries := slots.map fun s =>
    { key := { slotTy := shortHash (Ty.render s.ty)
               body := shortHash (Tm.render s.body)
               helpers := helperHashFor helpers s.body
               witness := shortHash (Tm.render s.witness)
               kernel := kernelVersion },
      baseRevision := s.bodyRevision }
  { gens := [g]
    helpers := helpers
    cache := { entries := entries, hits := 0, misses := 0 }
    memo := []
    forcing := [] }

/-- A snapshot is a generation id. It is an ordinary value (ω): it can be copied,
stored and passed; reading it is pure. -/
structure Pinned where
  gen : Nat
  deriving DecidableEq, BEq, Repr

/-- The surface slot descriptor. The real `Observable A` hides its private
constructor and carries only a slot id; the model keeps the toy `Ty` too so the
checker and the `#check` line can render it. -/
structure Observable where
  slot : SlotId
  ty : Ty
  deriving DecidableEq, BEq, Repr

def Runtime.snapshot (rt : Runtime) : Pinned :=
  match rt.current? with
  | some g => { gen := g.id }
  | none => { gen := 0 }

/-- Errors are a closed enum so the tests can match the *kind* of failure (a
failed check vs. a missing witness vs. a shape change), not just `false`. -/
inductive Err where
  | outOfFuel
  | noCurrent
  | unbound (i : Nat)
  | noGen (g : Nat)
  | noSlot (g : Nat) (s : SlotId)
  | unknownSlot (s : SlotId)
  | noHelper (n : String)
  | notFunction
  | typeError (msg : String)
  | notValue (ty : Ty)
  | witnessFailed (msg : String)
  | duplicateStage (s : SlotId)
  | internalNameReused (n : String)
  | cycle
  | staleBase (base current : Nat)
  | blackhole (g : Nat) (s : SlotId)
  deriving Repr

end HotReload
