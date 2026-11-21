import HotReload.Basic

/-!
# Hot-reload P0: checking, `Value A`, and the swap transaction

The checker here is deliberately a *toy*: it checks `Tm` against a signature of
**slot types only** (never slot bodies). That is the independence lemma of §6.3
made executable: if a body checks against the slot types, a later swap that keeps
the types cannot invalidate it, because `read` is opaque and no body is unfolded.

The transaction is stage / check / commit / abort. `commit` is a pure function:
it either returns a new `Runtime` with one appended generation or an `Err`, and a
caller that gets an `Err` still holds the old `Runtime`. In P0 that is the whole
atomicity story; the atomic cell and concurrent readers are P1 (§7.1).
-/

namespace HotReload

/-- A signature is the *types* of the slots plus the non-reloadable helpers. It
contains no slot body, so it is generation-independent as long as the slot types
and helper environment are. -/
structure Sig where
  slots : List (SlotId × Ty)
  helpers : List (String × Ty)
  kernel : String
  deriving Repr

def Sig.ofGen (g : Gen) (helpers : List Helper) (kernel : String) : Sig :=
  { slots := g.slots.map (fun s => (s.id, s.ty))
    helpers := helpers.map (fun h => (h.name, h.ty))
    kernel := kernel }

def Sig.slotTy? (sig : Sig) (s : SlotId) : Option Ty :=
  match sig.slots.find? (fun p => p.1 == s) with
  | some p => some p.2
  | none => none

def Sig.helperTy? (sig : Sig) (n : String) : Option Ty :=
  match sig.helpers.find? (fun p => p.1 == n) with
  | some p => some p.2
  | none => none

def Sig.helpersHash (sig : Sig) : String :=
  shortHash (sig.helpers.foldl (fun acc p => acc ++ "|" ++ p.1 ++ ":" ++ Ty.render p.2) "")

/-- The mode of the toy checker: check against an expected type, or infer one.
Using a mode keeps `tc` a single function with a fuel argument, so it is total
without a `mutual` block or a `partial` definition. -/
inductive Mode where
  | check (expect : Ty)
  | infer
  deriving Repr

def expectTy (mode : Mode) (actual : Ty) : Except String Ty :=
  match mode with
  | .infer => .ok actual
  | .check e =>
    if actual == e then .ok actual
    else .error s!"type mismatch: expected {Ty.render e}, got {Ty.render actual}"

def ctxGet? : List Ty → Nat → Option Ty
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: rest, n + 1 => ctxGet? rest n

/-- A small bidirectional checker. The cases that matter for the design:

* `read s` requires `self : Pinned` (only a slot body has it); pure code must use
  `readAt p s` with an explicit `p : Pinned`;
* `read s`/`readAt p s` have the slot's **type**, never its body, so the
  independence lemma holds;
* `snapshot` is an error: `snapshot : IO Pinned` cannot be a pure term;
* there is no dependent type, no proof, and no quantity; a real `Value` check is
  in `Ty.isValue`, and the real usage checker is the kernel's.
-/
def tc : Nat → Sig → List Ty → Bool → Tm → Mode → Except String Ty
  | 0, _, _, _, _, _ => .error "type checker out of fuel"
  | n + 1, sig, ctx, inSlot, tm, mode =>
    match tm with
    | .unit => expectTy mode .unit
    | .nat _ => expectTy mode .nat
    | .bool _ => expectTy mode .bool
    | .str _ => expectTy mode .str
    | .var i =>
      match ctxGet? ctx i with
      | none => .error s!"unbound variable #{i}"
      | some ty => expectTy mode ty
    | .lam b =>
      match mode with
      | .check (.arr a c) =>
        match tc n sig (a :: ctx) inSlot b (.check c) with
        | .error e => .error e
        | .ok _ => .ok (.arr a c)
      | .check _ => .error "a lambda checks against a function type"
      | .infer => .error "cannot infer the type of a lambda"
    | .app f a =>
      match tc n sig ctx inSlot f .infer with
      | .error e => .error e
      | .ok (.arr dom cod) =>
        match tc n sig ctx inSlot a (.check dom) with
        | .error e => .error e
        | .ok _ => expectTy mode cod
      | .ok _ => .error "applying a non-function"
    | .add a b | .sub a b | .mul a b =>
      match tc n sig ctx inSlot a (.check .nat) with
      | .error e => .error e
      | .ok _ =>
        match tc n sig ctx inSlot b (.check .nat) with
        | .error e => .error e
        | .ok _ => expectTy mode .nat
    | .eq a b =>
      match tc n sig ctx inSlot a .infer with
      | .error e => .error e
      | .ok ty =>
        match tc n sig ctx inSlot b (.check ty) with
        | .error e => .error e
        | .ok _ => expectTy mode .bool
    | .ifE c t e =>
      match tc n sig ctx inSlot c (.check .bool) with
      | .error err => .error err
      | .ok _ =>
        match mode with
        | .infer =>
          match tc n sig ctx inSlot t .infer with
          | .error err => .error err
          | .ok ty =>
            match tc n sig ctx inSlot e (.check ty) with
            | .error err => .error err
            | .ok _ => .ok ty
        | .check ty =>
          match tc n sig ctx inSlot t (.check ty) with
          | .error err => .error err
          | .ok _ =>
            match tc n sig ctx inSlot e (.check ty) with
            | .error err => .error err
            | .ok _ => .ok ty
    | .pair a b =>
      match mode with
      | .check (.prod x y) =>
        match tc n sig ctx inSlot a (.check x) with
        | .error e => .error e
        | .ok _ =>
          match tc n sig ctx inSlot b (.check y) with
          | .error e => .error e
          | .ok _ => .ok (.prod x y)
      | .check _ => .error "a pair checks against a product type"
      | .infer => .error "cannot infer the type of a pair"
    | .fst p =>
      match tc n sig ctx inSlot p .infer with
      | .error e => .error e
      | .ok (.prod a _) => expectTy mode a
      | .ok _ => .error "fst of a non-pair"
    | .snd p =>
      match tc n sig ctx inSlot p .infer with
      | .error e => .error e
      | .ok (.prod _ b) => expectTy mode b
      | .ok _ => .error "snd of a non-pair"
    | .nil elem => expectTy mode (.list elem)
    | .cons h tail =>
      match tc n sig ctx inSlot h .infer with
      | .error e => .error e
      | .ok elem =>
        match tc n sig ctx inSlot tail (.check (.list elem)) with
        | .error e => .error e
        | .ok _ => expectTy mode (.list elem)
    | .none elem => expectTy mode (.option elem)
    | .some v =>
      match tc n sig ctx inSlot v .infer with
      | .error e => .error e
      | .ok elem => expectTy mode (.option elem)
    | .read s =>
      if !inSlot then
        .error "read needs a Pinned: use `readAt p s` in pure code"
      else
        match sig.slotTy? s with
        | none => .error s!"unknown slot {s}"
        | some ty => expectTy mode ty
    | .readAt p s =>
      match tc n sig ctx inSlot p (.check .pinned) with
      | .error e => .error e
      | .ok _ =>
        match sig.slotTy? s with
        | none => .error s!"unknown slot {s}"
        | some ty => expectTy mode ty
    | .const name =>
      match sig.helperTy? name with
      | none => .error s!"unknown helper {name}"
      | some ty => expectTy mode ty
    | .snapshot =>
      .error "snapshot : IO Pinned cannot appear in a pure term"

def check (fuel : Nat) (sig : Sig) (ctx : List Ty) (self : Bool) (t : Tm)
    (expect : Ty) : Except String Unit :=
  match tc fuel sig ctx self t (.check expect) with
  | .error e => .error e
  | .ok _ => .ok ()

/-- A witness is checked at the slot type, but it must be read-free: otherwise
`reloadable def g : Unit → False := fun u => read self g u` could be admitted with
the witness `read self g`, which is the circular proof the note's example rules
out. The real elaborator needs a decision here; the prototype is deliberately
strict. -/
def checkWitness (fuel : Nat) (sig : Sig) (ty : Ty) (w : Tm) : Except String Unit :=
  if !w.isReadFree then
    .error "a witness may not read a slot or take a snapshot (it must be total and read-free)"
  else
    check fuel sig [] true w ty

/-- One staged slot body. `dependsOn` is the transaction's *definitional* ordering
edge: a new helper or a new body must be staged before a body that mentions it. A
reloadable call through `read` is **not** such an edge (§6.2). -/
structure Stage where
  slot : SlotId
  body : Tm
  witness : Tm
  dependsOn : List SlotId := []
  deriving Repr

structure Transaction where
  base : Nat
  stages : List Stage
  deriving Repr

/-- The revision a body's read-dependency contributes. A dependency staged earlier
in this transaction uses its new revision; an old slot uses the base generation's. -/
def depRevision (base : Gen) (prior : List Slot) (d : SlotId) : String :=
  match prior.find? (fun s => s.id == d) with
  | some s => s.revision
  | none =>
    match base.findSlot d with
    | some s => s.revision
    | none => "missing"

/-- The slot a successful stage produces; shared by the cache-hit and cache-miss
paths so the revision/internal-name rule cannot diverge between them. -/
def finishStage (old : Slot) (st : Stage) (bodyRev : String) (deps : List String)
    (cache : Cache) : Slot × Cache :=
  let revision := revisionFor bodyRev deps
  let internal := old.surface ++ "@" ++ bodyRev
  ({ old with
      body := st.body
      bodyRevision := bodyRev
      witness := st.witness
      revision := revision
      internal := internal
      version := old.version + 1
      checked := true
      deps := st.dependsOn }, cache)

/-- Stage one body: `Value A`, then the cache, then (on a miss) the type check
against slot **types** and the read-free witness check. A **hit skips the
checker**: the key names a body+type+helper+witness+kernel whose check already
succeeded. The revision is still recomputed because it includes the callees'
revisions. -/
def prepareStage (fuel : Nat) (base : Gen) (helpers : List Helper) (cache : Cache)
    (prior : List Slot) (st : Stage) : Except Err (Slot × Cache) :=
  match base.findSlot st.slot with
  | none => .error (.unknownSlot st.slot)
  | some old =>
    if !old.ty.isValue then .error (.notValue old.ty)
    else
      let sig := Sig.ofGen base helpers kernelVersion
      let deps := st.dependsOn.map (depRevision base prior)
      let helperRev := helperHashFor helpers st.body
      let key : CacheKey :=
        { slotTy := shortHash (Ty.render old.ty)
          body := shortHash (Tm.render st.body)
          helpers := helperRev
          witness := shortHash (Tm.render st.witness)
          kernel := kernelVersion }
      let bodyRev := bodyRevisionOf old.ty st.body st.witness helperRev
      match cache.lookup key with
      | some _ =>
        .ok (finishStage old st bodyRev deps (cache.recordHit))
      | none =>
        match check fuel sig [] true st.body old.ty with
        | .error msg => .error (.typeError msg)
        | .ok _ =>
          match checkWitness fuel sig old.ty st.witness with
          | .error msg => .error (.witnessFailed msg)
          | .ok _ =>
            .ok (finishStage old st bodyRev deps
              (cache.insert { key := key, baseRevision := bodyRev }))

/-- A topological order over the staged items' definitional edges. An edge to a
slot that is not staged is already satisfied by the base generation. A cycle is an
error, not a stack overflow. -/
def topoGo (fuel : Nat) (pending : List Stage) (done : List SlotId)
    (acc : List Stage) : Except Err (List Stage) :=
  match fuel with
  | 0 => .error .cycle
  | n + 1 =>
    match pending with
    | [] => .ok acc.reverse
    | _ =>
      let ready? := pending.find? (fun s =>
        s.dependsOn.all (fun d =>
          done.contains d || !(pending.any (fun p => p.slot == d))))
      match ready? with
      | none => .error .cycle
      | some s =>
        topoGo n (pending.filter (fun p => p.slot != s.slot)) (s.slot :: done) (s :: acc)

def topoOrder (stages : List Stage) : Except Err (List Stage) :=
  topoGo stages.length stages [] []

def prepareAll (fuel : Nat) (base : Gen) (helpers : List Helper)
    (ordered : List Stage) (cache : Cache) (seen : List SlotId)
    (prior : List Slot) : Except Err (List Slot × Cache) :=
  match ordered with
  | [] => .ok (prior, cache)
  | st :: rest =>
    if seen.contains st.slot then .error (.duplicateStage st.slot)
    else
      match prepareStage fuel base helpers cache prior st with
      | .error e => .error e
      | .ok (slot, cache') =>
        prepareAll fuel base helpers rest cache' (st.slot :: seen) (slot :: prior)

/-- Commit a multi-slot transaction. The new generation is built off to the side
and returned only if every check passed; on error the caller's `Runtime` (and so
the current generation) is untouched. A multi-slot swap is all-or-nothing (G5). -/
def Runtime.commit (rt : Runtime) (tx : Transaction) : Except Err Runtime :=
  match rt.current? with
  | none => .error .noCurrent
  | some base =>
    if base.id != tx.base then .error (.staleBase tx.base base.id)
    else
      match topoOrder tx.stages with
      | .error e => .error e
      | .ok ordered =>
        match prepareAll 10000 base rt.helpers ordered rt.cache [] [] with
        | .error e => .error e
        | .ok (staged, cache') =>
          let newSlots := base.slots.map (fun old =>
            match staged.find? (fun s => s.id == old.id) with
            | some s => s
            | none => old)
          let newSlots := refreshRevisions (newSlots.length + 2) (base.id + 1) newSlots
          let newNames := staged.foldl (fun acc s =>
            if acc.contains s.internal then acc else acc ++ [s.internal]) base.names
          -- `envHash` is the *non-reloadable* environment (helpers and slot
          -- types), so a slot swap does not change it. A new/changed helper is a
          -- new image or a separate transaction, never a silent slot swap (§6.3).
          let g' : Gen :=
            { id := base.id + 1
              parent := some base.id
              slots := newSlots
              names := newNames
              envHash := base.envHash
              ledger := base.ledger }
          .ok { rt with gens := rt.gens ++ [g'], cache := cache' }

end HotReload
