import HotReload.Interp

/-!
# Hot-reload P0: the acceptance cases (NOT RUN)

These are the P0 acceptance cases from `/workspace/wiz-notes/hot-reload.md` §10
(test numbers in the comments) as pure `Bool`s. **This lane does not run them**:
no `#eval`, no `lake`, no `wiz`, no build. A queue slot should build the library
and run `hotreload --allow-reload` (see `Main.lean`) or `#eval HotReload.tests`.

The cases that need a real kernel/runtime (the `#check` info tree, `Value` through
real structures, concurrent atomics, compiler agreement) are not here; they are
roadblocks in `README.md`.
-/

namespace HotReload

def isNat (r : Except Err (Val × Runtime)) (n : Nat) : Bool :=
  match r with
  | .ok (.nat m, _) => m == n
  | _ => false

def isBool (r : Except Err (Val × Runtime)) (b : Bool) : Bool :=
  match r with
  | .ok (.bool x, _) => x == b
  | _ => false

def xSlot : Slot := Slot.make 0 "x" .nat (.nat 1) (.nat 0)
def ySlot : Slot := Slot.make 1 "y" .nat (.nat 1) (.nat 0)
def xObs : Observable := { slot := 0, ty := .nat }
def yObs : Observable := { slot := 1, ty := .nat }

/-- Test 1: a failing swap is rejected and the old generation stays live. -/
def testFailedSwap : Bool :=
  let rt := Runtime.initial [] [xSlot]
  let p0 := rt.snapshot
  match rt.commit { base := 0, stages := [{ slot := 0, body := .bool true, witness := .nat 0 }] } with
  | .error _ => isNat (rt.read 1000 p0 xObs) 1
  | .ok _ => false

/-- Test 2: a multi-slot transaction is atomic; one bad item aborts both. -/
def testAtomicTransaction : Bool :=
  let rt := Runtime.initial [] [xSlot, ySlot]
  let p0 := rt.snapshot
  let tx : Transaction :=
    { base := 0
      stages :=
        [ { slot := 0, body := .nat 2, witness := .nat 0 }
        , { slot := 1, body := .bool true, witness := .nat 0 } ] }
  match rt.commit tx with
  | .error _ =>
    isNat (rt.read 1000 p0 xObs) 1 && isNat (rt.read 1000 p0 yObs) 1
  | .ok _ => false

/-- Test 3: a reader pinned across a swap sees one generation. -/
def testSnapshotConsistency : Bool :=
  let rt := Runtime.initial [] [xSlot, ySlot]
  let p0 := rt.snapshot
  let tx : Transaction :=
    { base := 0
      stages :=
        [ { slot := 0, body := .nat 2, witness := .nat 0 }
        , { slot := 1, body := .nat 2, witness := .nat 0 } ] }
  match rt.commit tx with
  | .error _ => false
  | .ok rt1 =>
    let p1 := rt1.snapshot
    isNat (rt1.read 1000 p0 xObs) 1 &&
    isNat (rt1.read 1000 p0 yObs) 1 &&
    isNat (rt1.read 1000 p1 xObs) 2 &&
    isNat (rt1.read 1000 p1 yObs) 2

/-- Test 6: no stale closure. `f0 = read p0 f` uses `p0`'s `g` after `g` is
swapped; a fresh read at `p1` uses the new `g`. -/
def gSlot : Slot := Slot.make 0 "g" (.arr .nat .nat) (.lam (.var 0)) (.lam (.var 0))
def fSlot : Slot :=
  Slot.make 1 "f" (.arr .nat .nat)
    (.lam (.add (.app (.read 0) (.var 0)) (.nat 1)))
    (.lam (.var 0))
def gObs : Observable := { slot := 0, ty := (.arr .nat .nat) }
def fObs : Observable := { slot := 1, ty := (.arr .nat .nat) }

def testNoStaleClosure : Bool :=
  let rt := Runtime.initial [] [gSlot, fSlot]
  let p0 := rt.snapshot
  match rt.read 1000 p0 fObs with
  | .error _ => false
  | .ok (f0, rt1) =>
    let tx : Transaction :=
      { base := 0
        stages :=
          [{ slot := 0
             body := .lam (.mul (.var 0) (.nat 10))
             witness := .lam (.var 0) }] }
    match rt1.commit tx with
    | .error _ => false
    | .ok rt2 =>
      match applyVal 1000 rt2 f0 (.nat 1) with
      | .error _ => false
      | .ok (.nat oldResult, rt3) =>
        let p1 := rt3.snapshot
        match rt3.read 1000 p1 fObs with
        | .error _ => false
        | .ok (f1, rt4) =>
          match applyVal 1000 rt4 f1 (.nat 1) with
          | .ok (.nat newResult, _) => oldResult == 2 && newResult == 11
          | _ => false

/-- The Loom-shaped case: the host's state is ordinary data and survives a swap;
only the view/update slot changes. The state's *type* does not change, so this is
a reload, not a new page. -/
def viewSlot : Slot := Slot.make 0 "view" (.arr .nat .nat) (.lam (.var 0)) (.lam (.var 0))
def viewObs : Observable := { slot := 0, ty := (.arr .nat .nat) }

def testStateSurvivesSwap : Bool :=
  let rt := Runtime.initial [] [viewSlot]
  let state := 5
  let p0 := rt.snapshot
  match rt.read 1000 p0 viewObs with
  | .error _ => false
  | .ok (v0, rt1) =>
    match applyVal 1000 rt1 v0 (.nat state) with
    | .error _ => false
    | .ok (.nat r0, rt2) =>
      let tx : Transaction :=
        { base := 0
          stages :=
            [{ slot := 0
               body := .lam (.add (.var 0) (.nat 1))
               witness := .lam (.var 0) }] }
      match rt2.commit tx with
      | .error _ => false
      | .ok rt3 =>
        let p1 := rt3.snapshot
        match rt3.read 1000 p1 viewObs with
        | .error _ => false
        | .ok (v1, rt4) =>
          match applyVal 1000 rt4 v1 (.nat state) with
          | .ok (.nat r1, _) => r0 == 5 && r1 == 6
          | _ => false

/-- Test 7: an unpinned `read` is rejected by the checker; `readAt` needs a
`Pinned` in the context. -/
def sigX : Sig := { slots := [(0, .nat)], helpers := [], kernel := kernelVersion }

def testUnpinnedRead : Bool :=
  match check 100 sigX [] false (.read 0) .nat with
  | .error _ => true
  | .ok _ => false

def testReadAtNeedsPinned : Bool :=
  match check 100 sigX [] false (.readAt (.var 0) 0) .nat with
  | .error _ => true
  | .ok _ => false

def testReadAtPinned : Bool :=
  match check 100 sigX [.pinned] false (.readAt (.var 0) 0) .nat with
  | .ok _ => true
  | .error _ => false

/-- Test 9: a linear/resource slot type is rejected before the body is checked. -/
def testLinearSlot : Bool :=
  let r := Slot.make 0 "r" (.uniq .region .nat) (.nat 0) (.nat 0)
  let rt := Runtime.initial [] [r]
  let tx : Transaction :=
    { base := 0, stages := [{ slot := 0, body := .nat 1, witness := .nat 0 }] }
  match rt.commit tx with
  | .error (.notValue _) => true
  | _ => false

/-- Test 10: pure code cannot observe the current generation. -/
def testSnapshotPure : Bool :=
  match check 100 sigX [] false .snapshot .nat with
  | .error _ => true
  | .ok _ => false

/-- The witness restriction: a witness that reads is refused even when it has the
slot's type. This is the circularity `README.md` roadblock 3 describes. -/
def testWitnessReadRejected : Bool :=
  let g := Slot.make 0 "g" (.arr .nat .nat) (.lam (.var 0)) (.lam (.var 0))
  let rt := Runtime.initial [] [g]
  let tx : Transaction :=
    { base := 0
      stages :=
        [{ slot := 0
           body := .lam (.app (.read 0) (.var 0))
           witness := .read 0 }] }
  match rt.commit tx with
  | .error (.witnessFailed _) => true
  | _ => false

/-- Test 12 (interpreter): normal code that mentions no slot is unchanged by a
swap. The same helper term is evaluated before and after; no memo/cache entry for
it is created. -/
def incHelper : Helper :=
  { name := "inc", ty := (.arr .nat .nat), body := .lam (.add (.var 0) (.nat 1)) }

def testNormalCode : Bool :=
  let rt := Runtime.initial [incHelper] [xSlot]
  let before := eval 1000 rt 0 [] (.app (.const "inc") (.nat 1))
  let tx : Transaction :=
    { base := 0, stages := [{ slot := 0, body := .nat 2, witness := .nat 0 }] }
  match rt.commit tx with
  | .error _ => false
  | .ok rt1 =>
    let after := eval 1000 rt1 1 [] (.app (.const "inc") (.nat 1))
    match before, after with
    | .ok (.nat a, _), .ok (.nat b, _) => a == 2 && b == 2 && rt1.memo.length == 0
    | _, _ => false

/-- The cache is generation-independent for a checked body: staging the same
body again is a hit, and its revision is stable when it has no callees. -/
def testCacheHit : Bool :=
  let rt := Runtime.initial [] [xSlot]
  let tx2 : Transaction :=
    { base := 0, stages := [{ slot := 0, body := .nat 2, witness := .nat 0 }] }
  let tx3 : Transaction :=
    { base := 1, stages := [{ slot := 0, body := .nat 3, witness := .nat 0 }] }
  let tx2' : Transaction :=
    { base := 2, stages := [{ slot := 0, body := .nat 2, witness := .nat 0 }] }
  match rt.commit tx2 with
  | .error _ => false
  | .ok rt1 =>
    match rt1.commit tx3 with
    | .error _ => false
    | .ok rt2 =>
      let rev2 := match rt1.revision rt1.snapshot xObs with
        | .ok r => r
        | .error _ => ""
      match rt2.commit tx2' with
      | .error _ => false
      | .ok rt3 =>
        let rev2' := match rt3.revision rt3.snapshot xObs with
          | .ok r => r
          | .error _ => ""
        rt3.cache.hits == 1 && rev2 == rev2'

/-- The versioned internal name: a new body gets a new name; re-staging the old
body keeps its old name (it is the old meaning), so no name is ever rebound. -/
def testInternalNames : Bool :=
  let rt := Runtime.initial [] [xSlot]
  let tx2 : Transaction :=
    { base := 0, stages := [{ slot := 0, body := .nat 2, witness := .nat 0 }] }
  let tx1 : Transaction :=
    { base := 1, stages := [{ slot := 0, body := .nat 1, witness := .nat 0 }] }
  match rt.commit tx2 with
  | .error _ => false
  | .ok rt1 =>
    let s2 := match rt1.findGen 1 with
      | some g => (match g.findSlot 0 with | some s => s.internal | none => "")
      | none => ""
    match rt1.commit tx1 with
    | .error _ => false
    | .ok rt2 =>
      let s1 := match rt2.findGen 2 with
        | some g => (match g.findSlot 0 with | some s => s.internal | none => "")
        | none => ""
      s1 != s2 && s1 == xSlot.internal

/-- A cycle among the staged items' definitional edges is rejected. -/
def testCycle : Bool :=
  let rt := Runtime.initial [] [xSlot, ySlot]
  let tx : Transaction :=
    { base := 0
      stages :=
        [ { slot := 0, body := .nat 2, witness := .nat 0, dependsOn := [1] }
        , { slot := 1, body := .nat 2, witness := .nat 0, dependsOn := [0] } ] }
  match rt.commit tx with
  | .error .cycle => true
  | _ => false

/-- A shape change is a new image, not a hot swap. -/
def testUnknownSlot : Bool :=
  let rt := Runtime.initial [] [xSlot]
  let tx : Transaction :=
    { base := 0, stages := [{ slot := 99, body := .nat 2, witness := .nat 0 }] }
  match rt.commit tx with
  | .error (.unknownSlot 99) => true
  | _ => false

/-- `readNow` is one snapshot + one read; `withPinned` is one snapshot for a
scope. Both are the same value here because there is no swap between them. -/
def testReadNow : Bool :=
  let rt := Runtime.initial [] [xSlot]
  isNat (rt.readNow 1000 xObs) 1

def testWithPinned : Bool :=
  let rt := Runtime.initial [] [xSlot]
  isNat (rt.withPinned 1000 (fun p r => r.read 1000 p xObs)) 1

/-- The `#check` line: the type is stable; slot, generation and revision are an
info message; the value is not printed. -/
def testCheckLine : Bool :=
  let rt := Runtime.initial [] [xSlot]
  let expected :=
    s!"x : Observable Nat\n" ++
    s!"  slot 0, latest checked generation 0, revision {xSlot.revision}\n" ++
    s!"  read it with `read p x` for `p : Pinned`; `snapshot : IO Pinned`"
  match rt.checkLine rt.snapshot xObs with
  | .ok line => line == expected
  | .error _ => false

/-- **Not run.** A queue slot evaluates this list; every entry must be `true`. -/
def tests : List (String × Bool) :=
  [ ("1 a failing swap is rejected", testFailedSwap)
  , ("2 a multi-slot transaction is atomic", testAtomicTransaction)
  , ("3 a pinned reader sees one generation", testSnapshotConsistency)
  , ("6 no stale closure", testNoStaleClosure)
  , ("state survives a view/update swap", testStateSurvivesSwap)
  , ("7 unpinned read is refused", testUnpinnedRead)
  , ("7 readAt needs a Pinned", testReadAtNeedsPinned)
  , ("7 readAt with a Pinned checks", testReadAtPinned)
  , ("9 a linear slot is refused", testLinearSlot)
  , ("10 pure code cannot snapshot", testSnapshotPure)
  , ("witness that reads is refused", testWitnessReadRejected)
  , ("12 normal code is unchanged", testNormalCode)
  , ("cache: a re-staged body is a hit", testCacheHit)
  , ("internal names are versioned, not rebound", testInternalNames)
  , ("a transaction cycle is rejected", testCycle)
  , ("an unknown slot is a shape change", testUnknownSlot)
  , ("readNow", testReadNow)
  , ("withPinned", testWithPinned)
  , ("#check line", testCheckLine)
  ]

end HotReload
