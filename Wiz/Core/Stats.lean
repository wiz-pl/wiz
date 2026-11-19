import Std.Data.HashMap

/-!
# Instrumentation for profiling elaboration (research, off by default)

`WIZ_STATS=1` turns on per-process counters; `WIZ_STATS_TIME=1` also accumulates
nanoseconds in a few functions (top-level only, so nested calls are not double counted).
`wiz check` prints them at the end (`Main.checkCmd`).

This is a measurement harness, not part of the kernel's semantics: nothing here is read
by `eval`, `conv`, `quote` or the checker except when the environment variable is set,
and the result of a run never depends on the counters.

The counters are `UInt64` cells behind `unsafeBaseIO`, as `Budget` and `memoThunk` are;
each `bump` reads the enable flag, which costs a pointer load when off. A timed region
uses `enter`/`leave`: `leave` takes the result as an argument, so the pure result is
computed before the closing clock read (and cannot be moved out of the region by the
compiler).
-/

namespace Wiz.Stats

abbrev Cell := IO.Ref UInt64

initialize enabledRef : IO.Ref Bool ← IO.mkRef false
initialize timeRef : IO.Ref Bool ← IO.mkRef false

unsafe def onImpl : Bool := unsafeBaseIO enabledRef.get
@[implemented_by onImpl] def on : Bool := false

unsafe def timingImpl : Bool := unsafeBaseIO timeRef.get
@[implemented_by timingImpl] def timing : Bool := false

def newCell : IO Cell := IO.mkRef 0

initialize dConv : IO.Ref UInt64 ← IO.mkRef 0
initialize dConvTy : IO.Ref UInt64 ← IO.mkRef 0
initialize dEval : IO.Ref UInt64 ← IO.mkRef 0
initialize dQuote : IO.Ref UInt64 ← IO.mkRef 0
initialize dWhnf : IO.Ref UInt64 ← IO.mkRef 0
initialize dUnify : IO.Ref UInt64 ← IO.mkRef 0
initialize dParse : IO.Ref UInt64 ← IO.mkRef 0

/-- A `UInt64` ref, used only to give `Cell` a default (a `Cells` constant needs one). -/
instance : Inhabited Cell := ⟨dConv⟩

unsafe def bumpImpl (c : Cell) : Unit := unsafeBaseIO do
  if ← enabledRef.get then c.modify (· + 1)
@[implemented_by bumpImpl] def bump (c : Cell) : Unit := ()

unsafe def bumpNImpl (c : Cell) (n : Nat) : Unit := unsafeBaseIO do
  if ← enabledRef.get then c.modify (· + UInt64.ofNat n)
@[implemented_by bumpNImpl] def bumpN (c : Cell) (n : Nat) : Unit := ()

/-- One sample in a histogram with `n` buckets, last bucket `n-1` and up. -/
unsafe def bumpIdxImpl (c : Array Cell) (i : Nat) : Unit := unsafeBaseIO do
  if ← enabledRef.get then
    match c[if i < c.size then i else c.size - 1]? with
    | some r => r.modify (· + 1)
    | none => pure ()
@[implemented_by bumpIdxImpl] def bumpIdx (c : Array Cell) (i : Nat) : Unit := ()

/-- One sample in a size histogram: buckets `0,1,2,3,4,5-8,9-16,17-32,33-64,65+`. -/
unsafe def bumpSizeImpl (c : Array Cell) (n : Nat) : Unit := unsafeBaseIO do
  if ← enabledRef.get then
    let i := if n ≤ 4 then n else if n ≤ 8 then 5 else if n ≤ 16 then 6
             else if n ≤ 32 then 7 else if n ≤ 64 then 8 else 9
    match c[i]? with
    | some r => r.modify (· + 1)
    | none => pure ()
@[implemented_by bumpSizeImpl] def bumpSize (c : Array Cell) (n : Nat) : Unit := ()

/-- Physical identity of two values (the same heap object). -/
unsafe def ptrSameImpl {α : Type} (a : α) (b : α) : Bool := ptrEq a b
@[implemented_by ptrSameImpl] def ptrSame {α : Type} (a : α) (b : α) : Bool := false

initialize probeMap : IO.Ref (Std.HashMap (UInt64 × UInt64 × UInt64) Unit) ← IO.mkRef {}

initialize kernelRef : IO.Ref Bool ← IO.mkRef false

unsafe def inKernelImpl : Bool := unsafeBaseIO kernelRef.get
@[implemented_by inKernelImpl] def inKernel : Bool := false

/-- Mark that the kernel's `addDecl` is on the stack (for splitting conversion counts). -/
unsafe def kernelOnImpl : Unit := unsafeBaseIO (kernelRef.set true)
@[implemented_by kernelOnImpl] def kernelOn : Unit := ()
unsafe def kernelOffImpl : Unit := unsafeBaseIO (kernelRef.set false)
@[implemented_by kernelOffImpl] def kernelOff : Unit := ()

/-- Has this `(a, b, ty)` triple by pointer been seen before in this process? (A probe for
a conversion cache: it says whether the same *objects* are compared again. The map is
cleared at 200k entries, so `hits` is a lower bound on a real cache's hits.) -/
unsafe def probeRepeatImpl {α β γ : Type} (a : α) (b : β) (c : γ) : Bool := unsafeBaseIO do
  if !(← enabledRef.get) then pure false else
  let k := ((ptrAddrUnsafe a).toUInt64, (ptrAddrUnsafe b).toUInt64, (ptrAddrUnsafe c).toUInt64)
  let m ← probeMap.get
  if m.contains k then pure true
  else
    if m.size ≥ 200000 then probeMap.set ((∅ : Std.HashMap (UInt64 × UInt64 × UInt64) Unit).insert k ())
    else probeMap.modify (·.insert k ())
    pure false
@[implemented_by probeRepeatImpl] def probeRepeat {α β γ : Type} (a : α) (b : β) (c : γ) : Bool := false

/-- `n` cells. -/
def hist (n : Nat) : IO (Array Cell) := do
  let mut a : Array Cell := #[]
  for _ in [0:n] do a := a.push (← IO.mkRef 0)
  pure a

def readHist (c : Array Cell) : IO (Array Nat) := c.mapM fun r => do
  let n ← r.get
  pure n.toNat

/-! ### Timed regions

`enter d` reads the clock if `d` was idle (depth 0) and marks this frame as the region's
owner; nested calls only bump the depth. `leave d acc s r` adds the elapsed time for the
owner (with `r` already computed) and restores the depth. -/

structure Stamp where
  top : Bool := false
  t0 : Nat := 0
  deriving Inhabited

unsafe def enterImpl (d : IO.Ref UInt64) : Stamp := unsafeBaseIO do
  if !(← timeRef.get) then pure {} else
  let n ← d.get
  if n == 0 then
    d.set 1
    let t ← IO.monoNanosNow
    pure { top := true, t0 := t }
  else
    d.set (n + 1)
    pure {}
@[implemented_by enterImpl] def enter (d : IO.Ref UInt64) : Stamp := {}

unsafe def leaveImpl {α : Type} (d : IO.Ref UInt64) (acc : Cell) (s : Stamp) (r : α) : α := unsafeBaseIO do
  if !s.top then
    if ← timeRef.get then d.modify (· - 1)
    pure r
  else
    let t1 ← IO.monoNanosNow
    acc.modify (· + UInt64.ofNat (t1 - s.t0))
    d.set 0
    pure r
@[implemented_by leaveImpl] def leave {α : Type} (d : IO.Ref UInt64) (acc : Cell) (s : Stamp) (r : α) : α := r

/-- The cells, named after what they count; `n*` are nanoseconds. -/
structure Cells where
  eval : Cell
  evalApp : Cell
  evalConst : Cell
  evalVar : Cell
  evalLam : Cell
  evalInd : Cell
  inst : Cell
  inst2 : Cell
  vApp : Cell
  vAppLam : Cell
  vAppNeutral : Cell
  vAppGlued : Cell
  whnf : Cell
  whnfUnfold : Cell
  whnfLazyInd : Cell
  vEq : Cell
  vCast : Cell
  quote : Cell
  -- conversion
  conv : Cell
  convTy : Cell
  convNe : Cell
  convGluedTry : Cell
  convGluedSome : Cell
  convGluedInd : Cell
  convPtrSame : Cell
  convRepeat : Cell
  convTyPtrSame : Cell
  convTyRepeat : Cell
  convKernel : Cell
  convElab : Cell
  convTyKernel : Cell
  convTyElab : Cell
  convProofIrr : Cell
  convNeutralAgree : Cell
  convEta : Cell
  isPropCall : Cell
  isPropTrue : Cell
  typeSortCall : Cell
  unCast : Cell
  sameQty : Cell
  -- elaborator
  metaNew : Cell
  metaSolve : Cell
  forceMeta : Cell
  zonk : Cell
  unify : Cell
  unifyFail : Cell
  unifyFailHit : Cell
  inferNe : Cell
  addDecl : Cell
  elabCmd : Cell
  parseCmd : Cell
  -- shapes
  convByType : Array Cell     -- sort pi sigma unit qty enum size desc mu nu neutral ulift other
  convByShape : Array Cell    -- a,b: neutral/other (4)
  convPairSize : Array Cell   -- size(a)+size(b)
  convNeSpine : Array Cell    -- spine length a+b
  quoteByVal : Array Cell     -- quote's argument constructor (40 classes)
  evalByTerm : Array Cell     -- eval's term constructor (64 classes)
  -- time (ns, top-level inclusive)
  nConv : Cell
  nConvTy : Cell
  nEval : Cell
  nQuote : Cell
  nWhnf : Cell
  nUnify : Cell
  nElab : Cell
  nAddDecl : Cell
  nParse : Cell
  nTotal : Cell
  deriving Inhabited

initialize cells : Cells ← do
  let x : Cells := {
    eval := (← newCell), evalApp := (← newCell), evalConst := (← newCell), evalVar := (← newCell)
    evalLam := (← newCell), evalInd := (← newCell), inst := (← newCell), inst2 := (← newCell)
    vApp := (← newCell), vAppLam := (← newCell), vAppNeutral := (← newCell)
    vAppGlued := (← newCell), whnf := (← newCell), whnfUnfold := (← newCell)
    whnfLazyInd := (← newCell), vEq := (← newCell), vCast := (← newCell), quote := (← newCell)
    conv := (← newCell), convTy := (← newCell), convNe := (← newCell)
    convGluedTry := (← newCell), convGluedSome := (← newCell), convGluedInd := (← newCell)
    convPtrSame := (← newCell), convRepeat := (← newCell), convTyPtrSame := (← newCell)
    convTyRepeat := (← newCell), convKernel := (← newCell), convElab := (← newCell)
    convTyKernel := (← newCell), convTyElab := (← newCell), convProofIrr := (← newCell)
    convNeutralAgree := (← newCell), convEta := (← newCell), isPropCall := (← newCell)
    isPropTrue := (← newCell), typeSortCall := (← newCell), unCast := (← newCell)
    sameQty := (← newCell), metaNew := (← newCell), metaSolve := (← newCell)
    forceMeta := (← newCell), zonk := (← newCell), unify := (← newCell)
    unifyFail := (← newCell), unifyFailHit := (← newCell), inferNe := (← newCell)
    addDecl := (← newCell), elabCmd := (← newCell), parseCmd := (← newCell)
    convByType := (← hist 12), convByShape := (← hist 4), convPairSize := (← hist 10)
    convNeSpine := (← hist 10), quoteByVal := (← hist 40), evalByTerm := (← hist 64)
    nConv := (← newCell), nConvTy := (← newCell), nEval := (← newCell), nQuote := (← newCell)
    nWhnf := (← newCell), nUnify := (← newCell), nElab := (← newCell)
    nAddDecl := (← newCell), nParse := (← newCell), nTotal := (← newCell) }
  pure x

/-- Turn counting on (from `Main`). -/
def start (timed : Bool) : IO Unit := do
  enabledRef.set true
  if timed then timeRef.set true

/-- Print every counter as `stat<TAB>name<TAB>value` on stderr, and the histograms as
comma-separated buckets. -/
def report : IO Unit := do
  let cs := cells
  let one (n : String) (c : Cell) : IO Unit := do
    let v ← c.get
    IO.eprintln s!"stat\t{n}\t{v}"
  let hist (n : String) (c : Array Cell) : IO Unit := do
    let xs ← readHist c
    let v := ",".intercalate (xs.toList.map toString)
    IO.eprintln s!"hist\t{n}\t{v}"
  one "eval" cs.eval; one "evalApp" cs.evalApp; one "evalConst" cs.evalConst
  one "evalVar" cs.evalVar; one "evalLam" cs.evalLam
  one "inst" cs.inst; one "inst2" cs.inst2
  one "vAppLam" cs.vAppLam; one "vAppNeutral" cs.vAppNeutral; one "vAppGlued" cs.vAppGlued
  one "whnf" cs.whnf; one "whnfUnfold" cs.whnfUnfold; one "whnfLazyInd" cs.whnfLazyInd
  one "vEq" cs.vEq; one "vCast" cs.vCast
  one "quote" cs.quote; one "conv" cs.conv; one "convTy" cs.convTy; one "convNe" cs.convNe
  one "convGluedTry" cs.convGluedTry; one "convGluedSome" cs.convGluedSome
  one "convGluedInd" cs.convGluedInd; one "convPtrSame" cs.convPtrSame
  one "convRepeat" cs.convRepeat; one "convTyPtrSame" cs.convTyPtrSame
  one "convTyRepeat" cs.convTyRepeat; one "convKernel" cs.convKernel
  one "convElab" cs.convElab; one "convTyKernel" cs.convTyKernel; one "convTyElab" cs.convTyElab
  one "convProofIrr" cs.convProofIrr; one "convNeutralAgree" cs.convNeutralAgree
  one "convEta" cs.convEta; one "isPropCall" cs.isPropCall; one "isPropTrue" cs.isPropTrue
  one "typeSortCall" cs.typeSortCall; one "unCast" cs.unCast
  one "metaNew" cs.metaNew; one "metaSolve" cs.metaSolve; one "forceMeta" cs.forceMeta
  one "zonk" cs.zonk; one "unify" cs.unify; one "unifyFail" cs.unifyFail
  one "unifyFailHit" cs.unifyFailHit; one "inferNe" cs.inferNe; one "addDecl" cs.addDecl
  one "elabCmd" cs.elabCmd; one "parseCmd" cs.parseCmd
  one "nConv" cs.nConv; one "nConvTy" cs.nConvTy; one "nEval" cs.nEval
  one "nQuote" cs.nQuote; one "nWhnf" cs.nWhnf; one "nUnify" cs.nUnify
  one "nElab" cs.nElab; one "nAddDecl" cs.nAddDecl; one "nParse" cs.nParse
  one "nTotal" cs.nTotal
  hist "convByType" cs.convByType; hist "convByShape" cs.convByShape
  hist "convPairSize" cs.convPairSize; hist "convNeSpine" cs.convNeSpine
  hist "quoteByVal" cs.quoteByVal; hist "evalByTerm" cs.evalByTerm

end Wiz.Stats
