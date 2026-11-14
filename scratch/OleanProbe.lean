import Lean
open Lean

/-- How Lean 4 loads `.olean`: the region reports whether it was mmap'd. -/
unsafe def main : IO Unit := do
  let f : System.FilePath := "/tmp/module-mmap/olean/T.olean"
  let t0 ← IO.monoNanosNow
  let (_, r1) ← readModuleData f
  let t1 ← IO.monoNanosNow
  IO.println s!"first read:  mmap={r1.isMemoryMapped} size={r1.size} time={(t1-t0)/1000000} ms"
  let (_, r2) ← readModuleData f
  IO.println s!"second read: mmap={r2.isMemoryMapped} (first still alive)"
  -- free and read again
  CompactedRegion.free r1
  CompactedRegion.free r2
  let t0 ← IO.monoNanosNow
  let (_, r3) ← readModuleData f
  let t1 ← IO.monoNanosNow
  IO.println s!"after free:  mmap={r3.isMemoryMapped} time={(t1-t0)/1000000} ms"
  CompactedRegion.free r3
  -- 20 mapped reads, freeing each (the normal import path)
  let t0 ← IO.monoNanosNow
  for _ in [0:20] do
    let (_, r) ← readModuleData f
    CompactedRegion.free r
  let t1 ← IO.monoNanosNow
  IO.println s!"20 mmap reads: {(t1-t0)/1000000} ms ({(t1-t0)/20000000} ms each)"
