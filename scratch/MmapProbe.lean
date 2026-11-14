import Lean.CompactedRegion
import Wiz

/-! Probe for `/workspace/wiz-notes/module-mmap.md`:
1. cold/warm time of `Cache.elaborateCached` vs `Cache.elaborateUncached`, with hits;
2. cost of decoding one `.wizc` (S-expression) entry;
3. round trip of the same `Cache.Effect` through `Lean.CompactedRegion` (mmap-able);
4. attempt to compact a whole `Globals` (expected: the `pp.run` closure blocks it). -/

open Wiz

def ms (a b : Nat) : String := toString ((b - a) / 1000000) ++ " ms"

def mkInit (lib : Std.HashMap Name String) : CommandState ZeroOneMany :=
  { loader := (lib[·]?), trustedModule := fun _ => false }

def names (e : Cache.Effect ZeroOneMany) : Array Name := e.decls.map (·.name)

unsafe def main : IO Unit := do
  let roots ← Module.roots ["lib"]
  let input ← match ← IO.getEnv "SRC" with
    | some f => IO.FS.readFile f
    | none => pure "import Prelude\nimport Std\n\ndef x : Nat := 2 + 2\n"
  let closure ← Module.loadClosure roots input
  let lib := closure.fold (fun m n (_, src) => m.insert n src) ({} : Std.HashMap Name String)
  let init := mkInit lib
  IO.println s!"modules: {closure.size}"

  let dir : System.FilePath := ((← IO.getEnv "CACHEDIR").map System.FilePath.mk).getD "/tmp/module-mmap/c3"
  if (← IO.getEnv "CLEAN").isSome && (← dir.pathExists) then IO.FS.removeDirAll dir
  let t0 ← IO.monoNanosNow
  let (s1, h1) ← Cache.elaborateCached dir input init 0
  let t1 ← IO.monoNanosNow
  let (_, h2) ← Cache.elaborateCached dir input init 0
  let t2 ← IO.monoNanosNow
  let (_, h3) ← Cache.elaborateCached dir input init 0
  let t3 ← IO.monoNanosNow
  IO.println s!"cached cold: {ms t0 t1} hits={h1} decls={s1.globals.order.size}"
  IO.println s!"cached warm: {ms t1 t2} hits={h2}"
  IO.println s!"cached warm: {ms t2 t3} hits={h3}"
  let t0 ← IO.monoNanosNow
  let s0 ← Cache.elaborateUncached input init
  let t1 ← IO.monoNanosNow
  IO.println s!"uncached:    {ms t0 t1} decls={s0.globals.order.size}"
  let mut n := 0
  let mut bytes : Nat := 0
  for e in ← dir.readDir do
    let st ← e.path.metadata
    n := n + 1
    bytes := bytes + st.byteSize.toNat
  IO.println s!"cache files: {n}, {bytes} bytes"

  -- (1b) decode the whole cache: how much of a warm run is S-expression decoding?
  let t0 ← IO.monoNanosNow
  let mut decoded := 0
  let mut failed := 0
  let mut textBytes : Nat := 0
  let decodeDir : System.FilePath := ((← IO.getEnv "WIZCACHE").map System.FilePath.mk).getD dir
  for e in ← decodeDir.readDir do
    if !e.fileName.endsWith ".wizc" then continue
    let text ← IO.FS.readFile e.path
    textBytes := textBytes + text.utf8ByteSize
    match Cache.Sx.parse text with
    | none => failed := failed + 1
    | some sx =>
      match Cache.Effect.ofSx? (R := ZeroOneMany) sx with
      | none => failed := failed + 1
      | some _ => decoded := decoded + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"decode all ({decodeDir}): {ms t0 t1} for {decoded} entries ({textBytes} text bytes), {failed} failed"

  -- (2) one artifact
  let some wizc ← IO.getEnv "WIZC" | IO.println "no WIZC"; return
  let text ← IO.FS.readFile wizc
  IO.println s!"wizc: {wizc}, {text.utf8ByteSize} bytes"
  let t0 ← IO.monoNanosNow
  let some sx := Cache.Sx.parse text | IO.println "Sx.parse failed"; return
  let t1 ← IO.monoNanosNow
  IO.println s!"Sx.parse: {ms t0 t1}"
  let some (e : Cache.Effect ZeroOneMany) := Cache.Effect.ofSx? (R := ZeroOneMany) sx
    | IO.println s!"Effect.ofSx? failed: {text.take 80}"; return
  let t2 ← IO.monoNanosNow
  IO.println s!"Effect.ofSx?: {ms t1 t2}, decls={e.decls.size}, infos={e.infos.size}"
  for _ in [1,2,3] do
    let t0 ← IO.monoNanosNow
    let some sx := Cache.Sx.parse text | return
    let t1 ← IO.monoNanosNow
    let some (_ : Cache.Effect ZeroOneMany) := Cache.Effect.ofSx? (R := ZeroOneMany) sx | return
    let t2 ← IO.monoNanosNow
    IO.println s!"decode repeat: parse {ms t0 t1}, ofSx {ms t1 t2}"

  -- (3) compacted region
  let ef : System.FilePath := "/tmp/module-mmap/effect.cregion"
  if ← ef.pathExists then IO.FS.removeFile ef
  let t0 ← IO.monoNanosNow
  let _ ← Lean.CompactedRegion.save ef `probe e #[] none
  let t1 ← IO.monoNanosNow
  let st ← ef.metadata
  IO.println s!"CompactedRegion.save: {ms t0 t1}, {st.byteSize.toNat} bytes"
  for _ in [1,2,3] do
    let t0 ← IO.monoNanosNow
    let (e2, r) ← Lean.CompactedRegion.read (α := Cache.Effect ZeroOneMany) ef #[]
    let t1 ← IO.monoNanosNow
    IO.println s!"CompactedRegion.read: {ms t0 t1}, decls={e2.decls.size}, mmap={r.isMemoryMapped}, same names={names e2 == names e}"
  -- (4) Globals
  let gf : System.FilePath := "/tmp/module-mmap/globals.cregion"
  if ← gf.pathExists then IO.FS.removeFile gf
  try
    let _ ← Lean.CompactedRegion.save gf `probe s1.globals #[] none
    IO.println "Globals saved (no closure!)"
  catch err =>
    IO.println s!"Globals save failed: {err}"

  -- (4b) the declaration map alone (the bulk of a module environment), and an array of
  -- all effects of the cache: one region per module instead of one per command
  for (what, f) in [("decls", "/tmp/module-mmap/decls.cregion")] do
    if ← (System.FilePath.mk f).pathExists then IO.FS.removeFile f
    let t0 ← IO.monoNanosNow
    let _ ← Lean.CompactedRegion.save f `declarations s1.globals.decls #[] none
    let t1 ← IO.monoNanosNow
    let st ← (System.FilePath.mk f).metadata
    let t2 ← IO.monoNanosNow
    let (m2, r) ← Lean.CompactedRegion.read (α := Std.HashMap Name (Decl ZeroOneMany)) f #[]
    let t3 ← IO.monoNanosNow
    let got := s1.globals.order.filter (fun n => m2.contains n) |>.size
    IO.println s!"{what}: save {ms t0 t1}, {st.byteSize.toNat} bytes, read {ms t2 t3}, mmap={r.isMemoryMapped}, found {got}/{s1.globals.order.size}"
  let ef2 : System.FilePath := "/tmp/module-mmap/effects.cregion"
  if ← ef2.pathExists then IO.FS.removeFile ef2
  let mut es : Array (Cache.Effect ZeroOneMany) := #[]
  for e in ← dir.readDir do
    if !e.fileName.endsWith ".wizc" then continue
    match Cache.Sx.parse (← IO.FS.readFile e.path) with
    | some sx => if let some e := Cache.Effect.ofSx? (R := ZeroOneMany) sx then es := es.push e
    | none => pure ()
  let t0 ← IO.monoNanosNow
  let _ ← Lean.CompactedRegion.save ef2 `effects es #[] none
  let t1 ← IO.monoNanosNow
  let st ← ef2.metadata
  let t2 ← IO.monoNanosNow
  let (es2, r) ← Lean.CompactedRegion.read (α := Array (Cache.Effect ZeroOneMany)) ef2 #[]
  let t3 ← IO.monoNanosNow
  IO.println s!"effects array ({es.size}): save {ms t0 t1}, {st.byteSize.toNat} bytes, read {ms t2 t3}, mmap={r.isMemoryMapped}, decls {es2.foldl (fun n e => n + e.decls.size) 0}"
  -- (5) replay cost: applying the decoded effects, vs inserting the decls into a map
  let t0 ← IO.monoNanosNow
  let mut st' := init
  for e in es do st' := e.apply st'
  let t1 ← IO.monoNanosNow
  IO.println s!"Effect.apply x{es.size}: {ms t0 t1}, decls={st'.globals.order.size}"
  let t2 ← IO.monoNanosNow
  let mut m : Std.HashMap Name (Decl ZeroOneMany) := {}
  for e in es do for d in e.decls do m := m.insert d.name d
  let t3 ← IO.monoNanosNow
  IO.println s!"HashMap.insert x{m.size}: {ms t2 t3}"
  -- (6) warm run with the effects kept in memory: how much of warm is decode + file I/O?
  let bin ← Cache.binaryId (some dir)
  let disk ← Cache.Store.disk dir bin
  let memo ← IO.mkRef ({} : Std.HashMap UInt64 (Cache.Effect ZeroOneMany))
  let memStore : Cache.Store ZeroOneMany := {
    get := fun k => do
      match (← memo.get)[k]? with
      | some e => pure (some e)
      | none => do
        let r ← disk.get k
        if let some e := r then memo.modify (·.insert k e)
        pure r
    put := disk.put
    seen := disk.seen
    markSeen := disk.markSeen }
  let t0 ← IO.monoNanosNow
  let (_, hm) ← Cache.elaborateWith memStore input init 0
  let t1 ← IO.monoNanosNow
  let (_, hm2) ← Cache.elaborateWith memStore input init 0
  let t2 ← IO.monoNanosNow
  IO.println s!"memory store cold: {ms t0 t1} hits={hm}, again: {ms t1 t2} hits={hm2} (memo {(← memo.get).size})"



