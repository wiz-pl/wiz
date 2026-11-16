import Lean.Data.Json

/-!
# Profiling a build

`wiz build --profile` times the phases of a build: the elaboration of each declaration,
the check of each imported module, the IR passes, code generation, the C compiler and the
linker, and how much of the elaboration came from the cache. `--profile-json FILE` writes
the same numbers for tooling (`scripts/profile-build.sh`).

Instrumentation is **off by default**: the frontend checks one `Bool`
(`CommandState.profile`) per command and takes no clock reading unless it is set; the
backend's phases are a handful of calls, each behind one `Profile.phase` check. The
reading is a monotonic clock (`IO.monoNanosNow`) behind `Profile.nowNanos`, an `opaque`
with an `implemented_by` (as the isolation cache does), so that the pure frontend can
time a command without becoming `IO`: same pattern as `Budget.tick`
(`Wiz/Core/Term.lean`).

What is **not** attributed: process start-up, parsing (beyond a command's own
elaboration), option handling, garbage collection, file-system I/O inside a phase, the C
compiler's own internal parallelism, and the time the OS takes to schedule the process.
The phases are wall time, not CPU time; nested module spans include the modules they
import, and a module's span includes its declarations (both are marked in the table).
-/

open Lean (Json)

namespace Wiz.Profile

/-- One timed thing: a declaration command, an imported module, or a phase. -/
structure Entry where
  /-- the declaration's name, the module's name, or the phase's name -/
  name : String
  /-- `def`, `theorem`, … (a command kind), `module`, or `phase` -/
  kind : String := ""
  /-- the module a declaration was checked in (`""` is the file being built) -/
  module : String := ""
  /-- for modules: `hit` (replayed from the cache) or `miss` (checked now) -/
  status : String := ""
  /-- wall time, in nanoseconds -/
  ns : Nat := 0
  deriving Inhabited, Repr, BEq

/-- Everything a build recorded. -/
structure Data where
  declarations : Array Entry := #[]
  modules : Array Entry := #[]
  phases : Array Entry := #[]
  /-- commands served from the cache -/
  hits : Nat := 0
  /-- commands elaborated (a cache miss, or no cache at all) -/
  misses : Nat := 0
  deriving Inhabited, Repr

initialize dataRef : IO.Ref Data ← IO.mkRef {}
initialize enabledRef : IO.Ref Bool ← IO.mkRef false

/-- Is profiling on? (Off by default.) -/
def enabled : IO Bool := enabledRef.get

/-- Start a profile: clear what an earlier run in this process recorded. -/
def start : IO Unit := do
  dataRef.set {}
  enabledRef.set true

def stop : IO Unit := enabledRef.set false

/-- The monotonic clock, read from pure code. -/
@[never_extract, noinline] unsafe def nowImpl (_ : Unit) : Nat := unsafeBaseIO IO.monoNanosNow
@[implemented_by nowImpl] opaque nowNanos : Unit → Nat

/-- Record a declaration command's time (called from the pure frontend). Returns the value
it is given, so that the command's result depends on the recording (a pure `Unit` call
could be dropped as dead code). -/
@[never_extract, noinline] unsafe def recordDeclImpl {α : Type} [Inhabited α] (x : α) (name kind module : String)
    (ns : Nat) : α :=
  unsafeBaseIO do
    if ← enabledRef.get then
      dataRef.modify fun d => { d with declarations := d.declarations.push { name, kind, module, ns } }
    pure x
@[implemented_by recordDeclImpl] opaque recordDecl {α : Type} [Inhabited α] (x : α) (name kind module : String)
  (ns : Nat) : α

/-- Add to a phase's time (a phase may run more than once, as `object` does in a split
build). -/
def addPhase (d : Data) (name : String) (ns : Nat) : Data :=
  match d.phases.findIdx? (·.name == name) with
  | some i => { d with phases := d.phases.set! i { d.phases[i]! with ns := d.phases[i]!.ns + ns } }
  | none => { d with phases := d.phases.push { name, kind := "phase", ns } }

def phaseIO (name : String) (ns : Nat) : IO Unit := do
  if ← enabledRef.get then dataRef.modify (addPhase · name ns)

/-- Like `recordDecl`, the value is returned, so a pure caller cannot drop the
recording as dead code. -/
@[never_extract, noinline] unsafe def recordPhaseImpl {α : Type} [Inhabited α] (x : α) (name : String)
    (ns : Nat) : α :=
  unsafeBaseIO do
    if ← enabledRef.get then dataRef.modify (addPhase · name ns)
    pure x
@[implemented_by recordPhaseImpl] opaque recordPhase {α : Type} [Inhabited α] (x : α) (name : String)
  (ns : Nat) : α

/-- A command came from the cache. -/
def cacheHit : IO Unit := do
  if ← enabledRef.get then dataRef.modify fun d => { d with hits := d.hits + 1 }

/-- A command had to be elaborated. -/
def cacheMiss : IO Unit := do
  if ← enabledRef.get then dataRef.modify fun d => { d with misses := d.misses + 1 }

/-- The cache counters (hits, misses), for taking a difference around a module. -/
def cacheCounts : IO (Nat × Nat) := do
  let d ← dataRef.get
  pure (d.hits, d.misses)

/-- Record an imported module's check, and whether it came from the cache. -/
def recordModule (m status : String) (ns : Nat) : IO Unit := do
  if ← enabledRef.get then
    dataRef.modify fun d => { d with modules := d.modules.push { name := m, kind := "module", module := m, status, ns } }

/-- Time an IO phase. One branch when profiling is off. -/
def phase {α : Type} (name : String) (act : IO α) : IO α := do
  if !(← enabledRef.get) then act else
    let t0 ← IO.monoNanosNow
    let a ← act
    phaseIO name ((← IO.monoNanosNow) - t0)
    pure a

def getData : IO Data := dataRef.get

def phaseNs (d : Data) (name : String) : Nat :=
  match d.phases.find? (·.name == name) with
  | some e => e.ns
  | none => 0

/-! ## The table -/

/-- Milliseconds with one decimal (`12.3`), without a `Float` printer. -/
def msText (ns : Nat) : String :=
  let tenths := ns / 100000
  s!"{tenths / 10}.{tenths % 10}"

/-- Percent of `total` with one decimal (`12.3`). -/
def pctText (ns total : Nat) : String :=
  if total == 0 then "0.0" else
  let tenths := ns * 1000 / total
  s!"{tenths / 10}.{tenths % 10}"

def padLeft (s : String) (n : Nat) : String :=
  if s.length ≥ n then s else String.ofList (List.replicate (n - s.length) ' ') ++ s

def padRight (s : String) (n : Nat) : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) ' ')

def byCost (es : Array Entry) : Array Entry := es.qsort fun a b => decide (a.ns > b.ns)

def line (total : Nat) (e : Entry) : String :=
  let what :=
    if e.kind == "module" then s!"module {e.name}" ++ (if e.status.isEmpty then "" else s!" ({e.status})")
    else if e.kind == "phase" then e.name
    else if e.kind.isEmpty then e.name
    else s!"{e.kind} {e.name}"
  let source :=
    if e.module.isEmpty || e.kind == "module" || e.kind == "phase" then "" else s!"  [{e.module}]"
  s!"  {padLeft (pctText e.ns total) 5}% {padLeft (msText e.ns) 9} ms  {padRight what 44} {source}"

/-- Print the table: declarations and modules (elaboration), then the backend phases,
each sorted by cost, with a percentage of the total. Declarations are capped at 25 rows;
`--profile-json` has all of them. -/
def report (total : Nat) (d : Data) : IO Unit := do
  let decls := byCost d.declarations
  let mods := byCost d.modules
  let phases := byCost (d.phases.filter (·.name != "elaboration"))
  IO.println ""
  IO.println s!"wiz build --profile: total {msText total} ms"
  IO.println s!"  elaboration {msText (phaseNs d "elaboration")} ms, cache {d.hits} hits, {d.misses} misses"
  IO.println ""
  IO.println "  %      time  declaration"
  for e in decls.take 25 do IO.println (line total e)
  if decls.size > 25 then
    IO.println s!"  … {decls.size - 25} more declarations (see --profile-json)"
  if !mods.isEmpty then
    IO.println ""
    IO.println "  %      time  module check (includes its declarations)"
    for e in mods do IO.println (line total e)
  IO.println ""
  IO.println "  %      time  backend phase"
  for e in phases do IO.println (line total e)
  IO.println ""
  IO.println "  not attributed: process start-up, parsing, option handling, GC, I/O inside a phase"

/-! ## The JSON -/

def entryJson (e : Entry) : Json :=
  Json.mkObj [("name", Json.str e.name), ("kind", Json.str e.kind), ("module", Json.str e.module),
              ("status", Json.str e.status), ("ns", Json.num e.ns)]

/-- The machine-readable record. Every backend phase is present (0 when the build did not
run it), so a tool can read a fixed set of keys. -/
def toJson (total : Nat) (d : Data) : Json :=
  Json.mkObj [
    ("schema", 1),
    ("generator", "wiz build --profile"),
    ("total_ns", Json.num total),
    ("elaboration_ns", Json.num (phaseNs d "elaboration")),
    ("declarations", Json.arr (d.declarations.map entryJson)),
    ("modules", Json.arr (d.modules.map entryJson)),
    ("backend", Json.mkObj [
      ("ir_ns", Json.num (phaseNs d "ir")),
      ("lower_ns", Json.num (phaseNs d "lower")),
      ("optimize_ns", Json.num (phaseNs d "optimize")),
      ("codegen_ns", Json.num (phaseNs d "codegen")),
      ("object_ns", Json.num (phaseNs d "object")),
      ("link_ns", Json.num (phaseNs d "link"))]),
    ("cache", Json.mkObj [("hits", Json.num d.hits), ("misses", Json.num d.misses)])]

/-- Finish a profile: write the JSON (if asked), print the table (if asked), turn the
instrumentation off. -/
def finish (total : Nat) (table : Bool) (json : Option String) : IO Unit := do
  let d ← dataRef.get
  if let some path := json then
    IO.FS.writeFile path (Json.pretty (toJson total d) ++ "\n")
  if table then report total d
  enabledRef.set false

end Wiz.Profile
