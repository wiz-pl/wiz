import Tests.Elab

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# Storage slice 3b: one writer, many readers

`drafts/storage-engine/Multiproc.wiz` adds `flock`-based sharing to the durable store:
a reader takes `LOCK_SH` for the meta handshake and then holds a snapshot lease (root +
descriptor) for its cursor, the writer holds `LOCK_EX` for the commit section only, and
validation runs inside that section. `MultiprocTest.wiz` exercises it with two open file
descriptions in one process (which `flock` treats as independent lockers): shared locks
coexist, the commit section waits for the exclusive lock, a scan that crosses a commit
still sees its old pages, two writers from one base either merge (`+1`) or are rejected
(`set`, a transaction begun before a delete), a base outside retention is `expired`, and a
truncated last commit is ignored on reopen.

The case concatenates the draft files (dropping their draft-local imports), because
the suite's loader only serves `lib/` modules. The `SIGKILL`-releases-the-lock case needs
the `flock` utility and is opt-in (`WIZ_MULTIPROC_KILL=1`, which the standalone
`test-multiproc.sh` sets); here it prints its skipped line.
-/

namespace Tests.Elab

def storageMultiprocExpected : String :=
  "lock: shares coexist, exclusive excludes both ways, commit section waits for the lock\n" ++
  "scan: pages 127 3, old values 0 0, new value 1, generation 1 -> 2\n" ++
  "writers: two +1s committed and summed to 3, stale set conflict, stale add merged, " ++
  "post-delete tx stale\n" ++
  "retention: a 9-commit-old base is expired, not rebased\n" ++
  "reopen: torn last commit ignored at generation 2, no lock held, next commit is 4\n" ++
  "kill: skipped (WIZ_MULTIPROC_KILL is not set)\n" ++
  "multiproc: all checks passed\n"

/-- The library imports the draft files need, once, at the top. -/
def storageMultiprocImports : String :=
  "import Sys\nimport Word\nimport Text\nimport WordMap\nimport Functor\nimport MVar\n" ++
  "import Optic\nimport OpticDerive\n\n"

/-- Every `import` line dropped, so the sources form one module. -/
def dropImports (src : String) : String :=
  "\n".intercalate ((src.splitOn "\n").filter (fun l => !(l.startsWith "import ")))

def storageMultiprocBody : IO String := do
  let files := ["drafts/storage-engine/Cursor.wiz",
    "drafts/storage-engine/Storage.wiz",
    "drafts/storage-engine/Registry.wiz",
    "drafts/storage-engine/Durable.wiz",
    "drafts/storage-engine/Multiproc.wiz",
    "drafts/storage-engine/MultiprocTest.wiz"]
  let mut body := storageMultiprocImports
  for f in files do
    body := body ++ dropImports (← IO.FS.readFile f) ++ "\n"
  pure body

def storageMultiproc : IO Unit := do
  cRunLibs (← storageMultiprocBody) storageMultiprocExpected

def storageMultiprocGroup : Group where
  name := "storage-multiproc"
  exercise := "storage slice 3b: flock, snapshot reads, two writers"
  cases := [
    { name := "flock contract: shared readers, deferred commit, mid-scan snapshot, two writers, torn reopen", run := fun _ =>
        storageMultiproc }
  ]

builtin_initialize registerGroup storageMultiprocGroup

end Tests.Elab
