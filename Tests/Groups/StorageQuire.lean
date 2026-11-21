import Tests.Elab

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# Quire: the page-backed store, its page cursor and its page-read assertions

`drafts/storage-engine/Quire.wiz` is the constant-page commit/open engine (a two-level
directory, index fact chains, format 2); `QuireCursor.wiz` is the page cursor
(`indexCursor`/`filterKey`, `Cost.pages`); `QuireTest.wiz` exercises both: a batched seed,
an update through the lens, a delete, stale/unique rejection, reopen, the page counts
(equality reads one slot's pages, a full scan reads every slot's, a range reads its
values' slots, and an index-only scan reads no primary page), and group commit (`putMany`:
one generation for a batch, the crash between its pages and its commit record, a stale
entry rejected on its own, and unique collisions against the base and inside the batch).

The case concatenates the modules (the suite's loader only serves `lib/` modules), as the
`storage-mmap` and `storage-multiproc` cases do.
-/

namespace Tests.Elab

/-- The library imports the draft files need, once, at the top. -/
def storageQuireImports : String :=
  "import Sys\nimport Word\nimport Text\nimport WordMap\nimport Functor\nimport MVar\n" ++
  "import WordArray\nimport IO\nimport Optic\nimport OpticDerive\n\n"

/-- Every `import` line dropped, so the sources form one module. -/
def dropImportsQ (src : String) : String :=
  "\n".intercalate ((src.splitOn "\n").filter (fun l => !(l.startsWith "import ")))

def storageQuireBody : IO String := do
  let files := ["drafts/storage-engine/Core.wiz",
    "drafts/storage-engine/Storage.wiz",
    "drafts/storage-engine/Cursor.wiz",
    "drafts/storage-engine/Registry.wiz",
    "drafts/storage-engine/Durable.wiz",
    "drafts/storage-engine/Mmap.wiz",
    "drafts/storage-engine/Quire.wiz",
    "drafts/storage-engine/QuireCursor.wiz",
    "drafts/storage-engine/QuireTest.wiz"]
  let mut body := storageQuireImports
  for f in files do
    body := body ++ dropImportsQ (← IO.FS.readFile f) ++ "\n"
  -- the case has no source file, so `link_c` resolves against the repo root
  pure (body.replace "link_c \"quire_seal.c\"" "link_c \"drafts/storage-engine/quire_seal.c\"")

def storageQuireExpected : String :=
  "quire: all checks passed: 60\n"

def storageQuire : IO Unit := do
  -- the C companion's header (`quire_seal.h`) is on the draft include path
  cRunLibs (← storageQuireBody) storageQuireExpected (cflags := ["-Idrafts/storage-engine"])

def storageQuireGroup : Group where
  name := "storage-quire"
  exercise := "storage: page-backed commits, opens and page-cursor costs"
  cases := [
    { name := "page commits/open/query: index facts, page counts, stale/unique, reopen", run := fun _ =>
        storageQuire }
  ]

builtin_initialize registerGroup storageQuireGroup

end Tests.Elab
