import Tests.Elab

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# Quire: the page-backed store, its page cursor and its page-read assertions

The engine is `lib/Scry/Quire.wiz` (the constant-page commit/open engine: a two-level
directory, index fact chains, format 2) and `lib/Scry/QuireCursor.wiz` (the page cursor:
`indexCursor`/`filterKey`, `Cost.pages`). The test body is
`drafts/storage-engine/QuireTest.wiz`: a batched seed, an update through the lens, a
delete, stale/unique rejection, reopen, the page counts (equality reads one slot's pages,
a full scan reads every slot's, a range reads its values' slots, and an index-only scan
reads no primary page), and group commit (`putMany`: one generation for a batch, the crash
between its pages and its commit record, a stale entry rejected on its own, and unique
collisions against the base and inside the batch).

The case is built with `linkRun`, which resolves modules and `link_c` from the tree the
way `wiz` does; the engine's C companion (`lib/Scry/quire_seal.c`) is linked from its own
directory, so the case no longer rewrites the `link_c` path.
-/

namespace Tests.Elab

/-- The imports the test body needs, once, at the top. -/
def storageQuireImports : String :=
  "import Sys\nimport Word\nimport Text\nimport WordMap\nimport Functor\nimport MVar\n" ++
  "import WordArray\nimport IO\nimport Optic\nimport OpticDerive\n" ++
  "import Scry.Quire\nimport Scry.QuireCursor\nimport Scry.Quire.Storage\n\n"

/-- Every `import` line dropped, so the body forms the main file. -/
def dropImportsQ (src : String) : String :=
  "\n".intercalate ((src.splitOn "\n").filter (fun l => !(l.startsWith "import ")))

def storageQuireSource : IO String := do
  let body ← IO.FS.readFile "drafts/storage-engine/QuireTest.wiz"
  pure (storageQuireImports ++ dropImportsQ body ++ "\n")

def storageQuireExpected : String :=
  "quire: all checks passed: 60\n"

def storageQuire : IO Unit := do
  linkRun [("main.wiz", ← storageQuireSource)] storageQuireExpected

def storageQuireGroup : Group where
  name := "storage-quire"
  exercise := "storage: page-backed commits, opens and page-cursor costs"
  cases := [
    { name := "page commits/open/query: index facts, page counts, stale/unique, reopen", run := fun _ =>
        storageQuire }
  ]

builtin_initialize registerGroup storageQuireGroup

end Tests.Elab
