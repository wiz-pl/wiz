import Tests.Elab

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# Storage slice 3: the `mmap` read path

`drafts/storage-engine/Mmap.wiz` is the read-only page decoder (the `mmap` native, the
32-byte page header and node records, the B+tree walk, the two meta slots, and a page
checksum that can be skipped). `drafts/storage-engine/MmapTest.wiz` builds a store file
in the version-1 format those modules document, maps it read-only and reads it: a torn
newer meta slot is ignored, three nodes and an index bucket are found, an unaligned load
is exact, and an out-of-range read is an error rather than a fault. A second file has a
corrupted leaf so the test can show `verify := true` reporting `corrupt` and
`verify := false` reading the page.

The case concatenates the decoder and the test (the test's own `import Mmap` line is
dropped), because the suite's loader only serves `lib/` modules.
-/

namespace Tests.Elab

def storageMmapExpected : String :=
  "len 24576\n" ++
  "maplen 24576\n" ++
  "gen 5\n" ++
  "root 4 index 5\n" ++
  "n10 10 1 100 7 5\n" ++
  "n20 20 2 200 8 5\n" ++
  "n30 30 1 300 9 5\n" ++
  "absent none\n" ++
  "bucket1 2 10 30\n" ++
  "bucket2 1 20\n" ++
  "bucket3 0\n" ++
  "oob none\n" ++
  "unaligned ok\n" ++
  "badpage outOfRange\n" ++
  "verify corrupt\n" ++
  "skip 10 1 100 99 5\n" ++
  "clean 20 2 200 8 5\n"

def storageMmap : IO Unit := do
  let decoder ← IO.FS.readFile "drafts/storage-engine/Mmap.wiz"
  let test ← IO.FS.readFile "drafts/storage-engine/MmapTest.wiz"
  let fragment := "\n".intercalate
    ((test.splitOn "\n").filter (fun l => !l.startsWith "import "))
  cRunLibs (decoder ++ "\n" ++ fragment) storageMmapExpected

def storageMmapGroup : Group where
  name := "storage-mmap"
  exercise := "storage slice 3: mmap reads"
  cases := [
    { name := "mmap a version-1 file: meta pick, checksums, walk, index bucket, out-of-range", run := fun _ =>
        storageMmap }
  ]

builtin_initialize registerGroup storageMmapGroup

end Tests.Elab
