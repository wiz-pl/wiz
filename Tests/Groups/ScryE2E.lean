import Wiz
import Tests.Harness

/-!
# The corpus parse invariant (`scry-e2e`)

The C and C# frontends parse with two different tree-sitter grammars. A spill under
`scry/corpus/**` records which grammar produced it (`language\tc` / `language\tc_sharp`)
and one flags column per node (`ERROR` = 2, `MISSING` = 4). This group is the cheap,
native-free half of the invariant:

* every checked-in `.cst` spill names the grammar its source file needs (`.cs` →
  `c_sharp`, everything else → `c`), so a `.cs` parsed as C fails here even without the
  native shim;
* every spill has **0** `ERROR`/`MISSING` nodes, unless its source is listed in
  `scry/corpus/parse-errors.tsv` with a reason;
* every exemption row names an existing source, and a row whose spill is now clean is a
  stale exemption (a regression in the other direction).

`scry/tests/corpus-parse.wiz` is the from-source half: it parses every `.c`/`.cs` with
the native grammars in CI's scry goldens job, including the files that have no spill.
-/

open Wiz

namespace Tests.ScryE2E

partial def walk (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut out : List System.FilePath := []
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← walk e.path)
    else
      out := out ++ [e.path]
  pure out

def fields (l : String) : List String := l.splitOn "\t"

def natAt (l : String) (i : Nat) : Nat :=
  match (List.getD (fields l) i "").toNat? with
  | some n => n
  | none => 0

def headerValue (lines : List String) (key : String) : Option String :=
  lines.findSome? fun l =>
    if l.startsWith (key ++ "\t") then some (l.drop (key.length + 1)).toString else none

def sectionIndex (lines : List String) (key : String) : Option Nat :=
  lines.findIdx? fun l => l.startsWith (key ++ "\t")

def nodeCount (lines : List String) : Nat :=
  match headerValue lines "nodes" with
  | some s => match s.trimAscii.toString.toNat? with | some n => n | none => 0
  | none => 0

/-- `ERROR` (flag 2) or `MISSING` (flag 4) nodes in the spill's node section. -/
def errorNodes (lines : List String) : Nat :=
  match sectionIndex lines "nodes" with
  | none => 0
  | some i =>
    let rows := (lines.drop (i + 1)).take (nodeCount lines)
    rows.countP fun l =>
      let f := natAt l 2
      (f / 2) % 2 == 1 || (f / 4) % 2 == 1

/-- The source beside a spill: `x.cst` → `x`, `x.c`, or `x.cs` (the last covers
`main.i.cst`'s preprocessed source, which is C). -/
def sourceOf (p : System.FilePath) : IO (Option System.FilePath) := do
  let s := p.toString
  if !s.endsWith ".cst" then pure none
  else
    let stem := (s.dropEnd 4).toString
    let mut found : Option System.FilePath := none
    for c in [stem, stem ++ ".c", stem ++ ".cs"] do
      if found.isNone then
        if ← (System.FilePath.mk c).pathExists then
          found := some (System.FilePath.mk c)
    pure found

def expectedLang (src : System.FilePath) : String :=
  if src.toString.endsWith ".cs" then "c_sharp" else "c"

/-- `path<TAB>reason`, skipping comments and blank lines. -/
def manifest : IO (List (String × String)) := do
  let text ← IO.FS.readFile "scry/corpus/parse-errors.tsv"
  let rows := (text.splitOn "\n").filterMap fun (line : String) =>
    let l := line.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then none
    else match l.splitOn "\t" with
      | p :: r :: _ => some (p.trimAscii.toString, r.trimAscii.toString)
      | _ => none
  pure rows

/-- The manifest is relative to `scry/` (the Wiz test's working directory); the Lean
suite runs at the repository root. -/
def scryRel (p : String) : String :=
  if p.startsWith "scry/" then (p.drop 5).toString else p

def exempt (rows : List (String × String)) (src : String) : Bool :=
  rows.any fun r => r.1 == scryRel src

def spillFailure (rows : List (String × String)) (p : System.FilePath) :
    IO (Option String) := do
  match ← sourceOf p with
  | none => pure (some s!"{p}: no source file beside the spill")
  | some src =>
    let text ← IO.FS.readFile p
    let lines := text.splitOn "\n"
    let want := expectedLang src
    let got := (headerValue lines "language").getD ""
    if got != want then
      pure (some s!"{p}: language \"{got}\", expected \"{want}\" for {src}")
    else
      let n := errorNodes lines
      let ex := exempt rows src.toString
      if n > 0 && !ex then
        pure (some s!"{p}: {n} ERROR/MISSING node(s) in a file expected to parse")
      else if n == 0 && ex then
        pure (some s!"{p}: stale exemption for {src} (the spill now parses)")
      else pure none

def corpusSpills : IO Unit := do
  let rows ← manifest
  let files ← walk "scry/corpus"
  let spills := files.filter fun p => p.extension == some "cst"
  check (spills.length > 0) "no checked-in spills under scry/corpus"
  let mut bad : List String := []
  for p in spills do
    if let some f ← spillFailure rows p then
      bad := f :: bad
  checkEq ([] : List String) bad.reverse
  for r in rows do
    check (← (System.FilePath.mk ("scry/" ++ r.1)).pathExists)
      s!"parse-errors.tsv names a missing file: scry/{r.1}"

def group : Group where
  name := "scry-e2e"
  exercise := "scry end-to-end corpus invariant (spill grammar and 0 parse-error nodes)"
  parallel := true
  cases := [
    { name := "every corpus spill names its source's grammar and has 0 ERROR/MISSING nodes (exemptions checked in)",
      run := fun _ => corpusSpills }
  ]

builtin_initialize registerGroup group

end Tests.ScryE2E
