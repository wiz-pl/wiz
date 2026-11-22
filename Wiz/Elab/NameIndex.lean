import Wiz.Elab.Basic

/-!
# The declaration index of the importable modules

A file that forgot an `import` gets the wrong advice from an edit-distance guess: the
name it wrote is declared *exactly* in a module it does not import, and that is the fix.
`wiz check` has the loader (`Grail/Elab.lean`), the language server has its library
(`LSP.lean`), and the tests have their module table, so each can name the modules
`import` can reach (`CommandState.modules`). This module builds `name → modules` from
those sources, once per state (the result is cached in `CommandState.declIndex`).

The scan is the source-level one the language server's "add the missing import" quick fix
already used (`Actions.declares`): a declaration's first word after its modifiers, and a
qualified name `T.c` belonging to the type `T`'s module. It is deliberately not a
re-elaboration: the loader's text is all the frontend is given, and the point is to tell
the user which `import` to write.
-/

namespace Wiz

/-- The names a source declares at the top of a line (public ones, and the constructors
and fields of a type it declares), in source order. -/
def declaredNamesIn (src : String) : List Name := Id.run do
  let kws := ["def", "theorem", "axiom", "inductive", "coinductive", "structure", "class",
    "extern", "instance", "foreign_type", "abbrev", "opaque"]
  let mut out : List Name := []
  for line in src.splitOn "\n" do
    let ws := ((line.trimAsciiStart.toString.splitOn " ").filter (· ≠ ""))
    -- skip modifiers (`partial`, `sealed`, `noncomputable`, `unsafe`, `private`, `local`)
    -- and a parenthesised option such as `partial (default := w)`
    let rec skip : List String → Nat → List String
      | w :: rest, depth + 1 => skip rest (if w.endsWith ")" then depth else depth + 1)
      | w :: rest, 0 =>
        if ["partial", "sealed", "noncomputable", "unsafe", "private", "local"].contains w then skip rest 0
        else if w.startsWith "(" then (if w.endsWith ")" then skip rest 0 else skip rest 1)
        else w :: rest
      | [], _ => []
    match skip ws 0 with
    | kw :: n :: _ =>
      if kws.contains kw then
        let n := String.ofList (n.toList.takeWhile fun c => !" (:{[".contains c)
        let n := ((n.splitOn ".{").headD n)
        unless n.isEmpty do out := n :: out
    | _ => pure ()
  pure out.reverse

/-- The classes a module registers a deriver for (`attribute [deriver C] f`). -/
def derivedClassesIn (src : String) : List Name := Id.run do
  let mut out : List Name := []
  for line in src.splitOn "\n" do
    let l := line.trimAsciiStart.toString
    let marker := "attribute [deriver "
    if l.startsWith marker then
      let rest := (l.drop marker.length).toString
      let C := String.ofList (rest.toList.takeWhile fun c => !"] ".contains c)
      unless C.isEmpty do out := C :: out
  pure out.reverse

/-- `name → modules` for the modules `import` can reach, and the classes each module
derives. Built from the loader's sources; `modules` is the reachable list (the loader
may also know the file being elaborated, which the caller leaves out). -/
structure DeclIndex where
  byName : Std.HashMap Name (List Name) := {}
  /-- class → modules that register a deriver for it -/
  derivers : Std.HashMap Name (List Name) := {}
  deriving Inhabited

/-- Build the index. Insertion keeps the modules in the given order (the caller sorts
them), so a suggestion is deterministic. -/
def buildDeclIndex (modules : Array Name) (loader : Name → Option String) : DeclIndex := Id.run do
  let mut idx : DeclIndex := {}
  for m in modules do
    let some src := loader m | continue
    for n in declaredNamesIn src do
      idx := { idx with byName := idx.byName.insert n ((idx.byName[n]?.getD []).concat [m]) }
    for C in derivedClassesIn src do
      idx := { idx with derivers := idx.derivers.insert C ((idx.derivers[C]?.getD []).concat [m]) }
  pure idx

/-- The modules (not imported) that declare `x` exactly. A qualified name whose own
entry the scan does not have (`Array.empty`, a member of a type) falls back to its base
type's module, as the language server's quick fix does. -/
def DeclIndex.modulesDeclaring (idx : DeclIndex) (imported : List Name) (self : Name) (x : Name) : List Name :=
  let of (n : Name) : List Name :=
    ((idx.byName[n]?.getD []).filter fun m => m != self && !imported.contains m).eraseDups
  let exact := of x
  if !exact.isEmpty then exact else
  match x.splitOn "." with
  | _ :: _ :: _ => of (".".intercalate (x.splitOn ".").dropLast)
  | _ => []

/-- The modules (not imported) that register a deriver for `C`. -/
def DeclIndex.modulesDeriving (idx : DeclIndex) (imported : List Name) (self : Name) (C : Name) : List Name :=
  ((idx.derivers[C]?.getD []).filter fun m => m != self && !imported.contains m).eraseDups

/-- The closest module name to `m` (edit distance at most 2), for `import Prelud`. -/
def suggestModule (modules : Array Name) (m : Name) : Option Name :=
  let scored := modules.filterMap fun n =>
    if n == m then none else
    let d := editDistance m n
    if d ≤ 2 then some (d, n) else none
  match scored.qsort (fun (d, n) (d', n') => d < d' || (d == d' && n < n')) |>.toList with
  | [] => none
  | (_, n) :: _ => some n

end Wiz
