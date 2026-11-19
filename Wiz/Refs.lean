import Wiz.Query

/-!
# References and rename

The info tree records every identifier the elaborator resolved, with what it resolved
to: a global by its name, a local by its name in its context. **References** to a
global are its identifiers in every document (the open ones and, under `grail lsp`, the
package's other modules), plus the name in its declaration. A local's references are the
identifiers of that name inside the declaration around the cursor that see the same
binder (the last binder of that name before the use: an approximation of scoping).
**Rename** edits the places that spell the whole name; the language server refuses a
global declared in the toolchain's library and a new name that isn't a name. A use
through generalised field notation (`p.norm` for `Point.norm p`) is not edited.

(#434) The cursor may also be on a name where it is declared: a `def`'s or an
`inductive`'s name, a constructor, a structure field (`declIdents` finds them in the
command's syntax, parsed again). That is the same target as a use of the name, so
references, rename and highlights from there give what they give from a use. A
constructor or field is written by its last component (`red` for `C.red`); rename edits
that spelling too when the new name keeps the prefix (`renameText`).
-/

namespace Wiz.Refs

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- What the cursor is on: a global, or a local (its name, and the declaration around it
as a range). -/
inductive Target where
  | global (n : Name)
  | «local» (x : Name) (scope : SourceInfo) (binder : Option SourceInfo)
  deriving BEq, Inhabited

/-- The command (declaration) range around `off`, from the declaration sites. -/
def commandAround (s : CommandState R) (off : Nat) : Option SourceInfo :=
  s.declSites.fold (init := none) fun acc _ (r, m) =>
    if m.isEmpty && r.start ≤ off && off ≤ r.stop then
      match acc with
      | some r' => if r.stop - r.start < r'.stop - r'.start then some r else acc
      | none => some r
    else acc

/-- The binders of the info tree: `recordBinder` pushes a binder's identifier and then
its goal (a `.term` of the same range); a use has its `.term` first. -/
def binders (s : CommandState R) : Array (Name × SourceInfo) := Id.run do
  let mut out : Array (Name × SourceInfo) := #[]
  let mut prev : Option (Name × SourceInfo) := none
  for i in s.infos do
    match i, prev with
    | Info.term r' _ false, some (x, r) => if r' == r && !r.synthetic then out := out.push (x, r)
    | _, _ => pure ()
    prev := match i with
      | Info.ident r x true .. => some (x, r)
      | _ => none
  out

/-- The binder of the local `x` used at `at_` within `scope`: the last binder of `x` in
`scope` starting at or before `at_` (scoping by position: a binder after the use, or one
whose scope ended, is not considered beyond that approximation). -/
def binderOf (bs : Array (Name × SourceInfo)) (scope : SourceInfo) (x : Name) (at_ : Nat) : Option SourceInfo :=
  bs.foldl (fun acc (n, r) =>
    if n == x && scope.start ≤ r.start && r.start ≤ at_ then
      match acc with
      | some r' => if r.start > r'.start then some r else acc
      | none => some r
    else acc) none

/-! ## Declaration sites (#434) -/

/-- Node kinds whose first identifier (a direct child, or inside an optional part) is the
name they declare. -/
def declaringKinds : List Name :=
  ["command.def", "command.defEqns", "command.axiom", "command.inductive", "command.structure",
   "command.class", "command.coinductive", "command.instance", "command.extern", "command.cStruct",
   "command.foreignType", "inductive.ctor", "structure.field", "structure.where"]

/-- The first identifier among `args`, looking into optional parts (`null` nodes) but not
into other nodes (binders, terms) or bracketed parts (`(priority := …)`, `.{u}`). -/
partial def firstIdent (args : Array Syntax) : Option (SourceInfo × Name) :=
  args.findSome? fun
    | .ident i n => some (i, n)
    | .node _ k xs =>
      if k == Syntax.nullKind && !((xs[0]? matches some (Wiz.Syntax.atom _ "(")) || (xs[0]? matches some (Wiz.Syntax.atom _ ".{"))) then
        firstIdent xs
      else none
    | _ => none

/-- The names a command's syntax declares, where they are written: the first identifier
of each node of `declaringKinds`, and of any other command that is a keyword followed
by an identifier (a `theorem`-like command a macro declares). -/
partial def declIdents : Syntax → Array (SourceInfo × Name)
  | .node _ k args =>
    let inner := args.foldl (fun acc a => acc ++ declIdents a) #[]
    let keywordIdent := k.startsWith "command." && (args[0]? matches some (Wiz.Syntax.atom ..)) &&
      (args[1]? matches some (Wiz.Syntax.ident ..))
    if declaringKinds.contains k || keywordIdent then
      match firstIdent args with
      | some x => if x.1.synthetic then inner else #[x] ++ inner
      | none => inner
    else inner
  | _ => #[]

/-- Does the identifier `written` (in a declaration) declare the global `n`? Exactly, or
by its last components (a constructor `red` of `C`, `C.red`). -/
def declares (written n : Name) : Bool :=
  !written.isEmpty && (n == written || n.endsWith ("." ++ written))

/-- The declaring identifiers of the command at `cmd` in `text` (`tables`: the grammar,
for commands a `syntax` declared). -/
def declIdentsAt (tables : ParserTables) (text : String) (cmd : SourceInfo) : Array (SourceInfo × Name) :=
  match parseCommand text.toList.toArray tables cmd.start with
  | .ok (stx, _) => declIdents stx
  | .error _ => #[]

/-- The global declared at `off`, if `off` is on a declaring identifier of the command
around it, and that identifier's range. An exact name wins over a suffix. -/
def declaredAt (s : CommandState R) (text : String) (off : Nat) : Option (Name × SourceInfo) := do
  let cmd ← commandAround s off
  let (r, written) ← (declIdentsAt s.tables text cmd).find? fun (r, _) => r.start ≤ off && off ≤ r.stop
  -- the names this command declares
  let names := s.declSites.fold (init := #[]) fun acc n (r', m) =>
    if m.isEmpty && r' == cmd && declares written n then acc.push n else acc
  let n ← names.find? (· == written) <|> (names.qsort (· < ·))[0]?
  pure (n, r)

/-- The identifier at `off`, as a target, and its range; (#434) or the name of a
declaration where it is declared. -/
def targetAt (s : CommandState R) (text : String) (off : Nat) : Option (Target × SourceInfo) :=
  match Query.innermost s off (· matches .ident ..) (endIn := true) with
  | some (.ident r n isLocal ..) =>
    if r.synthetic then none
    else if !isLocal then some (.global n, r)
    else do
      let scope ← commandAround s off
      pure (.local n scope (binderOf (binders s) scope n r.start), r)
  | _ => do
    let (n, r) ← declaredAt s text off
    pure (.global n, r)

/-- Where the name `n` is written in its declaration `cmd` (the first whole-word
occurrence), as a range. -/
def nameInDecl (text : String) (cmd : SourceInfo) (n : Name) : Option SourceInfo := Id.run do
  let chars := text.toList.toArray
  let ns := n.toList.toArray
  let mut i := cmd.start
  while i + ns.size ≤ min cmd.stop chars.size do
    if (List.range ns.size).all (fun k => chars[i + k]! == ns[k]!) &&
       (i == 0 || !(isIdRest chars[i - 1]! || chars[i - 1]! == '.')) &&
       (i + ns.size ≥ chars.size || !(isIdRest chars[i + ns.size]!)) then
      return some { start := i, stop := i + ns.size }
    i := i + 1
  none

/-- The ranges of `t` in a document (`s`, `text`), declaration included (for a global
declared in it). -/
def rangesIn (s : CommandState R) (text : String) (t : Target) : Array SourceInfo := Id.run do
  let mut out : Array SourceInfo := #[]
  match t with
  | .global n =>
    if let some (cmd, "") := s.declSites.get? n then
      -- (#434) the identifier that declares it; else the name's first occurrence
      let ids := declIdentsAt s.tables text cmd
      let site := ((ids.find? (·.2 == n)) <|> (ids.find? (declares ·.2 n))).map (·.1)
      if let some r := site <|> nameInDecl text cmd n then out := out.push r
    for i in s.infos do
      if let .ident r m false .. := i then
        if m == n && !r.synthetic && r.stop > r.start then out := out.push r
  | .local x scope b =>
    let bs := binders s
    for i in s.infos do
      if let .ident r m true .. := i then
        if m == x && !r.synthetic && scope.start ≤ r.start && r.stop ≤ scope.stop &&
           binderOf bs scope x r.start == b then out := out.push r
  -- (one per range)
  out.foldl (fun acc r => if acc.any (fun r' => r'.start == r.start && r'.stop == r.stop) then acc else acc.push r) #[]
    |>.qsort (·.start < ·.start)

/-- The text of a range of `text`: what an identifier there must read for a rename to
edit it (a qualified name used by its last part, `p.norm`, is not edited). -/
def textAt (text : String) (r : SourceInfo) : String :=
  String.ofList ((text.toList.drop r.start).take (r.stop - r.start))

/-- (#434) What a rename of `name` to `new` writes where `name` is spelled `spelled`: `new`
for the whole name; for its last component (a constructor or field where it is declared,
`red` for `C.red`), the last component of `new`, if `new` keeps the prefix; otherwise
nothing (the place is not edited). -/
def renameText (name new spelled : String) : Option String :=
  if spelled == name then some new else
  let split (n : String) : String × String :=
    match n.splitOn "." with
    | [] | [_] => ("", n)
    | parts => (".".intercalate parts.dropLast, parts.getLast!)
  let (p, l) := split name
  let (p', l') := split new
  if !p.isEmpty && p == p' && spelled == l then some l' else none

/-- Is `n` a name a rename may introduce? -/
def validName (n : String) : Bool :=
  !n.isEmpty && (n.splitOn ".").all fun p => !p.isEmpty && isIdStart p.front && p.all isIdRest

end Wiz.Refs
