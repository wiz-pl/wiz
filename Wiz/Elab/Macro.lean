import Wiz.Elab.Basic

/-!
# Macros by example

A macro rule rewrites syntax to syntax:

```
macro_rules
  | `(term| unless $c then $t else $e) => `(term| if $c then $e else $t)
notation:65 a:65 " + " b:66 => add a b
infixl:70 " * " => mul
```

* **Matching** compares syntax trees structurally; `$x` binds a subtree.
* **Splices** (13t): `$xs*` binds the children of a `many` node, `$xs,*` those of a
  `sepBy` (as a `null` node of elements), and the template splices them back.
* **Instantiation** replaces `$x` (and, for `notation`, the argument names) with what
  they matched.
* **Hygiene**: every other identifier the template introduces gets a fresh *macro
  scope*, `x ↦ x✝3`. A local variable only matches an identifier with the same scope,
  so a template's binders can't capture a user's variables. Globals are looked up with
  the scope stripped, so templates can still refer to `add`. (Lean does the same.)

Expansion happens in the elaborator: before elaborating a node, the latest matching
rule (if any) rewrites it.
-/

namespace Wiz.Elab

def antiquotName? : Syntax → Option Name
  | .node _ "antiquot" args => args[1]? >>= Syntax.getId?
  | _ => none

/-- (13t) A splice antiquotation: `$xs*` (no separator), or `$xs,*` (a `sepBy`, with
the separator `","`). -/
def antiquotSplice? : Syntax → Option (Name × Option String)
  | .node _ "antiquot.splice" args => match args[1]? with
    | some a => (Syntax.getId? a).map (·, none)
    | none => none
  | .node _ "antiquot.spliceSep" args =>
    let a : Syntax := args.getD 1 Syntax.missing
    let b : Syntax := args.getD 2 Syntax.missing
    match a, b with
    | .ident _ x, .atom _ s => some (x, some s)
    | _, _ => none
  | _ => none

/-- (13t) The elements of a splice's matched children: for `$xs,*`, the children at the
even positions, with the `sep` atoms between them; for `$xs*`, all of them. -/
def spliceElems (sep : Option String) (middle : Array Syntax) : Option (Array Syntax) :=
  match sep with
  | none => some middle
  | some s => Id.run do
    let mut out : Array Syntax := #[]
    let mut elem := true
    for a in middle do
      if elem then
        out := out.push a
        elem := false
      else match a with
        | .atom _ v => if v == s then elem := true else return none
        | _ => return none
    if middle.isEmpty || !elem then some out else none

mutual
/-- **Exercise 6.1a.** Match `stx` against a pattern, extending the bindings. -/
partial def matchPattern (pat stx : Syntax) (acc : List (Name × Syntax)) : Option (List (Name × Syntax)) :=
  --<sol
  match antiquotName? pat with
  | some x => some ((x, stx) :: acc)
  | none =>
    match pat, stx with
    | .node _ k as, .node _ k' bs =>
      if k == k' then matchSeq as bs acc else none
    | .atom _ v, .atom _ v' => if v == v' then some acc else none
    | .ident _ n, .ident _ n' => if n == n' then some acc else none
    | .missing, .missing => some acc
    | _, _ => none
  --|ex
  --| sorry
  --sol>

/-- (13t) Match the children of a node, with at most one splice (`$xs*`) in the pattern:
the children before and after it match positionally, and it binds the children between
them (as a `null` node of elements, separators removed for `$xs,*`). -/
private partial def matchSeq (pats sts : Array Syntax) (acc : List (Name × Syntax)) :
    Option (List (Name × Syntax)) := do
  let splice := (pats.toList.zipIdx.find? fun (p, _) => (antiquotSplice? p).isSome).map (·.2)
  match splice with
  | none =>
    guard (pats.size == sts.size)
    (pats.zip sts).foldlM (fun acc (p, s) => matchPattern p s acc) acc
  | some i =>
    let some (x, sep) := antiquotSplice? pats[i]! | none
    let pre := pats.extract 0 i
    let suf := pats.extract (i + 1) pats.size
    guard (sts.size ≥ pre.size + suf.size)
    let middle := sts.extract pre.size (sts.size - suf.size)
    let elems ← spliceElems sep middle
    let acc ← (pre.zip (sts.extract 0 pre.size)).foldlM (fun acc (p, s) => matchPattern p s acc) acc
    let acc ← (suf.zip (sts.extract (sts.size - suf.size) sts.size)).foldlM
      (fun acc (p, s) => matchPattern p s acc) acc
    pure ((x, .node {} "null" elems) :: acc)
end

/-- The base name of a (possibly macro-scoped) identifier. -/
def stripScope (n : Name) : Name := (n.splitOn "✝").headD n

/-- Identifiers under these node kinds are not references, so they get no scope. -/
def unscopedParents : List Name := ["term.dotIdent", "term.field", "level.param", "term.syntheticHole"]

/-- **Exercise 6.1b.** Instantiate a template: replace antiquotations (and the `vars` of a
`notation`) by their bindings, and add `scope` to every other plain identifier that
isn't under one of the `unscopedParents` (dotted names are global references: leave
them too). -/
partial def instantiate (binds : List (Name × Syntax)) (vars : List Name) (scope : Nat)
    (parent : Name) (t : Syntax) : Syntax :=
  --<sol
  match antiquotName? t with
  | some x => ((binds.find? (·.1 == x)).map (·.2)).getD t
  | none => match t with
    -- a `notation` argument used as a term: replace the whole `term.ident` node
    | .node _ "term.ident" #[.ident _ n] =>
      if vars.contains n then ((binds.find? (·.1 == n)).map (·.2)).getD t
      else .node t.info "term.ident" #[instantiate binds vars scope "term.ident" (.ident t.info n)]
    | .ident i n =>
      if vars.contains n then ((binds.find? (·.1 == n)).map (·.2)).getD t
      else if unscopedParents.contains parent || n.contains '.' then t
      else .ident i s!"{n}✝{scope}"
    | .node i k as => .node i k (Id.run do
      let mut out : Array Syntax := #[]
      for a in as do
        match antiquotSplice? a with
        | some (x, sep) =>
          match (binds.find? (·.1 == x)).map (·.2) with
          | some s => match s with
            | .node _ "null" es =>
              for (e, j) in es.toList.zipIdx do
                match sep with
                | some sep => if j > 0 then out := out.push (.atom a.info sep)
                | none => pure ()
                out := out.push (instantiate binds vars scope k e)
            | _ => out := out.push (instantiate binds vars scope k a)
          | none => out := out.push (instantiate binds vars scope k a)
        | none => out := out.push (instantiate binds vars scope k a)
      out)
    | s => s
  --|ex
  --| sorry
  --sol>

/-- Expand `stx` with the latest matching rule, if any; also returns the rule. The
template's ranges are marked synthetic (11q): they are in the file that declared the
rule, while what the antiquotations bind keeps the ranges the user wrote. -/
def expandMacroRule? (rules : List MacroRule) (stx : Syntax) (scope : Nat) : Option (Syntax × MacroRule) := do
  for r in rules do
    if r.kind == stx.kind then
      if let some binds := matchPattern r.pattern stx [] then
        return (instantiate binds r.vars scope "" r.template.markSynthetic, r)
  none

/-- Expand `stx` with the latest matching rule, if any. -/
def expandMacro? (rules : List MacroRule) (stx : Syntax) (scope : Nat) : Option Syntax :=
  (expandMacroRule? rules stx scope).map (·.1)

end Wiz.Elab
