import Wiz.Syntax.Basic

/-!
# Children of syntax nodes, by name

The elaborator used to read a node's children by position (`c.getArg 2`), and every
change to a grammar rule (an optional keyword before a constructor's name, say) silently
shifted the positions somewhere. `childNames` names the children of a node kind once, in
grammar order, and `Syntax.child` reads a child by name: a grammar change is then one
edit to the list here. The test group `parser: commands` checks every list against the
grammar (`Wiz.Builtin.childNamesMismatches`: the number of names is the number of
children the rule produces), so the list can't lag behind the rule.

Converted so far: the commands that declare types (`inductive`, `structure`, `class`,
`coinductive`) with their constructors and fields. Everything else still uses `getArg`.
-/

namespace Wiz

/-- The names of the children of a node of kind `k`, in order; `_` for a keyword or
punctuation that nothing reads. `[]`: the kind has no named children (yet). -/
def childNames : Name → List Name
  | "command.inductive" => ["_", "name", "univParams", "binders", "sig", "_", "ctors", "deriving"]
  | "command.structure" => ["_", "name", "univParams", "binders", "sig", "where", "fields", "deriving"]
  | "command.class" | "command.coinductive" => ["_", "name", "univParams", "binders", "sig", "_", "fields"]
  | "inductive.ctor" => ["_", "private", "name", "binders", "sig"]
  | "structure.field" => ["private", "quantity", "name", "_", "type"]
  | "structure.where" => ["_", "ctor"]
  | _ => []

namespace Syntax

/-- The child called `n` (see `childNames`). `missing` if `s` is not a node; a name
that the node's kind doesn't have is a bug in the caller, and is reported loudly. -/
def child (s : Syntax) (n : Name) : Syntax :=
  match s with
  | .node _ k args =>
    match (childNames k).idxOf? n with
    | some i => args[i]?.getD .missing
    | none => panic! s!"Syntax.child: a node of kind {k} has no child named '{n}'"
  | _ => .missing

end Syntax

end Wiz
