import Wiz.Syntax.Basic

/-!
# A registry for attributes and options (TT-04)

Attributes (`attribute [foo args] x`) and options (`set_option foo value`) are looked up
in one typed table instead of one parser rule and one match arm per name. An entry says
what payload it accepts and what it does; the command elaborator parses the payload,
reports an unknown name or a malformed payload, and then runs the action.

The built-in entries here are the ones the language already had. `[inline]` and the
`pp.notation`/`pp.all` options go through the registry (their old dedicated parser and
match arm are gone); the others are still written in their own parser forms, but they are
listed so that `register_attribute`/`register_option` reject a duplicate and an unknown
name gets a useful message.

`register_attribute` registers a user no-op attribute: it validates the target and
records the application (`CommandState.attrUses`), which is observable in the state and,
through `local`, removed at the end of the module. `register_option` registers a typed
no-op option (Bool, Nat, String or Name, with an optional inclusive range for Nat).
-/

namespace Wiz

/-! ## Attributes -/

/-- The payload an attribute takes after its name inside the brackets. -/
inductive AttrPayload where
  | flag
  | name
  | nameOptName
  | nameOptNat
  deriving Repr, BEq, Inhabited

def AttrPayload.expects : AttrPayload → String
  | .flag => "takes no arguments"
  | .name => "takes one name argument"
  | .nameOptName => "takes one or two name arguments"
  | .nameOptNat => "takes an optional numeral"

/-- What an attribute does. `noop` only records the application (a user attribute). -/
inductive AttrAction where
  | noop
  | macro
  | tactic
  | implementedBy
  | inline
  | defaultInstance
  | binop
  | deriver
  | unexpander
  deriving Repr, BEq, Inhabited

structure AttributeDecl where
  name : Name
  payload : AttrPayload
  action : AttrAction
  deriving Repr, BEq, Inhabited

/-- The built-in attribute names, latest first (the order only matters for messages). -/
def builtinAttributes : List AttributeDecl :=
  [ { name := "macro", payload := .name, action := .macro }
  , { name := "tactic", payload := .name, action := .tactic }
  , { name := "implemented_by", payload := .nameOptName, action := .implementedBy }
  , { name := "inline", payload := .flag, action := .inline }
  , { name := "default_instance", payload := .nameOptNat, action := .defaultInstance }
  , { name := "binop", payload := .flag, action := .binop }
  , { name := "deriver", payload := .name, action := .deriver }
  , { name := "app_unexpander", payload := .name, action := .unexpander } ]

/-! ## Options -/

inductive OptKind where
  | boolean
  | natural
  | string
  | name
  deriving Repr, BEq, Inhabited

def OptKind.describe : OptKind → String
  | .boolean => "Bool"
  | .natural => "Nat"
  | .string => "String"
  | .name => "Name"

def OptKind.expects : OptKind → String
  | .boolean => "expects `true` or `false`"
  | .natural => "expects a numeral"
  | .string => "expects a string"
  | .name => "expects a name"

/-- A typed option value. -/
inductive OptValue where
  | bool (b : Bool)
  | nat (n : Nat)
  | str (s : String)
  | name (n : Name)
  deriving Repr, BEq, Inhabited

def OptValue.kind : OptValue → OptKind
  | .bool _ => .boolean
  | .nat _ => .natural
  | .str _ => .string
  | .name _ => .name

def OptValue.asBool? : OptValue → Option Bool
  | .bool b => some b
  | _ => none

/-- What an option does besides storing its value. `ppNotation` and `ppAll` are the
migrated printing options; they both set `Globals.pp.useNotation` (the latter inverted,
as before). -/
inductive OptAction where
  | none
  | ppNotation
  | ppAll
  deriving Repr, BEq, Inhabited

structure OptDecl where
  name : Name
  kind : OptKind
  default : OptValue
  action : OptAction := .none
  /-- inclusive range for a `Nat` option -/
  range : Option (Nat × Nat) := none
  deriving Repr, BEq, Inhabited

/-- Check that `v` has the declared type and, for a natural option, lies in its range. -/
def OptDecl.validate (d : OptDecl) (v : OptValue) : Except String Unit :=
  if v.kind != d.kind then .error s!"expects a {d.kind.describe} value, not a {v.kind.describe}"
  else match d.kind, v, d.range with
    | .natural, .nat n, some (lo, hi) =>
      if lo ≤ n && n ≤ hi then .ok () else .error s!"must be between {lo} and {hi}"
    | _, _, _ => .ok ()

/-- The built-in options, latest first. -/
def builtinOptions : List OptDecl :=
  [ { name := "pp.notation", kind := .boolean, default := .bool true, action := .ppNotation }
  , { name := "pp.all", kind := .boolean, default := .bool false, action := .ppAll } ]

end Wiz
