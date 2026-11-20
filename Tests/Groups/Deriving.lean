import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def failsDeriving (input : String) (fragment : String) : IO Unit := do
  let s ← derivingRun input
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

/-- A command macro that defines `T.shape : List String`: the parameters, then each
constructor with its fields (`*` marks a recursive one) and indices. -/
def shapeMacro : String := "import Prelude
def strs : List String → Syntax
  | .nil => `(term| List.nil)
  | .cons s rest => let x := Syntax.mkStr s; let r := strs rest; `(term| List.cons $x $r)
def mark (f : FieldView) : String := match FieldView.recursive f with
  | .true => String.append \"*\" (FieldView.name f)
  | .false => FieldView.name f
def fieldStrs : List FieldView → List String
  | .nil => .nil
  | .cons f fs => .cons (mark f) (fieldStrs fs)
def idxStrs : List Syntax → List String
  | .nil => .nil
  | .cons _ _ => .cons \"(indexed)\" .nil
def ctorStrs : List CtorView → List String
  | .nil => .nil
  | .cons c cs => List.append (.cons (CtorView.name c) (fieldStrs (CtorView.fields c)))
      (List.append (idxStrs (CtorView.indices c)) (ctorStrs cs))
def paramStrs : List ParamView → List String
  | .nil => .nil
  | .cons p ps => .cons (ParamView.name p) (paramStrs ps)
syntax (name := shape) \"shape\" ident : command
def shapeM : CommandMacro := fun stx => do
  n ← Syntax.identName (Syntax.getArg stx 1);
  r ← MacroM.getInductive n;
  match r with
  | .none => MacroM.throw \"not an inductive type\"
  | .some v => do
    let x := Syntax.mkIdent (String.append n \".shape\");
    let kind := match IndView.isStructure v with
      | .true => \"structure\"
      | .false => \"inductive\";
    let l := strs (.cons kind (List.append (paramStrs (IndView.params v)) (ctorStrs (IndView.ctors v))));
    MacroM.pure (.cons `(command| def $x : List String := $l) .nil)
attribute [macro command.shape] shapeM
"

def derivingGroup : Group where
  name := "deriving"
  exercise := "HD8"
  parallel := true
  cases := [
    { name := "a command macro expands into several commands", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := two) \"two_defs\" ident ident : command\n" ++
          "def twoM : CommandMacro := fun stx => do\n  let a := Syntax.getArg stx 1;\n  let b := Syntax.getArg stx 2;\n" ++
          "  n ← Syntax.identName a;\n  let av := Syntax.mkVar n;\n  MacroM.pure (.cons `(command| def $a : Nat := 1) (.cons `(command| def $b : Nat := Nat.add $av $av) .nil))\n" ++
          "attribute [macro command.two] twoM\ntwo_defs one two\n#eval two") ["2"] },
    { name := "a `Macro` for a command kind expands to one command", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := one) \"one_def\" ident : command\n" ++
          "def oneM : Macro := fun stx => do\n  let a := Syntax.getArg stx 1;\n  MacroM.pure `(command| def $a : Nat := 7)\n" ++
          "attribute [macro command.one] oneM\none_def seven\n#eval seven") ["7"] },
    { name := "a failing command macro is an error at the command", run := fun _ =>
        failsLib ("import Prelude\nsyntax (name := bad) \"bad_cmd\" : command\n" ++
          "def badM : CommandMacro := fun _ => MacroM.throw \"nope\"\nattribute [macro command.bad] badM\nbad_cmd") "macro badM: nope" },
    { name := "reflection: an inductive type's parameters, constructors and fields", run := fun _ =>
        okLib (shapeMacro ++ "inductive T (A : Type) (n : Nat) where\n  | a\n  | b (x : A) (t : T A n) (k : Nat)\nshape T\n#eval T.shape")
          [".cons \"inductive\" (.cons \"A\" (.cons \"n\" (.cons \"a\" (.cons \"b\" (.cons \"x\" (.cons \"*t\" (.cons \"k\" .nil)))))))"] },
    { name := "reflection: a structure, and an indexed family", run := fun _ =>
        okLib (shapeMacro ++ "structure P where\n  x : Nat\n  y : Bool\nshape P\n#eval P.shape\n" ++
          "inductive V (A : Type) : Nat → Type where\n  | nil : V A 0\n  | cons {n : Nat} (x : A) (xs : V A n) : V A (.succ n)\nshape V\n#eval V.shape")
          [".cons \"structure\" (.cons \"mk\" (.cons \"x\" (.cons \"y\" .nil)))",
           ".cons \"inductive\" (.cons \"A\" (.cons \"nil\" (.cons \"(indexed)\" (.cons \"cons\" (.cons \"n\" (.cons \"x\" (.cons \"*xs\" (.cons \"(indexed)\" .nil))))))))"] },
    { name := "reflection: a declaration's type as syntax", run := fun _ =>
        okLib ("import Prelude\nsyntax (name := alias) \"alias\" ident ident : command\n" ++
          "def aliasM : CommandMacro := fun stx => do\n  let a := Syntax.getArg stx 1;\n  let b := Syntax.getArg stx 2;\n" ++
          "  n ← Syntax.identName b;\n  t ← MacroM.getType n;\n  match t with\n  | .none => MacroM.throw \"unknown\"\n" ++
          "  | .some ty => do\n    let bv := Syntax.mkVar n;\n    MacroM.pure (.cons `(command| def $a : $ty := $bv) .nil)\n" ++
          "attribute [macro command.alias] aliasM\nalias plus Nat.add\n#check plus") ["plus : Nat → Nat → Nat"] },
    { name := "deriving Repr, BEq, Inhabited for an enumeration", run := fun _ =>
        okDeriving ("import Deriving\ninductive C where\n  | r\n  | g\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr C.g\n#eval BEq.beq C.r C.g\n#eval BEq.beq C.g C.g\n#eval Repr.repr (Inhabited.default : C)")
          ["\"C.g\"", ".false", ".true", "\"C.r\""] },
    { name := "deriving with parameters and recursion", run := fun _ =>
        okDeriving ("import Deriving\ninductive Tree (A : Type) where\n  | leaf\n  | node (l : Tree A) (x : A) (r : Tree A)\n" ++
          "  deriving Repr, BEq, Inhabited\ndef t : Tree Nat := .node .leaf 1 (.node .leaf 2 .leaf)\n" ++
          "#eval Repr.repr t\n#eval BEq.beq t t\n#eval BEq.beq t (.node .leaf 1 .leaf)\n#check @instReprTreeA")
          ["\"Tree.node Tree.leaf 1 (Tree.node Tree.leaf 2 Tree.leaf)\"", ".true", ".false",
           "instReprTreeA : {A : Type} → [inst✝ : Repr A] → Repr (Tree A)"] },
    { name := "deriving for a structure, and for the prelude's types", run := fun _ =>
        okDeriving ("import Deriving\nstructure P where\n  x : Nat\n  s : String\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr (List.cons (P.mk 1 \"a\") List.nil)\n#eval BEq.beq (P.mk 1 \"a\") (P.mk 1 \"b\")\n#eval Repr.repr (Inhabited.default : P)")
          ["\"[P.mk 1 \\\"a\\\"]\"", ".false", "\"P.mk 0 \\\"\\\"\""] },
    { name := "deriving instance … for …, after the fact", run := fun _ =>
        okDeriving ("import Deriving\ninductive S where\n  | c (r : Nat)\n  | d (o : Option Bool) (w : Nat)\n" ++
          "deriving instance Repr, BEq for S\n#eval Repr.repr (S.d (Option.some Bool.true) 3)")
          ["\"S.d (Option.some Bool.true) 3\""] },
    { name := "Repr for an indexed family (implicit fields are not shown)", run := fun _ =>
        okDeriving ("import Deriving\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A 0\n" ++
          "  | cons {n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n  deriving Repr\n" ++
          "#eval Repr.repr (Vec.cons 1 (Vec.cons 2 Vec.nil))") ["\"Vec.cons 1 (Vec.cons 2 Vec.nil)\""] },
    { name := "Repr for mutual types: the constructors per type (Ev.s, Od.s), derived for the family", run := fun _ =>
        okDeriving ("import Deriving\nmutual\ninductive Ev where\n  | z\n  | s (o : Od)\n  deriving Repr\ninductive Od where\n  | s (e : Ev)\nend\n" ++
          "#eval Repr.repr (Ev.s (Od.s Ev.z))\n#eval Repr.repr (Od.s (.s (.s .z)))") ["\"Ev.s (Od.s Ev.z)\"", "\"Od.s (Ev.s (Od.s Ev.z))\""] },
    { name := "deriving BEq for an indexed family: Vec at the same and different indices", run := fun _ =>
        okDeriving ("import Deriving\ninductive Vec (A : Type) : Nat → Type where\n  | nil : Vec A 0\n" ++
          "  | cons {n : Nat} (x : A) (xs : Vec A n) : Vec A (.succ n)\n  deriving BEq\n" ++
          "def v0 : Vec Nat 0 := .nil\n" ++
          "def v2 : Vec Nat 2 := .cons 1 (.cons 2 .nil)\n" ++
          "def w2 : Vec Nat 2 := .cons 1 (.cons 2 .nil)\n" ++
          "def u2 : Vec Nat 2 := .cons 1 (.cons 3 .nil)\n" ++
          "#eval BEq.beq v0 v0\n#eval BEq.beq v2 w2\n#eval BEq.beq v2 u2\n" ++
          "#check @instBEqVecAX")
          [".true", ".true", ".false",
           "instBEqVecAX : {A : Type} → [inst✝ : BEq A] → {x : Nat} → BEq (Vec A x)"] },
    { name := "deriving instance BEq for lib/Vec and lib/Vec's Fin", run := fun _ =>
        okLibs ("import Deriving\nimport Vec\nderiving instance BEq for Vec\nderiving instance BEq for Fin\n" ++
          "def v : Vec Nat 3 := Vec.fromList [1, 2, 3]\n" ++
          "def w : Vec Nat 3 := Vec.fromList [1, 2, 3]\n" ++
          "def u : Vec Nat 3 := Vec.fromList [1, 2, 4]\n" ++
          "#eval BEq.beq v w\n#eval BEq.beq v u\n" ++
          "#eval BEq.beq (Vec.nil : Vec Nat 0) (Vec.nil : Vec Nat 0)\n" ++
          "#eval BEq.beq (Fin.of 5 3 rfl) (Fin.of 5 3 rfl)\n" ++
          "#eval BEq.beq (Fin.of 5 3 rfl) (Fin.of 5 4 rfl)")
          [".true", ".false", ".true", ".true", ".false"] },
    { name := "deriving BEq for a width-indexed family: the index is a compared field", run := fun _ =>
        okDeriving ("import Deriving\ninductive Bits : Nat → Type where\n  | mk (w : Nat) (bits : Nat) : Bits w\n" ++
          "  deriving BEq\n" ++
          "def b4 : Bits 4 := .mk 4 10\ndef c4 : Bits 4 := .mk 4 10\ndef d4 : Bits 4 := .mk 4 11\n" ++
          "def b8 : Bits 8 := .mk 8 10\ndef c8 : Bits 8 := .mk 8 10\ndef d8 : Bits 8 := .mk 8 11\n" ++
          "#eval BEq.beq b4 c4\n#eval BEq.beq b4 d4\n#eval BEq.beq b8 c8\n#eval BEq.beq b8 d8")
          [".true", ".false", ".true", ".false"] },
    { name := "deriving BEq for an indexed family compares a user-enum index", run := fun _ =>
        okDeriving ("import Deriving\ninductive Mode where\n  | slow\n  | medium\n  | fast\n  deriving BEq\n" ++
          "inductive Speed : Mode → Type where\n  | mk (m : Mode) (n : Nat) : Speed m\n  deriving BEq\n" ++
          "#eval BEq.beq (Speed.mk Mode.slow 1) (Speed.mk Mode.slow 1)\n" ++
          "#eval BEq.beq (Speed.mk Mode.slow 1) (Speed.mk Mode.slow 2)\n" ++
          "#eval BEq.beq (Speed.mk Mode.fast 1) (Speed.mk Mode.fast 1)")
          [".true", ".false", ".true"] },
    { name := "deriving BEq for an indexed family needs BEq on a compared index", run := fun _ =>
        failsDeriving ("import Deriving\ninductive Mode where\n  | slow\n  | medium\n  | fast\n" ++
          "inductive Speed : Mode → Type where\n  | mk (m : Mode) (n : Nat) : Speed m\n  deriving BEq")
          "failed to synthesize an instance of BEq Mode" },
    { name := "deriving BEq for mutual types (the joint family is indexed)", run := fun _ =>
        okDeriving ("import Deriving\nmutual\ninductive Ev where\n  | z\n  | s (o : Od)\n  deriving BEq\n" ++
          "inductive Od where\n  | s (e : Ev)\nend\n" ++
          "#eval BEq.beq (Ev.s (Od.s Ev.z)) (Ev.s (Od.s Ev.z))\n" ++
          "#eval BEq.beq (Ev.s (Od.s Ev.z)) Ev.z")
          [".true", ".false"] },
    { name := "deriving a class without a deriver is an error", run := fun _ =>
        failsDeriving "import Deriving\ninductive X where\n  | x\n  deriving Frob" "no deriver for Frob" },
    { name := "Inhabited needs a non-recursive constructor", run := fun _ =>
        failsDeriving "import Deriving\ninductive I where\n  | more (i : I)\n  deriving Inhabited" "every constructor of I is recursive" },
    { name := "deriving with proof fields: not shown, not compared, no default (F5)", run := fun _ =>
        okDeriving ("import Deriving\nstructure Pos where\n  n : Nat\n  h : Nat.lt 0 n = Bool.true\n  deriving Repr, BEq\n" ++
          "#eval Repr.repr (Pos.mk 3 (refl Bool.true))\n#eval BEq.beq (Pos.mk 3 (refl Bool.true)) (Pos.mk 4 (refl Bool.true))\n" ++
          "inductive W where\n  | a (n : Nat) (h : n = n)\n  | b\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr (W.a 2 (refl 2))\n#eval BEq.beq (W.a 2 (refl 2)) (W.a 2 (refl 2))\n#eval Repr.repr (Inhabited.default : W)")
          ["\"Pos.mk 3 _\"", ".false", "\"W.a 2 _\"", ".true", "\"W.b\""] },
    { name := "Inhabited skips a constructor with a proof field", run := fun _ =>
        failsDeriving "import Deriving\ninductive I where\n  | p (h : 0 = 0)\n  deriving Inhabited" "every constructor of I is recursive or has a proof field" },
    { name := "deriving for a universe-polymorphic type (no signature: Type u is inferred)", run := fun _ =>
        okDeriving ("import Deriving\ninductive Box.{u} (A : Type u) where\n  | mk (x : A)\n  deriving Repr, BEq, Inhabited\n" ++
          "structure P.{u} (A : Type u) where\n  x : A\n  n : Nat\n  deriving Repr, BEq, Inhabited\n" ++
          "#eval Repr.repr (Box.mk (P.mk 1 2))\n#eval BEq.beq (Box.mk 1) (Box.mk 2)\n#eval Repr.repr (Inhabited.default : P Nat)\n" ++
          "#check @instReprBoxA")
          ["\"Box.mk (P.mk 1 2)\"", ".false", "\"P.mk 0 0\"",
           "instReprBoxA : {A : Type ?u0} → [inst✝ : Repr A] → Repr (Box A)"] },
    { name := "deriving for a type above Type: lifted fields are seen through down (F5)", run := fun _ =>
        okDeriving ("import Deriving\ninstance : Repr Type := Repr.mk (fun _ _ => \"<type>\")\n" ++
          "instance : Inhabited Type := Inhabited.mk Nat\n" ++
          "inductive Big where\n  | b (n : Nat) (h : n = n)\n  | c (T : Type)\n  deriving Repr, Inhabited\n" ++
          "#eval Repr.repr (Big.b 3 (refl 3))\n#eval Repr.repr (Big.c Nat)\n#eval Repr.repr (Inhabited.default : Big)")
          ["\"Big.b 3 _\"", "\"Big.c <type>\"", "\"Big.c <type>\""] },
    { name := "the example runs", run := fun _ => do
        let src ← IO.FS.readFile "examples/deriving.wiz"
        let s ← derivingRun src
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}") },
    { name := "#eval uses Repr when the type has an instance, and reads back when it doesn't", run := fun _ =>
        okDeriving ("import Deriving\ninductive NoRep where\n  | a\n" ++
          "#eval [1, 2, 3]\n#eval ([] : List Nat)\n#eval [\"a\", \"b\"]\n" ++
          "#eval (Option.some 1 : Option Nat)\n#eval NoRep.a\n#eval Nat.succ 3\n" ++
          "def xs : List Nat := [1, 2, 3]\n#eval xs")
          ["[1, 2, 3]", "[]", "[\"a\", \"b\"]", "Option.some 1", ".a", "4", "[1, 2, 3]"] }
  ]

builtin_initialize registerGroup derivingGroup

end Tests.Elab
