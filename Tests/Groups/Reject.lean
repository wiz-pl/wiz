import Tests.Reject

open Wiz
open Tests.Reject

/-!
# `reject`: programs the elaborator must turn down

A corpus of negative programs: universe and level escapes, `Sort` misuse, instance
problems, ill-typed `implemented_by`, non-structural recursion, missing patterns,
quantity violations, foreign-function mistakes, duplicate declarations, malformed
attributes, bad `deriving`, and private/opaque-type escapes. Each case names the
diagnostic's stable code (or that it has none yet) and the source text its span covers,
and `wiz check` must exit nonzero — see `Tests/Reject.lean`. The `accept:` cases are
neighbours that must stay accepted, so the corpus cannot be gamed by over-rejection; the
`xfail:` cases are programs that should be rejected but are not (a `Tests.note` records
why, and the case fails once the elaborator rejects them).

`lake test -- '=reject'` runs the group.
-/

namespace Tests.RejectGroup

def prelude : String := "import Prelude\n"

def classPrelude : String := prelude ++
  "class Inhabited (A : Type) where\n  default : A\n" ++
  "instance : Inhabited Nat := Inhabited.mk 0\n" ++
  "instance {A : Type} [Inhabited A] : Inhabited (List A) where\n" ++
  "  default := List.cons Inhabited.default List.nil\n"

def streamPrelude : String := prelude ++
  "coinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n"

/-- A module with every kind of private name: a definition, a constructor and a type,
a structure's constructor and a field, and a structure. -/
def privMod : String := "import Prelude\nprivate def secret : Nat := 42\ndef reveal : Nat := secret\n" ++
  "structure Pos (A : Type) where\n  private mk ::\n  val : A\n" ++
  "def Pos.one : Pos Nat := Pos.mk 1\n" ++
  "private structure Hidden where\n  x : Nat\n" ++
  "inductive Tok where\n  | num (n : Nat)\n  | private secret (n : Nat)\n" ++
  "def Tok.hide (n : Nat) : Tok := Tok.secret n\n" ++
  "def Tok.value (t : Tok) : Nat := match t with\n" ++
  "  | .num n => n\n  | .secret n => Nat.add n 100\n" ++
  "private inductive Color where\n  | red\n  | blue\n" ++
  "def fav : Color := .red\n"

def group : Group where
  name := "reject"
  exercise := "negative corpus: soundness starts at rejection"
  parallel := true
  cases := [
    -- universe and level escapes
    rejected "universe: Type : Type" "def X : Type := Type\n"
      (some "type-mismatch") "Type" "type mismatch" (cli := true),
    rejected "universe: a Type-indexed Π is not small"
      "def T : Type := (A : Type) → A\n"
      (some "type-mismatch") "(A : Type) → A" "type mismatch",
    rejected "universe: Prop := Type" "def X : Prop := Type\n"
      (some "type-mismatch") "Type" "type mismatch",
    rejected "universe: unknown level parameter" "def f (A : Type u) : Type u := A\n"
      none "u" "unknown universe level",
    rejected "universe: too many explicit levels"
      "def id.{u} {A : Sort u} (x : A) : A := x\ndef t := id.{0, 1}\n"
      none "id.{0, 1}" "universe parameters",
    rejected "universe: unsolved level"
      "def id.{u} {A : Sort u} (x : A) : A := x\ndef t := @id\n"
      (some "unsolved-level") "@id" "could not infer",
    rejected "universe: duplicate level parameter"
      "def f.{u, u} (A : Type u) : Type u := A\n"
      (some "kernel-rejected") "def f.{u, u}" "duplicate universe level",
    accepted "accept: a Π into Type is one level up"
      "def f : Type 1 := (A : Type) → A\n" (cli := true),
    accepted "accept: Sort 0 is Prop, a Type" "def X : Type := Sort 0\n",
    accepted "accept: an inferred level at use"
      "def id.{u} {A : Sort u} (x : A) : A := x\ndef t (A : Type 3) (a : A) : A := id a\n",

    -- Sort misuse
    rejected "sort: a Prop-valued variable where a type is expected"
      "def f (A : Sort 0) : A := A\n"
      (some "type-mismatch") "A" "type mismatch",
    rejected "sort: a term where a type is expected"
      (prelude ++ "def f (x : 3) : Nat := x\n")
      (some "type-expected") "3" "type expected" (cli := true),
    rejected "sort: Prop is not a large Π" "def f : Prop := (A : Type) → A\n"
      (some "type-mismatch") "(A : Type) → A" "type mismatch",
    accepted "accept: Prop is impredicative"
      "def True : Prop := (P : Prop) → P → P\ndef trivial : True := fun P p => p\n",

    -- instances
    rejected "instance: missing instance" (classPrelude ++ "def s : String := Inhabited.default\n")
      none "Inhabited.default" "failed to synthesize an instance of Inhabited String" (cli := true),
    rejected "instance: of a non-class" (prelude ++ "instance : Nat := 0\n")
      (some "unknown-class") "instance : Nat := 0" "not a class",
    rejected "instance: a cycle is tabulated, not followed"
      (prelude ++ "class Loop (A : Type) where\n  x : A\n" ++
       "instance {A : Type} [Loop A] : Loop A := Loop.mk Loop.x\n#eval (Loop.x : Nat)\n")
      none "Loop.x" "failed to synthesize an instance of Loop Nat",
    rejected "instance: missing field"
      (prelude ++ "class C (A : Type) where\n  x : A\n  y : Nat\n" ++
       "instance : C Nat where\n  x := 1\n")
      (some "missing-field") "instance : C Nat where\n  x := 1" "missing field y",
    rejected "instance: unknown field"
      (prelude ++ "class C (A : Type) where\n  x : A\n" ++
       "instance : C Nat where\n  bogus := 1\n")
      (some "no-such-field") "instance : C Nat where\n  bogus := 1" "has no field bogus",
    rejected "instance: a definition is not a class"
      (prelude ++ "def D : Type := Nat\ninstance : D := 0\n")
      (some "unknown-class") "instance : D := 0" "is not a class",
    rejected "instance: a field has the wrong type"
      (prelude ++ "class C (A : Type) where\n  x : A\n" ++
       "instance : C Nat where\n  x := Bool.true\n")
      (some "type-mismatch") "Bool.true" "type mismatch",
    rejected "instance: a field given twice"
      (prelude ++ "class C (A : Type) where\n  x : A\n" ++
       "instance : C Nat where\n  x := 1\n  x := 2\n")
      (some "named-argument") "x := 2" "already given",
    accepted "accept: a later instance wins"
      (prelude ++ "class Inhabited (A : Type) where\n  default : A\n" ++
       "instance : Inhabited Nat := Inhabited.mk 1\ninstance : Inhabited Nat := Inhabited.mk 2\n" ++
       "#eval (Inhabited.default : Nat)\n") (cli := true),
    accepted "accept: a complete instance"
      (prelude ++ "class C (A : Type) where\n  x : A\n  y : Nat\n" ++
       "instance : C Nat where\n  x := 1\n  y := 2\n"),

    -- implemented_by
    rejected "implemented_by: the implementation has the wrong type"
      (prelude ++ "def f (n : Nat) : Nat := n\ndef g (b : Bool) : Nat := 0\n" ++
       "attribute [implemented_by g] f\n")
      none "g" "can't implement f" (cli := true),
    rejected "implemented_by: unknown implementation"
      (prelude ++ "def f (n : Nat) : Nat := n\nattribute [implemented_by nope] f\n")
      (some "unknown-declaration") "nope" "unknown declaration",
    rejected "implemented_by: itself"
      (prelude ++ "def f (n : Nat) : Nat := n\nattribute [implemented_by f] f\n")
      none "f" "implemented by itself",
    rejected "implemented_by: different universe parameters"
      (prelude ++ "def f.{u} (A : Type u) (a : A) : A := a\n" ++
       "def g.{u, v} (A : Type u) (B : Type v) (a : A) : A := a\n" ++
       "attribute [implemented_by g] f\n")
      none "g" "universe parameters",
    rejected "implemented_by: a result with no runtime content"
      (prelude ++ "def f (n : Nat) : Unit := ()\ndef g (n : Nat) : Unit := ()\n" ++
       "attribute [implemented_by g] f\n")
      none "f" "no runtime content",
    rejected "implemented_by: a builtin already has one"
      (prelude ++ "def g (m n : Nat) : Nat := m\nattribute [implemented_by g] Nat.add\n")
      none "Nat.add" "already has an implementation",
    accepted "accept: a well-typed implementation"
      (prelude ++ "def f (n : Nat) : Nat := n\ndef g (n : Nat) : Nat := Nat.succ n\n" ++
       "attribute [implemented_by g] f\n#eval f 3\n"),

    -- non-structural recursion
    rejected "recursion: not structural" "import Prelude\ndef f : Nat → Nat\n  | n => f n\n"
      (some "not-structural") "f n" "not structurally smaller" (cli := true),
    rejected "recursion: on a rebuilt argument"
      "import Prelude\ndef f : Nat → Nat\n  | .zero => 0\n  | .succ n => f (Nat.succ n)\n"
      (some "not-structural") "f (Nat.succ n)" "not a recursive field",
    rejected "recursion: without equations"
      "import Prelude\ndef f (g : Nat → Nat) : Nat := f g\n"
      (some "recursive-without-equations") "f" "without equations",
    rejected "recursion: a local variable shadows the definition"
      "import Prelude\ndef f : Nat → Nat\n  | n => let f := n; f\n"
      (some "not-structural") "let f := n; f" "rename a local variable",
    rejected "recursion: a parameter shadows the definition"
      "import Prelude\ndef f (f : Nat) : Nat → Nat\n  | .zero => f\n  | .succ n => f n\n"
      (some "not-structural") "f" "rename a local variable",
    accepted "accept: structural recursion through a list"
      "import Prelude\ndef len : List Nat → Nat\n  | .nil => 0\n  | .cons _ xs => Nat.succ (len xs)\n#eval len (.cons 1 (.cons 2 .nil))\n" (cli := true),
    accepted "accept: an explicit partial definition"
      "import Prelude\npartial def f : Nat → Nat\n  | n => f n\n",
    accepted "accept: a mutual block is general recursion"
      ("import Prelude\nmutual\ndef f : Nat → Nat\n  | n => g n\n" ++
       "def g : Nat → Nat\n  | n => f n\nend\n#check f\n"),

    -- the cons notation: `::` is `List.cons`, whose tail must be a list
    rejected "cons: the tail of `1 :: 2` is not a list"
      (prelude ++ "def bad : List Nat := 1 :: 2\n")
      none "2" "failed to synthesize an instance of OfNat (List Nat) 2",
    rejected "cons: `1 :: (2 : Nat)` has a Nat tail"
      (prelude ++ "def bad : List Nat := 1 :: (2 : Nat)\n")
      (some "type-mismatch") "(2 : Nat)" "type mismatch",

    -- missing coverage
    rejected "coverage: match misses a constructor"
      "import Prelude\ndef f (b : Bool) : Nat := match b with\n  | .true => 1\n"
      (some "missing-case") "match b with\n  | .true => 1" "missing case for constructor false" (cli := true),
    rejected "coverage: equations miss a constructor"
      "import Prelude\ndef f : Bool → Nat\n  | .true => 1\n"
      (some "missing-case") "def f : Bool → Nat\n  | .true => 1" "missing case for constructor false",
    rejected "coverage: a copattern misses an observation"
      (streamPrelude ++ "def ones : Stream Nat\n  | .head => 1\n")
      (some "missing-copattern") "def ones : Stream Nat\n  | .head => 1" "missing copattern .tail",
    accepted "accept: a catch-all covers the rest"
      "import Prelude\ndef f (b : Bool) : Nat := match b with\n  | .true => 1\n  | _ => 0\n",
    accepted "accept: complete equations"
      "import Prelude\ndef f : Bool → Nat\n  | .true => 1\n  | .false => 0\n#eval f .true\n",

    -- quantities
    rejected "quantity: a linear value is used twice"
      "import Prelude\ndef dup {A : Type} (1 x : A) : A × A := (x, x)\n"
      (some "quantity") "def dup" "used ω" (cli := true),
    rejected "quantity: a linear value is dropped"
      "import Prelude\ndef lose {A : Type} (1 x : A) : Unit := ()\n"
      (some "quantity") "def lose" "used 0",
    xfail "quantity: a linear value captured by an unrestricted closure"
      "import Prelude\ndef bad {A : Type} (1 x : A) : Unit → A := fun _ => x\n"
      "the closure's type is unrestricted, so it may be duplicated while the captured variable is linear; dropping it (`fun _ => ()`) is rejected, and `two (bad x)` is caught, but the definition is accepted",
    rejected "quantity: duplicating a closure that captured a linear value"
      ("import Prelude\ndef bad {A : Type} (1 x : A) : Unit → A := fun _ => x\n" ++
       "def app2 {A : Type} (f : Unit → A) : A × A := (f (), f ())\n" ++
       "def exploit {A : Type} (1 x : A) : A × A := app2 (bad x)\n")
      (some "quantity") "def exploit" "used ω",
    rejected "quantity: an erased value is used at run time"
      "import Prelude\ndef leak {A : Type} (0 x : A) : A := x\n"
      (some "quantity") "def leak" "used 1",
    rejected "quantity: a binder's quantity differs from the type"
      "import Prelude\ndef f : (1 x : Type) → Type := fun (ω x) => x\n"
      (some "binder-mismatch") "x" "binder quantity",
    rejected "quantity: a projection drops a linear component"
      "import Prelude\ndef bad {A : Type} (1 p : A × Nat) : A := p.1\n"
      (some "quantity") "def bad" "cannot project p.1",
    accepted "accept: a linear pair taken apart with let 1"
      ("import Prelude\ndef ok {A : Type} (1 p : A × Nat) : A × Nat :=\n" ++
       "  let 1 (a, b) := p; (a, b)\n"),
    accepted "accept: unrestricted values may be duplicated"
      "import Prelude\ndef ok {A : Type} (x : A) : A × A := (x, x)\n",

    -- foreign functions
    rejected "ffi: a pure foreign result with no runtime content"
      (prelude ++ "extern \"f\" f : Nat → Unit\n")
      none "extern \"f\" f : Nat → Unit" "result must carry" (cli := true),
    rejected "ffi: a foreign argument of an unknown type"
      (prelude ++ "extern \"f\" f : Foo → Nat\n")
      (some "unknown-identifier") "Foo" "unknown identifier",
    rejected "ffi: a foreign function called with too many arguments"
      ("import Prelude\nextern \"strlen\" (header := \"string.h\") strlen : String → Nat\n" ++
       "#check strlen \"a\" \"b\"\n")
      (some "wrong-argument-count") "strlen" "function expected",
    rejected "ffi: glue returns the wrong type"
      (prelude ++ "glue bad (n : Nat) : String := \"return n + 1;\"\n")
      none "\"return n + 1;\"" "expected a string",
    rejected "ffi: glue dereferences a pointer"
      (prelude ++ "glue bad (n : Nat) : Nat := \"return *n;\"\n")
      none "\"return *n;\"" "pointer dereference",
    rejected "ffi: glue calls a function it did not bind"
      (prelude ++ "glue bad (n : Nat) : Nat := \"return system(n);\"\n")
      none "\"return system(n);\"" "unknown C function",
    rejected "ffi: a foreign name declared twice"
      (prelude ++ "extern \"f\" f : Nat → Nat\nextern \"f\" f : Nat → Nat\n")
      (some "duplicate-declaration") "f" "already been declared",
    rejected "ffi: a foreign type declared twice"
      (prelude ++ "foreign_type F\nforeign_type F\n")
      (some "kernel-rejected") "foreign_type F" "already been declared",
    accepted "accept: a well-typed extern"
      ("import Prelude\nimport IO\n" ++
       "extern \"strlen\" (header := \"string.h\") strlen : String → Nat\n") (cli := true),
    accepted "accept: a callback parameter"
      (prelude ++ "extern \"f\" f : (Nat → Nat) → Nat\n"),

    -- duplicate declarations, attributes, builtins
    rejected "declaration: a name declared twice"
      (prelude ++ "def f : Nat := 1\ndef f : Nat := 2\n")
      (some "duplicate-declaration") "f" "already been declared" (cli := true),
    rejected "declaration: a constructor declared twice"
      (prelude ++ "inductive X where\n  | x\n  | x\n")
      (some "duplicate-constructor") "x" "declared twice",
    rejected "attribute: unknown attribute"
      (prelude ++ "def f (n : Nat) : Nat := n\nattribute [bogus] f\n")
      (some "parse-error") "bogus" "expected" (cli := true),
    rejected "attribute: malformed []"
      (prelude ++ "attribute [inline]\n")
      (some "parse-error") "" "expected identifier",
    rejected "attribute: inline of an unknown declaration"
      (prelude ++ "attribute [inline] nope\n")
      (some "unknown-declaration") "nope" "unknown declaration",
    rejected "attribute: a non-macro registered as a macro"
      (prelude ++ "attribute [macro command.def] Nat.add\n")
      none "attribute [macro command.def] Nat.add" "not a macro",
    rejected "attribute: a non-deriver registered as a deriver"
      (prelude ++ "attribute [deriver Nat] Nat.add\n")
      none "attribute [deriver Nat] Nat.add" "not a deriver",
    rejected "attribute: an unknown option"
      (prelude ++ "set_option pp.bogus true\n")
      none "pp.bogus" "unknown option",
    rejected "attribute: local on a definition"
      (prelude ++ "local def x : Nat := 1\n")
      none "local def x : Nat := 1" "can be `local`",
    rejected "builtin: nat.add with the wrong arity"
      ("inductive N where\n  | z\ndef K (a : N) : N := a\nbuiltin nat := N\nbuiltin nat.add := K\n")
      none "builtin nat.add := K" "must take 2 arguments",

    -- deriving
    rejected "deriving: no deriver for the class"
      (prelude ++ "inductive X where\n  | x\nderiving Frob\n")
      none "Frob" "no deriver for Frob" (cli := true),
    rejected "deriving: an indexed family"
      ("import Deriving\n" ++
       "inductive V (A : Type) : Nat → Type where\n" ++
       "  | nil : V A 0\n" ++
       "  | cons {n : Nat} (x : A) (xs : V A n) : V A (Nat.succ n)\n" ++
       "  deriving BEq\n")
      none "BEq" "indexed families are not supported",
    rejected "deriving: Inhabited of a recursive type"
      ("import Deriving\ninductive I where\n  | more (i : I)\n  deriving Inhabited\n")
      none "Inhabited" "every constructor of I is recursive",
    accepted "accept: deriving Repr, BEq and Inhabited"
      ("import Deriving\ninductive X where\n  | x\n  | y (n : Nat)\n" ++
       "  deriving Repr, BEq, Inhabited\n#eval Repr.repr (X.y 3)\n") (cli := true),
    accepted "accept: Repr for a mutual family"
      ("import Deriving\nmutual\ninductive Ev where\n  | z\n  | s (o : Od)\n  deriving Repr\n" ++
       "inductive Od where\n  | s (e : Ev)\nend\n"),

    -- private/opaque types
    rejected "opaque: a private constructor cannot be called" "import Priv\ndef x : Tok := Tok.secret 1\n"
      (some "private") "Tok.secret" "is private to module Priv" [("Priv", privMod)] (cli := true),
    rejected "opaque: another module cannot match on the type"
      "import Priv\ndef f (t : Tok) : Nat := match t with\n  | .num n => n\n  | _ => 0\n"
      (some "private") ".num n" "opaque outside module Priv" [("Priv", privMod)],
    rejected "opaque: the recursor is private" "import Priv\ndef f := @Tok.casesOn\n"
      (some "private") "@Tok.casesOn" "is private to module Priv" [("Priv", privMod)],
    rejected "opaque: a private definition" "import Priv\ndef f : Nat := secret\n"
      (some "private") "secret" "is private to module Priv" [("Priv", privMod)],
    rejected "opaque: a private type" "import Priv\ndef f : Color := .red\n"
      (some "private") "Color" "is private to module Priv" [("Priv", privMod)],
    rejected "opaque: a private structure" "import Priv\ndef f : Hidden := Hidden.mk 1\n"
      (some "private") "Hidden" "is private to module Priv" [("Priv", privMod)],
    rejected "opaque: a look-alike does not convert"
      ("import Priv\ninductive Fake where\n  | num (n : Nat)\n  | secret (n : Nat)\n" ++
       "def x : Tok := Fake.secret 1\n")
      (some "type-mismatch") "Fake.secret 1" "type mismatch" [("Priv", privMod)],
    rejected "opaque: a first-order solution cannot forge a private value"
      ("import Priv\nstructure Look (A : Type) where\n  val : A\n" ++
       "inductive G : Look Nat → Type where\n  | mk (l : Look Nat) : G l\n" ++
       "def sel {F : Pos Nat → Type} (p : Pos Nat) (w : F p) : Pos Nat := p\n" ++
       "def forge (x : Look Nat) : Pos Nat := sel _ (G.mk x)\n" ++
       "#eval (forge (Look.mk 11)).val\n")
      (some "private") "G.mk x" "hidden outside its module"
      [("Priv", privMod)],
    accepted "accept: a module's own private names, through its public API"
      ("import Priv\ndef x : Nat := Tok.value (Tok.hide 1)\n#eval x\n") [("Priv", privMod)] (cli := true),
    rejected "opaque: a first-order solution in equations cannot forge either"
      ("import Priv\nstructure Look (A : Type) where\n  val : A\n" ++
       "inductive G : Look Nat → Type where\n  | mk (l : Look Nat) : G l\n" ++
       "def sel {F : Pos Nat → Type} (p : Pos Nat) (w : F p) : Pos Nat := p\n" ++
       "def forge : Look Nat → Pos Nat\n  | x => sel _ (G.mk x)\n")
      (some "private") "G.mk x" "hidden outside its module"
      [("Priv", privMod)],
    accepted "accept: a first-order solution that uses no opaque shape"
      ("import Priv\nstructure Look (A : Type) where\n  val : A\n" ++
       "inductive G : Look Nat → Type where\n  | mk (l : Look Nat) : G l\n" ++
       "def sel {F : Look Nat → Type} (p : Look Nat) (w : F p) : Look Nat := p\n" ++
       "def forge (x : Look Nat) : Look Nat := sel _ (G.mk x)\n" ++
       "#eval (forge (Look.mk 11)).val\n") [("Priv", privMod)] (cli := true),
    rejected "inductive props: large elimination of a non-singleton proposition"
      (prelude ++ "inductive Le : Nat → Nat → Prop where\n  | refl (n : Nat) : Le n n\n  | step {n m : Nat} (h : Le n m) : Le n (.succ m)\n" ++
       "def bad (h : Le 0 0) : Nat := match h with\n  | .refl _ => 0\n  | .step _ => 0\n")
      none ".refl _" "large elimination",
    accepted "accept: singleton elimination of an inductive proposition"
      (prelude ++ "inductive EqP {A : Type} (a : A) : A → Prop where\n  | refl : EqP a a\n" ++
       "def out {A : Type} {a : A} (h : EqP a a) : Nat :=\n  EqP.rec (fun _ _ => Nat) 3 h\n#eval out (A := Nat) (a := 0) EqP.refl\n"),
    { name := "modules: two modules declaring one name"
      run := fun _ => do
        let dir ← IO.FS.createTempDir
        let files := [
          ("M/Base.wiz", "inductive Bool where\n  | true\n  | false\n"),
          ("M/A.wiz", "import M.Base\ndef b : Bool := Bool.true\ndef pa : b = Bool.true := refl Bool.true\n"),
          ("M/B.wiz", "import M.Base\ndef b : Bool := Bool.false\ndef pb : b = Bool.false := refl Bool.false\n")]
        for (p, text) in files do
          let f := dir / p
          if let some d := f.parent then IO.FS.createDirAll d
          IO.FS.writeFile f text
        let ms ← Module.loadAll [dir]
        let init : CommandState ZeroOneMany := { loader := fun m => (ms[m]?).map (·.2) }
        let cache ← IO.FS.createTempDir
        let src := "import M.A\nimport M.B\ndef x : Bool := b\n"
        let s := (← Cache.elaborateCached (some cache) [] src init 0).1
        noPanic s.messages
        let clash (s : CommandState ZeroOneMany) : Bool :=
          s.messages.any fun m => m.code == "duplicate-declaration" && m.text.contains "declared by both"
        unless clash s do
          let errs := s.messages.filter (·.severity == .error)
          throw (IO.userError s!"no module-name clash:\n{"\n".intercalate (errs.toList.map (describe src))}")
        let s2 := (← Cache.elaborateCached (some cache) [] src init 0).1
        unless clash s2 do throw (IO.userError "the module-name clash disappeared on a warm cache") }
  ]

builtin_initialize registerGroup group

end Tests.RejectGroup
