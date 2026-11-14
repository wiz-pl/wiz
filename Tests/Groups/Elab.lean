import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def group : Group where
  name := "elab"
  exercise := "Exercises 3.1–3.9"
  cases := [
    { name := "implicit arguments are inserted", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A := id a") },
    { name := "#check shows implicit binders", run := fun _ =>
        ok (prelude ++ "#check id") ["id : {A : Type} → A → A"] },
    { name := "@ makes implicits explicit", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A := @id A a") },
    { name := "implicit lambda insertion", run := fun _ =>
        ok "def id2 : {A : Type} → A → A := fun x => x" },
    { name := "explicit implicit lambda", run := fun _ =>
        ok "def id3 : {A : Type} → A → A := fun {A} x => x" },
    { name := "return type inferred", run := fun _ =>
        ok "def ap (A B : Type) (f : A → B) (a : A) := f a\n#check ap"
          ["ap : (A : Type) → (B : Type) → (A → B) → A → B"] },
    { name := "fun binder types inferred from use", run := fun _ =>
        ok (prelude ++ "def k (A : Type) := comp (fun (x : A) => x) (fun y => y)\n#check k")
          ["k : (A : Type) → A → A"] },
    { name := "holes solved by unification", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A := @id _ a") },
    { name := "unsolvable hole is reported", run := fun _ =>
        fails "def x : Type := _" "could not infer" },
    { name := "Church numerals and #reduce", run := fun _ =>
        ok (church ++ "#reduce add two two") ["fun A s z => s (s (s (s z)))"] },
    { name := "2 + 2 = 4 by refl, with implicit A", run := fun _ =>
        ok (church ++ "def p : Leibniz (add two two) four := lrefl four") },
    { name := "2 + 2 = 2 is a type mismatch", run := fun _ =>
        fails (church ++ "def p : Leibniz (add two two) two := lrefl two") "type mismatch" },
    { name := "type mismatch message", run := fun _ =>
        fails "def bad (A : Type) (a : A) : Type := a" "type mismatch" },
    { name := "unknown identifier", run := fun _ =>
        fails "def bad : Type := Nope" "unknown identifier 'Nope'" },
    { name := "no recursion yet", run := fun _ =>
        fails "def loop (A : Type) : A := loop A" "recursive call to loop in a definition without equations" },
    { name := "linearity is checked by the kernel", run := fun _ =>
        fails "def dup {A : Type} (f : A → A → A) (1 x : A) : A := f x x" "quantity" },
    { name := "erased implicit used at runtime", run := fun _ =>
        fails "def leak {A : Type} (x : A) : Type := A" "quantity" },
    { name := "binder quantity must match the expected type", run := fun _ =>
        fails "def f : (1 x : Type) → Type := fun (ω x) => x" "quantity" },
    { name := "linear identity checks", run := fun _ =>
        ok "def lid {A : Type} (1 x : A) : A := x" },
    { name := "self-application escapes the hole's scope", run := fun _ => do
        -- (with pruning, the escaping variable is pruned away and the occurs check fires
        -- instead: either is right)
        let errs := errors "def w (A : Type) := fun f => f f"
        unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
        unless (errs[0]!.splitOn "scope").length > 1 || (errs[0]!.splitOn "occurs check").length > 1 do
          throw (IO.userError s!"error mentions neither the scope nor the occurs check:\n{errs[0]!}") },
    { name := "occurs check", run := fun _ =>
        fails "def o (A : Type) (g : _ → A) := g g" "occurs" },
    { name := "not a function", run := fun _ =>
        fails "def bad (A : Type) (a : A) : A := a a" "function expected" },
    { name := "let", run := fun _ =>
        ok (prelude ++ "def t (A : Type) (a : A) : A :=\n  let b := id a\n  id b") },
    { name := "a parse error doesn't stop later commands", run := fun _ => do
        let msgs := run "def a : Type := (\ndef b : Type 1 := Type\n#check b"
        checkEq 2 msgs.size
        check ((msgs[1]!.splitOn "b : Type 1").length > 1) s!"{msgs}" },
    { name := "user syntax without an elaborator is reported", run := fun _ =>
        fails "syntax \"magic\" : term\ndef x : Type := magic" "the syntax term.magic has no meaning" },
    -- (13t) quotation splices `$xs*` / `$xs,*`
    { name := "13t: a quotation splices a list into a node's children", run := fun _ =>
        okLib ("import Prelude\ndef mkApp (f : Syntax) (args : List Syntax) : Syntax := `(term| $f $args*)\n" ++
          "def mkList2 (xs : List Syntax) : Syntax := `(term| [$xs,*])\n" ++
          "#eval mkApp (Syntax.mkVar \"f\") [Syntax.mkVar \"a\", Syntax.mkVar \"b\"]\n" ++
          "#eval mkList2 [Syntax.mkVar \"a\", Syntax.mkVar \"b\"]")
          [".node \"term.app\" (.cons (.node \"term.ident\" (.cons (.ident \"f\") .nil)) (.cons (.node \"null\" (.cons (.node \"term.ident\" (.cons (.ident \"a\") .nil)) (.cons (.node \"term.ident\" (.cons (.ident \"b\") .nil)) .nil))) .nil))",
           ".node \"term.listLit\" (.cons (.atom \"[\") (.cons (.node \"null\" (.cons (.node \"term.ident\" (.cons (.ident \"a\") .nil)) (.cons (.atom \",\") (.cons (.node \"term.ident\" (.cons (.ident \"b\") .nil)) .nil)))) (.cons (.atom \"]\") .nil)))"] },
    { name := "13t: macro rules match and rebuild `$args*` and `$xs,*`", run := fun _ =>
        okLib ("import Prelude\n" ++
          "macro_rules\n  | `(term| pack $f $args*) => `(term| $f $args*)\n" ++
          "#eval pack (fun (x : Nat) => x) 7\n" ++
          "#eval pack (fun (x y : Nat) => Nat.add x y) 8 9\n" ++
          "syntax (name := mylist) \"mylist[\" sepBy(term, \",\") \"]\" : term\n" ++
          "macro_rules\n  | `(term| mylist[$xs,*]) => `(term| [$xs,*])\n" ++
          "#eval mylist[1, 2, 3]\n" ++
          "macro_rules\n  | `(term| mylist[$x, $rest,*]) => `(term| [$rest,*])\n" ++
          "#eval mylist[4, 5, 6]")
          ["7", "17", ".cons 1 (.cons 2 (.cons 3 .nil))", ".cons 5 (.cons 6 .nil)"] },
    { name := "13t: a splice needs a `List Syntax`, and must be inside a node", run := fun _ => do
        failsLib "import Prelude\ndef q (x : Syntax) : Syntax := `(term| f $x*)" "type mismatch"
        failsLib "import Prelude\ndef q (xs : List Syntax) : Syntax := `(term| $xs*)" "only allowed where a node's children" },
    { name := "duplicate definition", run := fun _ =>
        fails "def a : Type 1 := Type\ndef a : Type 1 := Type" "already been declared" }
  ]

builtin_initialize registerGroup group

end Tests.Elab
