import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def macroPrelude : String := "inductive Nat where\n  | zero\n  | succ (n : Nat)\ndef add : Nat → Nat → Nat\n  | .zero, n => n\n  | .succ m, n => .succ (add m n)\ndef mul : Nat → Nat → Nat\n  | .zero, _ => .zero\n  | .succ m, n => add n (mul m n)\ninfixl:65 \" + \" => add\ninfixl:70 \" * \" => mul\nnotation \"two\" => Nat.succ (Nat.succ Nat.zero)\ninductive Bool where\n  | false\n  | true\nsyntax \"if\" term \"then\" term \"else\" term : term\nmacro_rules\n  | `(term| if $c then $t else $e) => `(term| match $c with | .true => $t | .false => $e)\nsyntax \"const_x\" term : term\nmacro_rules\n  | `(term| const_x $e) => `(term| (fun x => $e) Nat.zero)\ndef h (x : Nat) : Nat := const_x x\n\n"

def macroGroup : Group where
  name := "macros"
  exercise := "Exercise 6.1"
  cases := [
    { name := "infixl with precedence", run := fun _ =>
        ok (macroPrelude ++ "#eval two + two * two")
          [".succ (.succ (.succ (.succ (.succ (.succ .zero)))))"] },
    { name := "macro_rules with quotations", run := fun _ =>
        ok (macroPrelude ++ "#eval (if Bool.false then two else Nat.zero : Nat)") [".zero"] },
    { name := "hygiene: a template binder does not capture user variables", run := fun _ =>
        ok (macroPrelude ++ "#eval h two") [".succ (.succ .zero)"] },
    { name := "a user command defined by a macro", run := fun _ =>
        ok (macroPrelude ++ "syntax \"def_two\" ident : command\n" ++
            "macro_rules\n  | `(command| def_two $n) => `(command| def $n : Nat := two)\n" ++
            "def_two myTwo\n#eval myTwo") [".succ (.succ .zero)"] },
    { name := "a user syntax category with macros", run := fun _ =>
        ok (macroPrelude ++ "declare_syntax_cat digit\nsyntax \"I\" : digit\nsyntax \"digits\" digit* : term\n" ++
            "macro_rules\n  | `(term| digits) => `(term| Nat.zero)\n#eval (digits : Nat)") [".zero"] }
  ]

builtin_initialize registerGroup macroGroup

end Tests.Elab
