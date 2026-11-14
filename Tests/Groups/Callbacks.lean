import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def tickSrc (release : Bool) : String :=
  "import IO\nextern \"on_tick\" onTick : Callback (Nat → IO Unit) → IO Unit\n" ++
  "extern \"tick\" tick : Nat → IO Unit\nextern \"forget\" forget : IO Unit\n" ++
  "def say (p : String) (n : Nat) : IO Unit := IO.println (String.append p (Nat.toString n))\n" ++
  "def main : IO Unit := do\n  onTick (say (String.append \"tick \" \"#\"));\n  IO.println \"registered\";\n" ++
  "  tick 2;\n  onTick (fun n => say \"tock \" (n + 10));\n  tick 1" ++ (if release then ";\n  forget" else "")

def callbacksGroup : Group where
  name := "callbacks"
  exercise := "Stage 9g"
  cases := [
    { name := "qsort with a Wiz comparator (a closure, borrowed for the call)", run := fun _ =>
        ioRunC ("import IO\nextern \"sort_some\" sortSome : (Nat → Nat → Bool) → String\n" ++
          "def byShift (k : Nat) (a b : Nat) : Bool := Nat.lt (Nat.mod (a + k) 10) (Nat.mod (b + k) 10)\n" ++
          "def main : IO Unit := do\n  IO.println (sortSome (fun a b => Nat.lt a b));\n" ++
          "  IO.println (sortSome (fun a b => Nat.lt b a));\n  IO.println (sortSome (byShift 3))")
          sortHelper "1 3 4 5 7 9\n9 7 5 4 3 1\n7 9 1 3 4 5\n" },
    { name := "a callback kept by C and called later, in IO, released by C", run := fun _ =>
        ioRunC (tickSrc true) tickHelper "registered\ntick #0\ntick #1\ntock 10\n" },
    { name := "a kept callback that C never releases is a leak", run := fun _ =>
        ioRunC (tickSrc false) tickHelper "" (fails := some "leaked") },
    { name := "a C function calls an exported Wiz function", run := fun _ =>
        ioRunC ("import IO\nextern \"sum_squares\" sumSquares : Nat → Nat\n" ++
          "def square (n : Nat) : Nat := n * n\nexport \"wiz_square\" square : Nat → Nat\n" ++
          "def main : IO Unit := IO.println (Nat.toString (sumSquares 10))")
          "#include <stdint.h>\nuint64_t wiz_square(uint64_t);\nuint64_t sum_squares(uint64_t n) { uint64_t s = 0; for (uint64_t i = 1; i <= n; i++) s += wiz_square(i); return s; }\n"
          "385\n" },
    { name := "a C program uses a Wiz library (wiz build --lib)", run := fun _ =>
        libRunC ("import IO\ndef fact : Nat → Nat\n  | .zero => 1\n  | .succ n => (n + 1) * fact n\n" ++
          "export \"wiz_fact\" fact\n" ++
          "def greet (who : String) : String := String.append \"hello, \" who\nexport \"wiz_greet\" greet : String → String\n" ++
          "def shout (s : String) : IO Unit := IO.println (String.append s \"!\")\nexport \"wiz_shout\" shout\n" ++
          "structure Counter where\n  total : Nat\n  steps : Nat\n" ++
          "def Counter.zero : Counter := Counter.mk 0 0\ndef Counter.add (c : Counter) (n : Nat) : Counter := Counter.mk (c.total + n) (c.steps + 1)\n" ++
          "def Counter.get (c : Counter) : Nat := c.total * 100 + c.steps\n" ++
          "export \"wiz_counter_new\" Counter.zero\nexport \"wiz_counter_add\" Counter.add\nexport \"wiz_counter_get\" Counter.get\n")
          ("#include <stdio.h>\n#include <stdlib.h>\n#include \"lib.h\"\nint main(void) {\n" ++
           "  printf(\"%llu\\n\", (unsigned long long)wiz_fact(20));\n" ++
           "  char *s = wiz_greet(\"C\"); printf(\"%s\\n\", s); free(s);\n  wiz_shout(\"from Wiz\");\n" ++
           "  wiz_val c = wiz_counter_new();\n  for (int i = 1; i <= 4; i++) c = wiz_counter_add(c, i);\n" ++
           "  wiz_retain((void *)c); printf(\"%llu\\n\", (unsigned long long)wiz_counter_get(c));\n" ++
           "  wiz_release((void *)c);\n  printf(\"live %ld\\n\", wiz_live_objects());\n  return 0;\n}\n")
          "2432902008176640000\nhello, C\nfrom Wiz!\n1004\nlive 0\n" },
    { name := "a callback in IO needs a foreign function in IO", run := fun _ =>
        ioFails "import IO\nextern \"f\" f : (Nat → IO Unit) → Nat" "must be in IO" },
    { name := "only closed, marshallable functions are exported", run := fun _ =>
        ioFails "import IO\ndef app (f : Nat → Nat) : Nat := f 1\nexport \"wiz_app\" app" "exported function" },
    { name := "an export's type is the definition's", run := fun _ =>
        ioFails "import IO\ndef two : Nat := 2\nexport \"wiz_two\" two : String" "not String" }
  ]

builtin_initialize registerGroup callbacksGroup

end Tests.Elab
