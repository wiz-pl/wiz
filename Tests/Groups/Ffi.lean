import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

def ffiGroup : Group where
  name := "ffi"
  exercise := "Stage 9a"
  cases := [
    { name := "IO actions run in order", run := fun _ =>
        ioRun "import IO\ndef main : IO Unit := do\n  IO.println \"one\";\n  IO.println \"two\"" "one\ntwo\n" },
    { name := "the world is linear: it can't be duplicated", run := fun _ =>
        ioFails "import IO\ndef bad (x : IO Unit) : IO Unit := fun w =>\n  let 1 (a, w') := x w; x w" "quantity 1" },
    { name := "linear sequencing: IO.bind, IO.then1 and do1 take an action and a continuation that use a linear value (L6)", run := fun _ => do
        ioFails ("import IO\naxiom Tok : Type\naxiom Tok.close : (1 t : Tok) → IO Unit\n" ++
          "def seqs (1 t : Tok) : IO Nat := do1\n  IO.println \"closing\";\n  Tok.close t;\n  IO.pure 3\n" ++
          "def seq2 (1 t : Tok) : IO Nat := IO.then1 (Tok.close t) (IO.pure 3)\n" ++
          "def seq3 (1 t : Tok) : IO Nat := IO.bind (IO.println \"x\") (fun _ => IO.bind (Tok.close t) (fun _ => IO.pure 3))\n" ++
          "def bad (1 t : Tok) : IO Nat := do\n  IO.println \"closing\";\n  Tok.close t;\n  IO.pure 3")
          "variable t declared with quantity 1 but used ω"
        ioRun ("import IO\ndef main : IO Unit := do1\n  IO.println \"one\";\n  n ← IO.pure 2;\n  let m := n + n;\n  IO.println (Nat.toString m)") "one\n4\n" },
    { name := "... and a linear value is still used exactly once", run := fun _ =>
        ioFails ("import IO\naxiom Tok : Type\naxiom Tok.close : (1 t : Tok) → IO Unit\n" ++ "def bad (1 t : Tok) : IO Unit := do1\n  Tok.close t;\n  Tok.close t")
          "quantity 1 but used ω" },
    { name := "an action's result is split, not projected: (x w).1 would drop the world (R1)", run := fun _ => do
        ioFails ("import IO\ndef peek {A : Type} (1 x : IO A) (1 w : World) : A := (x w).1") "cannot project (x w).1"
        ioFails ("import IO\ndef peek {A : Type} (1 x : IO A) (1 w : World) : A := (x w).1") "which has quantity 1; take the pair apart with `let 1 (x, y) := x w; …`"
        ioFails ("import IO\ndef keep {A : Type} (1 x : IO A) (1 w : World) : World := (x w).2") "a projection needs an unrestricted pair"
        ioRun ("import IO\ndef twice (1 x : IO Nat) : IO Nat := fun w => let 1 (a, w') := x w; (a + a, w')\n" ++
          "def main : IO Unit := do\n  n ← twice (IO.pure 4);\n  IO.println (Nat.toString n)") "8\n" },
    { name := "... and compiled code never evaluates a 0 position (a let at 0, a 0 field, a split at 0, a 0 argument)", run := fun _ =>
        ioRun ("import IO\npartial def loop (u : Unit) : Nat × Nat := loop u\n" ++
          "def a : Nat := let 0 x : Nat := (loop ()).1; 1\ndef b : (0 x : Nat) × Nat := ((loop ()).1, 2)\n" ++
          "def c : Nat := let 0 (x, y) := loop (); 3\ndef d (f : (0 x : Nat) → Nat) : Nat := f (loop ()).1\n" ++
          "def main : IO Unit := IO.println (Nat.toString (a + b.2 + c + d (fun _ => 4)))") "10\n" },
    -- erasure used to bind `let s := <scrutinee>` for every split, so the action below ran
    -- (its usage of `w` is multiplied by 0, so the kernel accepted the second use of `w`)
    { name := "... nor performs an effect in the scrutinee of a split at 0 (C and LLVM)", run := fun _ => do
        let src := "import IO\ndef main : IO Unit := fun w =>\n  let 0 (a, w0) := IO.println \"ghost\" w;\n  IO.println \"real\" w"
        ioRun src "real\n"
        ioRun src "real\n" (llvm := true)
        let loop := "import IO\npartial def loop (u : Unit) : Nat × Nat := loop u\n" ++
          "def c : Nat := let 0 (x, y) := loop (); 3\ndef main : IO Unit := IO.println (Nat.toString c)"
        ioRun loop "3\n" (llvm := true) },
    { name := "... nor a constructor field at 0, a 0 field of a structure, a 0 argument of an extern (C and LLVM)", run := fun _ => do
        let src := "import IO\n" ++ zeroFieldDecls ++
          "extern \"strlen\" (header := \"string.h\") slen : (0 ghost : Nat) → String → Nat\n" ++
          "def e5 : Nat := slen (loop ()) \"abc\"\n" ++
          "def main : IO Unit := IO.println (Nat.toString (e1 + e2 + e3 + e4 + e5))"
        ioRun src "29\n"
        ioRun src "29\n" (llvm := true) },
    { name := "machine integers and floats", run := fun _ =>
        ioRun ("import IO\ndef main : IO Unit := do\n" ++
          "  IO.println (Nat.toString (UInt64.toNat (UInt64.mul (UInt64.ofNat 1000000) (UInt64.ofNat 1000000))));\n" ++
          "  IO.println (Float64.toString (Float64.div (Float64.ofNat 1) (Float64.ofNat 4)))") "1000000000000\n0.25\n" },
    { name := "strings are marshalled as UTF-8", run := fun _ =>
        ioRun "import IO\ndef main : IO Unit := IO.println \"λ ✓\"" "λ ✓\n" },
    { name := "a C library function, through its header", run := fun _ =>
        ioRun ("import IO\nextern \"strlen\" (header := \"string.h\") strlen : String → Nat\n" ++
          "def main : IO Unit := IO.println (Nat.toString (strlen \"hello\"))") "5\n" },
    { name := "import_c binds a header's functions", run := fun _ =>
        ioRun ("import IO\nimport_c \"string.h\"\nimport_c \"stdlib.h\" (pure)\ndef main : IO Unit := do\n" ++
          "  n ← C.strlen \"hello, world\";\n  IO.println (Nat.toString n);\n  IO.println (Nat.toString (C.atoi \"42\"))") "12\n42\n" },
    { name := "the C subset parser (Exercise 9.1)", run := fun _ => do
        let fs := FFI.parseHeader "typedef unsigned long size_t;\nextern size_t strlen (const char *__s) __attribute__ ((__pure__));\nstruct S { int x; };\ntypedef int (*cmp_t)(const void *, const void *);\nvoid qsort(void *b, size_t n, size_t s, cmp_t c);\nstatic inline int twice(int x) { return 2 * x; }\nint printf(const char *f, ...);"
        checkEq "[strlen, qsort, twice, printf]" (toString (fs.toList.map (·.name)))
        checkEq "true" (toString (fs.toList.find? (·.name == "printf") |>.map (·.variadic) |>.getD false))
        let q := (fs.toList.find? (·.name == "qsort")).get!
        checkEq "true" (toString (q.params.getLast! == FFI.CType.other "function pointer")) },
    { name := "glue: checked C snippets", run := fun _ =>
        ioRun ("import IO\nimport_c \"string.h\"\n" ++
          "glue sumTo (n : Nat) : Nat := \"uint64_t s = 0; for (uint64_t i = 0; i < n; i++) s += i; return s;\"\n" ++
          "glue twiceLen (s : String) : Nat := \"return strlen(s) * 2;\"\n" ++
          "def main : IO Unit := do\n  IO.println (Nat.toString (sumTo 100));\n  IO.println (Nat.toString (twiceLen \"hello\"))")
          "4950\n10\n" },
    { name := "glue: no pointers (Exercise 9.2)", run := fun _ =>
        ioFails "import IO\nglue bad (n : Nat) : Nat := \"return *n;\"" "pointer dereference" },
    { name := "glue: no indexing", run := fun _ =>
        ioFails "import IO\nglue bad (s : String) : Nat := \"return s[0];\"" "indexing" },
    { name := "glue: only declared functions", run := fun _ =>
        ioFails "import IO\nglue bad (n : Nat) : Nat := \"return system(n);\"" "unknown C function system" },
    { name := "observing codata is memoised", run := fun _ =>
        -- `noisy` prints when it runs. Building `s` unfolds `counter 0` (one step: the
        -- next state is computed with the payload); the first `s.head` unfolds `s` and
        -- overwrites it with its payload, so the second doesn't (`wiz_lazy_set`).
        ioRun ("import IO\nimport_c \"stdio.h\" (pure)\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n" ++
          "def noisy (n : Nat) : Nat := n + 0 * C.puts \"step\"\n" ++
          "def counter (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => counter (noisy (n + 1))\n" ++
          "def main : IO Unit := do\n  let s := (counter 0).tail;\n  IO.println (Nat.toString s.head);\n  IO.println (Nat.toString s.head)")
          "step\nstep\n1\n1\n" },
    { name := "a long stream observed twice computes each element once", run := fun _ =>
        ioRun ("import IO\nimport_c \"stdio.h\" (pure)\ncoinductive Stream (A : Type) where\n  head : A\n  tail : Stream A\n" ++
          "def noisy (n : Nat) : Nat := n + 0 * C.puts \"step\"\n" ++
          "def counter (n : Nat) : Stream Nat\n  | .head => n\n  | .tail => counter (noisy (n + 1))\n" ++
          "def sumN : Nat → Stream Nat → Nat\n  | .zero, _ => 0\n  | .succ k, s => s.head + sumN k s.tail\n" ++
          "def main : IO Unit := do\n  let s := counter 0;\n  IO.println (Nat.toString (sumN 1000 s));\n  IO.println (Nat.toString (sumN 1000 s))")
          (String.join (List.replicate 1000 "step\n") ++ "499500\n499500\n") },
    { name := "glue: types are checked", run := fun _ =>
        ioFails "import IO\nglue bad (n : Nat) : String := \"return n + 1;\"" "expected a string" },
    { name := "foreign pointers are released by their finalizer", run := fun _ =>
        ioRun ("import IO\nforeign_type FILE (finalizer := \"fclose\")\n" ++
          "extern \"fopen\" (header := \"stdio.h\") fopen : String → String → IO FILE\n" ++
          "extern \"fputs\" (header := \"stdio.h\") fputs : String → FILE → IO Nat\n" ++
          "def main : IO Unit := do\n  f ← fopen \"/tmp/wiz_test_fin.txt\" \"w\";\n  n ← fputs \"closed\\n\" f;\n" ++
          "  s ← IO.readFile \"/tmp/wiz_test_fin.txt\";\n  IO.print s") "closed\n" },
    { name := "byte buffers", run := fun _ =>
        ioRun ("import IO\ndef fill : Nat → Bytes → Bytes\n  | .zero, b => b\n  | .succ n, b => Bytes.push (fill n b) (65 + n)\n" ++
          "def main : IO Unit := do\n  IO.println (Bytes.toString (fill 3 Bytes.empty));\n" ++
          "  IO.println (Nat.toString (Bytes.size (Bytes.ofString \"λx\")))") "ABC\n3\n" },
    { name := "foreign types are checked", run := fun _ =>
        ioFails "import IO\nextern \"f\" f : ((Nat → Nat) → Nat) → Nat" "foreign function" },
    { name := "link_c: a C file and a library linked with the program (C backend)", run := fun _ =>
        linkRun linkFiles "42\n42\n" },
    { name := "link_c: the same with the LLVM backend", run := fun _ =>
        linkRun linkFiles "42\n42\n" (llvm := true) },
    { name := "link_c: a module's file is relative to the module", run := fun _ =>
        linkRun [("main.wiz", "import IO\nimport Lib.Glue\ndef main : IO Unit := IO.println (Nat.toString (three 0))\n"),
                 ("Lib/Glue.wiz", "import Prelude\nlink_c \"glue.c\"\nextern \"three\" three : Nat → Nat\n"),
                 ("Lib/glue.c", "#include <stdint.h>\nuint64_t three(uint64_t n) { return n + 3; }\n")] "3\n" },
    { name := "link_c: a missing file is an error at the command", run := fun _ => do
        let (s, src, _) ← elabTree [("main.wiz", "import IO\nlink_c \"nowhere.c\"\ndef main : IO Unit := IO.println \"x\"\n")]
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        checkEq #["2:8: error: link_c: no file nowhere.c (paths are relative to the .wiz file)"] errs
        let (s, src, _) ← elabTree [("main.wiz", "import Prelude\nlink_lib \"-lm\"\n")]
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        checkEq 1 errs.size },
    { name := "link_c: a file is linked once, however often it is named", run := fun _ => do
        let (s, _, _) ← elabTree [("main.wiz", "import Prelude\nlink_c \"a.c\"\nlink_c \"./a.c\"\nlink_lib \"m\"\nlink_lib \"m\"\n"), ("a.c", "")]
        checkEq 1 s.linkC.size
        checkEq #["m"] s.linkLibs }
  ]

builtin_initialize registerGroup ffiGroup

end Tests.Elab
