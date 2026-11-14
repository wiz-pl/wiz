import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- `lib/Text.wiz` (stage 9j): pure, so `#eval` runs it; and the same compiled. -/
def textGroup : Group where
  name := "text"
  exercise := "Stage 9j"
  cases := [
    -- two modules that declare one name are an error at import: the libraries that had
    -- copies of Text's functions use Text's
    { name := "Text imports together with Json, Deriving, Hoare, Hdl.Core and Functor", run := fun _ => do
        for m in ["Json", "Deriving", "Hoare", "Hdl.Core", "Functor"] do
          okLibs s!"import Text\nimport {m}\n#eval Nat.repr 120" ["\"120\""]
          okLibs s!"import {m}\nimport Text\n#eval String.eq \"ab\" \"ab\"" [".true"]
        okLibs ("import Json\nimport Deriving\nimport Hoare\nimport Hdl.Core\nimport Functor\nimport Text\n" ++
          "#eval List.reverse (.cons 1 (.cons 2 .nil))\n#eval String.beq \"a\" \"b\"")
          [".cons 2 (.cons 1 .nil)", ".false"] },
    { name := "split, join, trim, replace, prefixes, numbers (#eval)", run := fun _ =>
        okLibs ("import Text\n#eval String.splitOn \"a,b,,c\" \",\"\n#eval String.splitOn \"a::b::\" \"::\"\n" ++
          "#eval String.splitOn \"abc\" \"\"\n#eval String.intercalate \", \" (.cons \"a\" (.cons \"b\" .nil))\n" ++
          "#eval String.trim \"  hi there \\n\"\n#eval String.replace \"it's\" \"'\" \"'\\\\''\"\n" ++
          "#eval String.stripPrefix \"refs/tags/v1\" \"refs/tags/\"\n#eval String.stripSuffix \"v1^{}\" \"^{}\"\n" ++
          "#eval String.endsWith \"abc\" \"bc\"\n#eval String.contains \"hello world\" \"o w\"\n" ++
          "#eval String.parseNat \"1203\"\n#eval String.parseNat \"12a\"\n#eval Nat.repr 1234567890123\n" ++
          "#eval String.lt \"abc\" \"abd\"\n#eval String.dropEnd 3 \"abcdef\"\n" ++
          "#eval String.lookup \"b\" (.cons (\"a\", 1) (.cons (\"b\", 2) .nil))\n")
          [".cons \"a\" (.cons \"b\" (.cons \"\" (.cons \"c\" .nil)))", ".cons \"a\" (.cons \"b\" (.cons \"\" .nil))",
           ".cons \"abc\" .nil", "\"a, b\"", "\"hi there\"", "\"it'\\\\''s\"", ".some \"v1\"", ".some \"v1\"",
           ".true", ".true", ".some 1203", ".none", "\"1234567890123\"", ".true", "\"abc\"", ".some 2"] },
    { name := "compiled: long strings stay linear", run := fun _ =>
        -- 200000 characters split, joined and trimmed: quadratic code would not finish
        ioRun ("import IO\nimport Text\ndef build : Nat → List Char → List Char\n  | .zero, acc => acc\n" ++
          "  | .succ n, acc => build n (.cons (Char.mk 97) (.cons (Char.mk 44) acc))\n" ++
          "def main : IO Unit := do\n  let s := String.ofChars (build 100000 .nil);\n" ++
          "  let parts := String.splitOn s \",\";\n  IO.println (Nat.toString (List.length parts));\n" ++
          "  IO.println (Nat.toString (String.length (String.intercalate \";\" parts)));\n" ++
          "  IO.println (Nat.toString (String.length (String.trim (String.replace s \",\" \"  \"))))")
          "100001\n200000\n299998\n" }
  ]

builtin_initialize registerGroup textGroup

end Tests.Elab
