import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- Property checks for the standard library's hot structures (`examples/stdlib-props.wiz`):
`Array`, `StrMap`, `Bytes`, `String` (a `List Char`), and the sorted `U64Map.toList`
read-back. `allChecks` is 0 when every check holds. The `#eval` case runs the models; the
compiled cases run the natives (`String.eq`'s `implemented_by`, the hash cache in `Str`,
the map insert paths, and the radix sort). -/
def stdlibGroup : Group where
  name := "stdlib"
  exercise := "standard library data structures: examples/stdlib-props.wiz and bench/stdlib-bench.wiz"
  cases := [
    { name := "property checks over the models (#eval)", run := fun _ => do
        let src ← IO.FS.readFile "examples/stdlib-props.wiz"
        -- The pure `String` checks run in the evaluator (which has no Array, Bytes or
        -- StrMap natives); the compiled cases below run all of them.
        okLibs (src ++ "\n#eval textAll") ["0"] },
    { name := "property checks compiled (C)", run := fun _ => do
        let src ← IO.FS.readFile "examples/stdlib-props.wiz"
        cRunLibs src "0" },
    { name := "property checks compiled (LLVM)", run := fun _ => do
        let src ← IO.FS.readFile "examples/stdlib-props.wiz"
        cRunLibs src "0" (llvm := true) }
  ]

builtin_initialize registerGroup stdlibGroup

end Tests.Elab
