import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (15k) A program large enough to split by hand: 64 definitions whose calls cross
translation-unit boundaries. -/
def splitSrc : String :=
  "import Prelude\n" ++
  String.join ((List.range 64).map fun i => s!"def sf{i} : Nat := {i} * 3\n") ++
  "\ndef main : Nat := " ++
  String.intercalate " + " ((List.range 64).map fun i => s!"sf{i}") ++ "\n"

/-- (15k) The same program compiled as four C units (the split path): the result and the
generated code must be the single-unit ones. -/
def splitCase : Case :=
  { name := "a C program in four translation units", run := fun _ => cRun splitSrc "6048" false 4 }

/-- (8b) The generated C carries the pointer-width guard from `runtime/wiz_abi.h`: a
64-bit word selects 62 small-int bits and a 32-bit word 30, any other width is an error,
and a 32-bit build gets the checked `WIZ_BOX`. The 64-bit literal emission is unchanged
(below 2^62 `WIZ_BOX`, from 2^62 `wiz_nat_lit`), so adding the guard changes no
representation. -/
def abiGuardSrc : String := "import Prelude
def main : List Nat := .cons 1073741824 (.cons 2147483648 (.cons 4611686018427387904 .nil))
"

def abiGuardCase : Case :=
  { name := "the generated C carries the pointer-width guard (32-bit cannot take the 62-bit small-int path)", run := fun _ => do
      let s := runFrontend (R := ZeroOneMany) abiGuardSrc { trustedModule := Tests.libModule, loader := ← preludeLoader }
      let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render abiGuardSrc
      unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
      let decls ← match Build.irProgram s "main" with
        | .ok (decls, _) => pure decls
        | .error e => throw (IO.userError e)
      let c := C.program decls
      for needle in ["#if WIZ_WORD_BITS == 64",
                     "#define WIZ_SMALL_BITS 62",
                     "#define WIZ_SMALL_BITS 30",
                     "unsupported pointer width",
                     "wiz_box_checked",
                     "#define WIZ_MAX_SMALL ((((uintptr_t)1) << WIZ_SMALL_BITS) - 1)"] do
        check ((c.splitOn needle).length > 1) s!"the generated C lacks {needle}"
      -- the 64-bit emission is unchanged
      check ((c.splitOn "WIZ_BOX(1073741824UL)").length > 1) "a 2^30 literal must be WIZ_BOX"
      check ((c.splitOn "WIZ_BOX(2147483648UL)").length > 1) "a 2^31 literal must be WIZ_BOX"
      check ((c.splitOn "wiz_nat_lit(\"4611686018427387904\")").length > 1)
        "a 2^62 literal must be wiz_nat_lit"
      -- a split program's header uses the same ABI text
      let h := C.splitHeader decls []
      for needle in ["#define WIZ_SMALL_BITS 62", "#define WIZ_SMALL_BITS 30", "unsupported pointer width"] do
        check ((h.splitOn needle).length > 1) s!"the split header lacks {needle}"
  }

def cGroup : Group where
  name := "c"
  exercise := "Exercise 8.2"
  cases := nativeCases false ++ [splitCase, abiGuardCase]

builtin_initialize registerGroup cGroup

end Tests.Elab
