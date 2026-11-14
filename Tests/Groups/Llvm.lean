import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- The same programs, through LLVM (the toolchain's `llc`). -/
def llvmGroup : Group where
  name := "llvm"
  exercise := "Stage 8d"
  cases := nativeCases true

builtin_initialize registerGroup llvmGroup

end Tests.Elab
