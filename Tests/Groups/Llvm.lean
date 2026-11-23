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
  parallel := true
  cases := nativeCases true ++ [
    { name := "a partial application with no known arity is a compile error (F25)", run := fun _ => do
        let g : IR.Decl := { name := "g", params := #[0, 1], body := .ret 0 }
        let ok : IR.Decl := { name := "f", params := #[2], body := .vdecl 0 (.pap "g" #[2]) (.ret 0) }
        match LLVM.checkDecls #[g, ok] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"a valid partial application was rejected: {e}")
        -- (arity 0 used to be emitted: a closure that can never be applied)
        let bad : IR.Decl := { name := "f", params := #[], body := .vdecl 0 (.pap "nope" #[]) (.ret 0) }
        match LLVM.checkDecls #[bad] with
        | .error e => check ((e.splitOn "nope").length > 1) s!"the error does not name the function: {e}"
        | .ok _ => throw (IO.userError "a partial application of an unknown function was accepted") },
    { name := "the lowered IR of a program passes the checks and generates its module (F25)", run := fun _ => do
        -- (the toolchain-free half of the `=llvm` group: the checks must accept real IR)
        let s := runFrontend (R := ZeroOneMany)
          "import Prelude\ndef f (x : Nat) : Nat := x + 1\ndef main : Nat := f 41"
          { loader := ← preludeLoader }
        let (decls, _) ← match Build.irProgram s "main" with
          | .ok r => pure r
          | .error e => throw (IO.userError e)
        match LLVM.checkDecls decls with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"the LLVM backend rejected its own lowered IR: {e}")
        check (((LLVM.program decls).splitOn "define i32 @main").length > 1) "no `main` in the generated LLVM module" }
  ]

builtin_initialize registerGroup llvmGroup

end Tests.Elab
