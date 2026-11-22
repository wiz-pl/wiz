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

/-- (F25) A body whose joins bind repeated variables: `1`, then `3 4`, then `5`, then `3 1`.
The C function must declare each local once, in first-occurrence order. -/
def localsBody : IR.Body :=
  .vdecl 1 (.lit 1) <|
    .jdecl 2 #[3, 4] (.vdecl 5 (.lit 5) (.ret 5)) <|
      .vdecl 3 (.lit 3) (.vdecl 1 (.lit 1) (.ret 1))

/-- (F25) A partial application of a declaration whose parameters are known is fine. -/
def papOk : IR.Decl :=
  { name := "f", params := #[2], body := .vdecl 0 (.pap "g" #[2]) (.ret 0) }

/-- (F25) A jump to a join point in scope is fine. -/
def jmpOk : IR.Decl :=
  { name := "h", params := #[], body := .jdecl 0 #[] (.ret 0) (.jmp 0 #[]) }

def cGroup : Group where
  name := "c"
  exercise := "Exercise 8.2"
  parallel := true
  cases := nativeCases false ++ [splitCase,
    { name := "a body's locals are declared once each, in first-occurrence order (F25)", run := fun _ =>
        checkEq [1, 3, 4, 5] ((C.bound localsBody).toList) },
    { name := "a partial application with no known arity and a jump with no join point are compile errors (F25)", run := fun _ => do
        let g : IR.Decl := { name := "g", params := #[0, 1], body := .ret 0 }
        match C.checkDecls #[g, papOk] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"a valid partial application was rejected: {e}")
        match C.checkDecls #[g, jmpOk] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"a valid jump was rejected: {e}")
        -- (arity 0 used to be emitted: a closure that can never be applied)
        let badPap : IR.Decl := { name := "f", params := #[], body := .vdecl 0 (.pap "nope" #[]) (.ret 0) }
        match C.checkDecls #[badPap] with
        | .error e => check ((e.splitOn "nope").length > 1) s!"the error does not name the function: {e}"
        | .ok _ => throw (IO.userError "a partial application of an unknown function was accepted")
        -- (nothing used to be assigned to the join parameters)
        let badJmp : IR.Decl := { name := "h", params := #[], body := .jmp 3 #[] }
        match C.checkDecls #[badJmp] with
        | .error e => check ((e.splitOn "j3").length > 1) s!"the error does not name the join point: {e}"
        | .ok _ => throw (IO.userError "a jump to an unknown join point was accepted") },
    { name := "the lowered IR of a program passes the backend's checks and generates its main (F25)", run := fun _ => do
        -- (the toolchain-free half of the `=c` group: `checkDecls` must accept real IR)
        let s := runFrontend (R := ZeroOneMany)
          "import Prelude\ndef f (x : Nat) : Nat := x + 1\ndef main : Nat := f 41"
          { loader := ← preludeLoader }
        let (decls, _) ← match Build.irProgram s "main" with
          | .ok r => pure r
          | .error e => throw (IO.userError e)
        match C.checkDecls decls with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"the C backend rejected its own lowered IR: {e}")
        check (((C.program decls).splitOn "wiz_run_main").length > 1) "no `main` in the generated C" }]

builtin_initialize registerGroup cGroup

end Tests.Elab
