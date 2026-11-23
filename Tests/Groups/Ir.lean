import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! `wiz-ir/1` (`Wiz/Compiler/IRDoc.lean`, `lib/Ir.wiz`): the document is the IR a
package backend reads. The cases pair the two implementations (Lean emitter, pure Wiz
reader/printer) against the checked-in fixtures, and run the one pass on both sides. -/

/-- A fixture under `Tests/fixtures/ir/`. -/
def irFixture (name : String) : IO String :=
  IO.FS.readFile ("Tests/fixtures/ir/" ++ name)

/-- The info messages of a Wiz source (the tests' `lib/` loader, no errors allowed). -/
def irMessages (src : String) : IO (List String) := do
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure (s.messages.toList.map (·.text))

/-- Parse `doc` and print it again, in pure Wiz. -/
def irRoundTrip (doc : String) : IO (List String) :=
  irMessages ("import Ir\n\ndef doc : String := " ++ Tests.wizStr doc ++
    "\n\n#eval match Ir.parse doc with\n  | .ok d => Ir.render d\n  | .error e => \"ir: \" ++ e\n")

/-- Parse `doc`, run the one pass, and print the result, in pure Wiz. -/
def irInline (doc : String) : IO (List String) :=
  irMessages ("import Ir\n\ndef doc : String := " ++ Tests.wizStr doc ++
    "\n\n#eval match Ir.parse doc with\n  | .ok d => Ir.render (Ir.inlineIdentity d)\n  | .error e => \"ir: \" ++ e\n")

/-- The emitted document of `root` in `src`, and the same document after the Lean
`inlineIdentity` pass. -/
def irDocsOf (src : String) (root : Name := "main") : IO (String × String) := do
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  match Build.irProgram s root with
  | .error e => throw (IO.userError e)
  | .ok (decls, _) => pure (IRDoc.render decls, IRDoc.render (IRDoc.inlineIdentity decls))

def irGroup : Group where
  name := "ir"
  exercise := "`wiz-ir/1` (extensibility item 5)"
  parallel := true
  shard := "library"
  cases := [
    { name := "Tests/fixtures/ir/one.ir round-trips through lib/Ir.wiz byte for byte", run := fun _ => do
        let fixture ← irFixture "one.ir"
        checkEq [Tests.wizStr fixture] (← irRoundTrip fixture) },
    { name := "the Lean emitter writes one.ir for the same declaration (twice)", run := fun _ => do
        -- `Build.irProgram` can compile any top-level definition as the program's root,
        -- which is the `#ir twice` view in the document format: one declaration.
        let src := "import Prelude\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\n"
        let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← libLoader }
        let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
        unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
        let (decls, _) ← match Build.irProgram s "twice" with
          | .error e => throw (IO.userError e)
          | .ok r => pure r
        let some d := decls.find? (fun d => d.name == "twice")
          | throw (IO.userError "the program does not contain the `twice` declaration")
        let want ← irFixture "one.ir"
        checkEq want (IRDoc.render #[d]) },
    { name := "the identity pass agrees with lib/Ir.wiz on the hand-written fixture", run := fun _ => do
        let input ← irFixture "inline.ir"
        let want ← irFixture "inline.out.ir"
        let idDecl : IR.Decl := { name := "id", params := #[0], borrow := #[false], body := .ret 0 }
        let mainDecl : IR.Decl :=
          { name := "main", params := #[], borrow := #[],
            body := .vdecl 1 (.lit 41) (.vdecl 2 (.fap "id" #[1]) (.dup 2 (.ret 2))) }
        let lean := IRDoc.render (IRDoc.inlineIdentity #[idDecl, mainDecl])
        checkEq want lean
        checkEq [Tests.wizStr want] (← irInline input) },
    { name := "the document and the pass agree with the Lean side on three =backend programs", run := fun _ => do
        -- Sources from `=backend`: a higher-order call, a recursive count, and a list
        -- rebuild (constructors, a case, reuse). The pass is a no-op on lowered code
        -- that already inlined its trivial definitions; the round-trip is not.
        let sources : List String := [
          "import Prelude\ndef twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)\n" ++
            "def main : Nat := twice (fun x => x + 1) 41\n",
          "import Prelude\ndef count : Nat → Nat\n  | .zero => 0\n" ++
            "  | .succ n => count n + 1\ndef main : Nat := count 1000\n",
          "import Prelude\ndef inc : List Nat → List Nat\n  | .nil => .nil\n" ++
            "  | .cons x xs => .cons (x + 1) (inc xs)\ndef main : List Nat := inc (.cons 1 (.cons 2 .nil))\n" ]
        for src in sources do
          let (doc, inline) ← irDocsOf src
          checkEq [Tests.wizStr doc, Tests.wizStr inline]
            ((← irRoundTrip doc) ++ (← irInline doc)) },
    { name := "an unknown major is refused, naming wiz-ir/1; a non-wiz head is refused too", run := fun _ => do
        let bad := "(wiz-ir/2 (decl \"x\" (params) (borrow) (ret 0)))"
        let notIr := "(bpf-core/1)"
        let two ← irMessages ("import Ir\n\ndef a : String := " ++ Tests.wizStr bad ++
          "\ndef b : String := " ++ Tests.wizStr notIr ++
          "\n\n#eval match Ir.parse a with\n  | .ok _ => \"accepted\"\n  | .error e => e\n" ++
          "\n#eval match Ir.parse b with\n  | .ok _ => \"accepted\"\n  | .error e => e\n")
        checkEq [Tests.wizStr "ir: unsupported version wiz-ir/2 (this reader is wiz-ir/1)",
          Tests.wizStr "ir: not a wiz-ir document"] two }
  ]

builtin_initialize registerGroup irGroup

end Tests.Elab
