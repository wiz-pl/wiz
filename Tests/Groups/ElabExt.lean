import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## TT-04: the attribute and option registry

The registry is data in `CommandState`: `attrDecls`/`optDecls` say what a name accepts
and does, `register_attribute`/`register_option` add a user no-op, and applications are
looked up instead of one parser rule and one match arm per name. These cases cover
registration, duplicate/unknown/malformed errors, `local` isolation, cache replay and a
user extension. -/

def runExtWith (mods : List (Name × String)) (input : String) : IO (CommandState ZeroOneMany) := do
  let lib ← preludeLoader
  let loader : Name → Option String := fun m => match mods.lookup m with
    | some src => some src
    | none => lib m
  pure (runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader })

def extErrors (s : CommandState ZeroOneMany) (input : String) : Array String :=
  (s.messages.filter (·.severity == .error)).map fun m => m.render input

def failsExt (mods : List (Name × String)) (input fragment : String) : IO Unit := do
  let s ← runExtWith mods input
  let errs := extErrors s input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def elabExtGroup : Group where
  name := "elab-ext"
  exercise := "TT-04"
  cases := [
    { name := "a user registers a no-op attribute and option (user extension)", run := fun _ => do
        let s ← runExtWith [] ("import Prelude\n" ++
          "def f : Nat := 1\n" ++
          "register_attribute tag\nattribute [tag] f\n" ++
          "register_option answer : Nat := 42\nset_option answer 7\n#check f")
        check (extErrors s "").isEmpty "unexpected errors"
        check (s.attrDecl? "tag" == some { name := "tag", payload := .flag, action := .noop })
          "the user attribute was not registered"
        check (s.optDecl? "answer" == some { name := "answer", kind := .natural, default := .nat 42 })
          "the user option was not registered"
        check (s.attrUses.contains ("tag", "f", #[])) "the attribute application was not recorded"
        check (s.optValue? "answer" == some (.nat 7)) "the option value is not 7"
        check (s.messages.any (·.text == "f : Nat")) "the file did not check" },
    { name := "the migrated built-in attribute and option still work", run := fun _ => do
        let s ← runExtWith [] ("import Prelude\n" ++
          "def f (n : Nat) : Nat := n\n" ++
          "attribute [inline] f\n" ++
          "set_option pp.notation false")
        check (extErrors s "").isEmpty "unexpected errors"
        check (s.builtins.contains ("inline", "f")) "`[inline]` did not register the implementation"
        check (!s.globals.pp.useNotation) "`set_option pp.notation false` did not take effect"
        check (s.optValue? "pp.notation" == some (.bool false)) "the option value is not false"
        let s ← runExtWith [] "import Prelude\nset_option pp.all true"
        check (!s.globals.pp.useNotation) "`set_option pp.all true` did not turn notation off"
        check (s.optValue? "pp.all" == some (.bool true)) "the `pp.all` value is not true" },
    { name := "duplicate registrations are rejected", run := fun _ => do
        failsExt [] "import Prelude\nregister_attribute tag\nregister_attribute tag" "already registered"
        failsExt [] "import Prelude\nregister_option mine : Bool := false\nregister_option mine : Nat := 0"
          "already registered" },
    { name := "unknown attributes and options are rejected", run := fun _ => do
        failsExt [] "import Prelude\ndef f : Nat := 0\nattribute [nope] f" "unknown attribute 'nope'"
        failsExt [] "import Prelude\nset_option nope true" "unknown option 'nope'"
        failsExt [] "import Prelude\nregister_attribute tag\nattribute [tag] nope" "unknown declaration 'nope'"
        failsExt [] "import Prelude\ndef f : Nat := 0\nlocal attribute [inline] f" "only a no-op attribute can be `local`" },
    { name := "malformed payloads and values are rejected", run := fun _ => do
        failsExt [] "import Prelude\ndef f : Nat := 0\nattribute [inline 3] f" "takes no arguments"
        failsExt [] "import Prelude\ndef f : Nat := 0\nattribute [macro] f" "takes one name argument"
        failsExt [] "import Prelude\nset_option pp.notation 3" "expects `true` or `false`"
        failsExt [] "import Prelude\nregister_option o : Num := 0" "unknown option type 'Num'"
        failsExt [] "import Prelude\nregister_option o : Nat := true" "expects a numeral" },
    { name := "`local` attributes, registrations and options end with the module", run := fun _ => do
        let loc := "import Prelude\n" ++
          "register_attribute tag\n" ++
          "register_option mine : Bool := false\n" ++
          "def foo : Nat := 1\n" ++
          "attribute [tag] foo\n" ++
          "local attribute [tag] foo\n" ++
          "local register_attribute ltag\n" ++
          "local register_option lopt : Nat := 0\n" ++
          "def bar : Nat := 2\n" ++
          "attribute [ltag] bar\n" ++
          "local set_option mine true\n" ++
          "local set_option pp.notation false\n"
        let s ← runExtWith [("Loc", loc)] "import Loc\ndef x : Nat := 3"
        check (extErrors s "import Loc\ndef x : Nat := 3").isEmpty "unexpected errors"
        check (s.attrDecl? "tag").isSome "the non-local attribute registration was lost"
        check (s.attrDecl? "ltag").isNone "the local attribute registration escaped"
        check (s.optDecl? "mine").isSome "the non-local option registration was lost"
        check (s.optDecl? "lopt").isNone "the local option registration escaped"
        check (s.optValue? "mine" == some (.bool false)) "the module's option value escaped"
        check s.globals.pp.useNotation "the module's pp.notation escaped"
        checkEq 1 s.attrUses.length
        check (s.attrUses.head? == some ("tag", "foo", #[])) "the wrong attribute applications survived" },
    { name := "the cache replays attributes and options", run := fun _ => do
        let lib ← preludeLoader
        let init : CommandState ZeroOneMany := { trustedModule := Tests.libModule, loader := lib }
        let src := "import Prelude\n" ++
          "register_attribute tag\nregister_option mine : Bool := false\n" ++
          "set_option mine true\n" ++
          "def f : Nat := 1\nattribute [tag] f\n" ++
          "def g : Nat := 2\n"
        let dir ← IO.FS.createTempDir
        let (cold, h1) ← Cache.elaborateCached (some dir) [] src init 0
        let (warm, h2) ← Cache.elaborateCached (some dir) [] src init 0
        checkEq 0 h1
        check (h2 > 0) "nothing came from the cache"
        for (how, st) in [("cold", cold), ("warm", warm)] do
          check (st.attrUses.contains ("tag", "f", #[])) s!"{how}: the attribute application was lost"
          check (st.optValue? "mine" == some (.bool true)) s!"{how}: the option value was lost"
          check (st.globals.contains "g") s!"{how}: the cached definition is missing"
        -- through an import too: a module's registrations and options are replayed
        let m := "import Prelude\nregister_attribute tag\nregister_option mine : Bool := false\n" ++
          "set_option mine true\ndef f : Nat := 1\nattribute [tag] f\n"
        let main := "import M\ndef g : Nat := 2\n"
        let initM : CommandState ZeroOneMany :=
          { trustedModule := Tests.libModule, loader := fun n => (if n == "M" then some m else lib n) }
        let dir2 ← IO.FS.createTempDir
        let (cold, h3) ← Cache.elaborateCached (some dir2) [] main initM 0
        let (warm, h4) ← Cache.elaborateCached (some dir2) [] main initM 0
        checkEq 0 h3
        check (h4 > 0) "nothing came from the cache through the import"
        for (how, st) in [("cold import", cold), ("warm import", warm)] do
          check (st.attrUses.contains ("tag", "f", #[])) s!"{how}: the imported attribute application was lost"
          -- an imported module's options are its own: the registration survives, the value does not
          check (st.optDecl? "mine").isSome s!"{how}: the imported option registration was lost"
          check (st.optValue? "mine" == some (.bool false)) s!"{how}: the imported option value leaked"
        IO.FS.removeDirAll dir
        IO.FS.removeDirAll dir2 }
  ]

builtin_initialize registerGroup elabExtGroup

end Tests.Elab
