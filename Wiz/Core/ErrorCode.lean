/-!
# Error codes

Every common error carries a stable **code**, a short kebab-case name for its kind: the
language server sends it as the diagnostic's `code` and keys its quick fixes on it
(`Wiz/Actions.lean`), and `docs/error-codes.md` lists them (a test checks that the table
there and `ErrorCode.all` agree). A code names the kind of mistake, not the wording: the
message may change, the code does not. Messages without a code have `""`.
-/

namespace Wiz.ErrorCode

/-- a name that is neither a local nor a global in scope -/
def unknownIdentifier := "unknown-identifier"
/-- (13v) `__root__` not as the first segment of a name, or a declaration named exactly
`__root__` (it is the root escape, not a name) -/
def rootName := "root-name"
/-- (13t) a name that two `open`s (or an `open` and a declaration) both provide -/
def ambiguousName := "ambiguous-name"
/-- (13t) a `namespace` with no `end` (reported at the `namespace`) -/
def unclosedNamespace := "unclosed-namespace"
/-- `t.f` where the type of `t` has no field (or namespace member) `f` -/
def noSuchField := "no-such-field"
/-- `.c` or a pattern `.c …` where the type has no constructor `c` -/
def unknownConstructor := "unknown-constructor"
/-- `import M` where no root has a module `M` -/
def unknownModule := "unknown-module"
/-- an `import` that leads back to the module itself -/
def importCycle := "import-cycle"
/-- an `import` of a module that has errors of its own -/
def moduleErrors := "module-errors"
/-- a reference to a declaration whose own command failed to elaborate (reported once as
`failed-declaration`, with that root error as a related diagnostic; never repeated as
`unknown-identifier`) -/
def failedDeclaration := "failed-declaration"
/-- a name (or a `deriving` class) that exists in a module the file does not import -/
def missingImport := "missing-import"
/-- the file the command names cannot be read (`wiz check no.wiz`) -/
def noSuchFile := "no-such-file"
/-- an `import` after a declaration, or nested in a command (the header is fixed) -/
def importOrder := "import-order"
/-- a `match` (or equations) that misses constructors -/
def missingCase := "missing-case"
/-- a copattern definition that misses an observation -/
def missingCopattern := "missing-copattern"
/-- an instance that misses a field of its class -/
def missingField := "missing-field"
/-- the expected and the inferred type do not unify -/
def typeMismatch := "type-mismatch"
/-- `rfl` where the two sides are not definitionally equal -/
def notDefeq := "not-defeq"
/-- too many arguments (`function expected`), or a pattern or constructor with the
wrong number of fields -/
def wrongArgumentCount := "wrong-argument-count"
/-- a named argument `(x := e)` for which the function has no parameter `x` -/
def unknownParameter := "unknown-parameter"
/-- a named argument given twice, or after the explicit parameter it would follow; a
structure field updated twice, or an instance field given twice -/
def namedArgument := "named-argument"
/-- a hole (`_`, an implicit argument, a binder's type) nothing determines -/
def unsolvedHole := "unsolved-hole"
/-- a universe level nothing determines -/
def unsolvedLevel := "unsolved-level"
/-- an expression whose type cannot be inferred without an ascription -/
def cannotInfer := "cannot-infer"
/-- a tactic block that ends with goals left -/
def unsolvedGoals := "unsolved-goals"
/-- a tactic that failed -/
def tacticFailed := "tactic-failed"
/-- a type was expected (`(x : 3)`) -/
def typeExpected := "type-expected"
/-- a binder whose quantity or implicitness differs from the expected type's -/
def binderMismatch := "binder-mismatch"
/-- a private name of another module, or a type whose constructors are private to it taken
apart -/
def private_ := "private"
/-- a name declared twice -/
def duplicateDeclaration := "duplicate-declaration"
/-- a `match` that names its equation hypothesis twice (`match h : e, h : f with`) -/
def duplicateHypothesis := "duplicate-hypothesis"
/-- a constructor declared twice in one `inductive` -/
def duplicateConstructor := "duplicate-constructor"
/-- a local variable that shadows the recursive definition it is in -/
def shadowedRecursive := "shadowed-recursive"
/-- a recursive call that is not structural -/
def notStructural := "not-structural"
/-- syntax that no macro or elaborator gives a meaning -/
def unknownSyntax := "unknown-syntax"
/-- an instance of something that is not a class, or of an unknown class -/
def unknownClass := "unknown-class"
/-- a command (`builtin`, `attribute`, `export`, …) naming an unknown declaration -/
def unknownDeclaration := "unknown-declaration"
/-- `attribute [simp] f` where `f`'s type is not an equation after its binders -/
def simpLemmaNotEquation := "simp-lemma-not-equation"
/-- `attribute [simp] f` where `f` has a premise before its equation (S3) -/
def simpLemmaConditional := "simp-lemma-conditional"
/-- a variable used against its quantity (erased, linear) -/
def quantity := "quantity"
/-- any other error of the kernel's -/
def kernelRejected := "kernel-rejected"
/-- the parser's errors -/
def parseError := "parse-error"
/-- (internal) unification outside the pattern fragment: the elaborator postpones on it;
reported as `type-mismatch` -/
def nonPattern := "non-pattern"

/-- The codes, as `docs/error-codes.md` lists them (`nonPattern` is internal). -/
def all : List String :=
  [unknownIdentifier, rootName, ambiguousName, unclosedNamespace, noSuchField, unknownConstructor, unknownModule, importCycle, moduleErrors,
   failedDeclaration, missingImport,
   noSuchFile, importOrder,
   missingCase, missingCopattern, missingField, typeMismatch, notDefeq, wrongArgumentCount,
   unknownParameter, namedArgument, unsolvedHole, unsolvedLevel, cannotInfer, unsolvedGoals,
   tacticFailed, typeExpected, binderMismatch, private_, duplicateDeclaration,
   duplicateHypothesis, duplicateConstructor, shadowedRecursive, notStructural, unknownSyntax, unknownClass,
   unknownDeclaration, simpLemmaNotEquation, simpLemmaConditional, quantity, kernelRejected, parseError]

/-- The code a message is reported with: internal codes become the public ones. -/
def reported (code : String) : String :=
  if code == nonPattern then typeMismatch else code

end Wiz.ErrorCode
