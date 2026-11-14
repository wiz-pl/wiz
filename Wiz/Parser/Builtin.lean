import Wiz.Parser.Descr
import Wiz.Syntax.Children

/-!
# The built-in grammar

Everything here is ordinary `ParserDescr` data, registered exactly as a user `syntax`
declaration would be. Node kinds and the shape of their children are the contract with
the elaborator (`Wiz.Elab`), so they're listed with each parser.

Notation: `[x]` means "a `null` node", so `optional p` gives `[]` or `[p...]`.

```
quantity          := num | "ω" | "%" term
binder.explicit   := "(" [quantity] [names+] [":" type] ")"
binder.implicit   := "{" [quantity] [names+] [":" type] "}"
```

Quantities follow Idris 2: `(1 x : A)`, `{0 A : Type}`. An omitted quantity means ω
on explicit binders and 0 on implicit ones.
-/

namespace Wiz.Builtin

open ParserDescr

def term (prec : Nat := 0) : ParserDescr := cat "term" prec
def arrow : ParserDescr := orelse (atom "→") (atom "->")
def seqs (ps : List ParserDescr) : ParserDescr := seq ps.toArray

/-- `0`, `1`, `ω`, or `%t` for a quantity-valued term (stage 4d). -/
def quantity : ParserDescr :=
  node "quantity" (orelse num (orelse (atom "ω") (seqs ["%", noWs, cat "term" maxPrec])))

def hole : ParserDescr := node "term.hole" (atom "_")
def binderIdent : ParserDescr := orelse ident hole

/-- `[":" T]`, either optional or required (a required one is still a one-element
`null` node so both have the same shape). -/
def typeSpec (required : Bool) : ParserDescr :=
  if required then node "null" (seqs [":", term]) else optional (seqs [":", term])

def explicitBinder (requireType : Bool) : ParserDescr :=
  node "binder.explicit" <| seqs ["(", withoutPosition <| seqs
    [optional quantity, many1 binderIdent, typeSpec requireType], ")"]

def implicitBinder (requireType : Bool) : ParserDescr :=
  node "binder.implicit" <| seqs ["{", withoutPosition <| seqs
    [optional quantity, many1 binderIdent, typeSpec requireType], "}"]

/-- `[x : C A]` or `[C A]`: an instance-implicit binder (stage 7) -/
def instBinder : ParserDescr :=
  node "binder.inst" <| seqs ["[", withoutPosition <| seqs [optional (seqs [ident, ":"]), term], "]"]

def bracketedBinder (requireType : Bool) : ParserDescr :=
  orelse (explicitBinder requireType) (orelse (implicitBinder requireType) instBinder)

/-- Binders of `fun` and `∀`: a bare name or a bracketed group with optional type. -/
def simpleBinder : ParserDescr := orelse (bracketedBinder false) binderIdent

/-- `| p₁, …, pₙ => rhs` -/
def matchAlt : ParserDescr :=
  node "match.alt" (seqs ["|", sepBy1 (cat "term" 0) ",", "=>", cat "term" 0])

def precedence : ParserDescr := node "prec" (orelse num ident)

def level (prec : Nat := 0) : ParserDescr := cat "level" prec

/-- `.{u, v}` after a name -/
def univParams : ParserDescr := optional (seqs [noWs, ".{", sepBy1 ident ",", "}"])

/-- Universe levels.

| kind          | children |
|---------------|----------|
| `level.num`   | num |
| `level.param` | ident |
| `level.hole`  | "_" |
| `level.paren` | "(" level ")" |
| `level.max`, `level.imax` | "max" level level |
| `level.add` (trailing) | level "+" num |
-/
def levelLeading : List LeadingParser := [
  { kind := "level.num", prec := maxPrec, p := num },
  { kind := "level.param", prec := maxPrec, p := ident },
  { kind := "level.hole", prec := maxPrec, p := "_" },
  { kind := "level.paren", prec := maxPrec, p := seqs ["(", withoutPosition (level 0), ")"] },
  { kind := "level.max", prec := leadPrec, p := seqs [nonReserved "max", level maxPrec, level maxPrec] },
  { kind := "level.imax", prec := leadPrec, p := seqs [nonReserved "imax", level maxPrec, level maxPrec] }
]

def levelTrailing : List TrailingParser := [
  { kind := "level.add", prec := 65, lhsPrec := 65, p := seqs ["+", num] }
]

/-- `⟨t₁, …, tₙ⟩` (13h) -/
def anonCtor : ParserDescr := seqs ["⟨", withoutPosition (sepBy term ","), "⟩"]

/-- Term syntax.

| kind                 | prec | children |
|----------------------|------|----------|
| `term.ident`         | max  | ident |
| `term.num`, `term.str` | max | literal |
| `term.type`          | max  | "Type" [level] |
| `term.sort`          | max  | "Sort" [level] |
| `term.prop`          | max  | "Prop" |
| `term.identUniv`     | max  | ident ".{" [levels] "}" |
| `term.hole`          | max  | "_" |
| `term.syntheticHole` | max  | "?" ident |
| `term.paren`         | max  | "(" term ")" |
| `term.ascription`    | max  | "(" term ":" term ")" |
| `term.namedArg`      | max  | "(" ident ":=" term ")" (an argument of an application) |
| `term.explicit`      | max  | "@" ident |
| `term.fun`           | max  | "fun" [binder+] "=>" term |
| `term.let`           | lead | "let" [quantity] ident [":" T] ":=" term [";"] term |
| `term.forall`        | lead | ("∀" / "forall") [binder+] "," term |
| `term.depArrow`      | 25   | binder "→" term |
| `term.app` (trailing)| lead | f [args+] |
| `term.arrow` (trailing)| 25 | A "→" B |
| `term.depSigma`      | 35   | binder "×" term |
| `term.prod` (trailing) | 35 | A "×" B |
| `term.tuple`         | max  | "(" term "," [terms] ")" |
| `term.unitVal`       | max  | "(" ")" |
| `term.proj` (trailing) | max | t "." num |
| `term.field` (trailing) | max | t "." ident (a Σ field, or `T.f t` for a nominal `T`) |
| `term.letUnit`       | lead | "let" "(" ")" ":=" term [";"] term (the unit eliminator: consumes a `Unit`) |
| `term.letPair`       | lead | "let" [quantity] "(" ident "," ident ")" ":=" term [";"] term |
| `term.letTuple`      | lead | "let" [quantity] "(" ident "," ident "," [idents,+] ")" ":=" term [";"] term |
| `term.absurd`        | lead | "absurd" term |
| `term.eq` (trailing) | 50   | a "=" b |
| `term.refl`          | lead | "refl" term |
| `term.rfl`           | max  | "rfl" |
| `term.nativeRefl`    | max  | "native_refl" (27a: the whole body of a `def`, with `--trust-native`) |
| `term.cast`          | lead | "cast" term term |
| `term.transp`        | lead | "transp" term term term |
| `term.enum`          | max  | "Enum" "[" [idents] "]" |
| `term.tag`           | max  | "'" ident |
| `term.ecase`         | lead | "ecase" term "[" [terms] "]" |
| `term.dotIdent`      | max  | "." ident (a constructor of the expected type) |
| `term.match`         | lead | "match" [terms] "with" [alts] |
| `term.szInf`, `term.szSuc`, `term.sizeLt` | | "∞", "↑" s, "Size<" s |
| `term.sized` (trailing) | max | T "^" s: an inductive or coinductive type at size `s` |
| `term.asPat` (trailing) | max | x "@" p, without spaces: an as-pattern (13g; patterns only) |
| `term.anon`          | max  | "⟨" [terms] "⟩": the constructor of the expected structure (13h; also a pattern) |
| `term.letPat`        | lead | "let" [quantity] (`term.anon` / `term.paren`) ":=" term [";"] term (13h) |
| `term.structUpdate`  | max  | "{" term "with" [`structUpdate.field`: ident ":=" term],+ "}" (13i) |

The data primitives `Desc`, `Desc.ret`, `Desc.arg`, `Desc.rec`, `Desc.elim`,
`Desc.interp`, `Desc.All`, `μ`, `ν`, `con`, `ind`, `out`, `coit` and `cocon` have no syntax of their
own: they are names the elaborator recognises when applied (unless shadowed).

Field access by name (`p.x`) needs no syntax: `p.x` lexes as one dotted identifier,
and the elaborator resolves it.
-/
def termLeading : List LeadingParser := [
  { kind := "term.ident", prec := maxPrec, p := ident },
  { kind := "term.num", prec := maxPrec, p := num },
  { kind := "term.omega", prec := maxPrec, p := "ω" },
  { kind := "term.str", prec := maxPrec, p := str },
  -- the level must be right of the enclosing position: in a structure, `op : Type` and a
  -- field `ret` on the next line are two fields, not `Type ret`
  { kind := "term.type", prec := maxPrec, p := seqs ["Type", optional (seqs [checkPrec leadPrec, colGt, level maxPrec])] },
  { kind := "term.sort", prec := maxPrec, p := seqs ["Sort", optional (seqs [checkPrec leadPrec, colGt, level maxPrec])] },
  { kind := "term.prop", prec := maxPrec, p := "Prop" },
  { kind := "term.identUniv", prec := maxPrec, p := seqs [ident, noWs, ".{", sepBy1 (level 0) ",", "}"] },
  { kind := "term.hole", prec := maxPrec, p := "_" },
  { kind := "term.syntheticHole", prec := maxPrec, p := seqs ["?", noWs, ident] },
  { kind := "term.paren", prec := maxPrec, p := seqs ["(", withoutPosition term, ")"] },
  -- 13a: a named argument, only as an argument of an application
  { kind := "term.namedArg", prec := maxPrec, p := seqs ["(", withoutPosition (seqs [ident, ":=", term]), ")"] },
  { kind := "term.ascription", prec := maxPrec,
    p := seqs ["(", withoutPosition (seqs [term, ":", term]), ")"] },
  { kind := "term.explicit", prec := maxPrec, p := seqs ["@", noWs, ident] },
  { kind := "term.fun", prec := maxPrec,
    p := seqs [orelse "fun" "λ", many1 simpleBinder, orelse "=>" "↦", term] },
  { kind := "term.let", prec := leadPrec,
    p := seqs [withPosition (seqs ["let", optional quantity, ident, typeSpec false, ":=", term]),
      optional ";", term] },
  { kind := "term.forall", prec := leadPrec,
    p := seqs [orelse "∀" "forall", many1 simpleBinder, ",", term] },
  { kind := "term.depArrow", prec := 25, p := seqs [bracketedBinder true, arrow, term 25] },
  { kind := "term.depSigma", prec := 35, p := seqs [explicitBinder true, "×", term 35] },
  { kind := "term.tuple", prec := maxPrec,
    p := seqs ["(", withoutPosition (seqs [term, ",", sepBy1 term ","]), ")"] },
  { kind := "term.unitVal", prec := maxPrec, p := seqs ["(", ")"] },
  -- (linear-case stage 2) the unit eliminator `let () := u; b`
  { kind := "term.letUnit", prec := leadPrec,
    p := withPosition <| seqs ["let", "(", ")", ":=", term, optional ";", term] },
  { kind := "term.letPair", prec := leadPrec,
    p := seqs [withPosition (seqs ["let", optional quantity, "(", ident, ",", ident, ")", ":=", term]),
      optional ";", term] },
  -- three or more components: right-nested pairs (`Elab.letTupleToPairs`)
  { kind := "term.letTuple", prec := leadPrec,
    p := seqs [withPosition (seqs ["let", optional quantity, "(", ident, ",", ident, ",", sepBy1 ident ",", ")",
      ":=", term]), optional ";", term] },
  { kind := "term.absurd", prec := leadPrec, p := seqs ["absurd", term maxPrec] },
  { kind := "term.refl", prec := leadPrec, p := seqs [nonReserved "refl", term maxPrec] },
  { kind := "term.rfl", prec := maxPrec, p := "rfl" },
  -- (27a) only as the whole body of a definition (`Command.lean`), with `--trust-native`
  { kind := "term.nativeRefl", prec := maxPrec, p := "native_refl" },
  { kind := "term.cast", prec := leadPrec, p := seqs ["cast", term maxPrec, term maxPrec] },
  { kind := "term.transp", prec := leadPrec, p := seqs ["transp", term maxPrec, term maxPrec, term maxPrec] },
  { kind := "term.enum", prec := maxPrec, p := seqs [nonReserved "Enum", "[", sepBy ident ",", "]"] },
  { kind := "term.tag", prec := maxPrec, p := seqs ["'", noWs, ident] },
  { kind := "term.dotIdent", prec := maxPrec, p := seqs [".", noWs, ident] },
  -- 13h: the anonymous constructor (also a pattern), and `let` with a pattern
  { kind := "term.anon", prec := maxPrec, p := anonCtor },
  { kind := "term.letPat", prec := leadPrec,
    p := seqs [withPosition (seqs ["let", optional quantity,
      orelse (node "term.anon" anonCtor) (node "term.paren" (seqs ["(", withoutPosition term, ")"])),
      ":=", term]), optional ";", term] },
  -- 13i: structure update
  { kind := "term.structUpdate", prec := maxPrec,
    p := seqs ["{", withoutPosition (seqs [term, "with",
      sepBy1 (node "structUpdate.field" (seqs [ident, ":=", term])) ","]), "}"] },
  { kind := "term.szInf", prec := maxPrec, p := "∞" },
  { kind := "term.szSuc", prec := maxPrec, p := seqs ["↑", term maxPrec] },
  { kind := "term.sizeLt", prec := leadPrec, p := seqs ["Size<", term maxPrec] },
  { kind := "term.match", prec := leadPrec,
    -- alternatives line up at or right of the first `|`, so an outer match's next
    -- alternative ends a nested match (as in Lean)
    p := seqs ["match", sepBy1 term ",", "with", withPosition (many (seqs [colGe, matchAlt]))] },
  -- tactics line up (or are separated by `;`); the tactics themselves come from the prelude
  { kind := "term.by", prec := leadPrec,
    p := seqs ["by", withPosition (many1 (seqs [colGe, cat "tactic" 0, optional ";"]))] },
  { kind := "term.ecase", prec := leadPrec,
    p := seqs [nonReserved "ecase", term maxPrec, "[", withoutPosition (sepBy term ","), "]"] }
]

def termTrailing : List TrailingParser := [
  { kind := "term.app", prec := leadPrec, lhsPrec := maxPrec,
    p := many1 (seqs [colGt, term argPrec]) },
  { kind := "term.arrow", prec := 25, lhsPrec := 26, p := seqs [arrow, term 25] },
  { kind := "term.prod", prec := 35, lhsPrec := 36, p := seqs ["×", term 35] },
  { kind := "term.eq", prec := 50, lhsPrec := 51, p := seqs ["=", term 51] },
  { kind := "term.proj", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, ".", noWs, num] },
  { kind := "term.field", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, ".", noWs, ident] },
  -- (a priority: `T^s` without spaces is a sized type, not the operator `^` of
  -- lib/Prelude.wiz, which parses the same text as far, 7f)
  { kind := "term.sized", prec := maxPrec, lhsPrec := maxPrec, priority := 1, p := seqs [noWs, "^", term maxPrec] },
  -- 13g: an as-pattern `x@p` (no space around `@`; only in patterns)
  { kind := "term.asPat", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, "@", noWs, term maxPrec] }
]

/-- A field of a `structure`, `class` or `coinductive` (an observation), on its own line;
`private` (13b) makes its projection (observation) private to the module. -/
def structureField : ParserDescr :=
  node "structure.field" (withPosition (seqs [optional (atom "private"), optional quantity, ident, ":", term]))

/-- `where`, then optionally `private mk ::` (13b: a constructor private to the module) -/
def structureWhere : ParserDescr :=
  node "structure.where" (seqs ["where", optional (seqs [optional (atom "private"), ident, "::"])])

/-- `deriving C₁, C₂` after an `inductive` or `structure` (HD8) -/
def derivingClause : ParserDescr := optional (seqs ["deriving", sepBy1 ident ","])

/-- Commands. Each command is parsed inside `withPosition`, so an application can't
continue onto a line starting at the command's column.

| kind                         | children |
|------------------------------|----------|
| `command.def`                | "def" ident [".{" [us] "}"] [binders] [":" T] ":=" term |
| `command.axiom`              | "axiom" ident [".{" [us] "}"] [binders] ":" T |
| `command.check`              | "#check" term |
| `command.reduce`             | "#reduce" term |
| `command.declareSyntaxCat`   | "declare_syntax_cat" ident ["(" "keywords" ":=" ident ")"] |
| `command.syntax`             | "syntax" [":" prec] [name] [priority] [stx+] ":" ident |
| `command.inductive`          | "inductive" ident [".{" us "}"] [binders] [":" T] "where" [ctors] ["deriving" C,+] |
| `command.structure`          | "structure" ident [".{" us "}"] [binders] [":" T] where [fields] ["deriving" C,+] (where: `structure.where`, "where" [["private"] ident "::"]) |
| `command.private`            | "private" command (every name it declares is private to the module) |
| `command.sealed`             | "sealed" command (an `inductive`: no other declaration is this type) |
| `command.local`              | "local" command (13m: a `syntax`, `notation`, `infix…`, `macro_rules` or `attribute [macro …]` whose syntax stays in the module; 11w: an `instance` found only in the module) |
| `command.deriving`           | "deriving" "instance" C,+ "for" T,+ |
| `command.attrDeriver`        | "attribute" "[" "deriver" ident "]" ident |
| `command.attrInline`         | "attribute" "[" "inline" "]" ident |
| `command.attrDefaultInstance`| "attribute" "[" "default_instance" [num] "]" ident (7f) |
| `command.attrBinop`          | "attribute" "[" "binop" "]" ident (7f) |
| `command.coinductive`        | like `structure`; the fields are observations |
| `command.defEqns`            | "def" ident [".{" us "}"] [binders] ":" T [alts] |
| `command.partial`            | "partial" ["(" "default" ":=" w ")"] command (a `def`) |
| `command.mutual`             | "mutual" [command+] "end" (`def`s, all partial; or `partial (default := w) def`s) |
| `command.printAxioms`        | "#print" "axioms" ident |
| `command.cStruct`            | "c_struct" [str] ["(" "header" ":=" str ")"] ident "where" [fields] ["deriving" C,+] (9i) |

A constructor is `inductive.ctor`: "|" ["private"] ident [binders] [":" T]. A field is
`structure.field`: ["private"] [quantity] ident ":" T, on its own line (13b: `private`
makes the constructor, or the field's projection or observation, private to the module).
-/
def commandLeading : List LeadingParser := [
  { kind := "command.def", prec := maxPrec,
    p := seqs ["def", ident, univParams, many (bracketedBinder false), typeSpec false, ":=", term] },
  { kind := "command.defEqns", prec := maxPrec,
    p := seqs ["def", ident, univParams, many (bracketedBinder false), typeSpec true, many1 matchAlt] },
  -- 13b: every name the command declares is visible only in this module
  { kind := "command.private", prec := maxPrec, p := seqs ["private", cat "command" 0] },
  -- 22k: `sealed inductive T …`: only this declaration is the type `T` (a look-alike is
  -- another type); needed for a native representation
  { kind := "command.sealed", prec := maxPrec, p := seqs ["sealed", cat "command" 0] },
  -- 13m: notation that importers don't see (`local` is not reserved)
  { kind := "command.local", prec := maxPrec, p := seqs [nonReserved "local", cat "command" 0] },
  -- stage 13: general recursion; a `mutual` block's definitions are partial too
  -- (a partial definition's type needs a witness: found, or given with `(default := w)`)
  { kind := "command.partial", prec := maxPrec,
    p := seqs ["partial", optional (seqs ["(", nonReserved "default", ":=", term, ")"]), cat "command" 0] },
  { kind := "command.mutual", prec := maxPrec, p := seqs ["mutual", many1 (cat "command" 0), "end"] },
  { kind := "command.axiom", prec := maxPrec,
    p := seqs ["axiom", ident, univParams, many (bracketedBinder false), typeSpec true] },
  { kind := "command.check", prec := maxPrec, p := seqs ["#check", term] },
  { kind := "command.printAxioms", prec := maxPrec, p := seqs ["#print", nonReserved "axioms", ident] },
  { kind := "command.reduce", prec := maxPrec, p := seqs ["#reduce", term] },
  { kind := "command.eval", prec := maxPrec, p := seqs ["#eval", term] },
  { kind := "command.erase", prec := maxPrec, p := seqs ["#erase", ident] },
  { kind := "command.import", prec := maxPrec, p := seqs ["import", ident] },
  -- stage 8: run through the backend pipeline (IR, reference counting), print the IR
  { kind := "command.run", prec := maxPrec, p := seqs ["#run", term] },
  { kind := "command.ir", prec := maxPrec, p := seqs ["#ir", ident] },
  { kind := "command.builtin", prec := maxPrec, p := seqs ["builtin", ident, ":=", ident] },
  -- stage 9: a foreign (C) function
  { kind := "command.glue", prec := maxPrec,
    p := seqs ["glue", ident, many (bracketedBinder false), ":", term, ":=", str] },
  { kind := "command.foreignType", prec := maxPrec,
    p := seqs ["foreign_type", ident, optional (seqs ["(", nonReserved "finalizer", ":=", str, ")"]),
      -- 9i: the C pointer type it stands for in imported headers (`T *` for the type `T`)
      optional (seqs ["(", nonReserved "c", ":=", str, ")"])] },
  { kind := "command.importC", prec := maxPrec,
    p := seqs ["import_c", str, optional (seqs ["(", nonReserved "pure", ")"]),
      -- 9i: opt-outs of the automatic mapping of structs, pointers and buffers
      many (node "importC.opt" (seqs ["(", orelse (seqs [nonReserved "skip", ":=", str]) (nonReserved "no_auto"), ")"]))] },
  -- 9i: a C struct, as a Wiz structure: `c_struct ["struct t"] [(header := "h")] T where fields`
  { kind := "command.cStruct", prec := maxPrec,
    p := seqs ["c_struct", optional str, optional (seqs ["(", nonReserved "header", ":=", str, ")"]), ident,
      "where", many structureField, derivingClause] },
  -- 9f: C source files and libraries linked with the program
  { kind := "command.linkC", prec := maxPrec, p := seqs ["link_c", str] },
  { kind := "command.linkLib", prec := maxPrec, p := seqs ["link_lib", str] },
  { kind := "command.extern", prec := maxPrec,
    p := seqs ["extern", str, optional (seqs ["(", nonReserved "header", ":=", str, ")"]), ident, ":", term] },
  -- stage 9g: a C symbol for a Wiz function
  { kind := "command.export", prec := maxPrec,
    p := seqs ["export", str, ident, optional (seqs [":", term])] },
  { kind := "command.attrMacro", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "macro", ident, "]", ident] },
  { kind := "command.attrTactic", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "tactic", ident, "]", ident] },
  -- compiled code calls the first name instead of the second; the kernel keeps the second.
  -- On a constructor, two names: the native constructor and the native field (22d).
  { kind := "command.attrImplementedBy", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "implemented_by", ident, optional ident, "]", ident] },
  -- 22i: compiled code inlines the definition where it is applied (to all its arguments)
  { kind := "command.attrInline", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "inline", "]", ident] },
  -- 7f: a default instance (with a priority), and an operator whose numeral operands take
  -- the type of the others (Lean's `binop%`)
  { kind := "command.attrDefaultInstance", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "default_instance", optional num, "]", ident] },
  { kind := "command.attrBinop", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "binop", "]", ident] },
  -- HD8: `deriving`
  { kind := "command.attrDeriver", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "deriver", ident, "]", ident] },
  { kind := "command.deriving", prec := maxPrec,
    p := seqs ["deriving", "instance", sepBy1 ident ",", nonReserved "for", sepBy1 ident ","] },
  { kind := "command.declareSyntaxCat", prec := maxPrec, p := seqs ["declare_syntax_cat", ident, optional (seqs ["(", nonReserved "keywords", ":=", ident, ")"])] },
  { kind := "command.syntax", prec := maxPrec,
    p := seqs ["syntax", optional (seqs [noWs, ":", noWs, precedence]),
      optional (seqs ["(", nonReserved "name", ":=", ident, ")"]),
      optional (seqs ["(", nonReserved "priority", ":=", num, ")"]),
      many1 (cat "stx" 0), ":", ident] },
  { kind := "command.inductive", prec := maxPrec,
    p := seqs ["inductive", ident, univParams, many (bracketedBinder false), optional (seqs [":", term]),
      "where", many (node "inductive.ctor" (seqs ["|", optional (atom "private"), ident, many (bracketedBinder false),
        optional (seqs [":", term])])), derivingClause] },
  { kind := "command.structure", prec := maxPrec,
    p := seqs ["structure", ident, univParams, many (bracketedBinder false), optional (seqs [":", term]),
      structureWhere, many (structureField),
      derivingClause] },
  -- stage 7: a class is a structure whose values are found by instance resolution
  { kind := "command.class", prec := maxPrec,
    p := seqs ["class", ident, univParams, many (bracketedBinder false), optional (seqs [":", term]),
      "where", many (structureField)] },
  { kind := "command.instance", prec := maxPrec,
    p := seqs ["instance", optional (seqs ["(", nonReserved "priority", ":=", num, ")"]),
      -- (7f) an optional name (`instance instHAdd [Add A] : HAdd A A A`)
      optional ident,
      many (bracketedBinder false), ":", term,
      orelse (seqs [":=", term])
        (seqs ["where", withPosition (many1 (node "instance.field" (seqs [colGe, ident, ":=", term])))])] },
  { kind := "command.coinductive", prec := maxPrec,
    p := seqs ["coinductive", ident, univParams, many (bracketedBinder false), optional (seqs [":", term]),
      "where", many (structureField)] }
]

/-- The grammar of grammars, used by the `syntax` command.

| kind            | children |
|-----------------|----------|
| `stx.atom`      | str |
| `stx.cat`       | ident [":" prec] (`ident`, `num`, `str`, `colGt`, `colGe`, `noWs` are special) |
| `stx.group`     | "(" [stx+] ")" |
| `stx.sepBy`     | "sepBy" "(" [stx+] "," str ["," "allowTrailingSep"] ")" (also `sepBy1`) |
| `stx.withPosition` | "withPosition" "(" [stx+] ")" |
| `stx.many`, `stx.many1`, `stx.optional` (trailing) | stx "*" / "+" / "?" |
-/
def stxLeading : List LeadingParser := [
  { kind := "stx.atom", prec := maxPrec, p := str },
  { kind := "stx.cat", prec := maxPrec, p := seqs [ident, optional (seqs [noWs, ":", noWs, precedence])] },
  { kind := "stx.group", prec := maxPrec, p := seqs ["(", many1 (cat "stx" 0), ")"] },
  { kind := "stx.sepBy", prec := maxPrec,
    p := seqs [nonReserved "sepBy", noWs, "(", many1 (cat "stx" 0), ",", str,
      optional (seqs [",", nonReserved "allowTrailingSep"]), ")"] },
  { kind := "stx.sepBy1", prec := maxPrec,
    p := seqs [nonReserved "sepBy1", noWs, "(", many1 (cat "stx" 0), ",", str,
      optional (seqs [",", nonReserved "allowTrailingSep"]), ")"] },
  { kind := "stx.withPosition", prec := maxPrec,
    p := seqs [nonReserved "withPosition", noWs, "(", many1 (cat "stx" 0), ")"] }
]

def stxTrailing : List TrailingParser := [
  { kind := "stx.many", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, "*"] },
  { kind := "stx.many1", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, "+"] },
  { kind := "stx.optional", prec := maxPrec, lhsPrec := maxPrec, p := seqs [noWs, "?"] }
]

/-- Metaprogramming support for a category `c`: antiquotations `$x` inside it, and the
quotation `` `(c| …) `` as a term.

An antiquotation wins ties against the category's other rules (a user rule like
`syntax term : doSeq` would otherwise also read `$x` as a `doSeq`). To mean the
other reading, annotate the category: in a `doSeq`, `$x:term` is a term, because
it consumes more input than the `doSeq` antiquotation `$x`. -/
def addMetaParsers (t : ParserTables) (c : Name) : ParserTables :=
  let plain := seqs ["$", noWs, ident]
  let annotated := seqs ["$", noWs, ident, noWs, ":", noWs, nonReserved c]
  let t := t.addLeading c { kind := "antiquot", prec := maxPrec, priority := 1000, p := plain }
  let t := t.addLeading c { kind := "antiquot", prec := maxPrec, priority := 1000, p := annotated }
  let q : LeadingParser :=
    { kind := "quote." ++ c, prec := maxPrec,
      p := seqs ["`(", nonReserved c, "|", withoutPosition (cat c 0), ")"] }
  t.addLeading "term" q

/-- Macro commands.

| kind                   | children |
|------------------------|----------|
| `command.macroRules`   | "macro_rules" [alts] (each `| `(c| pattern) => `(c| template)`) |
| `command.notation`     | "notation" [":" prec] [items] "=>" term (items: str or ident [":" prec]) |
| `command.infix`        | ("infixl" / "infixr" / "infix") ":" num str "=>" term |
| `command.appUnexpander` | "app_unexpander" ident [alts] (11r: printing `ident`'s applications as notation) |
| `command.attrUnexpander` | "attribute" "[" "app_unexpander" ident "]" ident (11r) |
| `command.setOption`    | "set_option" ident (ident / num) (11r: `pp.notation`, `pp.all`) |
-/
def macroCommands : List LeadingParser := [
  { kind := "command.macroRules", prec := maxPrec, p := seqs ["macro_rules", many1 matchAlt] },
  { kind := "command.notation", prec := maxPrec,
    p := seqs ["notation", optional (seqs [noWs, ":", noWs, precedence]),
      many1 (node "notation.item" (orelse str (seqs [ident, optional (seqs [noWs, ":", noWs, precedence])]))),
      "=>", term] },
  { kind := "command.infix", prec := maxPrec,
    p := seqs [orelse "infixl" (orelse "infixr" "infix"), noWs, ":", noWs, num, str, "=>", term] },
  -- (11r) printing notation: unexpanders, and the `pp` options
  { kind := "command.appUnexpander", prec := maxPrec, p := seqs ["app_unexpander", ident, many1 matchAlt] },
  { kind := "command.attrUnexpander", prec := maxPrec,
    p := seqs ["attribute", "[", nonReserved "app_unexpander", ident, "]", ident] },
  { kind := "command.setOption", prec := maxPrec, p := seqs ["set_option", ident, orelse ident num] }
]

def tables : ParserTables :=
  let t : ParserTables := {}
  let t := ["term", "command", "stx", "level", "tactic"].foldl ParserTables.declareCategory t
  let t := levelLeading.foldl (·.addLeading "level" ·) t
  let t := levelTrailing.foldl (·.addTrailing "level" ·) t
  let t := termLeading.foldl (·.addLeading "term" ·) t
  let t := termTrailing.foldl (·.addTrailing "term" ·) t
  let t := commandLeading.foldl (·.addLeading "command" ·) t
  let t := stxLeading.foldl (·.addLeading "stx" ·) t
  let t := stxTrailing.foldl (·.addTrailing "stx" ·) t
  let t := macroCommands.foldl (·.addLeading "command" ·) t
  ["term", "command", "level", "tactic"].foldl addMetaParsers t

/-- The number of children a descriptor adds to its node, when that is fixed. -/
partial def arity? : ParserDescr → Option Nat
  | .atom _ | .nonReserved _ | .ident | .num | .str | .cat .. | .many _ | .many1 _ | .optional _
  | .sepBy .. | .sepBy1 .. | .node .. => some 1
  | .seq ps => ps.foldl (fun acc p => do pure ((← acc) + (← arity? p))) (some 0)
  | .orelse p q => do
    let a ← arity? p
    if (← arity? q) == a then some a else none
  | .withPosition p | .withoutPosition p => arity? p
  | .colGt | .colGe | .noWs | .checkPrec _ => some 0

/-- Every `node k p` inside a descriptor. -/
partial def nodesIn : ParserDescr → List (Name × ParserDescr)
  | .node k p => (k, p) :: nodesIn p
  | .seq ps => ps.toList.flatMap nodesIn
  | .many p | .many1 p | .optional p | .sepBy p .. | .sepBy1 p .. | .withPosition p | .withoutPosition p => nodesIn p
  | .orelse p q => nodesIn p ++ nodesIn q
  | _ => []

/-- The kinds whose `childNames` disagree with the grammar: a different number of
children, or a rule whose number of children isn't fixed. Empty when all is well (the
test group `parser: commands` checks that). -/
def childNamesMismatches : List String :=
  let rules := (termLeading ++ commandLeading).flatMap fun lp => (lp.kind, lp.p) :: nodesIn lp.p
  rules.filterMap fun (k, p) =>
    let names := childNames k
    if names.isEmpty then none
    else match arity? p with
      | some n => if n == names.length then none else
          some s!"{k}: the grammar produces {n} children, childNames lists {names.length}"
      | none => some s!"{k}: the number of children is not fixed"

end Wiz.Builtin
