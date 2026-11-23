import Wiz.Compiler.IR

/-!
# `wiz-ir/1`, the serialized IR document

`Wiz.Compiler.IR` is the backend's input: an untyped, first-order language in A-normal
form. This module writes it as a versioned text document so that a backend (or an IR
pass) can be a package that reads a file instead of a Lean module linked into the
compiler. The schema is specified in `wiz-notes/wiz-ir.md`; `lib/Ir.wiz` is the
independent pure-Wiz reader and printer, and `Tests/Groups/Ir.lean` checks the two
against each other.

The document is deliberately small and canonical:

```
(wiz-ir/1
  (decl "twice" (params 0 1) (borrow 0 0) (dup 0 (vdecl 2 (ap 0 (1)) (vdecl 3 (ap 0 (2)) (ret 3)))))
)
```

One declaration per line, one space between fields, LF line endings and one final
newline. Names and primitive keys are quoted strings (a Wiz name is not an atom: it may
contain punctuation); numbers, variables, join ids and borrow bits are atoms. A reader
that sees another `wiz-ir/N` major refuses the document (the rule is in the note).

There is no Lean parser here on purpose: the emitter is the producer, and the
independent parser is the Wiz module. That keeps the round-trip test honest (a parser
written against the emitter's own printer would prove much less).
-/

namespace Wiz.IRDoc

open Wiz.IR

/-- The generic S-expression tree the document is made of. It is an implementation
detail of the printer: a consumer reads the typed forms documented in the note. -/
inductive Sexp where
  | atom (s : String)
  | str (s : String)
  | list (xs : List Sexp)
  deriving Repr, BEq, Inhabited

namespace Sexp

/-- A string as a `wiz-ir/1` string literal. The escapes are the ones the Wiz reader
accepts (and the only ones it emits): backslash, quote, newline, tab and carriage
return. -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\t' => "\\t"
    | '\r' => "\\r"
    | c => c.toString) ++ "\""

/-- The canonical text of one form: no layout, one space between children. The
document's line breaks are added by `render`, not here. -/
def render : Sexp → String
  | .atom s => s
  | .str s => quote s
  | .list xs => "(" ++ " ".intercalate (xs.map render) ++ ")"

end Sexp

private def varS (x : Var) : Sexp := .atom (toString x)
private def varsS (xs : Array Var) : Sexp := .list (xs.toList.map varS)
private def natS (n : Nat) : Sexp := .atom (toString n)
private def bitS (b : Bool) : Sexp := .atom (if b then "1" else "0")

/-- An expression form. `prim` carries `PrimOp.key`: the document does not name Lean
constructors, so a package backend can implement its own primitive table. An `extern`
key is the whole `extern:` string (a foreign function is a program registration). -/
def exprS : Expr → Sexp
  | .erased => .list [.atom "erased"]
  | .lit n => .list [.atom "lit", natS n]
  | .ctor t as => .list [.atom "ctor", natS t, varsS as]
  | .proj i x => .list [.atom "proj", natS i, varS x]
  | .fap f as => .list [.atom "fap", .str f, varsS as]
  | .pap f as => .list [.atom "pap", .str f, varsS as]
  | .ap f as => .list [.atom "ap", varS f, varsS as]
  | .prim op as => .list [.atom "prim", .str op.key, varsS as]
  | .reset x => .list [.atom "reset", varS x]
  | .reuse tok t as => .list [.atom "reuse", varS tok, natS t, varsS as]

/-- A body form. The trailing `body` of `vdecl`/`dup`/`drop` is the continuation, as in
`Wiz.IR.Body`; `case` alternatives are in tag order (index 0 first). -/
partial def bodyS : Body → Sexp
  | .vdecl x e b => .list [.atom "vdecl", varS x, exprS e, bodyS b]
  | .case x alts => .list (.atom "case" :: varS x :: alts.toList.map bodyS)
  | .ret x => .list [.atom "ret", varS x]
  | .jdecl j ps body k =>
    .list [.atom "jdecl", varS j, varsS ps, bodyS body, bodyS k]
  | .jmp j as => .list [.atom "jmp", varS j, varsS as]
  | .dup x b => .list [.atom "dup", varS x, bodyS b]
  | .drop x b => .list [.atom "drop", varS x, bodyS b]
  | .unreachable => .list [.atom "unreachable"]

/-- The borrow array, padded to one bit per parameter: a document says `0`/`1` for every
parameter rather than relying on `Decl.borrow`'s "short means owned" default. -/
def borrowBits (d : Decl) : Array Bool :=
  d.params.mapIdx fun i _ => d.borrow[i]?.getD false

/-- One declaration. `borrow` has exactly one bit per parameter in the canonical form;
the reader refuses a document whose lengths disagree. -/
def declS (d : Decl) : Sexp :=
  .list [.atom "decl", .str d.name,
    .list (.atom "params" :: d.params.toList.map varS),
    .list (.atom "borrow" :: (borrowBits d).toList.map bitS),
    bodyS d.body]

/-- The canonical text of one declaration, without the two-space indent or newline. -/
def renderDecl (d : Decl) : String := Sexp.render (declS d)

/-- A complete `wiz-ir/1` document: a header, one declaration per line, a closing
parenthesis and one final newline. -/
def render (decls : Array Decl) : String :=
  let lines := decls.toList.map fun d => "  " ++ renderDecl d
  "(wiz-ir/1\n" ++ String.join (lines.map (· ++ "\n")) ++ ")\n"

/-! ### The one pass: identity elimination

The compiler's `Inline.lean` runs on `ETerm`, before lowering: its bodies are de Bruijn
terms with lambdas, so an IR-document consumer cannot reproduce it. `wiz-ir/1` therefore
defines one deliberately narrow IR-level Inline slice: a call of a definition whose
parameters are one variable and whose body is `ret` of that variable is the argument
itself. This is ownership-neutral (the call consumed its argument; the uses now read it
directly, and any `dup`/`drop` already in the body is substituted too), and it is
implemented identically in `lib/Ir.wiz`. A faithful IR inline needs the RC/borrow
analysis that this pass deliberately avoids; §"What remains" in the note says so. -/

/-- Is `d` the one-parameter identity function? -/
def isIdentity (d : Decl) : Bool :=
  match d.params.toList, d.body with
  | [p], .ret x => p == x
  | _, _ => false

/-- Is `f` declared as a one-parameter identity in `decls`? -/
def identityName (decls : Array Decl) (f : Name) : Bool :=
  decls.any fun d => d.name == f && isIdentity d

/-- Replace variable `x` by variable `y` in an expression. -/
def substExpr (x y : Var) : Expr → Expr
  | .erased => .erased
  | .lit n => .lit n
  | .ctor t as => .ctor t (as.map fun z => if z == x then y else z)
  | .proj i z => .proj i (if z == x then y else z)
  | .fap f as => .fap f (as.map fun z => if z == x then y else z)
  | .pap f as => .pap f (as.map fun z => if z == x then y else z)
  | .ap f as => .ap (if f == x then y else f) (as.map fun z => if z == x then y else z)
  | .prim op as => .prim op (as.map fun z => if z == x then y else z)
  | .reset z => .reset (if z == x then y else z)
  | .reuse tok t as =>
    .reuse (if tok == x then y else tok) t (as.map fun z => if z == x then y else z)

/-- Replace variable `x` by `y` in a body. Variables are globally unique in lowered IR,
so a binder named `x` shadows nothing that was not already out of scope; the function
still stops at it rather than substituting under a rebinding. -/
partial def substBody (x y : Var) : Body → Body
  | .vdecl z e b =>
    if z == x then .vdecl z e b
    else .vdecl z (substExpr x y e) (substBody x y b)
  | .case z alts => .case (if z == x then y else z) (alts.map (substBody x y))
  | .ret z => .ret (if z == x then y else z)
  | .jdecl j ps body k =>
    let body := if ps.contains x then body else substBody x y body
    .jdecl j ps body (substBody x y k)
  | .jmp j as => .jmp j (as.map fun z => if z == x then y else z)
  -- `dup`/`drop` are not binders: both name the variable the operation reads and then
  -- continue in the same scope, so the substitution reaches their argument and body.
  | .dup z b => .dup (if z == x then y else z) (substBody x y b)
  | .drop z b => .drop (if z == x then y else z) (substBody x y b)
  | .unreachable => .unreachable

/-- Inline identity calls in a body: `let x := f a; b` with `f` the identity is
`b[x := a]`, applied recursively. Other expressions are unchanged. -/
partial def inlineBody (decls : Array Decl) : Body → Body
  | .vdecl x (.fap f args) b =>
    match args.toList with
    | [a] =>
      if identityName decls f && a != x then inlineBody decls (substBody x a b)
      else .vdecl x (.fap f args) (inlineBody decls b)
    | _ => .vdecl x (.fap f args) (inlineBody decls b)
  | .vdecl x e b => .vdecl x e (inlineBody decls b)
  | .case x alts => .case x (alts.map (inlineBody decls))
  | .ret x => .ret x
  | .jdecl j ps body k => .jdecl j ps (inlineBody decls body) (inlineBody decls k)
  | .jmp j as => .jmp j as
  | .dup x b => .dup x (inlineBody decls b)
  | .drop x b => .drop x (inlineBody decls b)
  | .unreachable => .unreachable

/-- The IR-level Inline pass: eliminate calls of one-parameter identity definitions.
The declarations themselves are kept (a backend may still need an exported one). -/
def inlineIdentity (decls : Array Decl) : Array Decl :=
  decls.map fun d => { d with body := inlineBody decls d.body }

end Wiz.IRDoc
