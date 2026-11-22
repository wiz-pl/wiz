/-
# `bpf-core/1`: the serialised typed core (P0 fixture format)

`Wiz.Compiler.IR` is untyped, so the eBPF backend cannot read it (§1.2). Until the
elaborator → `STm` restriction pass is wired (that needs a build slot), P0's CLI consumes
the typed core directly. The format is a small S-expression, versioned in its first atom:

```
(bpf-core/1
  (ret (enum 5))
  (decl "flow" ((ctx xdp)) (enum 5)
    (ret (switch-option (enum 5) ... )))
  ...)
```

Every term carries its `Ty`, exactly as `BpfCore` does; the reader is therefore a syntax
check, and `Bpf.Check` is the semantic one. The manifest (`bpf.toml`) supplies the program
metadata and maps, because those are the loader's declarations, not the IR's.

This is deliberately **not** the public `bpf-core/1` specification of §9.4: the schema
name is reserved there for the serialised elaborated term, and this file is a P0 stand-in
with the same version string. P3 replaces the reader with the real serialiser.
-/
import Wiz.Compiler.Bpf.Core

namespace Wiz.Compiler.Bpf.Sexp

open Wiz.Compiler.Bpf

/-! ## Tokens -/

inductive Tok where
  | lp
  | rp
  | atom (s : String)
  | str (s : String)
  deriving Repr, BEq, Inhabited

partial def readString (cs : List Char) (buf : List Char) : Except String (String × List Char) :=
  match cs with
  | [] => .error "bpf-core: unterminated string"
  | '"' :: rest => pure (String.mk buf.reverse, rest)
  | '\\' :: '"' :: rest => readString rest ('"' :: buf)
  | '\\' :: '\\' :: rest => readString rest ('\\' :: buf)
  | c :: rest => readString rest (c :: buf)

partial def tokenize (cs : List Char) (acc : Array Tok) : Except String (Array Tok) :=
  match cs with
  | [] => pure acc
  | c :: rest =>
    if c.isWhitespace then tokenize rest acc
    else if c == ';' then tokenize (rest.dropWhile fun c => c != '\n') acc
    else if c == '(' then tokenize rest (acc.push .lp)
    else if c == ')' then tokenize rest (acc.push .rp)
    else if c == '"' then do
      let (s, rest) ← readString rest []
      tokenize rest (acc.push (.str s))
    else
      let (tok, rest) := (c :: rest).span fun c =>
        !c.isWhitespace && c != '(' && c != ')' && c != ';'
      tokenize rest (acc.push (.atom (String.mk tok)))

/-! ## A cursor -/

structure P where
  ts : Array Tok
  i : Nat

def P.next (p : P) : Except String (Tok × P) :=
  match p.ts[p.i]? with
  | some t => pure (t, { p with i := p.i + 1 })
  | none => .error "bpf-core: unexpected end of input"

def P.peek (p : P) : Except String Tok :=
  match p.ts[p.i]? with
  | some t => pure t
  | none => .error "bpf-core: unexpected end of input"

def P.expectLp (p : P) : Except String P := do
  let (t, p) ← p.next
  match t with
  | .lp => pure p
  | _ => .error "bpf-core: expected `(`"

def P.expectRp (p : P) : Except String P := do
  let (t, p) ← p.next
  match t with
  | .rp => pure p
  | _ => .error "bpf-core: expected `)`"

def P.atom (p : P) : Except String (String × P) := do
  let (t, p) ← p.next
  match t with
  | .atom s => pure (s, p)
  | _ => .error "bpf-core: expected a symbol"

def P.str (p : P) : Except String (String × P) := do
  let (t, p) ← p.next
  match t with
  | .str s => pure (s, p)
  | _ => .error "bpf-core: expected a string"

def P.nat (p : P) : Except String (Nat × P) := do
  let (s, p) ← p.atom
  match s.toNat? with
  | some n => pure (n, p)
  | none => .error s!"bpf-core: expected a number, got `{s}`"

/-! ## Types -/

def parseMapKind (s : String) : Except String MapKind :=
  match s with
  | "hash" => pure .hash
  | "array" => pure .array
  | "percpu_array" => pure .percpuArray
  | "lru_hash" => pure .lruHash
  | _ => .error s!"bpf-core: unknown map kind `{s}`"

mutual

partial def parseTy (p : P) : Except String (Ty × P) := do
  let (t, p) ← p.next
  match t with
  | .atom "unit" => pure (.unit, p)
  | .atom "bool" => pure (.bool, p)
  | .atom "u8" => pure (.u8, p)
  | .atom "u16" => pure (.u16, p)
  | .atom "u32" => pure (.u32, p)
  | .atom "u64" => pure (.u64, p)
  | .atom "i8" => pure (.i8, p)
  | .atom "i16" => pure (.i16, p)
  | .atom "i32" => pure (.i32, p)
  | .atom "i64" => pure (.i64, p)
  | .atom "packet" => pure (.packet, p)
  | .atom other => .error s!"bpf-core: unknown type `{other}`"
  | .str _ => .error "bpf-core: a type is a symbol, not a string"
  | .rp => .error "bpf-core: unexpected `)` in a type"
  | .lp =>
    let (head, p) ← p.atom
    match head with
    | "enum" =>
      let (n, p) ← p.nat
      let p ← p.expectRp
      pure (.enum n, p)
    | "option" =>
      let (t, p) ← parseTy p
      let p ← p.expectRp
      pure (.option t, p)
    | "ctx" =>
      let (k, p) ← p.atom
      let k ← match k with
        | "xdp" => pure .xdp
        | "tc" => pure .tc
        | other => .error s!"bpf-core: unknown context `{other}`"
      let p ← p.expectRp
      pure (.ctx k, p)
    | "struct" =>
      let p ← p.expectLp
      let (fields, p) ← parseTys p
      let p ← p.expectRp
      let p ← p.expectRp
      pure (.struct fields.toArray, p)
    | "map" =>
      let (k, p) ← parseTy p
      let (v, p) ← parseTy p
      let (kind, p) ← p.atom
      let kind ← parseMapKind kind
      let p ← p.expectRp
      pure (.map k v kind, p)
    | other => .error s!"bpf-core: unknown type constructor `{other}`"

partial def parseTys (p : P) : Except String (List Ty × P) := do
  let t ← p.peek
  match t with
  | .rp => pure ([], p)
  | _ => do
    let (ty, p) ← parseTy p
    let (rest, p) ← parseTys p
    pure (ty :: rest, p)

end

/-! ## Terms -/

def parseBinOp (s : String) : Except String BinOp :=
  match s with
  | "add" => pure .add
  | "sub" => pure .sub
  | "mul" => pure .mul
  | "div" => pure .div
  | "mod" => pure .mod
  | "land" => pure .land
  | "lor" => pure .lor
  | "xor" => pure .xor
  | "shl" => pure .shl
  | "shr" => pure .shr
  | _ => .error s!"bpf-core: unknown binary operator `{s}`"

def parseCmpOp (s : String) : Except String CmpOp :=
  match s with
  | "eq" => pure .eq
  | "ne" => pure .ne
  | "lt" => pure .lt
  | "le" => pure .le
  | _ => .error s!"bpf-core: unknown comparison `{s}`"

mutual

/-- A term, starting with its `(`. -/
partial def parseTm (p : P) : Except String (Tm × P) := do
  let (t, p) ← p.next
  match t with
  | .lp => parseTmForm p
  | _ => .error "bpf-core: a term is a parenthesised form"

/-- Terms until the closing `)`, which is left to the caller. -/
partial def parseTms (p : P) : Except String (List Tm × P) := do
  let t ← p.peek
  match t with
  | .rp => pure ([], p)
  | _ => do
    let (tm, p) ← parseTm p
    let (rest, p) ← parseTms p
    pure (tm :: rest, p)

partial def parseTmForm (p : P) : Except String (Tm × P) := do
  let (head, p) ← p.atom
  match head with
  | "at" =>
    let (file, p) ← p.str
    let (line, p) ← p.nat
    let (col, p) ← p.nat
    let (tm, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk { file, line, col } tm.node, p)
  | "var" =>
    let (ty, p) ← parseTy p
    let (x, p) ← p.nat
    let p ← p.expectRp
    pure (.mk {} (.var ty x), p)
  | "lit" =>
    let (ty, p) ← parseTy p
    let (v, p) ← p.nat
    let p ← p.expectRp
    pure (.mk {} (.lit ty v), p)
  | "bin" =>
    let (ty, p) ← parseTy p
    let (op, p) ← p.atom
    let op ← parseBinOp op
    let (a, p) ← parseTm p
    let (b, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.bin ty op a b), p)
  | "cmp" =>
    let (op, p) ← p.atom
    let op ← parseCmpOp op
    let (a, p) ← parseTm p
    let (b, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.cmp op a b), p)
  | "ite" =>
    let (ty, p) ← parseTy p
    let (c, p) ← parseTm p
    let (a, p) ← parseTm p
    let (b, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.ite ty c a b), p)
  | "let" =>
    let (ty, p) ← parseTy p
    let (x, p) ← p.nat
    let (v, p) ← parseTm p
    let (body, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.letE ty x v body), p)
  | "proj" =>
    let (ty, p) ← parseTy p
    let (i, p) ← p.nat
    let (s, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.proj ty i s), p)
  | "mk-struct" =>
    let (ty, p) ← parseTy p
    let p ← p.expectLp
    let (fields, p) ← parseTms p
    let p ← p.expectRp
    let p ← p.expectRp
    pure (.mk {} (.mkStruct ty fields.toArray), p)
  | "mk-some" =>
    let (ty, p) ← parseTy p
    let (v, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.mkSome ty v), p)
  | "mk-none" =>
    let (ty, p) ← parseTy p
    let p ← p.expectRp
    pure (.mk {} (.mkNone ty), p)
  | "switch-option" =>
    let (ty, p) ← parseTy p
    let (s, p) ← parseTm p
    let (onNone, p) ← parseTm p
    let (x, p) ← p.nat
    let (onSome, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.switchOption ty s onNone x onSome), p)
  | "switch-tag" =>
    let (ty, p) ← parseTy p
    let (s, p) ← parseTm p
    let p ← p.expectLp
    let (alts, p) ← parseTms p
    let p ← p.expectRp
    let p ← p.expectRp
    pure (.mk {} (.switchTag ty s alts.toArray), p)
  | "repeat" =>
    let (ty, p) ← parseTy p
    let (bound, p) ← p.nat
    let (init, p) ← parseTm p
    let (step, p) ← p.str
    let p ← p.expectRp
    pure (.mk {} (.repeat ty bound init step), p)
  | "pkt-load" =>
    let (ty, p) ← parseTy p
    let (w, p) ← p.nat
    let (be, p) ← p.atom
    let be ← match be with
      | "be" => pure true
      | "le" => pure false
      | other => .error s!"bpf-core: a packet load is `be` or `le`, not `{other}`"
    let (ptr, p) ← parseTm p
    let (off, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.pktLoad ty w be ptr off), p)
  | "ctx-packet" =>
    let (c, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.ctxPacket c), p)
  | "ctx-ifindex" =>
    let (c, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.ctxIfindex c), p)
  | "ctx-rx-queue" =>
    let (c, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.ctxRxQueue c), p)
  | "map-lookup" =>
    let (ty, p) ← parseTy p
    let (m, p) ← p.str
    let (k, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.mapLookup ty m k), p)
  | "map-update" =>
    let (ty, p) ← parseTy p
    let (m, p) ← p.str
    let (k, p) ← parseTm p
    let (v, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.mapUpdate ty m k v), p)
  | "map-delete" =>
    let (ty, p) ← parseTy p
    let (m, p) ← p.str
    let (k, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.mapDelete ty m k), p)
  | "map-add" =>
    let (ty, p) ← parseTy p
    let (m, p) ← p.str
    let (k, p) ← parseTm p
    let (n, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.mapAdd ty m k n), p)
  | "cast" =>
    let (ty, p) ← parseTy p
    let (src, p) ← parseTy p
    let (v, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.cast ty src v), p)
  | "call" =>
    let (ty, p) ← parseTy p
    let (f, p) ← p.str
    let p ← p.expectLp
    let (args, p) ← parseTms p
    let p ← p.expectRp
    let p ← p.expectRp
    pure (.mk {} (.call ty f args.toArray), p)
  | "helper" =>
    let (ty, p) ← parseTy p
    let (h, p) ← p.str
    let some helper := Helpers.find? h |
      .error s!"bpf-core: `{h}` is not in the P0 helper table"
    let p ← p.expectLp
    let (args, p) ← parseTms p
    let p ← p.expectRp
    let p ← p.expectRp
    pure (.mk {} (.helper ty helper args.toArray), p)
  | "ret" =>
    let (v, p) ← parseTm p
    let p ← p.expectRp
    pure (.mk {} (.ret v), p)
  | other => .error s!"bpf-core: unknown term form `{other}`"

end

/-! ## Files -/

/-- A `bpf-core/1` file: the program's result type and its definitions. The manifest
supplies everything else (name, section, licence, version, maps). -/
structure CoreFile where
  ret : Ty
  decls : Array Decl

def parseRet (p : P) : Except String (Ty × P) := do
  let p ← p.expectLp
  let (head, p) ← p.atom
  unless head == "ret" do
    .error s!"bpf-core: expected `(ret T)`, got `({head} …)`"
  let (ty, p) ← parseTy p
  let p ← p.expectRp
  pure (ty, p)

def parseDecl (p : P) : Except String (Decl × P) := do
  let p ← p.expectLp
  let (head, p) ← p.atom
  unless head == "decl" do
    .error s!"bpf-core: expected `(decl …)`, got `({head} …)`"
  let (name, p) ← p.str
  let p ← p.expectLp
  let (params, p) ← parseTys p
  let p ← p.expectRp
  let (ret, p) ← parseTy p
  let (body, p) ← parseTm p
  let p ← p.expectRp
  pure ({ name, params := params.toArray, ret, body }, p)

partial def parseDecls (p : P) (acc : Array Decl) : Except String (Array Decl × P) := do
  let t ← p.peek
  match t with
  | .rp => pure (acc, p)
  | .lp =>
    let (d, p) ← parseDecl p
    parseDecls p (acc.push d)
  | _ => .error "bpf-core: expected a declaration or the closing `)`"

/-- Read a `bpf-core/1` file. A schema other than `bpf-core/1` is refused by name, not
parsed as a malformed v1 (§9.4). -/
def parseCore (input : String) : Except String CoreFile := do
  let ts ← tokenize input.toList #[]
  let p : P := { ts, i := 0 }
  let p ← p.expectLp
  let (head, p) ← p.atom
  unless head == "bpf-core/1" do
    .error s!"bpf-core: this toolchain reads `bpf-core/1`, not `{head}`"
  let (ret, p) ← parseRet p
  let (decls, p) ← parseDecls p #[]
  let p ← p.expectRp
  if p.i != p.ts.size then .error "bpf-core: trailing input after the program"
  pure { ret, decls }

end Wiz.Compiler.Bpf.Sexp
