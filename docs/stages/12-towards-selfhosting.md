# Stage 12: towards self-hosting

## 12a (part 1): compiled recursion

* **Direct recursion.** For a structurally recursive definition, the elaborator also
  produces the compiler's version (`Decl.impl`, not checked by the kernel): the same
  equations, with case analysis and the definition calling itself. Only the recursive
  calls the program makes are computed, instead of every induction hypothesis.
* **Case analysis.** `T.casesOn`'s method no longer threads the hypotheses through, and
  erasure applies such a method directly instead of computing them.
* **Stack.** Compiled programs run on a thread with a 1 GB stack (`$WIZ_STACK_MB`), so
  deep non-tail recursion (`sumTo 100000`) works.

## 12a (part 2): a standard library for systems code

`lib/Std.wiz`: `Array A`, native text `Str` (UTF-8, with slicing and comparison), and
`StrMap V` (hash maps from text), all functional but **updated in place when unique**
(as Perceus reuse does for constructors). Plus `IO.writeFile`, and `do let x := e; …`.
Foreign functions can now take erased arguments (`{A : Type}`) and pass Wiz values as
they are.

## 12b: the lexer in Wiz

`selfhost/Lex.wiz` reads tokens at an offset of the input (an array of code points),
like `Wiz/Parser/Token.lean`: whitespace and nested comments, dotted identifiers,
numbers, string literals with escapes, and the longest symbol of the token table. The
test lexes a program with the full built-in token table and compares with the Lean lexer.

| #    | Where              | What                                          |
|------|--------------------|-----------------------------------------------|
| 12.1 | `selfhost/Lex.wiz` | `longest`: the longest token at an offset     |

## 12c: flat constructor objects

A data value is one object `⟨tag f₁ … fₙ⟩` at runtime instead of a tag and a chain of
pairs (lists stay linked lists; `Array` stays a vector). Erasure builds constructors
directly and resolves case analysis to field reads (**views**); generic code (`ind`
with hypotheses) converts with `pack`/`unpack`, which walk the description. Numbers stay
native. Redexes become `let`s, and scalars get no reference counting.

## 12d: the parser in Wiz

`selfhost/Parse.wiz` interprets the grammar descriptors (`ParserDescr`) like
`Wiz/Parser/Interp.lean`: Pratt parsing of syntax categories, the longest alternative
wins, and category parses are memoised (packrat) in a `StrMap`. The test turns
`Builtin.tables` into Wiz data and compares the trees (and errors) with the Lean parser.

| #    | Where                | What                                                   |
|------|----------------------|--------------------------------------------------------|
| 12.2 | `selfhost/Parse.wiz` | `runDescr`: `many`, `many1`, `optional`, `sepBy(1)`    |
| 12.3 | `selfhost/Parse.wiz` | `trailingLoop`, `manyLoop`, `sepLoop`                  |

Along the way: induction on a big numeral is lazy in the kernel (`Val.lazyInd`, glued,
so fuel arguments like `100000000` cost nothing), constructor fields no longer shadow
variables in `match` alternatives, and reuse only recycles constructor cells.
`WIZ_LEAKS=1` lists the objects a compiled program leaks (`WIZ_WATCH=<address>` traces
one).
