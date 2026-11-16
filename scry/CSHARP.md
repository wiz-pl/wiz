# scry C# frontend

Status: **design + first slice, parsing on tree-sitter-c-sharp** (2026-11-16;
the working copy of this note is `wiz-notes/scry-csharp.md`). The user chose option B
of §1 on 2026-11-16: the hand-written parser of the first draft is gone, and
tree-sitter-c-sharp v0.23.5 (fetched by Nix, `.#tree-sitter-c-sharp`) parses C# through
the same shim as C. The branch is based on `agent/scry-integrate` (PR #376), because
the pieces the frontend plugs into exist only there: `Scry.Cst` (the read-only CST view
the C lowering walks), `Scry.Warning`/`Scry.TU`, `Wil.Span` origins on every
statement, and the rule-pack taint engine (`Scry.RuleTaint`, `Scry.Interproc`,
`Scry.analyze`). The PR declares `Depends-on: #376`.

Design context: `code-analysis-design.md` §4.8 (C# second, decided 2026-11-12, 3–4 wk),
§4.3 (Wil), `scry-c2wil.md` (the C lowering this mirrors), `scry-taint.md` (the engine).

## 1. Parsing approach

Three candidates. None may need the network at analysis time.

| | A. hand-written RD in Wiz | B. tree-sitter-c-sharp via the shim | C. Roslyn → JSON |
|---|---|---|---|
| what runs | a Wiz lexer + recursive-descent parser that emits a `Scry.Cst` | the vendored grammar's `parser.c`/`scanner.c` through `native/ts_shim.c`, as for C | a small .NET tool (`dotnet scry-roslyn.dll`) that writes the syntax tree (and, optionally, bound symbols) as JSON; scry ingests it |
| coverage | only what we write; every construct is work | the full language (C# 12/13), error recovery, incremental reparse | exact: it is the compiler |
| name/type resolution | ours (CHA, usings, a small BCL table) | ours | Roslyn's `SemanticModel` gives exact symbols, overloads, generic instantiations, nullability flow |
| cost to ship | no native code, no vendoring; runs in the Lean test interpreter (`#eval`) and compiled | vendor tree-sitter-c-sharp: `parser.c` is tens of MB (the design's §4.1 compile-time warning), pinned grail git dep; a network fetch to obtain it once, and a big `link_c` compile in CI | a .NET SDK on every analysing machine (present on this host, not in CI/Nix); a second implementation language; a trusted external component on the findings path |
| trust | all in Wiz; the lowering's `Scry.Cst` is the same interface as C's | the shim is already trusted for C; one more grammar | Roslyn is a big trusted base, and the JSON schema is ours to keep in sync |
| speed | interpreted lists today (fine for fixtures, slow for a repo) | C speed, threads | fast, but process start + JSON parse per project |

**Decision (user, 2026-11-16): B.** The first draft shipped A (a hand-written lexer and
recursive-descent parser in Wiz whose rows used tree-sitter-c-sharp's vocabulary, behind
`Scry.Cst`); it was replaced by B in the same PR:

* tree-sitter-c-sharp is the upstream generated `parser.c` + `scanner.c` of tag v0.23.5
  (`native/README.md`: licence, commit, hash). Generated code is not committed, so
  `flake.nix` fetches it (`fetchFromGitHub`, pinned commit and hash) and builds it with
  the shim and the vendored runtime as `.#scry-native` (pushed to Cachix). A native scry
  build compiles it through the uncommitted out-link `native/tree-sitter-c-sharp`
  (`nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp`). `parser.c` is
  29.7 MB and compiles at `-O2` in about 1.5 s; it is not regenerated.
* `ts_shim.c`'s `scry_parse` takes `"c_sharp"`; `Scry.Native.parseFile` picks the
  language by extension, so `scry-cst FILE.cs` spills a C# store.
* `Scry.CsCst` is the adapter: the store's view as the `Scry.Cst` the lowering reads,
  with the few fields the grammar leaves unnamed normalised (its module doc has the
  table). The lowering itself did not change: `lower/basic.wil` is byte-identical
  between the two parsers, and the four taint fixtures give the same findings.
* As for C, the Lean tests read checked-in spills (`*.cst` next to each `.cs`), so they
  need no native build; the compiled CLI parses directly.
* The hand-written parser is **not** kept as a fallback: nothing needs it (the
  interpreter reads spills, the compiled tools have the shim), and keeping two parsers
  in sync would be its own cost. It is in this PR's history (`12f29f45`) if a
  dependency-free parser is ever wanted again.
* C (Roslyn) remains an option for exact name resolution later (offline symbol tables),
  not for parsing.

## 2. The first subset

Lexer: identifiers (incl. `@ident`), all keywords, integer/real/char literals,
`"…"` with escapes, verbatim `@"…"`, interpolated `$"…{e}…"` (holes re-lexed with
their offsets), `//` and `/* */` comments, preprocessor lines (`#nullable`, `#region`,
… skipped; `#if` is not evaluated in this slice: a warning), all operators and
punctuation including `?.`, `??`, `??=`, `=>`, `::`.

Parser (one node per construct, tree-sitter-c-sharp names):

* `compilation_unit`: `using_directive`, `namespace_declaration` (block and
  file-scoped), `class_declaration`, `struct_declaration`, `interface_declaration`,
  `record_declaration` (positional parameters as properties — later).
* members: `field_declaration`, `method_declaration` (block or `=>` body),
  `constructor_declaration`, `property_declaration` (auto `{ get; set; }`, accessor
  bodies, `=>`), modifiers and attributes (attributes are skipped as `attribute_list`).
* types: `predefined_type`, `identifier`, `qualified_name`, `generic_name` +
  `type_argument_list`, `array_type`, `nullable_type`, `implicit_type` (`var`).
* statements: `block`, `local_declaration_statement`, `expression_statement`,
  `if_statement`, `while_statement`, `do_statement`, `for_statement`,
  `foreach_statement`, `return_statement`, `break_statement`, `continue_statement`,
  `throw_statement`, `try_statement` + `catch_clause` + `finally_clause`,
  `using_statement` (block form and `using var`), `empty_statement`.
* expressions: precedence climbing over assignment (incl. compound, `??=`),
  `conditional_expression`, `??`, `||`, `&&`, bitwise, equality, relational with `is`/
  `as`, shifts, additive, multiplicative, `prefix_unary_expression`, `cast_expression`
  (predefined types always, `(Name)` when followed by an operand start),
  `postfix_unary_expression` (`++`, `--`, `!`), `member_access_expression`,
  `conditional_access_expression` (`?.`), `invocation_expression` (+ generic method
  calls `M<T>(…)` by a backtracking type-argument probe), `element_access_expression`,
  `object_creation_expression` (+ object initialiser), `array_creation_expression`,
  `implicit_array_creation_expression`, `parenthesized_expression`, literals,
  `this_expression`, `base_expression`, `typeof_expression`, `default_expression`,
  `lambda_expression` (parsed, lowered as an opaque value in slice 1).

Out of the first subset (parse error or `ERROR` node + warning, never a guess):
LINQ query syntax, `switch` expressions and patterns beyond `is T x`, `async`/`await`
(parsed as a prefix later), iterators (`yield`), local functions, tuples and
deconstruction, `ref`/`out` arguments (parsed, lowered as havoc of the target),
`unsafe`/pointers, events and delegates, operator overloading, attributes' semantics.

## 3. C# semantics on Wil

| C# | Wil |
|---|---|
| a method `N.C.M` | `Wil.Func` named `N.C.M` (namespace + class + method). Overloads: the first keeps the name, later ones get `#k` (arity-qualified resolution is a later slice). Instance methods take `this` as parameter 0. A constructor is `N.C..ctor`, takes `this` and returns it. |
| value types `int`/`long`/`short`/`byte`/`char`/`bool`/enums | `Wil.Ty.int w s` (32/64/16/u8/u16/u1), C# wrap-around semantics in `unchecked` (Wil's default) |
| reference types (`string`, classes, arrays, `object`, interfaces, generic parameters) | `Wil.Ty.ptr Wil.Ty.dyn`: a reference is a pointer to a heap block. **Generics are erased**: `List<T>` is the type `List` with `dyn` elements. `struct`s are values — slice 1 treats them like classes (a heap block); stack-slot structs are later. |
| `new C(a…)` for a class the unit defines | `alloc (fields)` then a direct call `N.C..ctor(obj, a…)`; a field read/write is `gep obj k` + `load`/`store` (field index `k` in declaration order), so points-to and memory taint see objects |
| `new T(a…)` for an external type | a direct call `T..ctor(a…)` whose result is the object; the rule engine's "a call's result is tainted by any tainted input" carries taint from constructor arguments into the object (this is what makes `new SqlCommand(query, conn)` tainted) |
| `x.M(a…)` on an external receiver | `T.M(x, a…)`: **the receiver is argument 0**, so a rule names `sink System.Data.SqlClient.SqlCommand.ExecuteReader arg 0`. `T` is the receiver's static type when known (declared local/parameter/field type, `new T`), else `?`; a static call `T.M(a…)` has no receiver |
| properties `x.P` / `x.P = v` on external types | calls `T.get_P(x)` / `T.set_P(x, v)` (the CLR names). On a unit's own class, an auto-property is a field. |
| `a[i]` on an array | `gepVar a i 1` + `load`/`store` (bounds: see below); on another type it is `T.get_Item(a, i)` / `T.set_Item(a, i, v)` |
| string literals | `globalRef "$str:<text>"` (an immutable object, never tainted) |
| `s1 + s2` (either side `string`), `$"…{e}…"`, `string.Format`, `string.Concat` | a call `System.String.Concat(parts…)`: taint flows from any part to the result |
| `null` | `cst nul`; `x?.M()`, `??`: a branch on `x == null` |
| exceptions | `throw e` goes to the innermost `catch` dispatch block, else returns (`ret none`, an exceptional exit). Inside `try`, every statement boundary may branch (on a havoc'd bit) to the catch dispatch, so a definition made in the `try` reaches the handler; `catch (T e)` binds `e` to a havoc'd reference; `finally` is lowered on the normal and the catch paths (duplicated blocks). `using` is `try { … } finally { x.Dispose() }`. |
| `if`/`while`/`do`/`for`/`foreach`/`break`/`continue`/`return` | as in C; `foreach (var x in e)` is `e.GetEnumerator()` + a loop on `MoveNext()`/`get_Current()` calls, so taint flows from the collection to `x` |
| lambdas, delegates | slice 1: an opaque `fnptr "$lambda:<n>"` value + warning; later each lambda body becomes its own `Wil.Func` with captured locals as parameters |

### Nullability (CWE-476 → `NullReferenceException`)

* Facts: a `?`-annotated reference type (`string? s`) is *maybe-null*; under `#nullable
  enable` an unannotated one is *non-null by contract*; `null` literals, `as`, `?.`,
  `FirstOrDefault()`-style models produce maybe-null; `!` (null-forgiving) is an
  assertion the analysis records but trusts.
* The check: a dereference (member access, call with receiver, element access, unboxing)
  of a value the nullness domain (`Scry.AiDomain`, already planned in §4.6) says may be
  null is a finding `scry/cs/null-dereference`. Guards `x != null`, `x is not null`,
  `x is T y` refine through `Wil.assume` on the branch, as for C.
* Annotations become facts in the EDB (`nullable(var)`), so a Datalog rule can also
  report "annotated non-null but assigned maybe-null" (CS8600-like) without the AI.

### Bounds (CWE-125/787 → `IndexOutOfRangeException`, `ArgumentOutOfRangeException`)

The CLR checks bounds, so these are crashes (denial of service) rather than memory
corruption. `new T[n]` records the length (`alloc` with a symbolic size, `.Length` as a
`T[].get_Length` read of that size); `a[i]` emits an implicit check
`assume (0 <= i && i < len)` in the lowering's *alarm* form, and the interval domain
reports a check it cannot discharge. `List<T>` indexers, `Substring`, `Span<T>` slicing
get the same check from models. A `Span<T>`/`stackalloc`/`unsafe` pointer is the
real-memory case and is out of the first subset.

### Taint sources, sanitisers and sinks (`scry/corpus/csharp/csharp.scry` today)

| CWE | sources (result unless noted) | sinks |
|---|---|---|
| 78 command injection | `System.Console.ReadLine`, `System.Environment.GetEnvironmentVariable`, `System.Environment.GetCommandLineArgs`, ASP.NET `HttpRequest.get_Query`/`get_Form`/`get_Headers`/`get_Cookies`/`get_Body`, `get_Item` on those, `Main`'s `args` (entry policy), `System.IO.StreamReader.ReadLine` | `System.Diagnostics.Process.Start` (every argument), `ProcessStartInfo..ctor` (args), `ProcessStartInfo.set_FileName`/`set_Arguments` arg 1 |
| 89 SQL injection | same | `SqlCommand..ctor` arg 0, `SqlCommand.set_CommandText` arg 1, `SqlCommand.ExecuteReader`/`ExecuteNonQuery`/`ExecuteScalar` arg 0 (the receiver, tainted through its constructor), `DbContext`'s `FromSqlRaw`/`ExecuteSqlRaw` arg 1 |
| 22 path traversal | same | `System.IO.File.*` (`ReadAllText`, `WriteAllText`, `Open`, `Delete`, …) arg 0, `FileStream..ctor` arg 0, `StreamReader..ctor` arg 0, `Path.Combine` as a propagator, not a sink |
| 79 XSS (later) | same | `HttpResponse.WriteAsync` arg 1, `HtmlString..ctor` |

Sanitisers: `System.Int32.Parse`/`TryParse` (arg 1 written clean), `Long.Parse`,
`Guid.Parse`, `Path.GetFileName` (for 22), `SqlParameter` use (a `Parameters.Add`
call does not taint the command; the query text stays the constant), and
`HtmlEncoder.Encode`/`WebUtility.HtmlEncode` (for 79).

Names are fully qualified when the type is in a known BCL namespace that the file
imports (`using System.Diagnostics;` + `Process` → `System.Diagnostics.Process`); an
unknown type stays as written and `?` stands for an unknown receiver type, so a rule
can use `*` (`sink *.ExecuteReader arg 0`) when resolution is weak.

## 4. Test corpus plan

* `scry/corpus/csharp/parse/*.cs` + `*.cst` + `*.sexp`: the tree-sitter spill and the
  golden rendering of the lowering's view of it (S-expressions with field names), one
  fixture per construct family; small and hand-written.
* `scry/corpus/csharp/taint/*.cs`: paired unsafe/safe fixtures per CWE (78 first, then
  89, 22), named like the C corpus (`cwe78-process-unsafe.cs`,
  `cwe78-process-safe.cs`), with a `manifest.json` row each once `scry bench` reads C#.
* Later, without downloading big corpora: a few hand-reduced cases modelled on the
  Juliet C# suite's CWE-78/89/476 shapes and on OWASP Benchmark-style servlets;
  real-world differential runs only with the user's OK.
* Lean group `scry-csharp` (the `library` shard), reading the fixtures from disk, no
  tree-sitter and no .NET needed.

## 5. Milestones

| # | deliverable | est. |
|---|---|---|
| M1 | this note; lexer + parser for §2 with golden tests | 3 d |
| M2 | lowering of classes/methods/statements/expressions to Wil; CWE-78 end-to-end (unsafe fires, sanitised twin does not) | 3 d |
| M3 | name resolution: usings, a BCL type table, CHA call graph with interface dispatch and overloads by arity; fields/properties of the unit's classes as memory | 3 d |
| M4 | rule pack `csharp.scry` (78/89/22), models for `String.Concat`/`Format`/`StringBuilder`, `scry taint` accepting `.cs` (SARIF ids `scry/cs/…`) | 2 d |
| M5 | exceptions/`using`/`foreach` desugarings complete; lambdas as functions; nullability facts + the null-dereference check on the nullness domain | 4 d |
| M6 | bounds checks on arrays/`List<T>` via the interval domain | 2 d |
| M7 | ~~vendored tree-sitter-c-sharp behind the same `Scry.Cst`~~ done early (user chose B, 2026-11-16); left: a `scry-cst --recover` mode so the interpreter tests can also pin syntax-error reporting | 1 d |

Total ≈ 4 weeks, in line with §4.8.

## 6. Slice 1 as implemented

| file | contents |
|---|---|
| `flake.nix` (`tree-sitter-c-sharp`, `scry-native`) | the fetched grammar (v0.23.5, MIT) and the Nix build of the native parse library; `scry/native/tree-sitter-c-sharp` is its uncommitted out-link |
| `scry/native/ts_shim.c`, `scry/src/Scry/Native.wiz` | `scry_parse "c_sharp"`; `languageOf` picks C# for `*.cs`; `toCstStoreIn` records the spill's language |
| `scry/tools/CstMain.wiz` | `scry-cst FILE.cs` spills a C# store (refuses a tree with `ERROR`/`MISSING` nodes, as for C) |
| `scry/src/Scry/CsCst.wiz` | `Scry.Cs.ofStore` (store → the lowering's `Scry.Cst`, with the normalised fields), `Scry.Cs.renderSpill` (S-expression golden renderer) |
| `scry/src/Scry/CsLower.wiz` | class pre-pass (fields, auto-properties, methods, ctors), C# → Wil lowering (§3 table), Wil text printer for goldens, `Scry.Cs.programOf path text spill` |
| `scry/corpus/csharp/parse/` | `hello`, `members`, `statements`, `expressions` (`.cs` + `.cst` spill + `.sexp` view golden) |
| `scry/corpus/csharp/lower/basic.{cs,cst,wil}` | classes, ctor, fields, string concat/interpolation, for/if/continue, try/catch/rethrow; also executed (`Sum`, `Fact`) under `Wil.runFunction` |
| `scry/corpus/csharp/taint/cwe78-*.{cs,cst}` | the end-to-end pair plus two more unsafe cases |
| `scry/corpus/csharp/csharp.scry` | the first C# rule pack (CWE-78 only) |
| `Tests/Groups/ScryCSharp.lean` | group `scry-csharp` (library shard): spill freshness, 4 view goldens, lowering golden + execution, 4 taint cases |

A spill is regenerated with `scry-cst FILE.cs > FILE.cst` (build it with
`wiz build tools/CstMain.wiz -I src -I ../lib -o …` from `scry/`, passing the
toolchain's `--cflags`/`--ldflags`; this host's `grail` link of executables fails on a
pre-existing `__isoc23_strtol` glibc/gmp mismatch). The freshness case fails when a
spill's root does not span its `.cs` text. Goldens are regenerated with
`SCRY_CS_WRITE=1 tests =scry-csharp`, which writes the files **and fails**, so a new
golden is always reviewed in the diff.

The spills are tool output, but they stay checked in as small goldens (9 files, 70 KB):
the test groups run Wiz in the Lean interpreter, which can't call the native shim, and
neither the `.#tests` closure nor CI builds `scry-cst` (it needs the out-link, a C
compile of the grammar and a `wiz build` of `CstMain`). This is the same arrangement as
`scry-c2wil`'s spills. The fetched `src/` is byte-identical to the copy the spills were
generated from, so they are current.

Known approximations in slice 1 (all listed in `CsLower`'s module doc): `X.Y.M()` where
`X` is a type and `Y` a static property (`Console.Error.WriteLine`) resolves as a type
path `System.Console.Error.WriteLine`; overloads share a name; `return` inside `try`
skips `finally`; `using var` does not call `Dispose`; `switch` labels are not compared
(tree-sitter gives `case 1: case 2:` as two sections; every section is reachable
anyway); field initialisers are not run by constructors (each one gets a warning);
lambdas are opaque.
