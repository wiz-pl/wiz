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

Out of the first subset, each either lowered since or reported by name (§7): LINQ query
syntax, `switch` expressions and patterns beyond `is T x`, `async`/`await` (parsed as a
prefix), iterators (`yield`), local functions, tuples and deconstruction, `ref`/`out`
arguments (parsed, lowered as havoc of the target), `unsafe`/pointers, events and
delegates, operator overloading, attributes' semantics.

The rule for everything outside the subset: **a warning that names the construct**, never
a silent skip. A construct that lowers to nothing without a diagnostic is worse than a
parse error, because the analysis then reports "no findings" about code it never read.
`tests =scry-csharp` has a case ("silent skip") that fails when one of the warnings in §7
disappears.

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
| `scry/corpus/csharp/parse/` | `hello`, `members`, `statements`, `expressions`, `modern` (`.cs` + `.cst` spill + `.sexp` view golden) |
| `scry/corpus/csharp/lower/` | `basic` (classes, ctor, fields, string concat/interpolation, for/if/continue, try/catch/rethrow; also executed under `Wil.runFunction`), `modern` (record, record struct, partial parts, switch expression, LINQ, `with`, collection expression, constructor initialiser, async/await), `toplevel` (top-level statements become `<stem>.Main`, e.g. `toplevel.Main`), `unsupported` (the warnings for everything out of scope) |
| `scry/corpus/csharp/taint/cwe78-*.{cs,cst}` | the end-to-end pair plus two more unsafe cases, and the `modern` pair (source → sink through LINQ, a switch expression, a record field and a `with` copy) |
| `scry/corpus/csharp/csharp.scry` | the first C# rule pack (CWE-78 only) |
| `Tests/Groups/ScryCSharp.lean` | group `scry-csharp` (library shard): spill freshness, 5 view goldens, 4 lowering goldens + execution, 6 taint cases, and the "silent skip" case (§2) |

A spill is regenerated with `scry-cst FILE.cs > FILE.cst` (build it with
`wiz build tools/CstMain.wiz -I src -I ../lib -o …` from `scry/`, passing the
toolchain's `--cflags`/`--ldflags`; this host's `grail` link of executables fails on a
pre-existing `__isoc23_strtol` glibc/gmp mismatch). The freshness case fails when a
spill's root does not span its `.cs` text. Goldens are regenerated with
`SCRY_CS_WRITE=1 tests =scry-csharp`, which writes the files **and fails**, so a new
golden is always reviewed in the diff.

The spills are tool output, but they stay checked in as small goldens (15 files, 164 KB):
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

## 7. Real-code coverage (`Crux.Api`, 2026-11-18)

The slice was checked against a real solution, not a language tour: `Nexus`
(`Crux.slnx`, 2,483 `.cs` files under `src/`) and, as the starting project,
`src/Crux.Api` (75 files; `node_modules/`, `bin/` and `obj/` excluded). The numbers
below are reproduced by

```
scry/scripts/cs-coverage.sh /workspace/Nexus/src/Crux.Api
scry/scripts/cs-coverage.sh /workspace/Nexus/src
```

which prints the per-construct regular expressions (and, given `CS_COVER`, runs the
parse → lower → taint pipeline over every file). Regular-expression counts are a lower
bound: a construct in a comment or split across lines is missed, an English `is` in a
comment is counted. The table quotes the count and the file count, not a claim of
semantic precision.

### 7.1 The failure this pass exists to prevent

The first honest run over `Crux.Api` produced **no functions and no warnings** — a
clean-looking result over code that was never analysed. The cause: every one of the 75
files uses a file-scoped namespace (`namespace X;`), and `typeDecls` treated
`file_scoped_namespace_declaration` as a container and recursed into its children.
tree-sitter-c-sharp v0.23.5 gives that node only the name (`namespace X;` is 29 bytes
in the spill); the declarations that follow it are its **siblings** in the
`compilation_unit`. So nothing was scanned, nothing was lowered, and nothing was
reported — for the whole project. `lower/basic` never caught it (block namespace), and
`parse/members` covers the syntax but not the lowering.

`typeDecls` now prefixes the *remaining siblings* with the namespace name, and
`lower/modern` and `lower/unsupported` are file-scoped fixtures whose goldens fail if
it regresses. This is the task's hard rule in practice: **a construct that cannot be
lowered must produce a warning naming it, never a silent skip**; a clean "no findings"
over unanalysed code is the failure mode, not the goal.

### 7.2 Frequencies (regex, occurrences / files)

| construct | `src/Crux.Api` | `src/` |
|---|---|---|
| nullable annotation (`string?`, `T?`) | 339 / 44 | 13,358 / 1,328 |
| `is` pattern | 165 / 39 | 12,032 / 1,405 |
| `await` | 228 / 38 | 8,733 / 1,058 |
| `record` / `record struct` | 149 / 27 | 2,799 / 860 |
| `async` | 121 / 37 | 3,734 / 1,052 |
| file-scoped `namespace X;` | 74 / 74 | 2,464 / 2,464 |
| LINQ method call (`.Where(`, `.Select(`, …) | 68 / 28 | 6,584 / 1,001 |
| string interpolation (`$"…"`) | 59 / 27 | 5,451 / 1,038 |
| attribute list (`[Foo]` at line start) | 47 / 14 | 9,730 / 338 |
| collection expression (`[…]`) | 10 / 7 | 867 / 301 |
| `switch` expression | 6 / 5 | 541 / 322 |
| `with` expression | 4 / 3 | 99 / 72 |
| target-typed `new()` | 4 / 4 | 149 / 105 |
| `lock` | 2 / 1 | 68 / 25 |
| generic constraint (`where T : …`) | 1 / 1 | 124 / 63 |
| `partial` type | 1 / 1 | 1,321 / 158 |
| primary-constructor class (`class C(T t)`) | 1 / 1 | 335 / 259 |
| `using static` | 0 / 0 | 16 / 14 |
| LINQ query syntax (`from x in …`) | 0 / 0 | 35 / 17 |
| `yield` | 0 / 0 | 215 / 37 |
| `unsafe` | 0 / 0 | 11 / 8 |
| `goto` | 0 / 0 | 0 / 0 |

### 7.3 Construct → parses / lowers / taints / silence

`parses` is tree-sitter-c-sharp with no `ERROR`/`MISSING` node; `lowers` is what
`Scry.CsLower` does with it; `taints` is whether a source → sink flow through the
construct is preserved (the `taint/cwe78-*` fixtures are the evidence); `silent before`
is what happened **before this pass** — a construct that lowered to nothing without a
diagnostic.

| construct | parses | lowers | taints | silent before? |
|---|---|---|---|---|
| file-scoped `namespace X;` | yes (74/74) | prefix of every function name | flows | **yes: every type in the file dropped** (all 75 files) → fixed |
| `record` / `record struct` | yes | positional parameters become leading fields; `new R(a, b)` stores the arguments | flows (`cwe78-modern`) | **yes: parameters and arguments dropped** → fixed |
| primary-constructor class | yes | positional parameters become fields (as a record) | flows | **yes** → fixed |
| `partial` parts in one file | yes | parts merged by qualified name | flows | **yes: the second part was shadowed** → fixed |
| top-level statements | yes | `<stem>.Main` (`Program.Main` for `Program.cs`) | flows | **yes: not a type, so ignored; a minimal API `Program.cs` produced no functions** → fixed |
| `async` method | yes | body lowered synchronously | flows | no (by design) |
| `await e` | yes | the value of `e` | flows | no (by design) |
| nullable `T?` | yes | erased to `T` | n/a | no (no nullness domain yet, documented) |
| generic parameters/constraints | yes | erased to `dyn` | n/a | no (as C# erases them) |
| `is T x` (and every other pattern) | yes | `x` bound to the left value; the boolean is havoc'd (both branches reachable) + warning | flows through `x` | no (warning) |
| `switch` expression | yes | nondeterministic choice among the arms, each value copied to one register + warning | flows (`cwe78-modern`) | no (warning) |
| `with { P = e }` | yes | `e` evaluated; the result is a copy of the source + warning (members not updated) | flows (same object) | no (warning) |
| collection expression `[a, ..b]` | yes | `System.Array.$new(a, b)` | flows | was havoc per element with a warning → fixed |
| LINQ query syntax | yes (none in `Crux.Api`) | source, range variable, `where`/`let`/`select`; `join`/`group`/`orderby` warn | flows (`cwe78-modern`) | no (warning) |
| string interpolation | yes | `System.String.Concat(holes…)` | flows | no |
| attributes | yes | parsed and ignored (no rule depends on one) | n/a | no (documented) |
| `using static` | yes | directive ignored; a bare imported call is named in a "not a method" warning | n/a | warning |
| target-typed `new()` in a declaration | yes | the declared type is used | flows | no |
| target-typed `new()` in an expression | yes | havoc + warning | n/a | no (warning) |

### 7.4 The 75-file run, in numbers

`CS_COVER=$PWD/scry/build/cs-cover scry/scripts/cs-coverage.sh /workspace/Nexus/src/Crux.Api`:

* 75/75 files parse (no `ERROR`/`MISSING` node) and 75/75 lower;
* 240 functions, 513 warnings, 0 findings (the pack's only rule is CWE-78; these
  endpoints do not build a command line from a request value);
* 14 files produce no function: every one is `Dtos/*.cs`, and the 14 contain 83
  `public sealed record` declarations and nothing with a `=>` or `{` body. A
  declaration-only file is not a silent skip;
* **0 files with an executable member and neither a function nor a warning** — the
  number that must be zero. Before the file-scoped-namespace fix it was every non-DTO
  file (61 of them), all silently empty;
* the warning groups (all named, none silent): `unknown name` 162 (mostly method groups
  passed as delegates, plus §7.8), `is` test 88, lambda body 60, field initialiser 47,
  `tuple_expression` 30, target-typed `new()` 30, `out`/`ref` 19, property initialiser
  10, deconstruction 8, switch labels/arms 6, `with` 3, throw expression 4,
  `range_expression` 3, `initializer_expression` 3, `lock_statement` 2.

### 7.5 Fixes in this pass

* **File-scoped namespaces** (§7.1) — the whole file was dropped silently.
* **Top-level statements** are unwrapped from `global_statement` (they were a
  `global_statement not modelled` warning with no code) and lowered as `<stem>.Main`.
* **Records and primary constructors**: the parameter list becomes the leading fields;
  `new R(a, b)` allocates, stores each argument into its field, then calls a declared
  constructor if there is one.
* **`partial` parts in one file** are merged by qualified name.
* **Collection expressions**: the element wrappers are
  `collection_element → expression_element|spread_element → expression`; only the first
  was unwrapped, so every element was a havoc (with a warning). All three are unwrapped
  now, so an element's taint reaches the array.
* **`with` initialisers**: the initialiser is a `with_initializer` per member
  (`member_name expression`); the first attempt lowered the member name as an
  expression (a spurious "unknown name" havoc). Only the value is lowered, for every
  member.
* **Inherited calls** (`Reject(…)` in a derived class) resolve through `base_list` to
  the declaring class instead of a "not a method" warning.
* **Deconstruction** (`var (a, b) = …`) evaluates the right-hand side (so a sink inside
  it is analysed), binds each name to a fresh havoc and names the construct; the names
  used to be unknown at every later use, which turned one tuple into a trail of
  `unknown name` warnings and lost their flow.
* **A nested `delegate` member** now warns (`delegate_declaration member not modelled`)
  instead of being treated as lowered code.
* **A `switch` expression** names its approximation (arms not compared) like a
  `switch` statement already did.
* **`switch` expressions**, **LINQ query syntax** and **target-typed `new()` in a
  declaration** are lowered with their value flow (a nondeterministic choice among the
  arms, the query's source/range variable/`select`, the declared type) instead of being
  havoc'd.
* **Constructor initialisers** (`: base(…)`, `: this(…)`) evaluate their arguments and
  call the target constructor; unsupported members (indexer, operator, destructor,
  event with accessors, `#if`-guarded member) are each named.

### 7.6 Still out of scope, with the warning each produces

| construct | warning |
|---|---|
| lambda body | `lambda body not lowered: an opaque function value` |
| local function | `local function NAME not modelled: its body is not lowered and calls to it are unknown` |
| indexer | `indexer_declaration member not modelled: no code is lowered for it` |
| operator / conversion operator | `operator_declaration member not modelled: …` |
| destructor | `destructor_declaration member not modelled: …` |
| event with accessors | `event_declaration member not modelled: …` |
| nested delegate / `#if`-guarded member | `delegate_declaration member not modelled: …`, `preproc_if not modelled: …` |
| `#if` / `#else` block (top level) | `preproc_if not modelled: no code is lowered for it` |
| `lock`, `goto`, a label | `lock_statement not modelled`, `goto_statement not modelled`, `labeled_statement not modelled` |
| `yield return` | `yield_statement not modelled` |
| `unsafe`, `fixed`, `checked` | `unsafe_statement not modelled`, … |
| `is` test | `is test not modelled: havoc` (both branches stay reachable) |
| `switch` statement labels / expression arms | `switch labels are not compared: every section is reachable`, `switch expression arms are not compared: every arm is reachable` |
| target-typed `new()` in an expression | `target-typed new() without a declared type not modelled: havoc` |
| `join`/`group`/`orderby` in a query | `… in a query is not modelled: its value is havoc` |
| field/property initialiser | `field initialiser of X not modelled: the field starts as its default` |
| deconstruction `var (a, b) = …` | `deconstruction not modelled: each name is a havoc` |
| `out`/`ref` target | `out/ref argument not modelled: havoc` |
| `with` member updates | `with expression: the copy's members are not updated (it keeps the original's values)` |
| a bare `using static` import call | `call to M: not a method of T (delegate or unknown)` |
| `base.M(…)` / a delegate-valued call | `base_expression not modelled: havoc`, `call through a delegate value: unknown target` |

`async`/`await`, nullable annotations and generics are modelled by design and
deliberately produce **no** warning: the body is lowered synchronously, nullness is a
later slice, and generics are erased exactly as C# erases them. Attributes are parsed
and ignored.

### 7.7 What runs today

There is **no command on this branch that analyses a directory of `.cs` files**. C# is
not wired into `scry taint`; `scry parse --stats` reads a spill. Two things exist:

```
# 1. the measurement harness (this section's numbers; needs the native grammar)
nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp   # once per checkout
cd scry && wiz build tools/CsCover.wiz -I src -I ../lib -o build/cs-cover
        # (add --cc /path/to/cc and, if GMP's headers are not in the default
        #  search path, --cflags/--ldflags as `grail.local.wiz` lists them)
cd .. && CS_COVER=$PWD/scry/build/cs-cover scry/scripts/cs-coverage.sh DIR

# 2. the test group (checked-in spills, no native build)
./.lake/build/bin/tests '=scry-csharp'
```

A `scry cs PATH` driver (`scry/src/Scry/CsCmd.wiz`, which walks a directory,
`.csproj` or `.sln`, prints per-file coverage rows and exits 3 when nothing could be
analysed) is being added on the sibling branch `agent/cs-driver`; it is not part of
this branch.

### 7.8 A known caveat: non-ASCII text

Two of the 75 files contain non-ASCII text (an em dash in a comment, a `§`). `Scry.Cst`
slices a node's text by **character** index while tree-sitter's spans are **byte**
offsets (`Scry.Cst.textOf`'s doc says so; the C frontend has the same limitation). Every
identifier after such a character is read shifted — `outcome` becomes `ome` — so those
two files report `unknown name …` warnings for real locals. It is loud, not silent, but
it loses precision. The fix is a byte→character index map in `Scry.Cst.ofPreprocessed`;
it is left as its own change because it is shared with C.

## 8. The repository driver: `scry cs`

A single `.cs` file is useful for a fixture; a codebase is a tree. `scry cs`
(`scry/src/Scry/CsCmd.wiz`) walks a directory, a `.csproj` or a `.sln`/`.slnx`, parses
every file with the same native shim, lowers it with `Scry.CsLower`, runs the rule pack
over the merged program, and writes a summary whose **coverage** section is the point:

```
scry cs PATH [--json] [--fail-on error|warning|note] [--rules FILE] [--no-taint]
```

`PATH` is a directory, a `.csproj`, a `.sln`/`.slnx`, or one `.cs` file. An
SDK-style project (no `<Compile Include=` items) is walked; an explicit item list is
used when present. `<Compile Remove=` and `EnableDefaultCompileItems` are not
interpreted.

Discovery is sorted, so two runs over one tree report the same rows. The walk applies a
built-in, `.gitignore`-style rule list (it does not read a `.gitignore` file):

* any path segment `bin/`, `obj/` or `node_modules/`;
* any hidden directory (a segment starting with `.`);
* a basename ending `.g.cs` or `.Designer.cs`;
* symbolic links.

The report prints the number of `.cs` files **before** exclusions and **after** them, and
each rule is a coverage row with its count and one example. An excluded directory is not
descended for analysis, but its `.cs` files are still counted (names only) so the
"before" number is real. An explicitly named `.cs`, `.csproj` or `.sln` is not excluded
itself; files discovered inside it are.

### What the summary says

Measured on a real codebase (Nexus `src/Crux.Api`, 75 kept files):

```
walk: 79 .cs file(s) before exclusions; 75 kept, 4 excluded by rule
files: 75 found, 75 parsed, 57 lowered, 0 failed
functions: 239 lowered
rules: scry/corpus/csharp/csharp.scry (4 rule(s))
findings: 0 (error 0, warning 0, note 0)
coverage: 25 row(s) — what was skipped or warned about
  SEVERITY COUNT  CONSTRUCT                                   EXAMPLE
  warning  2933   unmodelled-external                         Authentication/AuthenticatedPartner.cs:16:12
  warning  205    await not modelled: havoc                   Dtos/TransactionDtos.cs:87:23
  warning  168    unknown name not modelled: havoc            Dtos/SchemeIngressDtos.cs:16:31
  ...
  note     4      excluded: obj/                              obj/Debug/net10.0/…AssemblyAttributes.cs
```

The whole Nexus tree (5 560 `.cs` before exclusions, 4 621 kept) walked, parsed and lowered
in 311.8 s and about 4.1 GiB with `--no-taint` on the build that first ran the sweep:
4 605 parsed, 4 250 lowered, 16 parse failures, 36 319 functions and 46 coverage rows.
The 2026-11-18 re-run that named all 16 failures (commit `e3f27195`, before merging
master) reports the same 4 621/4 605/16, 4 263 lowered, 36 334 functions and 363 coverage
rows: the lowering now names more constructs, and each failed file is its own row. Taint
dominates: Crux.Api took 219.8 s with taint and 2.0 s without, so a full tainted sweep of
the tree is hours, not minutes, and is not attempted by default. All 16 failures are two
upstream grammar gaps, not malformed files and not our walker: §8.2.

`files found / parsed / lowered / failed` distinguishes native parsing from lowering:
`failed` means the grammar returned `ERROR`/`MISSING` nodes, so the file was not lowered
at all. A failed file gets **its own** `parse failure` row (errors are never summed), and
the row's location is the first failing node's position and kind — `path:line:col
(MISSING identifier)` or `(ERROR)`. A file that parses but produces no method is a `no
functions lowered` warning, not a zero. An unreadable file or a directory that cannot be
listed is a row, never an omission.

Lowering messages interpolate identifiers and types; the coverage row normalises them to
the construct (`lambda body not lowered: an opaque function value`, `out/ref argument not
modelled: havoc`, `operator not modelled: havoc`, an unsupported statement kind, a
field/property initialiser, …). The human report shows the construct and one example;
the JSON has the same two fields per row.

### Exit status and `--fail-on`

* `0` at least one file was lowered, and nothing reaches `--fail-on`;
* `1` a finding **or a coverage row** is at or above `--fail-on` (a parse failure is
  `error`, a lowering/skip row is `warning`, an exclusion is `note`);
* `2` usage or IO (a bad flag, a missing path, an unreadable project/solution);
* `3` nothing could be analysed: no `.cs` file, or every discovered file failed.

`3` is what tells "no findings" from "did not run". The native grammar is a build-time
dependency (`native/tree-sitter-c-sharp`, §6): a binary built without it fails to link,
so a grammar-less run cannot masquerade as a clean one; at run time the same class of
failure surfaces as every file failing, which is also `3`.

`--no-taint` stops after parse/lower and reports coverage only (the `taint not run`
row says so). `--rules FILE` selects a pack; otherwise the walk tries
`scry/corpus/csharp/csharp.scry`, then `../scry/corpus/csharp/csharp.scry`, then
`lib/Scry/rules/csharp.scry`. With no pack the findings section is empty and a
`taint not run: no rule pack found` row is printed.

### Fixture and tests

`scry/corpus/csharp/repo/` is a small tree: three analysable files (one with a real
finding), three files that do not parse (`Broken.cs` is invalid C#; the other two are
valid C# that tree-sitter-c-sharp refuses — §8.2), and five excluded paths (`bin/`,
`obj/`, `node_modules/`, `.g.cs`, `.Designer.cs`). `src/Unsupported.cs` carries a lambda
and a `from … where … select` query: the lambda is still an opaque `fnptr` (its own
warning), while the query lowers to `System.Int32[].get_Item` and
`System.Linq.Enumerable.Select` calls, so those two calls are part of the five
`unmodelled-external` rows (with `Console.ReadLine`, `Process.Start` and
`System.Int32[].get_Length`) instead of a `query_expression not modelled` row: a query
the lowering handles is analysed, not skipped. The `scry-csharp` group enumerates it,
applies `Scry.Cs.walkOfPaths` (the driver's exclusion rule) and `Scry.Cs.reportOf` (the
driver's aggregation) to checked-in spills, and asserts the before/after counts, the
coverage rows (one `parse failure` row per failed file, each named), both report
renderings and all four exit statuses. The Lean interpreter cannot call the native shim,
so the spills are checked in exactly as for the other C# fixtures; the three invalid
files have no spill and their `.err` results are built directly.

### 8.2 The 16 Nexus parse failures: two upstream grammar gaps (2026-11-18)

The first whole-tree run reports `4 621 kept, 4 605 parsed, 4 250 lowered, 16 failed`.
All sixteen are files **tree-sitter-c-sharp v0.23.5 cannot parse although they are valid
C#**; none is a truncated write, an encoding problem (all 4 621 decode as UTF-8, and the
grammar's `extras` accept a BOM), a preprocessor form (Nexus has no `#if`/`#region`), or a
walker bug. Each failed file now gets its own row, with the first failing node's position
and kind, so the sweep names the sixteen instead of summing them into one row with one
example:

| file (below `/workspace/Nexus/`) | first node | rejected construct |
|---|---|---|
| `src/Crux.Demo.Api/Execution/RealServerActionExecutor.cs:865:82` | `ERROR` | `.. var selector` in a list pattern (gap B) |
| `tests/Crux.Api.Tests/AgentCashEndpointsTests.cs:473:17` | `ERROR` | `required` as a local (gap A) |
| `tests/Crux.Api.Tests/CardChargebackTests.cs:227:9` | `ERROR` | `partial` as a local (gap A) |
| `tests/Crux.Application.Tests/Compliance/ApplicationRegistersTests.cs:84:9` | `ERROR` | `var with` (gap A; also `partial`) |
| `tests/Crux.Application.Tests/Compliance/OwnershipRegisterTests.cs:280:9` | `ERROR` | `var with` (gap A) |
| `tests/Crux.Application.Tests/Compliance/ReserveBankDirectionsTests.cs:99:17` | `ERROR` | `required` as a local (gap A) |
| `tests/Crux.Application.Tests/Compliance/StructureRegistersTests.cs:179:9` | `ERROR` | `partial` as a local (gap A; also `var with`) |
| `tests/Crux.Application.Tests/Identity/AppKeyAttestationsTests.cs:165:15` | `ERROR` | `required` as a local (gap A) |
| `tests/Crux.Application.Tests/Treasury/PartyCalendarsTests.cs:47:17` | `ERROR` | `required` as a local (gap A) |
| `tests/Crux.Architecture.Tests/ContainerDirectoryTests.cs:1:1` | `ERROR` | `required` as a local (gap A); recovery's node spans the unit |
| `tests/Crux.Communications.Tests/SegmentEvaluatorTests.cs:174:9` | `ERROR` | `var with` (gap A) |
| `tests/Crux.Dashboard.Api.Tests/CertificationContentTests.cs:241:16` | `ERROR` | `partial` as a local (gap A) |
| `tests/Crux.Demo.Api.Tests/CardMachineValueTourTests.cs:45:17` | `ERROR` | `partial` as a local (gap A) |
| `tests/Crux.Domain.Tests/Compliance/InternalAuditRecordTests.cs:80:9` | `ERROR` | `required` as a local (gap A) |
| `tests/Crux.Tenant.Api.Tests/AgentTests.cs:415:15` | `ERROR` | `partial` as a local (gap A) |
| `tests/Crux.Worker.Tests/NextDaySegregationTests.cs:186:15` | `ERROR` | `partial` as a local (gap A) |

**Gap A (15 files): `with`, `partial` and `required` are not reserved identifiers.**
C# makes these *contextual* keywords: outside a `with` expression, a `partial` modifier or
a `required` member modifier, each is an ordinary identifier, and Nexus uses them as local
names (`var with = await …;`, then `partial.Detail.Should()`, `required.Should()`). The
grammar's `_reserved_identifier` rule lists the contextual keywords it accepts as names
(`alias`, `ascending`, … `yield`) but omits these three
(`native/tree-sitter-c-sharp/src/grammar.json`, v0.23.5). The parse fails where the name is
used: `var with = …` is an `ERROR` at `var`, while `var required = 1;` and
`WriteLine(required)` parse and the member access `required.M` is the `ERROR` (at the
`.`, or at the identifier depending on recovery). The smallest reproduction is
`corpus/csharp/repo/src/KeywordIdentifier.cs`:

```csharp
public static int Count(int[] items)
{
    var with = items.Length;
    var partial = with;
    var required = partial;
    return required;
}
```

Upstream has not fixed it since: `tree-sitter-c-sharp` 0.24.0 (master, checked 2026-11-18)
has the same `_reserved_identifier` list without these three, so a grammar bump alone
would not clear the fifteen.

**Gap B (1 file): a list-pattern slice with a designation.** C# 11 allows
`['[', .. var selector, ']']`; the grammar's `list_pattern` accepts a bare `..` only, so
the `ERROR` starts at the `var`. The smallest reproduction is
`corpus/csharp/repo/src/SlicePattern.cs` (`text is ['[', .. var middle, ']']`).

Both fixtures are deliberately **left failing**: they are in the repo tree without a
spill, and the sweep reports them as `parse failure` rows. Renaming the identifiers before
the parse, or patching the generated `parser.c`, would hide a real gap (and a rewrite would
move every span); the honest result is the named failure. When the grammar gains either
construct, add the spill and delete the fixture's row from this section — the group's
`repoFailureRows` case names all three failed files (and `repoCoverage` counts them), so
both change with it.

