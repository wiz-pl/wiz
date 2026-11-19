# scry C# frontend

Status: **design + first slice, parsing on tree-sitter-c-sharp** (2026-11-16;
the working copy of this note is `wiz-notes/scry-csharp.md`). Option B of §1 was chosen
on 2026-11-16: the hand-written parser of the first draft is gone, and
tree-sitter-c-sharp v0.23.5 (fetched by Nix, `.#tree-sitter-c-sharp`) parses C# through
the same shim as C. The analysis stack the frontend plugs into is on master (PR #376,
merged 2026-11-16): `Scry.Cst` (the read-only CST view the C lowering walks),
`Scry.Warning`/`Scry.TU`, `Wil.Span` origins on every statement, and the rule-pack taint
engine (`Scry.RuleTaint`, `Scry.Interproc`, `Scry.analyze`).

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
  (`native/README.md`: licence, commit, hash), with two grammar backports (the
  contextual-keyword identifiers and the list-pattern slice; §8.2). Generated code is
  not committed, so `flake.nix` fetches it (`fetchFromGitHub`, pinned commit and hash),
  applies the patch, regenerates the parser and builds it with the shim and the vendored
  runtime as `.#scry-native` (pushed to Cachix). A native scry
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
syntax, `switch` expressions, pattern shapes other than a single type test (`{ … }`
property, positional, relational, list, and `is not T y`, which binds on the false
edge), `async`/`await` (parsed as a prefix), iterators (`yield`), local functions, tuples
and deconstruction, `ref`/`out` arguments (parsed, lowered as havoc of the target),
`unsafe`/pointers, events and delegates, operator overloading, attributes' semantics.

The rule for everything outside the subset: **a warning that names the construct**, never
a silent skip. A construct that lowers to nothing without a diagnostic is worse than a
parse error, because the analysis then reports "no findings" about code it never read.
`tests =scry-csharp` has a case ("silent skip") that fails when one of the warnings in §7
disappears.

### `is` tests and pattern bindings

`o is T x` is two things, and the lowering models both:

* the **test**: a fresh nondeterministic bit. The lowering does not know an object's
  runtime type, so both outcomes are possible — the honest abstraction for taint, and
  the same one `switch` sections get. No warning: nothing is skipped.
* the **binding**: `x` is a local of the canonical pattern type `T` (so a later call
  `x.M()` names `T.M(x)` and a rule for `T.M` matches), and it is assigned `o` **on the
  test's true edge only** — the `copy` is emitted into the true block, not before the
  branch. A use of `x` therefore carries `o`'s taint exactly on the paths where the
  test held. The false branch keeps `x` in scope (as C# does) with no definition, so a
  use there has no taint flow.

The same lowering covers `is T` (the test with no binding), `is var x` (always true, `x`
is `o`), `is null` / `is not null` (an exact `==`/`!=` comparison against the default
value), integer constant patterns (an `==`), and `or`/`and` patterns (a disjunction /
conjunction of their alternatives' bits).

Two more shapes need a word, because they are where the grammar and the language
disagree:

* **A property or positional pattern** (`o is { Count: > 0 } x`) is a test whose
  conditions are *not compared*: it is a nondeterministic bit, like a `switch` label's,
  and its own name `x` is installed on the true edge exactly as `is T x`'s. The
  subpattern expressions (a relational pattern's operand) are lowered for their effects,
  and a name declared *inside* a subpattern (`{ P: var y }`) is reported: the lowering
  would have to install it on a path it does not build.
* **The grammar swallows the rest of a condition into a constant pattern**:
  `x is null || rest` parses as `constant_pattern(binary_expression(null || rest))`, and
  `x is not null && rest` as a negated one. The lowering recovers the shape — the left
  spine is the constant compared with `x`, the `||`/`&&` tail is ordinary code — and
  lowers the tail, so a sink or an `is` inside it is not skipped.

A pattern in a `switch` label or a `when` clause is not one of these condition sites, so
its binding is not installed there (reported). A binding on a *false* edge (`is not T y`,
or an `is` under `!`) is installed on the branch's false edge, so
`if (x is not { } y) return; use y;` flows. A name declared *inside* a subpattern
(`{ P: var y }`) is reported: its path is not built. A binding is **not** available in
the right operand of a `&&`/`||` that contains its test, because conditions are lowered
without short-circuit blocks; the copy sits on the branch edge instead.

## 3. C# semantics on Wil

| C# | Wil |
|---|---|
| a method `N.C.M` | `Wil.Func` named `N.C.M` (namespace + class + method). Overloads: the first keeps the name, later ones get `#k` (arity-qualified resolution is a later slice). Instance methods take `this` as parameter 0. A constructor is `N.C..ctor`, takes `this` and returns it. |
| value types `int`/`long`/`short`/`byte`/`char`/`bool`/enums | `Wil.Ty.int w s` (32/64/16/u8/u16/u1), C# wrap-around semantics in `unchecked` (Wil's default) |
| reference types (`string`, classes, arrays, `object`, interfaces, generic parameters) | `Wil.Ty.ptr Wil.Ty.dyn`: a reference is a pointer to a heap block. **Generics are erased**: `List<T>` is the type `List` with `dyn` elements. `struct`s are values — slice 1 treats them like classes (a heap block); stack-slot structs are later. |
| `new C(a…)` for a class the unit defines | `alloc (fields)` then a direct call `N.C..ctor(obj, a…)`; a field read/write is `gep obj k` + `load`/`store` (field index `k` in declaration order), so points-to and memory taint see objects |
| `new T(a…)` for an external type | a direct call `T..ctor(a…)` whose result is the object; the rule engine's "a call's result is tainted by any tainted input" carries taint from constructor arguments into the object (this is what makes `new SqlCommand(query, conn)` tainted) |
| a `record`/primary constructor's parameter list | an implied constructor `R..ctor(this, p…)` that stores each positional parameter into its field and runs `: B(a…)` first (§9.1) |
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
| `flake.nix` (`tree-sitter-c-sharp`, `scry-native`) | the fetched grammar (v0.23.5, MIT) plus `tree-sitter-c-sharp-v0.23.5-fixes.patch` (both §8.2 gaps), regenerated at build time, and the Nix build of the native parse library; `scry/native/tree-sitter-c-sharp` is its uncommitted out-link |
| `scry/native/ts_shim.c`, `scry/src/Scry/Native.wiz` | `scry_parse "c_sharp"`; `languageOf` picks C# for `*.cs`; `toCstStoreIn` records the spill's language |
| `scry/tools/CstMain.wiz` | `scry-cst FILE.cs` spills a C# store (refuses a tree with `ERROR`/`MISSING` nodes, as for C) |
| `scry/src/Scry/CsCst.wiz` | `Scry.Cs.ofStore` (store → the lowering's `Scry.Cst`, with the normalised fields), `Scry.Cs.renderSpill` (S-expression golden renderer) |
| `scry/src/Scry/CsLower.wiz` | class pre-pass (fields, auto-properties, methods, ctors), C# → Wil lowering (§3 table), Wil text printer for goldens, `Scry.Cs.programOf path text spill` |
| `scry/corpus/csharp/parse/` | `hello`, `members`, `statements`, `expressions`, `modern` (`.cs` + `.cst` spill + `.sexp` view golden) |
| `scry/corpus/csharp/lower/` | `basic` (classes, ctor, fields, string concat/interpolation, for/if/continue, try/catch/rethrow; also executed under `Wil.runFunction`), `modern` (record, record struct, partial parts, switch expression, LINQ, `with`, collection expression, constructor initialiser, async/await), `toplevel` (top-level statements become `<stem>.Main`, e.g. `toplevel.Main`), `patterns` (`is` tests and bindings on both edges, `is null`/`is not null`), `switch` (constant int/string/enum labels compared, typed labels, `when` guards, stacked labels, arms), `unsupported` (the warnings for everything out of scope) |
| `scry/corpus/csharp/taint/cwe78-*.{cs,cst}` | the end-to-end pair plus two more unsafe cases, the `modern` pair (source → sink through LINQ, a switch expression, a record field and a `with` copy), the `pattern` pair (a pattern binding carries the sink on the test's true edge), and the `switch` case (a `case T x` binding and an arm binding reach the sink) |
| `scry/corpus/csharp/csharp.scry` | the first C# rule pack (CWE-78 only) |
| `Tests/Groups/ScryCSharp.lean` | group `scry-csharp` (library shard): spill freshness, 5 view goldens, 6 lowering goldens + execution, 8 taint cases, and the "silent skip" case (§2) |

A spill is regenerated with `scry-cst FILE.cs > FILE.cst`. Build the tool with
`wiz build tools/CstMain.wiz -I src -I ../lib -o …` from `scry/`, passing the
toolchain's `--cflags`/`--ldflags`. The C# grammar is the uncommitted out-link
`scry/native/tree-sitter-c-sharp`, created with
`nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp` (what
`.github/workflows/scry.yml` does before `grail build scry`). The freshness case fails
when a spill's root does not span its `.cs` text. Goldens are regenerated with
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
| `await e` | yes | the value of `e`, typed as the awaited `T` of `Task<T>`/`ValueTask<T>` | flows (`cwe78-await`) | no: every await warned `await not modelled: havoc` until the operand lookup stopped naming a field the grammar does not give it; the awaited type is recovered in this pass |
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
  declaration-only file is not a silent skip. (After §9.1 those records' implicit
  constructors are lowered, so the 14 files now produce a function each.)
* **0 files with an executable member and neither a function nor a warning** — the
  number that must be zero. Before the file-scoped-namespace fix it was every non-DTO
  file (61 of them), all silently empty;
* the warning groups (all named, none silent): `unknown name` 162 (mostly method groups
  passed as delegates, plus §7.8), `is` test 88, lambda body 60, field initialiser 47,
  `tuple_expression` 30, target-typed `new()` 30, `out`/`ref` 19, property initialiser
  10, deconstruction 8, switch labels/arms 6, `with` 3, throw expression 4,
  `range_expression` 3, `initializer_expression` 3, `lock_statement` 2.

`await` is the class this tree used to lose: on `origin/master` (`4ad29792`) the same run
reports **205** `await not modelled: havoc` warnings (653 lowering warnings in total),
because the operand was read through a field name tree-sitter-c-sharp does not give the
node. On this branch the class is **0** and the 513 warnings above are the whole lowering
list; the awaited type is now recovered (a `Task<T>` method's `T`), which is what makes
`taint/cwe78-await-unsafe` fire. An await whose callee has no summary is still **one**
`unmodelled-external` warning at its call site (4,028 on this tree, one per call node) and
does not havoc the locals around it — the summary machinery in `Scry.Interproc` owns
that, not the lowering.

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
* **`await e` is sequencing, not havoc.** The value is `e`'s value (a tainted call
  result is still tainted after the await, and the locals before it are unchanged), and
  its static type is the awaited `T` read from a unit method's raw `Task<T>`/
  `ValueTask<T>`, a local declared as `Task<T>`, or the async BCL method-name table
  (`GetAsync` → `HttpResponseMessage`, `ReadAsStringAsync` → `string`, …). That type is
  what makes a property setter after the await the modelled sink: in `cwe78-await`,
  `psi = await ShellAsync()` must be a `ProcessStartInfo`, not a `Task`, for
  `psi.Arguments = command` to be `set_Arguments`. An await of an unknown external is
  one `unmodelled-external` warning at its call site (the summary machinery in
  `Scry.Interproc`), not a havoc of the state, so the surrounding locals stay known.

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
| `is` test's *conditions* | none: a type test, a property/positional/relational/list pattern's conditions and an unknown constant are nondeterministic bits (like a switch label's type test), so both edges stay reachable; `is null` / `is not null` and integer constants are exact |
| a pattern binding no condition site installs | `a pattern binding outside a condition is not installed` (a bare expression, or a binding used in the right operand of `&&`/`||`) |
| a name declared inside a subpattern | `nested pattern binding NAME not modelled` |
| a declaration inside an `or`/`and` pattern | `a binding in an or_pattern (NAME) is not installed` (invalid C#; reported rather than dropped) |
| a switch label the lowering cannot compare (a property, relational or list pattern; a constant of unknown value against an integer scrutinee) | `switch label (…) is not compared: the section is reached by an unknown test` (`arm` for an expression), §7.10 |
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

Two commands exist for a tree of C# (the driver landed in §8; this section's numbers were
taken with the first):

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

`scry cs PATH` (§8) is the directory/project/solution driver: it walks the tree, prints
per-file coverage rows and exits 3 when nothing could be analysed. `cs-externals`
(§9.1) is the measurement tool for the `unmodelled-external` frequency table.

### 7.8 Non-ASCII text: byte spans, character columns

A Wiz `String` is a list of characters, while tree-sitter's spans are UTF-8 **byte**
offsets. `Scry.ByteMap` (`Scry.Preproc`) is the single conversion between the two: it is
built once per text (`Scry.Preprocessed.textMap` for the preprocessed text and
`fileMaps` for the originals) and every call site that slices a `String` or emits a
column goes through it. `Scry.Cst.nodeText` maps the span's byte ends to character
indices and slices the code-point array; `Scry.mapSpan` and `Scry.lineOrigin` slice and
convert through the map. A `Wil.Span` range stays a **byte** offset, as `Scry.Schema`
documents; its `col` is a 1-based **character** column. The SARIF report goes through
`Scry.TextIndex`, which carries the same map, so `startColumn`/`endColumn` are character
columns too. The C frontend shares `Scry.Cst.ofPreprocessed` and `Scry.mapSpan`, so it
gets the same fix.

Two of the 75 files of `src/Crux.Api` contain an em dash or a `§`; before this change
every identifier after such a character was read shifted (`outcome` became `ome`) and
those files reported `unknown name …` warnings for real locals. The corpus case
`lower/unicode` keeps a local declared before the em dash and used after it; its
`lower/unicode.loc` golden pins that the use still resolves and that the one genuine
`unknown name Missing` warning is at the `M` (line 12, column 26), not at a byte
column.

### 7.9 `is` tests and pattern bindings (2026-11-19)

The 88 `is test not modelled` warnings of §7.4 were not, as assumed, mostly `is T x`
declaration patterns: `src/Crux.Api` contains **none of those**. Attributing every
lowered `is_pattern_expression` by the shape tree-sitter-c-sharp gives it (the CST holds
108; 88 reach the lowering, and 20 sit in lambdas, field initialisers, swallowed tails
or the 17 files with no function, so the driver never warns for them):

| shape | the 88 | lowered as |
|---|---:|---|
| `x is null` | 26 | `x == default` |
| `x is A or B` (type tests) | 20 | nondeterministic test (bits disjoined) |
| `x is { … } y` (property pattern + binding) | 20 | nondeterministic test, `y` on the true edge |
| `x is not null` | 7 | `x != default` |
| `x is null \|\| rest` (the grammar swallowed the tail) | 6 | `==`, and the tail lowered |
| `x is not { … } y` | 3 | nondeterministic test, `y` on the false edge |
| `x is not null && rest` | 2 | `!=`, and the tail lowered |
| `x is { … }` (property pattern, no name) | 1 | nondeterministic test |
| `x is > 0 and <= 30` | 1 | nondeterministic test |
| `x is null or { … }` | 1 | `==` or nondeterministic |
| `x is SomeConstant` | 1 | nondeterministic test |
| **total** | **88** | |

Not among the 88: `is T x` **0**, a bare `is T` 0, `as T` 2 (already typed; unchanged),
`switch` with patterns 8 switches / 35 pattern nodes (§7.10).

The binding lowering, and what it fixed:

* `x` is a local of the pattern's type (the operand's when the pattern has none), and its
  copy is emitted into the **edge where the binding holds**: the true block of an `if`,
  `while`, `for` or `?:`, the false block for `is not T x` and for an `is` under `!`. A
  use of `x` therefore carries the operand's taint exactly where the test held, and a
  call `x.M()` names `T.M`, which is what a rule for `T.M` matches.
* The test itself is a fresh nondeterministic bit: the lowering cannot know a runtime
  type or a property pattern's conditions. That is the `switch` section's abstraction and
  needs no warning.
* `is null`, `is not null` and integer constants are exact comparisons.
* The grammar's `x is null || rest` parse (the `||`/`&&` tail is inside the constant
  pattern) is recovered: the left spine is the test, the tail is lowered as code.
* A `catch … when (F(ex) is { } s)` filter installs `s` at the start of the handler.

Measured on `src/Crux.Api` with the same walk (`scry cs`, `--no-taint` unless stated):

| | before | after |
|---|---:|---:|
| functions | 240 | 240 |
| warnings (excluding the 17 `no functions lowered` rows) | 513 | 409 |
| `is test not modelled` | 88 | 0 |
| `unknown name` | 173 | 155 |
| `a pattern binding outside a condition is not installed` | 0 | 1 |
| findings (rule pack, taint on) | 0 | 0 |

The 18 `unknown name` warnings that went are property-pattern bindings that used to be
unknown at every later use. The one new warning is
`Middleware/PartnerBasicAuthMiddleware.cs`'s `… is not { } endpoint || endpoint.…`: the
binding is used in the right operand of `||`, and conditions are lowered without
short-circuit blocks, so the copy sits on the branch edge rather than before the operand.
The `lambda body` row goes 60 → 61 because the recovered tail of
`payments is null || payments.Any(p => …)` now reaches a lambda the old lowering never
visited: newly reached code, reported.

Fixtures: `lower/patterns` (a true-edge binding used by a call, `is not` and `!` bindings,
`is null` / `is not null`, a conditional-expression binding) and
`taint/cwe78-pattern-unsafe` (the console line reaches `Process.Start` through
`input is string command` on the true branch, while its safe method shows the binding
does not leak out of the branch). `lower/unsupported` keeps a named warning for a nested
binding.

### 7.10 `switch` labels and arms (2026-11-19)

§7.9 left `switch` out: every section was a nondeterministic choice
(`switch labels are not compared: every section is reachable`), and a `switch`
statement's `when` clause was not reached at all — the CST view renamed every named
child of a `switch_section` that is not a statement to `case_switch_label`, so the guard
looked like a second label and was filtered out with the pattern. Both are fixed.

The §7.4 corpus has **3 `switch` statements / 10 sections** (9 `case` + 1 `default`)
and **5 `switch` expressions / 24 arms**. Three of the five expressions reach the
lowering: one sits in a lambda body (an opaque function value, §7.6) and one in a
target-typed `new(…)` whose arguments are havoc'd, so their arms were never lowered
either.

| | sections/arms | constant label (compared) | type test | binding | `when` |
|---|---:|---:|---:|---:|---:|
| `switch` statements | 10 | 9 (6 enum, 3 string) | 0 | 0 | 2 |
| `switch` expressions | 24 | 17 (8 enum, 2 int, 7 external string `const`) | 2 (1 bare type name, 1 `or` of two) | 1 | 0 |
| **lowered** (3 statements + 3 expressions) | 27 | 20 (10 enum, 3 string, 7 external `const`) | 2 | 1 | 2 |

The one binding declares an exception-typed value that is only a call receiver (a
property read and `ToString()`), not a sink argument, so **0 of the labels' bindings
reach a sink** in this corpus; the taint fixture below is what pins that flow.

The lowering:

* A constant label is a **value comparison**: the scrutinee is evaluated once and each
  label compares against it (`eq`, or `ne` for a negated one). A literal (int, string,
  char, bool, `null`) uses its lowered value; an enum member of an enum the analysed
  tree declares uses its ordinal (explicit decimal values honoured, implicit ones
  counted, a non-decimal initialiser makes that member and the rest unknown); an enum
  member of an enum it does not declare, or a `const` of unknown value, is compared
  against a **distinct symbolic value** (`globalRef "$const:<name>"`), so two labels
  never alias but the value stays unknown (the analysis does not evaluate either).
  This is what a string-literal label, an in-tree enum member label and an external
  string-`const` label get.
* A **typed** label (`case string s:`, `case T:`, `=> T s`) keeps a nondeterministic
  runtime type test (the lowering cannot know an object's runtime type) and declares
  `s` as a local of the pattern's type; the copy from the scrutinee is emitted in the
  label's **edge block**, the only way into the section/arm.
* A label's `when` guard is lowered **after** that copy, in the same edge block, and
  branches to the section on hold and to the next label's test on failure. A guard that
  declares its own bindings (`when o is T x`) installs them on its true edge.
* Stacked labels (`case 1: case 2:`) are consecutive sections, the first with no
  statements; they are grouped so both labels enter the one body (before this pass the
  empty section was a reachable block that fell out of the switch).
* A section sees only its own label's names: two sections may both declare `text`, and
  the body must not resolve the other section's binding.
* A property, relational or list label is an unknown test, reported by name
  (`switch label (a property pattern) is not compared: …`), with its binding installed;
  an external constant that an integer scrutinee would need is reported the same way.
  A bare type name in a label is the C# type-pattern shorthand (tree-sitter parses it as
  a `constant_pattern` around an identifier), so it is a type test, not a warning.

Measured on the §7.4 corpus with its probe (`scry/scripts/cs-coverage.sh`, per-file
lowering warnings, taint on; the driver's `scry cs` reaches the same lowering):

| | before | after |
|---|---:|---:|
| functions | 240 | 240 |
| warnings | 409 | 403 |
| `switch labels are not compared` | 3 | 0 |
| `switch expression arms are not compared` | 3 | 0 |
| `switch label (…) is not compared` | 0 | 0 |
| findings (rule pack, taint on) | 0 | 0 |

No warning is added: the `when` guards' calls are modelled calls, not warnings (the
driver's `unmodelled-external` coverage row gains the two calls, which used to vanish
with the guard). No label in this corpus is an unknown test — the external constants
are compared symbolically — so the `switch label (…)` row stays 0.

Fixtures: `lower/switch` (int, string and in-unit enum labels, stacked labels, a typed
`case string text:` used by a call, a guard that uses the binding, and two switch
expressions — one with `1 or 2` and `_`, one with a guarded binding) and
`taint/cwe78-switch-unsafe` (the console line reaches `Process.Start` through
`case string command` and through a `string command =>` arm).

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
the tree is hours, not minutes, and is not attempted by default. All 16 failures were two
grammar gaps, not malformed files and not our walker; both are fixed by scry's grammar
patch, and the patched build parses the whole tree: §8.2.

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
finding), one file that does not parse (`Broken.cs` is deliberately invalid C#; the two
grammar-gap reproducers `KeywordIdentifier.cs` and `SlicePattern.cs` now parse — §8.2),
and five excluded paths (`bin/`, `obj/`, `node_modules/`, `.g.cs`, `.Designer.cs`). `src/Unsupported.cs` carries a lambda
and a `from … where … select` query: the lambda is still an opaque `fnptr` (its own
warning), while the query lowers to `System.Int32[].get_Item` and
`System.Linq.Enumerable.Select` calls, which the CLR model table (§10) covers, so the
tree's remaining `unmodelled-external` rows are the calls the model does not know
(`Console.ReadLine`, `Process.Start`; §10.3), and the query is analysed rather than
skipped as a `query_expression not modelled` row. The `scry-csharp` group enumerates it,
applies `Scry.Cs.walkOfPaths` (the driver's exclusion rule) and `Scry.Cs.reportOf` (the
driver's aggregation) to checked-in spills, and asserts the before/after counts, the
coverage rows (one `parse failure` row per failed file, each named), both report
renderings and all four exit statuses. The Lean interpreter cannot call the native shim,
so the spills are checked in exactly as for the other C# fixtures; `Broken.cs` is the only
file without a spill, and its `.err` result is built directly.

### 8.2 The 16 Nexus parse failures: two grammar gaps, now fixed (2026-11-18)

The first whole-tree run reported `4 621 kept, 4 605 parsed, 4 250 lowered, 16 failed`.
All sixteen were **valid C# that tree-sitter-c-sharp v0.23.5 refused**; none was a
truncated write, an encoding problem (all 4 621 decode as UTF-8, and the grammar's
`extras` accept a BOM), a preprocessor form (Nexus has no `#if`/`#region`), or a walker
bug. They fell into exactly two grammar gaps, and scry's grammar patch fixes both
(`native/README.md`; `scry/native/tree-sitter-c-sharp-v0.23.5-fixes.patch` backports the
two upstream-master rules and the Nix derivation regenerates `src/parser.c`):

| gap | construct | files | fix |
|---|---|---|---|
| A | `with`, `partial`, `required` used as identifiers | 15 | add the three to `_reserved_identifier` |
| B | a list-pattern slice with a designation (`['[', .. var selector, ']']`) | 1 | master's `slice_pattern` rule |

Each failure is still one row per file, with the first failing node's position and kind,
so a sweep names every failed file instead of summing them into one row with one example.
The 16, as the old grammar reported them (all `ERROR`):

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
(`alias`, `ascending`, … `yield`) but omits these three in v0.23.5 — and upstream
0.24.0/master still does, so a plain grammar bump would not clear the fifteen. The patch
adds them; the smallest reproduction is `corpus/csharp/repo/src/KeywordIdentifier.cs`:

```csharp
public static int Count(int[] items)
{
    var with = items.Length;
    var partial = with;
    var required = partial;
    return required;
}
```

**Gap B (1 file): a list-pattern slice with a designation.** C# 11 allows
`['[', .. var selector, ']']`; v0.23.5's `list_pattern` accepts a bare `..` only, so the
`ERROR` starts at the `var`. Master (0.24.0) has a `slice_pattern` rule, which the patch
backports verbatim; the smallest reproduction is `corpus/csharp/repo/src/SlicePattern.cs`.

**Before and after, whole tree.** A differential parse of all 5 560 `.cs` files under
`/workspace/Nexus` with the old and patched grammars: 16 files had `ERROR`/`MISSING`
nodes before, **0 after**; no file that parsed gained an error. 43 further files keep
their error-free status but change node shape: 34 gain the keyword's explicit token node
(`new(required: true)` now names the argument `required`) and 9 gain a `slice_pattern`
node. The new trees are the better ones where they differ: `ContractSamples.cs` goes
from a wrong `invocation_expression` around `Find(key) is not var (a, b)` to the correct
`declaration_pattern`. The corpus goldens
pin the target shape: `parse/contextual.{cs,cst,sexp}` covers both gaps and both keyword
positions, and the two repo fixtures now have spills.

The driver's own report on the patched build (`scry cs /workspace/Nexus --no-taint
--json`) is **4 621 kept, 4 621 parsed, 4 279 lowered, 0 failed**, 36 667 functions and
367 coverage rows, exit 0. The same tree on the pre-patch build reports 4 605 parsed,
4 263 lowered, 16 failed, 36 334 functions and 363 rows. The parse-failure list is empty
for the whole tree; `Broken.cs` in the repo fixture is the only remaining deliberate
parse failure, and it is invalid C#, not a grammar gap. Nothing on this list is left as
"out of scope".

The second list the sweep separates is **lowering**: 342 of the 4 621 parsed files produce
no function (`4 621 - 4 279`), the same 342 as before the fix (the 16 now parse *and*
lower). Those are not parse failures and are not conflated with them: each is either a
declaration-only file or carries a lowering warning that `scry cs`'s coverage rows name,
and §7.6 lists the out-of-scope constructs behind them.

## 9. The parsed-but-not-lowered files (Nexus, 2026-11-18)

`files: … parsed, … lowered` counts a file as **lowered only when it produced a
function**, so the difference is files that parse and lower to nothing. §8 recorded
4 605 parsed and 4 250 lowered (355 files). Re-running the same walk against the tree as
it is now

```
scry cs /workspace/Nexus --json --no-taint
```

gives `walk: 5 560 before exclusions; 4 621 kept`, `files: 4 621 found, 4 605 parsed,
4 263 lowered, 16 failed` (342 parsed-but-not-lowered files) and 36 334 functions — 13
more files lower than in the recorded run, from changes that landed after it. The set is
not one bug, and most of it is not a bug at all. The classes are exclusive: the 17 files
that have both a primary constructor and an initialiser are counted as primary
constructors here (they are §9.1's), although the classifier that produced the raw
counts tested initialisers first and reported them in the initialiser row:

| class | files | what the file contains | status |
|---|---|---|---|
| declaration-only | 161 | no member with a body, no initialiser, no primary constructor: 130 `interface` / `const`-only `static class` / attribute-class files, 31 `enum` files | out of scope **by design**: there is no executable member to lower |
| primary constructor | 149 | a `record` / `record struct` / `class` / `struct` with a parameter list (`record R(int X, …)`, `class C(T t)`); 17 of them also have an initialiser | **fixed**, §9.1 |
| initialisers only | 31 | the only executable code is a field or property initialiser (`T x = e;`, `T P { get; } = e;`) | out of scope for this slice, named by its warning |
| empty | 1 | one `[assembly: …]` attribute and no declaration | nothing to lower |

The 161 declaration-only files have no statement or expression to lower, so
`no functions lowered` is the correct row (an `enum` is additionally named by
`enum_declaration not modelled: no code is lowered for it`). The 31 initialiser-only
files keep the warning `field initialiser of X not modelled: the field starts as its
default` (or the property form); running field/property initialisers from a constructor
is its own change, and such a file would still have no *function* until that is done. The
17 initialiser-plus-primary-constructor files are the exception: §9.1 gives them a
`..ctor`, so they are lowered, but their initialiser is still warned and not run.

**No file in the set has a method, constructor or accessor body and no function.** The
dangerous class — executable members that lowered to nothing without a diagnostic, the
failure §7.1 is about — is empty: every file that parsed with a body produced at least
one function. The classes above are declaration-only files (correct), generated
constructors (§9.1), executable initialisers (still named) and one empty file.

### 9.1 The fix: primary constructors

A positional record lowered its parameters to fields, and `new R(a, b)` stored the
arguments into them, but the constructor that the parameter list implies was never
emitted. A file of DTO records (`public sealed record AgentDtos(…)` and nothing else)
therefore produced **no function**, so the whole file counted as "not lowered"; and the
`: this(…)` target of an explicit constructor overload was a call to a function that did
not exist.

`Scry.Cs.lowerPrimaryCtor` now lowers the implied constructor for a `record`,
`record struct`, `class` or `struct` with a parameter list: the parameters are the
leading fields, the body stores each one into its field (`gep` + `store`, exactly what
`new R(a, b)` already did at the call site), runs the `: B(a…)` base call first, and
returns the object. `Scry.Cs.baseArgsOf` unwraps the
`primary_constructor_base_type` node tree-sitter uses for a record's base call (a
class writes the base type directly), and `Scry.Cs.baseOf` reads the type through the
same wrapper, so inherited calls from a record resolve too.

Before/after on the same walk:

| | before | after |
|---|---|---|
| files lowered | 4 263 | 4 412 |
| parsed but not lowered | 342 | 193 |

The 193 that remain are exactly the 161 declaration-only + 31 initialiser-only + 1 empty
files above (`4 605 − 4 412 = 193`); the change lowers the 149 primary-constructor files
(the 132 the classifier reported plus the 17 it put in the initialiser row). The fixture
`scry/corpus/csharp/lower/primary-ctor.{cs,cst,wil}` is the
regression test: it has `record`, `record struct`, a record with a base call, and a class
primary constructor with a base call. Before this change it lowered to zero functions;
`lower/*.wil` now pins the five `..ctor` functions, their field stores, and the two base
calls.

## 10. External models (`Scry.Models` §CLR)

`Scry.Models` was a C table: libc names, policy sanitisers and the C pure calls. The C#
frontend emits CLR spellings (`Namespace.Type.Method`, `T[].get_Item`), so on real code
*none* of the BCL reads it lowers to matched an entry. Every one became an
`unmodelled-external` warning — the coverage marker `Scry.Interproc.unmodelledWarningsOf`
prints for a call with a pointer result or argument and no model. That was 4,028 call
sites over 75 `Crux.Api` files: noise on the coverage report, not a taint fact (an
unmodelled call has no source fact either; only its result's points-to location is
`unknown`, which is what every external call's result is anyway).

### 10.1 The frequency table

`scry/tools/CsExternalsMain.wiz` (`grail build cs-externals`) prints it from the same walk,
lowering and merged-program analysis `scry cs` uses, so the numbers are comparable:

```
cd scry && grail build cs-externals
.grail/bin/cs-externals /workspace/Nexus/src/Crux.Api corpus/csharp/csharp.scry
```

`count-before` is the same selection against `Scry.Models.coreModels` (libc/policy/pure,
without the CLR layer), so one run gives both sides of a model change. The model is keyed
by the exact callee spelling (or by the shape rules in §10.2), so a call disappears from
`count` exactly when a model covers it.

Top of `src/Crux.Api` (75 files, 240 functions, merged program), before → after:

| # | callee | before | after | model |
|---|---|---|---|---|
| 1 | `StatusCodes.get_Status422UnprocessableEntity` | 180 | — | getter |
| 2 | `TypedResults.Problem` | 160 | — | `Results` factory |
| 3 | `?.Produces` | 155 | — | ASP.NET fluent |
| 4 | `?.ProducesProblem` | 126 | — | ASP.NET fluent |
| 5 | `StatusCodes.get_Status404NotFound` | 99 | — | getter |
| 6 | `?.WithName` | 96 | — | ASP.NET fluent |
| 7 | `StatusCodes.get_Status200OK` | 92 | — | getter |
| 8 | `?.WithSummary` | 90 | — | ASP.NET fluent |
| 9 | `System.String.Concat` | 75 | — | exact |
| 10 | `TypedResults.Ok` | 71 | — | `Results` factory |
| 11 | `HttpContext.RequireAuthenticatedPartner` | 63 | 63 | not modelled: another Nexus project's method |
| 12 | `?.MapPost` | 59 | — | ASP.NET fluent |
| 13 | `?.get_TenantId` | 49 | — | getter |
| 14 | `?.Refuses` | 46 | 46 | not modelled: another Nexus project's method |
| 15 | `?.get_PartyId` | 44 | — | getter |
| 16 | `CruxValidationException.get_Message` | 42 | — | getter |
| 17 | `?.get_Status` | 42 | — | getter |
| 18 | `HttpContext.PartnerTenantId` | 41 | 41 | not modelled: another Nexus project's method |
| 19 | `?.get_IsReplay` | 35 | — | getter |
| 20 | `?.get_TransactionId` | 35 | — | getter |
| 21 | `BoundaryRejectionRecorder.RecordAsync` | 34 | 34 | not modelled: another Nexus project's method |
| 22 | `StatusCodes.get_Status201Created` | 31 | — | getter |
| 23 | `System.Array.$new` | 30 | — | collection-expression allocation |
| 24 | `?.WithTags` | 29 | — | ASP.NET fluent |
| 25 | `BoundaryRejectionRecorder..ctor` | 28 | 28 | not modelled: a constructor writes its object |
| 26 | `CruxNotFoundException.get_Message` | 28 | — | getter |
| 27 | `System.String.get_Empty` | 26 | — | getter |
| 28 | `AuthorizeRefusals.get_PartyClosed` | 24 | — | getter |
| 29 | `?.get_Services` | 22 | — | getter |
| 30 | `IEndpointRouteBuilder.MapGroup` | 22 | — | ASP.NET fluent |

Totals: **4,028 → 917** call sites (`unmodelled-external`), 1,179 → 485 distinct
callees, on the same input and the same rule pack. The remaining 917, by shape:

| shape | calls | why it stays |
|---|---|---|
| named type, other method | 487 | almost all another `Nexus` project's code (`HttpContext.RequireAuthenticatedPartner`, `BoundaryRejectionRecorder.RecordAsync`, `IOrchestrator.ExecuteAsync`), which the model table has no honest entry for |
| `?.method` (unknown receiver) | 215 | user mapping/DI/logging extensions (`?.ToWire`, `?.GetRequiredService`, `?.LogError`); a name alone does not say what they do |
| `T..ctor` | 170 | a constructor writes the object it returns; modelling it `copy` would taint `Loc.unknown` |
| `T.set_*` / `set_Item` | 39 | a setter writes through its receiver |
| `System.*` | 5 | `Encoding.UTF8.GetBytes` (has a write-into-buffer overload), `String.Any`/`String[].Any` (a lowering approximation, not `Enumerable.Any`) |

### 10.2 What is modelled, and why each is conservative

The table gains `System.Console.ReadLine` (a source: stdin text is attacker-controlled;
the rule pack already names it, and pack and model sources are deduplicated) and the
rest as **reads**. A read model is an empty effect list under the new family `clr-read`
(`clr-fluent` for the ASP.NET registration calls, `clr-alloc` for `System.Array.$new`):

* **any property getter** (`T.get_P`): the member segment starts with `get_`, and the
  name contains a `.` — every CLR member name does, and no C identifier can, so the shape
  rule cannot capture a C function called `get_Foo`. This is the single biggest class
  (1,943 call sites). A getter's only input is the receiver, so its result derives from it
  and `gen` carries the receiver's taint to the result. It has no data argument to write
  through, and it does not free. `set_*` is deliberately not matched.
* **array/string/collection element and length reads** are getters under that rule
  (`System.Int32[].get_Item`, `?.get_Length`, `System.String.get_Empty`).
* **`String` operations** (`Concat`, `Format`, `Join`, `Substring`, `Split`, `Replace`,
  `Trim*`, `ToLower`/`ToUpper`, `Contains`/`StartsWith`/`EndsWith`, `IndexOf`, `Pad*`,
  `IsNullOrEmpty`, …) and the `?`-receiver spellings of the same: a string operation
  returns a value derived from its parts, and `Concat`/`Format` are what the lowering
  emits for `+`, interpolation and `String.Format`.
* **LINQ operators** (`System.Linq.Enumerable.*` and the `?`-receiver spellings):
  projections/aggregations over their source; `gen` carries the source's taint to the
  result.
* **ASP.NET Core minimal-API registration/fluent calls** (`?.Produces`, `?.WithName`,
  `?.MapPost`, `?.RequireAuthorization`, …): the result derives from the receiver and the
  builder's internal registration state is outside the points-to model either way.
* **`TypedResults.*` / `Results.*` factories**: they return an `IResult` carrying the
  argument values; `gen` taints the result when an argument is tainted.
* **`System.Array.$new`**: the collection-expression array — a fresh object whose
  elements are its arguments (`alloc`, nothing else).
* **`System.Convert.FromBase64String`/`ToBase64String`**: conversions of their input.

A model never launders and never narrows taint: the taint layer's ordinary `gen` rule
still carries taint from the receiver and every argument to the result, so
`s.Substring(1)` of a tainted `s` is tainted and `xs.Select(f)` of a tainted `xs` is
tainted. It also does not *widen* it: an unmodelled call has no source fact either, so
the two differ in the warning and in the effects a model names, not in the flow. No model
is a sanitiser; the policy sanitisers are still the only names that clean a value, and a
pack has to trust them.

### 10.3 What is deliberately not modelled

* **Writes through the receiver or an argument**: `set_*`, `set_Item`, `Add`, `Append`,
  `Insert`, `Remove`, `Clear`, `CopyTo`, `Array.Copy`, `Read`/`ReadOnlySpan` fills,
  `Encoding.GetBytes(dest, …)`. Modelling a store into an unknown `Loc` would taint every
  later load through an unknown pointer: more false positives, not more soundness.
* **Constructors** (`T..ctor`): they write the object they return; the result is tainted
  by the arguments through `gen` already, and a `copy` effect would land in
  `Loc.unknown`.
* **`Dispose`**: `free` would claim the managed object dies; a `using` block's `Dispose`
  does not, and the lifetime rule would report a false use-after-free.
* **The rule pack's sinks** (`Process.Start`, `ProcessStartInfo.set_Arguments`, …): a
  sink needs a rule class and the pack owns those; duplicating them in the table would
  add nothing (the facts would be deduplicated).
* **Cross-project code**: a call into another assembly's own methods is not a BCL call,
  and the name alone (especially on an unknown `?.` receiver) does not say whether it
  writes or allocates. It keeps its explicit warning.

### 10.4 Findings

`src/Crux.Api` has **0 findings before and after** (the pack's only rule is CWE-78 and
these endpoints do not build a command line from a request value). This is the expected
direction: a read model adds no sanitiser and no filter, and the one source model
(`Console.ReadLine`) duplicates a pack source, so the finding set can only stay or grow.
The repo fixture's finding (`src/Helper.cs`, `Console.ReadLine` → `Process.Start`) still
fires, and its `unmodelled-external` row drops from 5 to 1 (only `Process.Start` is
left). The `taint/cwe78-stringop-unsafe` case pins the pair: `Substring` between the
source and the sink is no longer a warning, and the finding still fires.

## 11. Known expansions (2026-11-19)

C# has no preprocessor macros, so "macro expansion" here is the narrower thing the
frontend can do honestly: a **table of known expansions** (`Scry.Cs.expansions`) mapping
a callee spelling to a *term template over the call's already-lowered arguments*
(receiver first, the convention everywhere else in this frontend). It is not a C#
preprocessor. It cannot invent resolution: an entry is used only for an exact spelling,
and a name with no entry keeps its ordinary call — and, when nothing models it, the
analysis's `unmodelled-external` warning. The one shape rule is a method group, whose
name is looked up in the unit's own method table (the `methodOwner` used by every call);
an unknown name is still a havoc with a warning, never a silent value.

### 11.1 Where the warnings are (`src/Crux.Api`, 75 files, 240 functions)

Measured with `scry cs src/Crux.Api --no-taint --json` (lowering warnings) and
`scry-externals` (the merged program's unmodelled callees), at the head of this branch
(which includes §9's models). The brief's guess — that macro-shaped constructs are a
large warning source — is mostly wrong. The lowering warnings are dominated by semantic
gaps, not by macros:

| class | count | macro? |
|---|---|---|
| `unknown name … havoc` | 173 | mixed: 93 are method groups (this section); the rest are unbound `is { } x` designations, `out var` targets and §7.8's byte→char shift (36 in one non-ASCII file) |
| `is` test | 88 | no (pattern matching) |
| lambda body | 60 | no (a function body, not a name→template) |
| field initialiser | 48 | no (constructor semantics) |
| target-typed `new()` | 30 | no |
| tuple expression | 30 | no |
| `out`/`ref` | 20 | no (needs an address) |
| property initialiser | 10 | no |
| everything else | 54 | — |

The macro-shaped family itself:

| construct | sites | warnings before | after |
|---|---|---|---|
| property-like accessor (`x.P`, `x[i]`, `get_*`) | 1,943 lowered call sites | 1,943 `unmodelled-external` | 0 by §9's read model — **not** by an expansion: the lowering already emitted `get_P` |
| method group (`Foo.Sink` in delegate position) | 93 | 1 `unknown name … havoc` each | 0 (this section) |
| `nameof(x)` | 76 | 0, but every site was one shared `$str:nameof` constant | 0, now one constant per name |
| `string.Format` | 0 in `Crux.Api` | — | — |
| exception message formatting | 6 `new …Exception(…)`, none interpolated | an unmodelled constructor, deliberately (§9.3) | refused |
| `ArgumentNullException.ThrowIfNull(x)` | 6 | `unmodelled-external` | 0 (a guard) |
| `ConfigureAwait` / `Task.FromResult` | 5 / 2 | `unmodelled-external` | 0 (pass-through) |

So the largest class (property-like accessors) needed a *model*, not an expansion, and
the expansion for it already existed. The largest class that was **lowered to a havoc**
is the method group: 93 of the 173 `unknown name` warnings are `unknown name <a unit
method>` (31 of them are `.MapGet("/", Handler)` / `.MapPost(…, Handler)` route-handler
arguments; the rest are `.Select(ResponseOf)`, `var h = Method` and other delegate
positions), and the expansion is a function value, not a call.

Numbers to reproduce (the same lowering-only probe built twice, `-I src` and with the
previous `CsLower`): lowering warnings 513 → 420 and `unknown name` 173 → 80 on the 75
files; every one of the 93 that disappears is `unknown name <a unit method>`, and no
other warning class changes. The unmodelled-external table falls 917 → 906: the method
groups were not external calls (a `get_Handler` read was modelled), so only the 6
`ThrowIfNull` and 5 `ConfigureAwait` call sites leave it. The taint fixture
`cwe78-macro-unsafe` goes from 0 to 1 finding: before, `handler(input)` called a local
the analysis could not resolve and the sink inside `Sink` was unreachable; after, the
call reaches `Dispatcher.Sink`.

### 11.2 What is expanded

* **Method group → function value.** A bare identifier or `Type.M` that names a method
  of a unit class is `fnptr "$method:<Ns.Class.Method>"` (`Scry.Cs.methodGroup`). The
  unit's `methodOwner` (which walks `base_list`) is the only lookup, so no new symbol
  resolution is introduced. A local initialised from a **static** method group remembers
  the target; a later `handler(x)` is the direct call `Ns.Class.M(x)`, and an assignment
  to the local updates or clears the target (a re-assigned delegate must not keep
  calling the old method — `cwe78-macro-unsafe` pins this). An instance method group
  still gets its function value, but not the target: the receiver would have to be
  captured, and the value alone does not say how.
* **`nameof(x)`** → `$str:<name>` (the argument's spelling after the last `.`), instead
  of the one shared `$str:nameof`. A complex or generic argument is approximated by its
  spelling; no symbol is resolved.
* **A small call table** (`Scry.Cs.expansions`), each entry a template over the
  lowered arguments:
  `String.Format(fmt, …)` → `System.String.Concat(fmt, …)` (the shape §3 already
  promised); `ConfigureAwait` and `Task.FromResult` → argument 0; and
  `ArgumentNullException.ThrowIfNull(x)` / `ArgumentException.ThrowIfNullOrEmpty(x)` →
  `assume x != null` (the call either returns with a non-null argument or throws).

### 11.3 What is refused

* **Property-like accessors.** The lowering already expands `x.P` to `get_P(x)`; the
  missing piece was the *model* (§9), not a term template. An external object's fields
  are not in the points-to model, so "expand `get_P` to a field load" would invent a
  layout.
* **Exception message formatting.** `new XException($"…")` is a constructor call; §9.3
  refuses to model constructors because they write the object they return. The message
  value does not become a sink-visible flow by calling it a macro.
* **Lambdas and local functions.** Their bodies are functions, not name→template
  expansions; lowering them is M5's work (captures, parameters, a new `Wil.Func`).
* **`is { } x`, tuples, deconstruction, `out`/`ref`, target-typed `new()`.** These are
  binding or address problems. A template cannot bind a name, and `out` needs a location
  the lowering does not have.
* **Unknown names.** A bare name that is not a local, a field or a unit method — an
  external method group, a `using static` import, a missing local-function body — stays
  a havoc with `unknown name … not modelled` (`lower/expansions`'s `Mystery`). The table
  never turns an unknown into a value.

Method groups in the table are recognised by the unit's method table, so the guard is
structural: remove a method and the name falls back to the warning; there is no
permissive suffix rule.


## 11. The first finding on real code (2026-11-19)

§10 measured a tree with **0 findings** — the lowering and the external-read models were
right, but no finding could exist. This section traces one true positive in `src/Crux.Api`
and fixes the two model-side causes; the trace tool is `scry/tools/CsTraceMain.wiz`
(`grail build cs-trace`, or `wiz build tools/CsTraceMain.wiz -I src -I ../lib`).

### 11.1 The shape

`src/Crux.Api/Schemes/SchemeInboundReceiver.cs:35`:

```csharp
logger.LogWarning(
    "Scheme {SchemeKey} did not recognise a {MessageName} message ({ContentType}, {Length} characters).",
    schemeKey, messageName ?? "inbound", httpRequest.ContentType ?? "no content type", body.Length);
```

`schemeKey` and `messageName` are route values (attacker-controlled, URL-decoded) and
`httpRequest.ContentType` is a request header. The rendered line is written by Serilog to
`Logs/Api/api-.log` (`Program.cs:36-41`). A route value with a newline forges a log record:
CWE-117. `SchemeOperatorAdmission.cs:28` logs `schemeKey` the same way.

### 11.2 The trace, before

`cs-trace src/Crux.Api SchemeInboundReceiver.ReceiveAsync` printed:

```
%21 = call HttpRequest.get_ContentType(%4)
...
%37 = call ILogger.LogWarning(%27, %28, %1, %30, %34, %36)
sources 0
sinks   0
tainted 0
findings 0
```

Three name-resolution gaps and one missing model explain it; the first is the largest.

1. **The source name is bare.** `SchemeInboundReceiver.cs` has no
   `using Microsoft.AspNetCore.Http;` (the project's implicit global usings supply it), so
   `canon` leaves the parameter type as `HttpRequest` and the lowering emits
   `HttpRequest.get_ContentType`, not `Microsoft.AspNetCore.Http.HttpRequest.get_ContentType`.
   The pack's sources are fully qualified, so no `src` fact is added. The same happens
   for `HttpContext.Request.Headers` (`?.get_Headers`), `HttpRequest.get_Body`, and every
   other implicit-using type. The externals work (§9) modelled the **reads** by shape
   (`get_P`, `T[].get_Item`); it did not add the request accessors as **sources**, and
   the fully qualified source list was dead on real code.
2. **Cross-file calls keep short names.** `Scry.CsCmd` lowers each file with its own
   class table, so `BootstrapPartnerCredentialSeeder.RunAsync` from `Program.cs` is
   emitted as `BootstrapPartnerCredentialSeeder.RunAsync`, while the merged program's
   function is `Crux.Api.Hosting.BootstrapPartnerCredentialSeeder.RunAsync`. The call
   graph sees no edge: summaries do not connect across files, the callee looks
   external (inflating `unmodelled-external`), and under the entry policy it looks like
   an entry (so its parameters become sources). `BoundaryRejectionRecorder.RecordAsync`
   alone had 34 such call sites.
3. **A method-group value is not a callback according to the entry test.** `CsLower`
   emits `fnptr "$method:Ns.Class.Method"`; `Scry.fnptrNamesOfStmt` returned the whole
   spelling and `isExportedEntry` compared it with `fn.name`, so the "address taken ⇒
   callback" guard never matched for C#.
4. **There is no sink.** `ILogger.LogWarning` was one of the 917 `unmodelled-external`
   rows: the C# pack's only sinks are `Process.Start`/`ProcessStartInfo`, and §9
   deliberately left writes out of the read table. A tainted argument to a log call is a
   log-line write, so it is a sink (CWE-117).

Classification: **name resolution** (items 1–3, the largest cause) and **missing sink**
(item 4). There is no havoc or points-to loss in this flow: the `??` copies and the call
arguments are ordinary uses.

### 11.3 The fix

* `Scry.Cs.resolveCalls` reconciles a **merged** program's direct callees with its
  function names: a short `Class.Method` becomes the unique `Ns.Class.Method` whose
  qualified name ends with it (an ambiguous name is left alone; an external name matches
  none). It also resolves the name inside `$method:` function values. `scry cs` applies
  it after lowering every file. This is what makes the cross-file call graph, the
  per-parameter summaries and the entry policy agree.
* `Scry.fnptrNamesOfStmt` strips `$method:` before the entry test, so a handler passed
  to `MapPost` or a LINQ selector is a callback, not an exported entry.
* `Scry.Models` carries the **HTTP request sources** under the three spellings the
  frontend emits: fully qualified (`Microsoft.AspNetCore.Http.HttpRequest.get_Body`),
  bare when the file relies on implicit usings (`HttpRequest.get_Body`), and `?.get_P`
  when the receiver type is unknown. It covers `Body`, `ContentType`, `Query`, `Form`,
  `Headers`, `Cookies`, `RouteValues`, `Path`, `QueryString`, `ReadFormAsync`,
  `ReadFromJsonAsync` and `ReadFromJson`.
* `Scry.Models` has a `log` sink class; `ILogger.Log*`, `?.Log*` and
  `LoggerExtensions.Log*` are modelled with pointer-like arguments 1–8 as sinks. The
  receiver (argument 0) is not a sink, and an integer (a length) is not one either, so a
  tainted logger object or a `Length` cannot fire. The rule id is `log-injection`
  (CWE-117); `scry/corpus/csharp/csharp.scry` declares it.
* `scry cs` uses `Scry.analyzeC`: on a partial tree, a public method with no caller in
  the analysed files is reachable from outside, so its parameters are source seeds (the
  C-ABI policy `scry taint` already uses). With `resolveCalls` in place this seeds the
  genuinely external methods, not every cross-file callee.
* A static method's bare identifier reads a static field (including `const`) through
  `globalRef`, not field 0 of parameter 0. Before, `SecretVariable`/`CliFlag` read
  `gep %0,1` and were tainted by the first parameter, which produced six false
  `log-injection` findings in `BootstrapPartnerCredentialSeeder`.

The corpus pair `taint/cwe117-log-unsafe.cs` / `cwe117-log-safe.cs` pins the model: an
entry parameter reaches `ILogger.LogWarning` (one finding, `arg 2`), and a constant log
line with the same parameter has none. Both run under `Scry.analyzeC`, the driver's
analysis.

### 11.4 After

`scry cs src/Crux.Api` (same 75 files, 240 functions):

| measure | before | after |
|---|---|---|
| findings | 0 | **7** (`log-injection`) |
| `unmodelled-external` call sites | 917 (485 distinct) | **845** |
| `unknown-memory` | 59 | **36** |
| lowering warnings (all rows except the taint warnings, `no functions lowered` excluded) | 420 | **420** |
| `await not modelled` havocs | 0 | **0** |

The 7 findings are 4 in `SchemeInboundReceiver.ReceiveAsync` (line 35 `arg 2` route
`schemeKey`, `arg 3` `messageName`, `arg 4` `ContentType`; line 50 `arg 2` `schemeKey`)
and 3 in `SchemeOperatorAdmission.AdmitAsync` (line 28 `arg 2` `schemeKey`, `arg 3` the
caller certificate thumbprint, `arg 4` `verdict.Reason`). The route arguments are the
true positives: `%0A` in a path segment is URL-decoded before it reaches the log line.
The thumbprint and content-type arguments are may-findings of the model (the whole
`HttpContext` is an entry value); the trace names every step, so a reviewer can see
which argument they came from. The trace for the receiver is 12 `src` facts (six entry
parameters and six request accessors), 6 sinks, and 4 alerts; before the fix it was
0 / 0 / 0.

The remaining `unmodelled-external` 845 are another Nexus project's methods (the
majority), extension methods called through `HttpContext`/`this` (the 63
`HttpContext.RequireAuthenticatedPartner` sites), unknown-receiver user extensions,
constructors and setters — the classes §9 left out. They are coverage rows, not taint
facts.
