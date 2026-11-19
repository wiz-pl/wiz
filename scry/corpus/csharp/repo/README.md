# `scry cs` fixture tree

A small real tree for `scry cs scry/corpus/csharp/repo` and the `scry-csharp` tests.

| path | why it is here |
|---|---|
| `src/Clean.cs` | parses and lowers with no warning |
| `src/Helper.cs` | `Console.ReadLine` reaches `Process.Start`, so the report has a finding |
| `src/Unsupported.cs` | a lambda (its own warning) and a LINQ query lowered to `get_Item`/`Enumerable.Select`, which add unmodelled-external calls rather than a query row |
| `src/Broken.cs` | deliberately not valid C#; the native parse fails, so it is a `parse failure` row |
| `src/KeywordIdentifier.cs` | valid C#: `with`/`partial`/`required` as local names; used to be grammar gap A, now fixed by scry's grammar patch (spill checked in), `scry/CSHARP.md` §8.2 |
| `src/SlicePattern.cs` | valid C#: a list-pattern slice with a designation (`.. var x`); used to be gap B, now fixed by the same patch (spill checked in), §8.2 |
| `src/Form1.Designer.cs` | excluded by `*.Designer.cs` |
| `src/Generated.g.cs` | excluded by `*.g.cs` |
| `obj/Debug/Ghost.cs` | excluded by `obj/` |
| `bin/Release/Ghost.cs` | excluded by `bin/` |
| `node_modules/vendor/Ghost.cs` | excluded by `node_modules/` |

All files have checked-in `scry-cst` spills except `Broken.cs` (the Lean test group runs
in the interpreter and cannot call tree-sitter); `Broken.cs` is deliberately invalid C#
and `scry-cst` refuses a tree with `ERROR` nodes. The test constructs its failed result
directly, which is the same `.err` path the driver takes; the report gives it a named
`parse failure` row (errors are never summed into one row, so every failed file is
named). `KeywordIdentifier.cs` and `SlicePattern.cs` were the two grammar-gap
reproducers and now parse, so they have spills and appear as lowered files.
