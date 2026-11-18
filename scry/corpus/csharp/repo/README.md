# `scry cs` fixture tree

A small real tree for `scry cs scry/corpus/csharp/repo` and the `scry-csharp` tests.

| path | why it is here |
|---|---|
| `src/Clean.cs` | parses and lowers with no warning |
| `src/Helper.cs` | `Console.ReadLine` reaches `Process.Start`, so the report has a finding |
| `src/Unsupported.cs` | a lambda and a LINQ query: parses, lowers with two coverage rows |
| `src/Broken.cs` | deliberately not valid C#; the native parse fails, so it is a `parse failure` row |
| `src/Form1.Designer.cs` | excluded by `*.Designer.cs` |
| `src/Generated.g.cs` | excluded by `*.g.cs` |
| `obj/Debug/Ghost.cs` | excluded by `obj/` |
| `bin/Release/Ghost.cs` | excluded by `bin/` |
| `node_modules/vendor/Ghost.cs` | excluded by `node_modules/` |

`Clean.cs`, `Helper.cs` and `Unsupported.cs` have checked-in `scry-cst` spills (the Lean
test group runs in the interpreter and cannot call tree-sitter); `Broken.cs` has none,
because `scry-cst` refuses a tree with `ERROR` nodes. The test constructs its failed
result directly, which is the same `.err` path the driver takes.
