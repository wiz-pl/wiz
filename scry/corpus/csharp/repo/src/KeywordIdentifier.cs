namespace Repo;

// C# contextual keywords are valid identifiers: `with`, `partial` and `required` may
// name a local. tree-sitter-c-sharp v0.23.5 does not list them in `_reserved_identifier`
// (nor does 0.24.0/master), so each use is an ERROR and this file does not parse. It has
// no spill: `scry-cst` refuses a tree with ERROR nodes, which is the point. Named in
// CSHARP.md §8.2; 15 of the 16 Nexus parse failures are this gap.
public static class KeywordIdentifier
{
    public static int Count(int[] items)
    {
        var with = items.Length;
        var partial = with;
        var required = partial;
        return required;
    }
}
