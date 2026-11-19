namespace Repo;

// C# contextual keywords are valid identifiers: `with`, `partial` and `required` may
// name a local. tree-sitter-c-sharp v0.23.5 did not list them in `_reserved_identifier`
// (nor does 0.24.0/master), so each use was an ERROR and this file did not parse: 15 of
// the 16 Nexus parse failures were this gap (CSHARP.md section 8.2). scry's grammar patch adds
// them and this file's checked-in spill pins the fix.
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
