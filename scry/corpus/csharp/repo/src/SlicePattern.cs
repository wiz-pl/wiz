namespace Repo;

// A list pattern slice may carry a designation: `.. var middle` (C# 11). The grammar's
// `list_pattern` accepts a bare `..` only, so this is an ERROR at the `var`. It has no
// spill: the tree does not parse. Named in CSHARP.md §8.2 (one Nexus file, a Demo
// executor); kept as the smallest reproduction.
public static class SlicePattern
{
    public static string Middle(string text) =>
        text is ['[', .. var middle, ']'] ? middle : text;
}
