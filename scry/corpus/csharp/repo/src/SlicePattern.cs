namespace Repo;

// A list pattern slice may carry a designation: `.. var middle` (C# 11). v0.23.5's
// `list_pattern` accepted a bare `..` only, so this was an ERROR at the `var` (CSHARP.md
// section 8.2; the one other file was a Demo executor). scry's grammar patch backports upstream
// master's `slice_pattern` rule, and this file's checked-in spill pins the fix.
public static class SlicePattern
{
    public static string Middle(string text) =>
        text is ['[', .. var middle, ']'] ? middle : text;
}
