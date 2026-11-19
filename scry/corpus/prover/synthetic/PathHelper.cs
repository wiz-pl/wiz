using System;
using System.IO;
using System.Text.RegularExpressions;

namespace Fixtures.Files;

public static class PathHelper
{
    private static readonly Regex Segment = new("^[A-Za-z0-9._-]+$", RegexOptions.Compiled);

    public static string? Resolve(string root, string file)
    {
        if (!IsSegment(file) || !file.EndsWith(".log", StringComparison.OrdinalIgnoreCase))
        {
            return null;
        }

        var full = Path.GetFullPath(Path.Combine(root, file));
        var dir = Path.GetFullPath(root);
        return PathEquals(Path.GetDirectoryName(full), dir) ? full : null;
    }

    private static bool IsSegment(string s) =>
        !string.IsNullOrWhiteSpace(s) && s.Length <= 128
        && s is not "." and not ".." && Segment.IsMatch(s);

    private static bool PathEquals(string? a, string? b) =>
        a is not null && b is not null
        && string.Equals(a.TrimEnd(Path.DirectorySeparatorChar), b.TrimEnd(Path.DirectorySeparatorChar),
            StringComparison.OrdinalIgnoreCase);
}
