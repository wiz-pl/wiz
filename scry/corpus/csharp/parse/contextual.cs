// Both grammar gaps of scry/CSHARP.md section 8.2, in one small file: `with`, `partial` and
// `required` used as ordinary identifiers (they are contextual keywords in C#), and a
// list-pattern slice with a designation (`.. var middle`, C# 11). tree-sitter-c-sharp
// v0.23.5 refused each; scry's grammar patch (native/README.md) accepts them, and the
// keyword positions below (`partial class`, a `required` member, a `with` expression)
// still parse.
namespace Corpus;

public record Amount(int Minor);

public partial class Contextual
{
    public required int Scale { get; set; }

    public Amount Convert(Amount amount) => amount with { Minor = amount.Minor * Scale };

    public static int Count(int[] items)
    {
        var with = items.Length;
        var partial = with;
        var required = partial;
        return required;
    }

    public static string Middle(string text) =>
        text is ['[', .. var middle, ']'] ? middle : text;
}
