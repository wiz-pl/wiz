// The span conversion's risk case: tree-sitter gives spans in **UTF-8 bytes** and the
// reader's `Source.Span` is **UTF-16 units**, so a file where the two disagree is the
// one that tells a correct conversion from a plausible one. Everything below the first
// non-ASCII line is shifted by more than the parser's own bookkeeping can absorb:
//
//   * `é` (U+00E9) is 2 bytes and 1 unit, and `ü` (U+00FC) the same: +1 byte each;
//   * `→` (U+2192) and the `—` in a comment are 3 bytes and 1 unit: +2 bytes each;
//   * `😀` (U+1F600) is 4 bytes and **2** units: +2 bytes, and the one character that
//     moves a code-point count as well as a byte count.
//
// So a byte/unit mix-up puts the sink's span 12 units past its statement, and a
// code-point count puts it 2 units short: neither lands on `Process.Start(cmd)`. The
// golden pins the sink's span and `spanText`, so both mistakes are a diff, not a
// silently plausible underline.
using System;
using System.Diagnostics;

namespace Fixtures;

// The console's prompt is “value →” (three non-ASCII code points before the sink).
public class Unicode
{
    // Padding: café ünïcode 😀 → done.
    public static void Run()
    {
        var prompt = "value → é ü 😀";
        var cmd = Console.ReadLine();
        Process.Start(cmd);
        Console.WriteLine(prompt);
    }
}
