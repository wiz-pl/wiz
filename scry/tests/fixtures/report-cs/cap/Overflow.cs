using System;
using System.Diagnostics;

namespace Fixtures;

// The seed of the export's AST cap. `scry cs --bundle` writes at most
// `Scry.Cs.astFactCap` (2000) `ast` rows per file, and this file's tree is far smaller:
// too few rows, and `tests/web-bundle-cs.wiz` pads it to just over the cap it reads from
// the manifest, so the cap is exercised whatever the cap is. The two lines a padded file
// must keep at their own offsets are the sink below and this class's name.
public class Overflow
{
    public static void Run(string input)
    {
        var total = 0;
        for (var i = 0; i < input.Length; i = i + 1)
        {
            total = total + i * 2;
        }
        var cmd = Console.ReadLine();
        Process.Start(cmd);
        Console.WriteLine(total);
    }
}
