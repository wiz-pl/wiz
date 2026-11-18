using System;
using System.Diagnostics;

namespace Fixtures
{
    // CWE-78 with modelled calls in the chain: `Substring` and the `+` concatenation are
    // modelled reads (so neither is an `unmodelled-external` warning), and the model must
    // not launder the value either — the console input still reaches `Process.Start`.
    public class Slicer
    {
        public static void Main()
        {
            string line = Console.ReadLine();
            string host = line.Substring(0, 8);
            Process.Start("/bin/sh", "ping -c 1 " + host);
        }
    }
}
