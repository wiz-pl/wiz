using System;
using System.Diagnostics;

namespace Fixtures
{
    // CWE-78 through a pattern binding: the console line is a string only on the true
    // branch of `is string command`, and the shell is reached through that binding.
    public class PatternGate
    {
        public static void Run()
        {
            object input = Console.ReadLine();
            if (input is string command)
            {
                Process.Start("/bin/sh", "-c " + command);
            }
        }

        // The same pattern with the binding used only in a non-sink call: the pattern
        // branch must not taint the literal command line outside it.
        public static void Safe()
        {
            object input = Console.ReadLine();
            if (input is string command)
            {
                Console.WriteLine(command);
            }
            Process.Start("/bin/sh", "-c ls");
        }
    }
}
