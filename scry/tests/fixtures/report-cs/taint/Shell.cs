using System;
using System.Diagnostics;

namespace Fixtures;

// The same shape as the C fixture `report/taint.c`: a request value read from the
// console reaches a process command line.
public class Shell
{
    public static void Run()
    {
        var cmd = Console.ReadLine();
        Process.Start(cmd);
    }
}
