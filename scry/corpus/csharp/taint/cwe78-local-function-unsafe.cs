using System;
using System.Diagnostics;

namespace Fixtures;

// CWE-78 through a local function: `Launch` is a function of its own with `cmd` as a
// leading capture parameter, so the sink is analysed in `Run.$local:Launch` and the call
// from `Run` is the flow's edge.
public class LocalShell
{
    public static void Run()
    {
        string cmd = Console.ReadLine();

        void Launch()
        {
            Process.Start("/bin/sh", cmd);
        }

        Launch();
    }
}
