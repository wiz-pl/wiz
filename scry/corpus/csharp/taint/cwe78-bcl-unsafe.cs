using System;
using System.Diagnostics;

namespace Fixtures;

// CWE-78 through a modelled BCL call: `Process.GetCurrentProcess().StartInfo` has the
// known result type ProcessStartInfo, so the assignment to `Arguments` is the modelled
// sink. Without the summary, the receiver type is `?` and `?.set_Arguments` matches no
// rule.
public class BclShell
{
    public static void Run()
    {
        var process = Process.GetCurrentProcess();
        var psi = process.StartInfo;
        psi.Arguments = Console.ReadLine();
        Process.Start(psi);
    }
}
