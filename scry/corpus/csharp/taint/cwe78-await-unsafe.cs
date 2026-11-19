using System;
using System.Diagnostics;
using System.Threading.Tasks;

namespace Fixtures;

// CWE-78 with an `await` between the source and the sink. `ShellAsync` returns a
// `Task<ProcessStartInfo>`, so the value of `await ShellAsync()` is the *awaited*
// ProcessStartInfo: `psi.Arguments` is then the modelled property setter
// (`ProcessStartInfo.set_Arguments`, argument 1) and the console input reaches it.
// Without modelling the await as sequencing the value is a havoc (old first-child
// walk) or its type is the `Task` wrapper, so no setter sink matches and the console
// input never reaches `Arguments`.
public class AsyncShell
{
    private static async Task<ProcessStartInfo> ShellAsync()
    {
        await Task.Yield();
        return new ProcessStartInfo("sh");
    }

    public static async Task Run()
    {
        var command = Console.ReadLine();
        var psi = await ShellAsync();
        psi.Arguments = command;
        Process.Start(psi);
    }
}
