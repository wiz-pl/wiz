using System;
using System.Diagnostics;
using System.Threading.Tasks;

namespace Fixtures;

// CWE-78 through `await`: the value of an async unit method's result reaches a
// ProcessStartInfo argument. Without lowering `await e` to the value of `e`, the
// command is a havoc and the sink sees nothing.
public class AsyncShell
{
    private static async Task<string> ReadCommandAsync()
    {
        await Task.Yield();
        return Console.ReadLine();
    }

    public static async Task Run()
    {
        var command = await ReadCommandAsync();
        var psi = new ProcessStartInfo("sh");
        psi.Arguments = command;
        Process.Start(psi);
    }
}
