using System;
using System.Diagnostics;

namespace Fixtures;

// CWE-78 through a `lock` body: the statement is a wrapper, and the sink inside it is
// ordinary code. `lock` also gives its body a scope of its own and models
// Enter/Exit, so the read and the sink are on the same path.
public class LockShell
{
    public static void Run()
    {
        string cmd = Console.ReadLine();
        object gate = new object();
        lock (gate)
        {
            Process.Start("/bin/sh", cmd);
        }
    }
}
