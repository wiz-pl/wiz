using System.Diagnostics;

namespace Project;

public static class Sink
{
    public static void Run(string cmd)
    {
        Process.Start("/bin/sh", cmd);
    }
}
