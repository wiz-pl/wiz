using System;
using System.Diagnostics;

namespace Fixtures;

// The safe twin: the command line is a constant, so nothing reaches Process.Start.
public class Safe
{
    public static void Run(string mode)
    {
        var cmd = "echo safe";
        if (mode == "wizard")
        {
            cmd = "echo wizard";
        }
        Process.Start(cmd);
    }
}
