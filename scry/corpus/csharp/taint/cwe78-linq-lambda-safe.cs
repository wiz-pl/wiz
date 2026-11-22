using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Fixtures;

// The sanitised twin of cwe78-linq-lambda-unsafe: the same tainted collection and the
// same direct lambda, but the sink's argument is a constant, so the flow stops before it.
public class CallbackShell
{
    public static void Run(List<string> items)
    {
        items.ForEach(item => Process.Start("/bin/sh", "echo safe"));
    }
}
