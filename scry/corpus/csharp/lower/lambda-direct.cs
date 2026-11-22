using System;
using System.Collections.Generic;
using System.Diagnostics;

// A lambda passed directly to a callee whose invocation policy the callback table knows
// (`List.ForEach`) is lowered at the call site: the sink is in the caller, the emitted
// call still passes an opaque function value, and there is no `lambda body not lowered`
// row for this shape.
namespace Demo.DirectLambda
{
    public static class Runner
    {
        public static void Run(List<string> items)
        {
            items.ForEach(item => Process.Start("/bin/sh", item));
        }
    }
}
