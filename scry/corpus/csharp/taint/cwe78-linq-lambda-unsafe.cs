using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Fixtures;

// CWE-78 through a lambda passed directly to a framework member: `ForEach` invokes its
// argument, so the body is lowered at the call site and its parameter receives the
// receiver's value (the element abstraction the lowering has). `Run` is an entry, so
// `items` is a source and the element reaches the sink.
public class CallbackShell
{
    public static void Run(List<string> items)
    {
        items.ForEach(item => Process.Start("/bin/sh", item));
    }
}
