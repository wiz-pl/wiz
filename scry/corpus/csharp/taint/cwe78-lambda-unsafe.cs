using System;
using System.Diagnostics;

namespace Fixtures;

// CWE-78 through a lambda: a `Func<string>` assigned to a local and invoked in the same
// method, plus an `Action<string>` whose body contains the sink. The captured local is
// the only taint path to the result and the sink is only emitted when the lambda body is
// lowered inline; without that the calls are opaque indirect calls with no visible flow.
public class LambdaShell
{
    public static void Run()
    {
        var raw = Console.ReadLine();
        Func<string> get = () => raw;
        var command = get();
        Action<string> start = s => Process.Start(s);
        start(command);
    }
}
