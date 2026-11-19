// A method group carries the taint path: `Sink` is lowered as its own function, and a
// call through the local that holds the method group must reach it. Before the method
// group expansion the local held a havoc and the call named the local, so the sink was
// never reached. The re-assignment to `Silent` must clear the target (no second finding).
using System;
using System.Diagnostics;

namespace Fixtures.Macro;

public class Dispatcher
{
    public static void Sink(string cmd)
    {
        Process.Start(cmd);
    }

    public static void Silent(string cmd)
    {
    }

    public static void Run()
    {
        var input = Console.ReadLine();
        var handler = Dispatcher.Sink;
        handler(input);
        handler = Dispatcher.Silent;
        handler(input);
    }
}
