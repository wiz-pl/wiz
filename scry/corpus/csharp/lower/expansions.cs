// The known expansions and the guard around them. `Handlers.Sink` is a method group (a
// function value, not a call); `string.Format`, `Task.FromResult`, `ConfigureAwait` and
// `ArgumentNullException.ThrowIfNull` are name -> template expansions; `Mystery` is not
// a method of this unit and must stay a havoc with a warning, never a silent value.
using System;
using System.Diagnostics;
using System.Threading.Tasks;

namespace Demo.Expansions;

public static class Handlers
{
    public static void Sink(string cmd)
    {
        Process.Start(cmd);
    }

    public static void Silent(string cmd)
    {
    }

    public static void Run(string input)
    {
        var handler = Handlers.Sink;
        handler(input);
        handler = Handlers.Silent;
        handler(input);

        var formatted = string.Format("{0}", input);
        var task = Task.FromResult(input);
        var configured = task.ConfigureAwait(false);
        ArgumentNullException.ThrowIfNull(input);
        Console.WriteLine(formatted + configured);

        var label = nameof(input) + nameof(Handlers.Sink);
        Console.WriteLine(label);

        var unknown = Mystery;
    }
}
