using System;
using System.Diagnostics;
using System.Linq;

namespace Fixtures.Modern;

#nullable enable

/// <summary>A command to run for a report.</summary>
public record CommandRequest(string Command, int Retries = 0);

// The sanitised twin: the console input is parsed as a port number before it reaches the
// command line, so the same record/switch/LINQ/`with` path carries no taint.
public sealed class CommandEndpoints
{
    public void Run(string mode)
    {
        var port = int.Parse(Console.ReadLine());

        var words = new[] { mode, "listen" };
        var parts =
            from w in words
            where w.Length > 0
            select w;

        var command = mode switch
        {
            "safe" => "echo safe",
            _ => $"nc -z localhost {port} {string.Join(' ', parts)}",
        };

        var request = new CommandRequest(command);
        var copy = request with { Retries = 1 };
        var psi = new ProcessStartInfo("sh") { Arguments = copy.Command };
        Process.Start(psi);
    }
}
