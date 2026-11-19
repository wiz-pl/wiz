using System;
using System.Diagnostics;
using System.Linq;

namespace Fixtures.Modern;

#nullable enable

/// <summary>A command to run for a report.</summary>
public record CommandRequest(string Command, int Retries = 0);

// CWE-78 through the constructs a real endpoint file uses: LINQ query syntax, a switch
// expression, an interpolated string, a record's positional field and a `with` copy.
public sealed class CommandEndpoints
{
    public void Run(string mode)
    {
        var raw = Console.ReadLine();
        if (raw is null)
        {
            return;
        }

        var words = raw.Split(' ');
        var parts =
            from w in words
            where w.Length > 0
            select w;

        var command = mode switch
        {
            "safe" => "echo safe",
            _ => $"{string.Join(' ', parts)}",
        };

        var request = new CommandRequest(command);
        var copy = request with { Retries = 1 };
        var psi = new ProcessStartInfo("sh") { Arguments = copy.Command };
        Process.Start(psi);
    }
}
