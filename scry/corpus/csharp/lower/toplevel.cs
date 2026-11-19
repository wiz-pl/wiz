// A minimal-API Program.cs: top-level statements (C# 9), which are `Program.<Main>$`
// in the language and `Program.Main` here, plus the types the file declares.
using System;
using System.Diagnostics;

var prefix = Environment.GetEnvironmentVariable("REPORT_PREFIX") ?? "daily";
var args = Console.ReadLine();

var command = prefix + " " + args;
Process.Start("/bin/sh", command);

using var scope = new ReportScope(command);
scope.Mark("started");

if (args is null)
{
    return;
}

Console.WriteLine($"ran {command}");

public sealed class ReportScope : IDisposable
{
    private readonly string _command;

    public ReportScope(string command) => _command = command;

    public void Mark(string step) => Console.WriteLine($"{_command}: {step}");

    public void Dispose() => Console.WriteLine("done");
}
