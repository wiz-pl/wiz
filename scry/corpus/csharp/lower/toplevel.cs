// A minimal-API Program.cs: top-level statements (C# 9), which are `Program.<Main>$`
// in the language and `toplevel_Program.<Main>$` here, plus the types the file declares.
using System;
using System.Diagnostics;

var prefix = Environment.GetEnvironmentVariable("REPORT_PREFIX") ?? "daily";
var input = Console.ReadLine();

var command = prefix + " " + input;
Process.Start("/bin/sh", command);

using var scope = new ReportScope(command);
scope.Mark("started");

if (input is null)
{
    return;
}

Usage();
Emit(command);

// A top-level local function is a nested method of the synthetic `<Main>$`; it may be
// called before its declaration, and the class below keeps its own scope.
static void Usage()
{
    Console.WriteLine("usage: report [prefix]");
}

void Emit(string text)
{
    Console.WriteLine(text);
}

public sealed class ReportScope : IDisposable
{
    private readonly string _command;

    public ReportScope(string command) => _command = command;

    public void Mark(string step) => Console.WriteLine($"{_command}: {step}");

    public void Dispose() => Console.WriteLine("done");
}
