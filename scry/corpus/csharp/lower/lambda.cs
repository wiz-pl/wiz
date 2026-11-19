using System;
using System.Diagnostics;
using System.Linq;

// Ported from Joern's LambdaTests (csharpsrc2cpg): a lambda becomes a method and a
// method reference. scry lowers it as an opaque `fnptr` and warns; the body is not
// part of the program, so a sink inside a lambda never reaches the rule engine.
public static class Program
{
    public static void Main()
    {
        int[] numbers = { 2, 3, 4, 5 };
        var squaredNumbers = numbers.Select(x => x * x);
    }

    public static void Run()
    {
        Action<string> run = cmd => Process.Start("/bin/sh", cmd);
        run(Console.ReadLine());
    }
}
