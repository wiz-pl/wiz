using System;
using System.Diagnostics;
using System.Linq;

// Ported from Joern's LambdaTests (csharpsrc2cpg): a lambda becomes a method and a
// method reference. scry lowers a lambda assigned to a local and invoked in the same
// method inline (so `Run`'s sink below is in the program); a lambda passed to a callee
// whose call site is unknown (the `Select` here) is still an opaque `fnptr` plus a
// warning, so that body is absent and the case stays a characterization skip.
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
