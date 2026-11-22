using System;
using System.Diagnostics;

namespace Fixtures;

// A field initialiser runs in the constructor, before the body: the console read is
// stored into the object by the implicit constructor, and the method that later reads the
// field reaches the sink. `Main` constructs the object so the initialiser is on the path.
public class FieldShell
{
    private string command = Console.ReadLine();

    public void Run()
    {
        Process.Start("/bin/sh", command);
    }

    public static void Main()
    {
        new FieldShell().Run();
    }
}
