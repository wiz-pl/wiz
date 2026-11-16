using System;
using System.Diagnostics;

namespace Fixtures
{
    // The sanitised twin: the console input is parsed as a port number first, so only an
    // integer reaches the command line.
    public class Runner
    {
        public static void Main()
        {
            int port = int.Parse(Console.ReadLine());
            string cmd = $"nc -z localhost {port}";
            Process.Start("/bin/sh", "-c \"" + cmd + "\"");
        }
    }
}
