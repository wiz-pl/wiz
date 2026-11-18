using System;
using System.Diagnostics;

namespace Fixtures
{
    // CWE-78: a host name read from the console is spliced into a shell command line.
    public class Runner
    {
        public static void Main()
        {
            string host = Console.ReadLine();
            string cmd = "ping -c 1 " + host;
            Process.Start("/bin/sh", "-c \"" + cmd + "\"");
        }
    }
}
