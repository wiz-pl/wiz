using System;
using System.Diagnostics;

namespace Fixtures
{
    // CWE-78 across methods: an instance helper builds the command line, and the
    // tainted value flows through its parameter and return value.
    public class Shell
    {
        private string prefix = "ping -c 1 ";

        private string Build(string host)
        {
            return prefix + host;
        }

        public void Run()
        {
            var line = Console.ReadLine();
            Process.Start("/bin/sh", Build(line));
        }
    }
}
