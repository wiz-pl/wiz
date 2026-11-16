using System;
using System.Diagnostics;

namespace Fixtures
{
    // CWE-78 through an interpolated string and a ProcessStartInfo object: the
    // environment variable taints the constructor argument and the object itself.
    public class Pinger
    {
        public static void Ping()
        {
            string host = Environment.GetEnvironmentVariable("TARGET_HOST");
            var psi = new ProcessStartInfo("/bin/sh", $"-c \"ping -c 1 {host}\"");
            Process.Start(psi);
        }
    }
}
