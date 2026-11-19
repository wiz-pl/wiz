using System;
using System.Diagnostics;

namespace Repo
{
    public class Runner
    {
        public static void Run()
        {
            string cmd = Console.ReadLine();
            Process.Start(cmd);
        }
    }
}
