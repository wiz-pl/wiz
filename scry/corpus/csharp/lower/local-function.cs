using System;
using System.Diagnostics;

// A local function is a function of its own (`Caller.$local:Name`) with the caller's
// locals it reads as leading parameters, and a call to it is a direct call that passes
// them: the sink in the body is in the program, at its own function.
namespace Demo.Local
{
    public static class Launcher
    {
        public static void Run(string cmd, int depth)
        {
            int remaining = depth;

            void Launch(string suffix)
            {
                Process.Start("/bin/sh", cmd + suffix);
            }

            string Wrap()
            {
                return cmd + "/wrapped";
            }

            Launch("!");
            Process.Start(Wrap());
        }

        public int Field = 3;

        public void Instance()
        {
            int local = Field;

            int Twice(int n)
            {
                return n * 2;
            }

            Process.Start("/bin/sh", Twice(local).ToString());
        }
    }
}
