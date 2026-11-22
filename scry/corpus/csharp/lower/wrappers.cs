using System;
using System.Diagnostics;

// The wrapper statements whose bodies used to be dropped: `lock`, `fixed`, `checked`,
// `unsafe`, a labelled statement and a preprocessor `#if`/`#elif`/`#else`. Every body is
// lowered as its own block; only the wrapper's *semantics* keeps a warning.
namespace Demo.Wrappers
{
    public unsafe class Wrapped
    {
        public static void Run(string cmd, int[] items)
        {
            object gate = new object();

            lock (gate)
            {
                Process.Start("/bin/sh", cmd);
            }

            fixed (int* p = items)
            {
                Process.Start("/bin/sh", cmd);
            }

            checked
            {
                Console.WriteLine(cmd);
            }

            unsafe
            {
                Console.WriteLine(cmd);
            }

            goto done;

            done:
            Process.Start("/bin/sh", cmd);

#if DEBUG
            Process.Start("/bin/sh", "debug");
#elif RELEASE
            Console.WriteLine("release");
#else
            Console.WriteLine("other");
#endif
        }
    }
}
