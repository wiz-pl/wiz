using System;
using System.Diagnostics;

namespace Fixtures
{
    // A switch section's typed label binds the scrutinee, and the binding carries its
    // taint into the section: the console line reaches `Process.Start` only through
    // `case string command:`. The `when` guard is evaluated after the binding is
    // installed (so taint in the guard reaches the guarded code too).
    public class SwitchGate
    {
        public static void Run()
        {
            object input = Console.ReadLine();
            switch (input)
            {
                case string command when command.Length > 0:
                    Process.Start("sh", command);
                    break;
                default:
                    break;
            }
        }

        public static void RunExpression()
        {
            object input = Console.ReadLine();
            var run = input switch
            {
                string command => Process.Start("sh", command),
                _ => null,
            };
        }
    }
}
