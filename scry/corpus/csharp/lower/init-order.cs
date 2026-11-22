using System;

// Field and property initialisers run in declaration order: the synthetic `..cctor`
// stores `Counter`, `A`, `B` and `C` in that order (B reads A, and the Tick calls are
// visible in the body), and every constructor runs the instance initialisers after the
// base call and before its body. A `: this()` constructor leaves them to its target, so
// `Ordered(int)` does not run them twice. `D` reads `E`, which is initialised later: that
// is the one shape the lowering cannot order, so it keeps a named warning.
namespace Demo.InitOrder
{
    public class Ordered
    {
        private int counter = 1;
        private string suffix = "!";
        public string Label { get; } = "label";

        public Ordered()
        {
            suffix = suffix + "?";
        }

        public Ordered(int seed) : this()
        {
            counter = counter + seed;
        }

        private static int Counter = 0;
        public static int A = Tick(2);
        public static int B = A * 10;
        public static int C = Tick(B + 1);
        public static int D = E + 1;
        public static int E = Tick(5);

        private static int Tick(int n)
        {
            Counter = Counter + 1;
            return n;
        }
    }
}
