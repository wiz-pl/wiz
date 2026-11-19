using System;

namespace Demo
{
    // `is` tests and pattern bindings: `o is string s` declares `s` on the true edge of
    // the runtime type test, `o is null` / `o is not null` are comparisons, and
    // `o is int n ? n : 0` binds `n` in the consequence only.
    public class Match
    {
        public static int Length(object o)
        {
            if (o is string s)
            {
                return s.Length;
            }
            return -1;
        }

        public static bool IsNull(object o)
        {
            return o is null;
        }

        public static bool NotNull(object o)
        {
            return o is not null;
        }

        public static bool TypeTest(object o)
        {
            return o is string;
        }

        public static int Guarded(object o)
        {
            var n = o is int k ? k : 0;
            return n;
        }

        // `is not T x`: x is the operand on the *false* edge, so the else branch and
        // the code after the join see it.
        public static string OrNone(object o)
        {
            if (o is not string s)
            {
                return "none";
            }
            return s;
        }

        // The same binding under `!` (the test is inverted, so its edge is swapped).
        public static string NotEither(object o)
        {
            if (!(o is string t))
            {
                return "none";
            }
            return t;
        }
    }
}
