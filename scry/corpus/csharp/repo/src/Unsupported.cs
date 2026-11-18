using System;
using System.Linq;

namespace Repo
{
    public class Unsupported
    {
        public static int Count(int[] items)
        {
            Func<int, int> twice = x => x * 2;
            var positive = from x in items where x > 0 select x;
            return items.Length;
        }
    }
}
