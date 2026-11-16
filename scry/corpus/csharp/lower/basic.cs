using System;

namespace Demo
{
    public class Counter
    {
        private int count;
        public string Name { get; set; }

        public Counter(string name)
        {
            Name = name;
            count = 0;
        }

        public int Bump(int by)
        {
            count += by;
            return count;
        }
    }

    public static class Calc
    {
        public static int Sum(int n)
        {
            int total = 0;
            for (int i = 0; i < n; i++)
            {
                if (i % 2 == 0 && i > 100) { continue; }
                total += i;
            }
            return total;
        }

        public static int Fact(int n) => n <= 1 ? 1 : n * Fact(n - 1);

        public static string Greet(string who)
        {
            var c = new Counter(who);
            c.Bump(2);
            try
            {
                Console.WriteLine($"hi {c.Name}");
            }
            catch (Exception e)
            {
                Console.Error.WriteLine(e.Message);
                throw;
            }
            return "hello " + who;
        }
    }
}
