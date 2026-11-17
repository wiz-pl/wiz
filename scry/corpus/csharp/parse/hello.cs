using System;
using System.Collections.Generic;

namespace Demo
{
    // a comment
    public static class Program
    {
        public static void Main(string[] args)
        {
            var name = args.Length > 0 ? args[0] : "world";
            Console.WriteLine($"Hello, {name}!");
        }
    }
}
