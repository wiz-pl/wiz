using System;

namespace Repo;

public class Math
{
    public static int Add(int a, int b)
    {
        return a + b;
    }

    public static int Sum(int n)
    {
        int total = 0;
        for (int i = 0; i <= n; i++)
        {
            total = total + i;
        }
        return total;
    }
}
