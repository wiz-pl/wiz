using System.Diagnostics;

namespace Project;

public static class ShellExtensions
{
    public static void Exec(this string cmd)
    {
        Process.Start("/bin/sh", cmd);
    }

    public static int Count(this string s, int n)
    {
        return n;
    }

    public static T Identity<T>(this T x)
    {
        return x;
    }
}
