class E
{
    object M(object o, int a, int b)
    {
        int c = a + b * 2 - (a - b) % 3 << 1 >> 2;
        bool d = a < b && b <= c || !(a == c) ^ true;
        var s = o as string ?? "none";
        var n = (int)o + (long)a;
        var t = (a) - b;
        var u = o is string str ? str.Length : -1;
        var v = o is not null;
        var arr = new int[a];
        var arr2 = new[] { 1, 2, 3 };
        var arr3 = new string[] { "x", @"c:\dir", 'q'.ToString() };
        var list = new List<string> { "a", "b" };
        var p = new Point { X = 1, Y = 2 };
        Func<int, int> f = x => x * 2;
        Func<int, int, int> g = (x, y) => { return x + y; };
        var r = Enumerable.Empty<int>().Count();
        c += f(a)[0]?.Length ?? 0;
        c >>= 1;
        a = b = c;
        var q = typeof(string);
        var z = default(int);
        var w = s!.Length;
        var i = $"{a,5} and {b:N2} and {{literal}} {s.Substring(0, 1)}";
        var vi = $@"C:\{s}\x";
        Helper(ref a, out var k, out int k2, name: "x");
        return a++ + --b;
    }
}
