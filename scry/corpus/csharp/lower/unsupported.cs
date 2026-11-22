// Every construct the first slice does not model, in one file: the lowering must
// report each of them by name rather than skip the code silently (the test case
// "silent skip" fails when one of these warnings disappears).
using System;
using System.Collections;
using System.Threading;

namespace Demo.Unsupported;

public delegate int Handler(int value);

public interface IBox
{
    int this[int i] { get; }
}

public class OutOfScope : IEnumerable
{
    public event EventHandler? Changed;
    public int this[int i] => i * 2;

    public static OutOfScope operator +(OutOfScope a, OutOfScope b) => a;

    ~OutOfScope()
    {
    }

    public IEnumerator GetEnumerator()
    {
        yield return 1;
    }
}

public class Control
{
    public static int Apply(Func<int, int> f) => f(1);

    public void Flow(object value)
    {
        static int Local(int x) => x + 1;
        Func<int, int> twice = x => x * 2;
        Func<int, int> unused = x => x + 1;

        value = Local(1) + twice(2) + Apply(x => x * 3);

        lock (this)
        {
            Console.WriteLine(value);
        }

        goto done;

        done:
        if (value is OutOfScope box)
        {
            Console.WriteLine(box);
        }

        // A name declared inside a subpattern is on a path the lowering does not build:
        // it must stay a named warning.
        if (value is OutOfScope { Id: var inner })
        {
            Console.WriteLine(value);
        }

        try
        {
            throw new Exception();
        }
        catch (Exception e) when (e is not null)
        {
            Console.WriteLine(e);
        }
    }
}

#if DEBUG
public class DebugOnly
{
    public void Nothing()
    {
    }
}
#endif
