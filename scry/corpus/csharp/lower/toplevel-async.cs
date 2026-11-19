// A top-level program with await, return and Environment.Exit: all three live in the
// synthetic `toplevel-async_Program.<Main>$` (C# makes that method async).
using System;
using System.Threading.Tasks;

var input = await Console.In.ReadLineAsync();
if (input is null)
{
    Environment.Exit(2);
}

Console.WriteLine(input);
return;

static void Fail()
{
    Environment.Exit(1);
}

static int Double(int x)
{
    return x * 2;
}
