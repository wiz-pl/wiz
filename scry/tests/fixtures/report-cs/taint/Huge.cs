// The C# twin of `tests/fixtures/report`, with one file whose tree overflows the
// export's AST cap: `scry cs --bundle` writes at most `Scry.Cs.astFactCap` (2000) `ast`
// rows per file, shallowest first, and the manifest names every file it truncated.
using System;
using System.Diagnostics;

namespace Fixtures;

public class Huge
{
    public static void Run(string input)
    {
        int total = 0;
        total += input.Length * 1 + input.Length * 2 + input.Length * 3 + input.Length * 4;
        total += input.Length * 5 + input.Length * 6 + input.Length * 7 + input.Length * 8;
        total += input.Length * 9 + input.Length * 10 + input.Length * 11 + input.Length * 12;
        total += input.Length * 13 + input.Length * 14 + input.Length * 15 + input.Length * 16;
        total += input.Length * 17 + input.Length * 18 + input.Length * 19 + input.Length * 20;
        total += input.Length * 21 + input.Length * 22 + input.Length * 23 + input.Length * 24;
        total += input.Length * 25 + input.Length * 26 + input.Length * 27 + input.Length * 28;
        total += input.Length * 29 + input.Length * 30 + input.Length * 31 + input.Length * 32;
        total += input.Length * 33 + input.Length * 34 + input.Length * 35 + input.Length * 36;
        total += input.Length * 37 + input.Length * 38 + input.Length * 39 + input.Length * 40;
        total += input.Length * 41 + input.Length * 42 + input.Length * 43 + input.Length * 44;
        total += input.Length * 45 + input.Length * 46 + input.Length * 47 + input.Length * 48;
        total += input.Length * 49 + input.Length * 50 + input.Length * 51 + input.Length * 52;
        total += input.Length * 53 + input.Length * 54 + input.Length * 55 + input.Length * 56;
        total += input.Length * 57 + input.Length * 58 + input.Length * 59 + input.Length * 60;
        total += input.Length * 61 + input.Length * 62 + input.Length * 63 + input.Length * 64;
        total += input.Length * 65 + input.Length * 66 + input.Length * 67 + input.Length * 68;
        total += input.Length * 69 + input.Length * 70 + input.Length * 71 + input.Length * 72;
        total += input.Length * 73 + input.Length * 74 + input.Length * 75 + input.Length * 76;
        total += input.Length * 77 + input.Length * 78 + input.Length * 79 + input.Length * 80;
        total += input.Length * 81 + input.Length * 82 + input.Length * 83 + input.Length * 84;
        total += input.Length * 85 + input.Length * 86 + input.Length * 87 + input.Length * 88;
        total += input.Length * 89 + input.Length * 90 + input.Length * 91 + input.Length * 92;
        total += input.Length * 93 + input.Length * 94 + input.Length * 95 + input.Length * 96;
        total += input.Length * 97 + input.Length * 98 + input.Length * 99 + input.Length * 100;
        total += input.Length * 101 + input.Length * 102 + input.Length * 103 + input.Length * 104;
        total += input.Length * 105 + input.Length * 106 + input.Length * 107 + input.Length * 108;
        total += input.Length * 109 + input.Length * 110 + input.Length * 111 + input.Length * 112;
        total += input.Length * 113 + input.Length * 114 + input.Length * 115 + input.Length * 116;
        total += input.Length * 117 + input.Length * 118 + input.Length * 119 + input.Length * 120;
        total += input.Length * 121 + input.Length * 122 + input.Length * 123 + input.Length * 124;
        total += input.Length * 125 + input.Length * 126 + input.Length * 127 + input.Length * 128;
        total += input.Length * 129 + input.Length * 130 + input.Length * 131 + input.Length * 132;
        total += input.Length * 133 + input.Length * 134 + input.Length * 135 + input.Length * 136;
        total += input.Length * 137 + input.Length * 138 + input.Length * 139 + input.Length * 140;
        total += input.Length * 141 + input.Length * 142 + input.Length * 143 + input.Length * 144;
        total += input.Length * 145 + input.Length * 146 + input.Length * 147 + input.Length * 148;
        total += input.Length * 149 + input.Length * 150 + input.Length * 151 + input.Length * 152;
        total += input.Length * 153 + input.Length * 154 + input.Length * 155 + input.Length * 156;
        total += input.Length * 157 + input.Length * 158 + input.Length * 159 + input.Length * 160;
        total += input.Length * 161 + input.Length * 162 + input.Length * 163 + input.Length * 164;
        var cmd = Console.ReadLine();
        Process.Start(cmd);
        Console.WriteLine(total);
    }
}
