using System;
using static System.Math;

namespace Demo.Modern;

public record Point(int X, int Y);

public class Shapes
{
    public string Label(int n) => n switch
    {
        0 => "zero",
        _ => $"n={n}",
    };

    public Point Move(Point p) => p with { X = p.X + 1 };

    public int[] Sizes() => [1, 2, 3];

    public string Join(string[] parts) =>
        string.Join(',', from p in parts where p.Length > 0 select p.Trim());
}
