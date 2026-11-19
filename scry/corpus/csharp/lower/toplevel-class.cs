// Top-level statements followed by a type in a namespace: the declarations after the
// statements keep their own scope (`Geometry.Point`, not a member of the synthetic
// `toplevel-class_Program`).
using System;

var origin = new Geometry.Point(3, 4);
Console.WriteLine($"{origin.X},{origin.Y}");

namespace Geometry
{
    public sealed class Point
    {
        public int X { get; }
        public int Y { get; }

        public Point(int x, int y)
        {
            X = x;
            Y = y;
        }
    }
}
