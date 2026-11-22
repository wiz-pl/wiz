using System;

namespace Demo
{
    // Switch labels and arms: a constant label is compared against the scrutinee (int,
    // string, enum), a typed label binds the scrutinee at the start of the section, a
    // `when` guard is a condition of the section (not decoration), and stacked labels
    // are alternative labels of one section.
    public enum Mode
    {
        Idle,
        Busy,
        Failed,
    }

    public class Router
    {
        public static string IntLabel(int n)
        {
            switch (n)
            {
                case 0:
                    return "zero";
                case 1:
                case 2:
                    return "small";
                default:
                    return "many";
            }
        }

        public static string StringLabel(string s)
        {
            switch (s)
            {
                case "a":
                    return "first";
                case "b":
                    return "second";
                default:
                    return "other";
            }
        }

        public static string EnumLabel(Mode m)
        {
            switch (m)
            {
                case Mode.Idle:
                    return "idle";
                case Mode.Busy:
                    return "busy";
                default:
                    return "down";
            }
        }

        // `case string text:` binds `text` to the scrutinee on the section's true edge,
        // so `text.Length` is `System.String.get_Length(text)`.
        public static int Typed(object o)
        {
            switch (o)
            {
                case string text:
                    return text.Length;
                default:
                    return 0;
            }
        }

        // The guard runs with the label's binding installed: `text.Length` is called
        // only where `o is string text` held, and the section only where the guard held.
        public static string Guarded(object o)
        {
            switch (o)
            {
                case string text when text.Length > 3:
                    return "long";
                case string text:
                    return "short";
                default:
                    return "other";
            }
        }

        public static string Arms(int n) => n switch
        {
            0 => "zero",
            1 or 2 => "small",
            _ => "many",
        };

        public static string ArmBinding(object o) => o switch
        {
            string text when text.Length > 3 => "long " + text,
            string text => "short " + text,
            _ => "other",
        };
    }
}
