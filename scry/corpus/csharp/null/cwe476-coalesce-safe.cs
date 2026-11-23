#nullable enable

namespace NullFixtures
{
    public static class Coalesce
    {
        public static int Length(string? text)
        {
            return text?.Length ?? 0;
        }

        public static string Choose(string? text)
        {
            return text ?? "none";
        }

        public static int Fallback(string? text)
        {
            return (text ?? "none").Length;
        }
    }
}
