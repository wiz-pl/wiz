#nullable enable

namespace NullFixtures
{
    public static class Forgiving
    {
        public static int Length(string? text)
        {
            return text!.Length;
        }
    }
}
