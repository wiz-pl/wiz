#nullable enable

namespace NullFixtures
{
    public static class Guarded
    {
        public static int Length(string? text)
        {
            if (text != null)
            {
                return text.Length;
            }
            return 0;
        }

        public static int LengthIs(string? text)
        {
            if (text is not null)
            {
                return text.Length;
            }
            return 0;
        }

        public static int Cast(string? text)
        {
            if (text is string value)
            {
                return value.Length;
            }
            return 0;
        }
    }
}
