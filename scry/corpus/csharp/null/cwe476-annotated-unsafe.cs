#nullable enable

namespace NullFixtures
{
    public static class Violation
    {
        public static int Length()
        {
            string text = null;
            return text.Length;
        }
    }
}
