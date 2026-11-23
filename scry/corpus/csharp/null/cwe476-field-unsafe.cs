#nullable enable

namespace NullFixtures
{
    public sealed class Holder
    {
        public string? Name;

        public int Length()
        {
            return Name.Length;
        }
    }
}
