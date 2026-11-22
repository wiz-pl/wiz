#nullable enable

using System.Collections.Generic;

namespace NullFixtures
{
    public static class Models
    {
        public static int AsLength(object value)
        {
            string text = value as string;
            return text.Length;
        }

        public static int FirstLength(List<string> items)
        {
            string text = items.FirstOrDefault();
            return text.Length;
        }
    }
}
