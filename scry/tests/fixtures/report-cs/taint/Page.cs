using System;
using System.Diagnostics;

namespace Fixtures;

// The same shape as the C fixture `report/xss.c`: the sink is real and the markup sits
// in the source, so the reader's page must escape it, not run it.
public class Page
{
    public static string Render()
    {
        var cmd = Console.ReadLine();
        const string html = "<script>alert('x&y')</script></style>";
        Process.Start(cmd); /* <script>alert(1)</script> & "quoted" */
        return html;
    }
}
