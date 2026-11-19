using System.IO;
using Microsoft.AspNetCore.Http;

namespace ProverDogfood
{
    // A helper written for the dogfood run: the fifth proof isolates the proof
    // language from the real code's lowering. SafeWrite sanitises the file name with
    // Path.GetFileName; UnsafeWrite splices the header value into the path.
    public static class Files
    {
        public static void SafeWrite(HttpRequest request)
        {
            string raw = request.Headers["X-File"];
            string name = Path.GetFileName(raw);
            string path = Path.Combine("/tmp/prover-dogfood", name);
            File.WriteAllText(path, "ok");
        }

        public static void UnsafeWrite(HttpRequest request)
        {
            string raw = request.Headers["X-File"];
            string path = Path.Combine("/tmp/prover-dogfood", raw);
            File.WriteAllText(path, "ok");
        }
    }
}
