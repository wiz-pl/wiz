using System.IO;
using System.Threading.Tasks;
using Microsoft.AspNetCore.Http;

namespace Fixtures.Requests;

public interface IEventProcessor
{
    Task ProcessAsync(string payload);
}

public sealed class EventEndpoint
{
    public async Task HandleAsync(HttpRequest request, IEventProcessor processor)
    {
        var signature = request.Headers["X-Signature"].ToString();
        if (signature.Length == 0)
        {
            return;
        }

        var body = await new StreamReader(request.Body).ReadToEndAsync();
        var payload = body.Trim();
        await processor.ProcessAsync(payload);
    }
}
