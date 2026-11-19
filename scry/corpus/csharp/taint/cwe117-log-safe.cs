using Microsoft.Extensions.Logging;

namespace Fixtures;

// The safe twin: the same entry parameter, but the log line is a constant, so nothing
// attacker-controlled reaches the log.
public sealed class LoggerSafe
{
    public void Record(string user, ILogger logger)
    {
        logger.LogWarning("Login seen; the user is not written to the line.");
    }
}
