using Microsoft.Extensions.Logging;

namespace Fixtures;

// CWE-117: a log line carries a parameter of a public entry method. The method has no
// caller in the analysed unit, so `Scry.analyzeC` seeds its parameters (the entry
// policy) and the log model makes `ILogger.LogWarning` a sink at its data arguments.
public sealed class Logger
{
    public void Record(string user, ILogger logger)
    {
        logger.LogWarning("Login from {User}", user);
    }
}
