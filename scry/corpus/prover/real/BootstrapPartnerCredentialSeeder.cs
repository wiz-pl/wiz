using Microsoft.EntityFrameworkCore;
using Crux.Application.Identity;
using Crux.Domain.Identity;
using Crux.Hosting.Supervision;
using Crux.Infrastructure.Persistence;
using Crux.Infrastructure.Configuration;
using Crux.Infrastructure.Security;

namespace Crux.Api.Hosting;

internal static class BootstrapPartnerCredentialSeeder
{
    public const string CliFlag = "--issue-partner";
    internal const string SecretVariable = "CRUX_PARTNER_SECRET";

    public static bool Requested(string[] args) =>
        args.Any(a => string.Equals(a, CliFlag, StringComparison.OrdinalIgnoreCase));

    internal static (string? Username, string? Secret) ReadRequest(string[] args, Func<string, string?> environment) =>
        (CommandLine.ArgValue(args, "--username")?.Trim(), environment(SecretVariable));

    public static async Task RunAsync(WebApplication app, string[] args, TextWriter output, TextWriter error)
    {
        var logger = app.Services.GetRequiredService<ILoggerFactory>()
            .CreateLogger("Crux.Api.BootstrapPartnerCredentialSeeder");

        var (username, secret) = ReadRequest(args, Environment.GetEnvironmentVariable);

        if (string.IsNullOrWhiteSpace(username) || string.IsNullOrWhiteSpace(secret))
        {
            logger.LogError("Usage: set {Variable}, then run Crux.Api {Flag} --username <username>.", SecretVariable, CliFlag);
            await error.WriteLineAsync($"Usage: set {SecretVariable}, then run Crux.Api {CliFlag} --username <username>.");
            Environment.ExitCode = 2;
            return;
        }

        using var scope = app.Services.CreateScope();
        var db = scope.ServiceProvider.GetRequiredService<CruxDbContext>();
        if (!db.Database.IsRelational())
        {
            logger.LogError("{Flag} requires a relational database; aborting.", CliFlag);
            await error.WriteLineAsync($"{CliFlag} requires a relational database; aborting.");
            Environment.ExitCode = 2;
            return;
        }

        var credentials = scope.ServiceProvider.GetRequiredService<IApiCredentialRepository>();
        var hasher = scope.ServiceProvider.GetRequiredService<CredentialHasher<ApiCredential>>();
        var clock = scope.ServiceProvider.GetRequiredService<TimeProvider>();
        var tenantId = CruxDbConfigurationBuilderExtensions.ResolveBootstrapTenantId(app.Configuration);

        var issuerPartyId = await db.Parties
            .InstitutionOf(tenantId)
            .Select(p => p.Id)
            .FirstOrDefaultAsync();
        if (issuerPartyId == Guid.Empty)
        {
            logger.LogError(
                "Tenant {TenantId} has no institution party, so a partner credential has nothing to act for.", tenantId);
            await error.WriteLineAsync(
                $"Tenant {tenantId} has no institution party, so a partner credential has nothing to act for.");
            Environment.ExitCode = 2;
            return;
        }

        var outcome = await EnsureAsync(
            credentials, hasher, clock, tenantId, issuerPartyId, username, secret);
        if (outcome == Outcome.HeldByAnotherTenant || outcome == Outcome.Revoked)
        {
            logger.LogError(
                "Partner credential '{Username}' was left unchanged: {Reason}",
                username,
                outcome == Outcome.HeldByAnotherTenant
                    ? "another tenant holds the username, and partner usernames are unique across the estate."
                    : "the credential is revoked; issue a new username.");
            Environment.ExitCode = 2;
            return;
        }

        await db.SaveChangesAsync(CancellationToken.None);

        var action = outcome == Outcome.Issued ? "issued" : "rotated";
        logger.LogWarning(
            "Partner credential '{Username}' {Action} for tenant {TenantId}. " +
            "Remove {Variable} from the environment now.",
            username, action, tenantId, SecretVariable);
        await output.WriteLineAsync(
            $"Partner credential '{username}' {action} for tenant {tenantId}. Remove {SecretVariable} from the environment now.");
    }

    internal enum Outcome { Issued, Rotated, HeldByAnotherTenant, Revoked }

    internal static async Task<Outcome> EnsureAsync(
        IApiCredentialRepository credentials,
        CredentialHasher<ApiCredential> hasher,
        TimeProvider clock,
        Guid tenantId,
        Guid issuerPartyId,
        string username,
        string secret)
    {
        var existing = await credentials
            .FindByUsernameAsync(username, CancellationToken.None)
            .ConfigureAwait(false);
        if (existing is not null)
        {
            if (existing.TenantId != tenantId) return Outcome.HeldByAnotherTenant;
            if (!existing.IsActive) return Outcome.Revoked;
            var tracked = await credentials.GetAsync(existing.Id, CancellationToken.None)
                .ConfigureAwait(false) ?? existing;
            tracked.Rotate(hasher.Hash(tracked, secret), clock);
            return Outcome.Rotated;
        }

        var credential = ApiCredential.Issue(tenantId, issuerPartyId, username, "_pending", clock);
        credential.Rotate(hasher.Hash(credential, secret), clock);
        credentials.Add(credential);
        return Outcome.Issued;
    }
}
