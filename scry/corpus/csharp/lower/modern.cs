// The shape of a real endpoint file: a record DTO, a partial service class, a switch
// expression, LINQ, collection expressions, `with`, async/await and a local function.
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading.Tasks;
using static System.Math;

namespace Crux.Api.Endpoints;

#nullable enable

/// <summary>What a payout request carries.</summary>
[Serializable]
public record PayoutRequest(string Account, long AmountMinorUnits, string? Reference = null);

public readonly record struct PayoutResult(int Status, string Detail)
{
    public bool Accepted => Status is 202 or 200;
}

public interface IPayments
{
    Task<PayoutResult> SubmitAsync(PayoutRequest request);

    // A default interface method (C# 8).
    string Describe(PayoutRequest request) => $"payout {request.Account}";
}

public abstract class PaymentBase
{
    protected abstract string Route { get; }

    public virtual PayoutResult Reject(string detail) => new(422, detail);
}

public sealed partial class PayoutService : PaymentBase, IPayments
{
    private readonly List<string> _trace = new();
    private static readonly string[] Refusals = ["ValidationFailed", "InsufficientFunds"];

    public string Account { get; }
    public int Retries { get; init; }
    public string? LastError { get; private set; }

    // Expression-bodied members.
    public int Count => _trace.Count;
    protected override string Route => "payouts";

    public PayoutService(string account) : base()
    {
        Account = account;
    }

    public static T? Find<T>(IEnumerable<T> items) where T : class, new()
        => items.FirstOrDefault() ?? new T();

    public async Task<PayoutResult> SubmitAsync(PayoutRequest request)
    {
        await Task.Yield();

        var words = request.Account.Split('-');
        var magnitude = Abs(request.AmountMinorUnits);
        var parts =
            from w in words
            where w.Length > 1
            select w.ToUpperInvariant();

        var route = request.AmountMinorUnits switch
        {
            0 => "zero",
            _ when request.Reference is not null => $"by-ref {request.Reference}",
            _ => "by-account",
        };

        var copy = request with { Reference = route };
        var refusals = [.. Refusals, "KycNotVerified"];
        _trace.Add(route + string.Join('/', parts) + copy.Reference + refusals.Length
            + magnitude.ToString());
        return new PayoutResult(202, route);
    }

    public override string ToString()
    {
        static string Label(string s) => $"[{s}]";
        return Label(Account);
    }
}

public sealed partial class PayoutService
{
    [Obsolete("use SubmitAsync")]
    public PayoutResult Submit(PayoutRequest request) => Reject(request.Account);
}
