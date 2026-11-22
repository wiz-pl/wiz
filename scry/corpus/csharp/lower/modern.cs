// The shape of a real endpoint file: a record DTO, a partial service class, a switch
// expression, LINQ, collection expressions, `with`, async/await and a local function.
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading.Tasks;
using static System.Math;

namespace Fixtures.Modern;

#nullable enable

/// <summary>What a work request carries.</summary>
[Serializable]
public record WorkRequest(string Name, long Count, string? Label = null);

public readonly record struct WorkResult(int Status, string Detail)
{
    public bool Accepted => Status is 202 or 200;
}

public interface IWorkService
{
    Task<WorkResult> SubmitAsync(WorkRequest request);

    // A default interface method (C# 8).
    string Describe(WorkRequest request) => $"work {request.Name}";
}

public abstract class ServiceBase
{
    protected abstract string Route { get; }

    public virtual WorkResult Reject(string detail) => new(422, detail);
}

public sealed partial class WorkService : ServiceBase, IWorkService
{
    private readonly List<string> _trace = new();
    private static readonly string[] Limits = ["Invalid", "OverLimit"];

    public string Name { get; }
    public int Retries { get; init; }
    public string? LastError { get; private set; }

    // Expression-bodied members.
    public int Count => _trace.Count;
    protected override string Route => "work";

    public WorkService(string name) : base()
    {
        Name = name;
    }

    public static T? Find<T>(IEnumerable<T> items) where T : class, new()
        => items.FirstOrDefault() ?? new T();

    public async Task<WorkResult> SubmitAsync(WorkRequest request)
    {
        await Task.Yield();

        var words = request.Name.Split('-');
        var magnitude = Abs(request.Count);
        var parts =
            from w in words
            where w.Length > 1
            select w.ToUpperInvariant();

        var route = request.Count switch
        {
            0 => "zero",
            _ when request.Label is not null => $"by-label {request.Label}",
            _ => "by-name",
        };

        var copy = request with { Label = route };
        var extras = [.. Limits, "NotReady"];
        _trace.Add(route + string.Join('/', parts) + copy.Label + extras.Length
            + magnitude.ToString());
        return new WorkResult(202, route);
    }

    public override string ToString()
    {
        static string Label(string s) => $"[{s}]";
        return Label(Name);
    }
}

public sealed partial class WorkService
{
    [Obsolete("use SubmitAsync")]
    public WorkResult Submit(WorkRequest request) => Reject(request.Name);
}
