using System;
using System.Threading.Tasks;

namespace Fixtures.Hosting;

public interface IRecordStore
{
    Task<string?> FindAsync(string name);
    Task AddAsync(string name, string value);
}

public sealed class RecordSeeder
{
    private readonly IRecordStore _store;

    public RecordSeeder(IRecordStore store)
    {
        _store = store;
    }

    public async Task RunAsync(string[] args)
    {
        if (args.Length == 0)
        {
            return;
        }

        var store = _store;
        var existing = await store.FindAsync(args[0]);
        if (existing is null)
        {
            await EnsureAsync(store, args[0], "pending");
        }
    }

    public static async Task EnsureAsync(IRecordStore store, string name, string value)
    {
        var existing = await store.FindAsync(name);
        if (existing is null)
        {
            await store.AddAsync(name, value);
        }
    }
}
