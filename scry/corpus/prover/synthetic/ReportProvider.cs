using System;
using System.Collections.Generic;
using System.Data;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Data.SqlClient;

namespace Fixtures.Data;

public sealed class ReportProvider
{
    private readonly string _connectionString;

    public ReportProvider(string connectionString)
    {
        _connectionString = connectionString;
    }

    public async Task<List<string>> FetchAsync(IReadOnlyList<DateOnly> requestedDates)
    {
        var names = requestedDates.Select((_, i) => $"@date{i}").ToArray();
        var sql = $"""
                   SELECT [Reference]
                   FROM [dbo].[Records]
                   WHERE [Chain] = @chain
                     AND [Reference] IN ({string.Join(", ", names)})
                   """;

        var result = new List<string>();
        await using var connection = new SqlConnection(_connectionString);
        await connection.OpenAsync();

        await using var command = new SqlCommand(sql, connection);
        command.Parameters.AddWithValue("@chain", "FIX");
        for (var i = 0; i < requestedDates.Count; i++)
        {
            command.Parameters.Add($"@date{i}", SqlDbType.Date).Value =
                requestedDates[i].ToDateTime(TimeOnly.MinValue);
        }

        await using var reader = await command.ExecuteReaderAsync();
        while (await reader.ReadAsync())
        {
            result.Add(reader.GetString(0));
        }
        return result;
    }
}
