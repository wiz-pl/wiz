using System.Data;
using Microsoft.Data.SqlClient;
using ReportService.Models;

namespace ReportService.Provider;

public class SqlReportProvider : IReportProvider
{
    private readonly string _reconConnectionString;
    private readonly string _massCloudApiConnectionString;
    private const string ChainCode = "MPIG";

    public SqlReportProvider(DatabaseConnections settings)
    {
        _reconConnectionString = settings.ReconDatabase;
        // Logic to fallback to MassCloudApi if not explicitly provided
        _massCloudApiConnectionString = !string.IsNullOrWhiteSpace(settings.MassCloudApi)
            ? settings.MassCloudApi
            : new SqlConnectionStringBuilder(_reconConnectionString) { InitialCatalog = "MassCloudApi" }
                .ConnectionString;
    }

    public async Task<List<string>> FetchRrnsAsync(IReadOnlyList<DateOnly> requestedDates)
    {
        var dateParameterNames = requestedDates.Select((_, i) => $"@date{i}").ToArray();
        var sql = $"""
                   SELECT DISTINCT LTRIM(RTRIM([RetrievalReference]))
                   FROM [dbo].[Transactions]
                   WHERE [chain] = @chain
                     AND [SettlementId] IS NULL
                     AND [Success] = 1
                     AND [RetrievalReference] IS NOT NULL
                     AND CAST([DateTime] AS date) IN ({string.Join(", ", dateParameterNames)})
                   """;

        var rrns = new List<string>();
        await using var connection = new SqlConnection(_reconConnectionString);
        await connection.OpenAsync();

        await using var command = new SqlCommand(sql, connection);
        command.Parameters.AddWithValue("@chain", ChainCode);

        for (var i = 0; i < requestedDates.Count; i++)
        {
            command.Parameters.Add($"@date{i}", SqlDbType.Date).Value = requestedDates[i].ToDateTime(TimeOnly.MinValue);
        }

        await using var reader = await command.ExecuteReaderAsync();
        while (await reader.ReadAsync()) rrns.Add(reader.GetString(0));

        return rrns;
    }

    public async Task<DataTable> FetchReportDataAsync(IReadOnlyList<string> rrns)
    {
        var rnnValueParameters = rrns.Select((_, i) => $"(@rrn{i})").ToArray();
        var sql = $"""
                   SET NOCOUNT ON;
                   DECLARE @rrns TransactionIdentifierList;
                   INSERT INTO @rrns (TransactionIdentifier) VALUES {string.Join(",", rnnValueParameters)};
                   EXEC dbo.ReportExtractByRRN @TransactionIds = @rrns;
                   """;

        await using var connection = new SqlConnection(_massCloudApiConnectionString);
        await connection.OpenAsync();

        await using var command = new SqlCommand(sql, connection);
        for (var i = 0; i < rrns.Count; i++)
        {
            command.Parameters.AddWithValue($"@rrn{i}", rrns[i]);
        }

        using var adapter = new SqlDataAdapter(command);
        var dataSet = new DataSet();
        adapter.Fill(dataSet);

        return dataSet.Tables.Cast<DataTable>()
            .LastOrDefault(t => t.Columns.Count > 0) ?? new DataTable();
    }

    public async Task<DataTable> FetchServiceReportDataAsync(int month, int year)
    {
        var sql = @"
        WITH report AS (
            SELECT T.Id, [DateTime], [Chain], [TransactionType],
                   CASE WHEN [Aggregator] IS NULL THEN 'N/A' ELSE [Aggregator] END as Aggregator,
                   PrincipalAmount,
                   CASE WHEN Success = 1 THEN 'Successful' else 'Failed' END as Success,
                   CASE WHEN ServiceMessageType = 'Light' THEN T.Error ELSE T.ResponseCode END Result,
                   ImportSource
            FROM Transactions T WITH (NOLOCK)
            WHERE DATEPART(MONTH, [DateTime]) = @Month
              AND DATEPART(YEAR, [DateTime]) = @Year
              AND ImportSource != 'POS')
        SELECT COUNT(Id) TransactionCount,
               CONVERT(varchar(10), [DateTime], 121) Date,
               Chain, TransactionType Type, Aggregator,
               CAST (SUM([PrincipalAmount]) / 100.00 as MONEY) as 'SumAmount',
               Success, Result, ImportSource
        FROM report
        GROUP BY CONVERT(varchar(10), [DateTime], 121), Aggregator, TransactionType, Chain, Success, ImportSource, Result
        ORDER BY Date, Chain";

        await using var connection = new SqlConnection(_reconConnectionString);
        await using var command = new SqlCommand(sql, connection);
        command.Parameters.AddWithValue("@Month", month);
        command.Parameters.AddWithValue("@Year", year);

        using var adapter = new SqlDataAdapter(command);
        var table = new DataTable();
        adapter.Fill(table);
        return table;
    }

    public async Task<DataTable> FetchVasLightReportAsync(int month, int year)
    {
        // Calculate the start and end of the month in C# to keep the SQL cleaner
        var startDate = new DateTime(year, month, 1, 0, 0, 0, DateTimeKind.Utc);
        var endDate = startDate.AddMonths(1).AddSeconds(-1);

        var sql = """
                      SELECT 
                          FORMAT (DateTime, 'yyyy-MM-dd hh:mm:ss') as [DateTime],
                          Chain,
                          TransactionGuid TransactionId,
                          Store,
                          TerminalId Terminal,
                          RetrievalReference,
                          AlternateRetrievalReference RetrievalReference2,
                          InvoiceId,
                          CASE 
                              WHEN ServiceMessageType = 'EFT' THEN ProductSerialNumber
                              WHEN ServiceMessageType = 'Heavy' THEN PaymentReferenceNo
                              ELSE T.ReceiverReference
                          END ReceiverReference,
                          TransactionType VASType,
                          CASE 
                              WHEN ServiceMessageType = 'Light' THEN ResponseProductId
                              ELSE T.Barcode
                          END Barcode,
                          CASE 
                              WHEN ServiceMessageType = 'Heavy' THEN Aggregator
                              ELSE T.SettlementEntity
                          END SettlementEntity,
                          SettlementId,
                          T.ReceiverName Receiver,
                          CASE 
                              WHEN ServiceMessageType = 'Light' THEN ReceiverId
                              ELSE T.ReceiverReference
                          END ReceiverId,
                          CASE 
                              WHEN ServiceMessageType = 'Heavy' THEN '' 
                              ELSE T.PaymentReferenceNo
                          END PaymentReferenceNo,
                          [PrincipalAmount],
                          CASE 
                              WHEN ServiceMessageType = 'Heavy' THEN T.FeeAmount
                              ELSE 0
                          END FeeAmount,
                          TenderType
                      FROM [Transactions] T WITH (NOLOCK)
                      JOIN Tender WITH (NOLOCK) ON Tender.TransactId = T.Id
                      -- We assume 'ALL' for these filters as per your snippet
                      WHERE T.[DateTime] >= @DateFrom 
                        AND T.[DateTime] <= @DateTo
                        AND Success IN (1, 2)
                        AND ImportSource IN ('POSTILION', 'MASSCLOUD')
                  """;

        await using var connection = new SqlConnection(_reconConnectionString);
        await using var command = new SqlCommand(sql, connection);

        // Using explicit types for DateTimeOffset to match your original script
        command.Parameters.Add("@DateFrom", SqlDbType.DateTimeOffset).Value = (DateTimeOffset)startDate;
        command.Parameters.Add("@DateTo", SqlDbType.DateTimeOffset).Value = (DateTimeOffset)endDate;

        using var adapter = new SqlDataAdapter(command);
        var table = new DataTable("VasLightReport");
        adapter.Fill(table);

        return table;
    }
    
    public async Task<DataTable> GetTransactionStatusAsync(IEnumerable<string> rrns)
    {
        var rrnList = rrns.Distinct().ToList();
        if (!rrnList.Any()) return new DataTable("TransactionStatus");

        // CRITICAL: Aliases must match the Excel Header names exactly
        var sql = $"""
                   SELECT 
                       [DateTime] AS [Transaction Date],
                       [PrincipalAmount] AS [Amount],    
                       [RetrievalReference] AS [RRN],
                       CASE 
                           WHEN [Success] = 1 THEN 'Success'
                           ELSE 'Failed'
                       END AS [Status]                    -- Matches template
                   FROM [dbo].[Transactions] WITH (NOLOCK)
                   WHERE [RetrievalReference] IN ({string.Join(",", rrnList.Select((_, i) => $"@rrn{i}"))})
                   ORDER BY [DateTime] ASC;
                   """;

        await using var connection = new SqlConnection(_reconConnectionString);
        await connection.OpenAsync(); // Ensure connection is open

        await using var command = new SqlCommand(sql, connection);

        for (var i = 0; i < rrnList.Count; i++)
        {
            // Use Trim() to ensure no accidental whitespace causes a mismatch in the DB
            command.Parameters.AddWithValue($"@rrn{i}", rrnList[i].Trim());
        }

        using var adapter = new SqlDataAdapter(command);
        var table = new DataTable("TransactionStatus");
        adapter.Fill(table);

        return table;
    }
}