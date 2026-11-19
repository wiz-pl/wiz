using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.Hosting;
using Crux.Dashboard.Api.Dtos;

namespace Crux.Dashboard.Api.LogViewer;

public sealed class LogFileReader
{
    public const long DefaultMaxBytes = 1L * 1024 * 1024;

    public const long HardMaxBytes = 8L * 1024 * 1024;

    private static readonly Regex SegmentPattern = new("^[A-Za-z0-9._-]+$", RegexOptions.Compiled);
    private static readonly Regex DateInName = new(@"(\d{4})(\d{2})(\d{2})", RegexOptions.Compiled);

    private readonly string _root;

    public LogFileReader(string root) => _root = root;

    public static string ResolveRoot(IHostEnvironment env, IConfiguration config)
    {
        var configured = config["LogViewer:RootPath"];
        if (!string.IsNullOrWhiteSpace(configured)) return configured;
        var contentRoot = Path.TrimEndingDirectorySeparator(env.ContentRootPath);
        var installRoot = Directory.GetParent(contentRoot)?.FullName ?? contentRoot;
        return Path.Combine(installRoot, "Logs");
    }

    public IReadOnlyList<LogServiceDto> ListServices()
    {
        if (!Directory.Exists(_root)) return [];
        var result = new List<LogServiceDto>();
        foreach (var dir in Directory.EnumerateDirectories(_root))
        {
            var files = LogFilesIn(dir);
            if (files.Count == 0) continue;
            result.Add(new LogServiceDto(
                Path.GetFileName(dir),
                files.Count,
                files.Sum(f => f.Length),
                files.Max(f => (DateTimeOffset?)f.LastWriteTimeUtc)));
        }
        return result.OrderBy(s => s.Service, StringComparer.OrdinalIgnoreCase).ToList();
    }

    public IReadOnlyList<LogFileDto>? ListFiles(string service)
    {
        var dir = ResolveServiceDir(service);
        if (dir is null) return null;
        return LogFilesIn(dir)
            .OrderByDescending(f => f.Name, StringComparer.OrdinalIgnoreCase)
            .Select(f => new LogFileDto(f.Name, DateKey(f), f.Length, f.LastWriteTimeUtc))
            .ToList();
    }

    public LogContentDto? Read(string service, string file, long? maxBytes, long? sinceOffset = null)
    {
        var fi = Resolve(service, file);
        if (fi is null) return null;

        using var fs = new FileStream(fi.FullName, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
        return ReadFrom(
            fs,
            Path.GetFileName(Path.GetDirectoryName(fi.FullName)!),
            fi.Name,
            fi.LastWriteTimeUtc,
            maxBytes,
            sinceOffset);
    }

    internal static LogContentDto ReadFrom(
        Stream fs, string service, string file, DateTimeOffset lastWriteUtc, long? maxBytes, long? sinceOffset)
    {
        var cap = Math.Clamp(maxBytes ?? DefaultMaxBytes, 4096, HardMaxBytes);
        var total = fs.Length;

        bool honoured = sinceOffset is long s && s >= 0 && s <= total && (total - s) <= cap;
        long start = honoured ? sinceOffset!.Value : Math.Max(0, total - cap);
        bool reset = sinceOffset.HasValue && !honoured;
        bool truncated = start > 0;

        if (start > 0) fs.Seek(start, SeekOrigin.Begin);
        var bytes = new byte[total - start];
        fs.ReadExactly(bytes);
        using var reader = new StreamReader(new MemoryStream(bytes), Encoding.UTF8, detectEncodingFromByteOrderMarks: true);
        var text = reader.ReadToEnd();

        if (truncated && !honoured)
        {
            var nl = text.IndexOf('\n');
            text = nl >= 0 && nl + 1 <= text.Length ? text[(nl + 1)..] : text;
        }

        return new LogContentDto(
            service,
            file,
            total,
            start,
            Encoding.UTF8.GetByteCount(text),
            truncated,
            reset,
            lastWriteUtc,
            text);
    }

    public FileInfo? Resolve(string service, string file)
    {
        var dir = ResolveServiceDir(service);
        if (dir is null) return null;
        if (!IsSegment(file) || !file.EndsWith(".log", StringComparison.OrdinalIgnoreCase)) return null;

        var full = Path.GetFullPath(Path.Combine(dir, file));
        if (!PathEquals(Path.GetDirectoryName(full), dir)) return null;

        var fi = new FileInfo(full);
        return fi.Exists ? fi : null;
    }

    private string? ResolveServiceDir(string service)
    {
        if (!Directory.Exists(_root) || !IsSegment(service)) return null;
        foreach (var dir in Directory.EnumerateDirectories(_root))
            if (string.Equals(Path.GetFileName(dir), service, StringComparison.OrdinalIgnoreCase))
                return Path.GetFullPath(dir);
        return null;
    }

    private static List<FileInfo> LogFilesIn(string dir) =>
        [.. new DirectoryInfo(dir).EnumerateFiles("*.log", SearchOption.TopDirectoryOnly)];

    private static bool IsSegment(string s) =>
        !string.IsNullOrWhiteSpace(s) && s.Length <= 128
        && s is not "." and not ".." && SegmentPattern.IsMatch(s);

    private static bool PathEquals(string? a, string? b) =>
        a is not null && b is not null
        && string.Equals(a.TrimEnd(Path.DirectorySeparatorChar), b.TrimEnd(Path.DirectorySeparatorChar),
            StringComparison.OrdinalIgnoreCase);

    private static string DateKey(FileInfo f)
    {
        var m = DateInName.Match(f.Name);
        return m.Success
            ? $"{m.Groups[1].Value}-{m.Groups[2].Value}-{m.Groups[3].Value}"
            : f.LastWriteTimeUtc.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture);
    }
}
