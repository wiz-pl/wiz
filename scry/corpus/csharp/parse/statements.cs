class S
{
    int Run(int[] xs, string path)
    {
        int total = 0;
        for (int i = 0; i < xs.Length; i++) { total += xs[i]; }
        foreach (var x in xs) total -= x;
        while (total > 100) total /= 2;
        do { total++; } while (total < 10);
        if (total == 3) return 1; else if (total == 4) { return 2; }
        switch (total)
        {
            case 1:
            case 2:
                total = 0;
                break;
            default:
                return -1;
        }
        try
        {
            using (var r = new StreamReader(path)) { total = r.Read(); }
        }
        catch (IOException e) when (e.HResult != 0)
        {
            throw;
        }
        catch
        {
            throw new InvalidOperationException("bad");
        }
        finally
        {
            total = -total;
        }
        using var w = File.OpenWrite(path);
        ;
        return total;
    }
}
