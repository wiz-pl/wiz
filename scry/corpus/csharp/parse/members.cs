namespace Demo.Members;

#nullable enable
[Serializable]
public sealed class Account<T> : Base, IComparable<Account<T>> where T : class
{
    private readonly int _id = 0, _count;
    public string? Owner { get; set; }
    public int Id => _id;
    public List<List<int>> Grid { get; } = new List<List<int>>();
    public decimal Balance
    {
        get { return balance; }
        private set { balance = value; }
    }

    public Account(int id, string owner) : base(owner)
    {
        _id = id;
    }

    public static T? Find<U>(IEnumerable<U> items, Func<U, bool> pred) where U : notnull => default;

    public abstract void Close();
}

public enum Color { Red, Green = 2, Blue }

struct Point { public int X; public int Y; }

interface IShape { double Area(); }
