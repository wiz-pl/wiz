namespace Project;

public static class Program
{
    public static void Main()
    {
        string a = Input.Read();
        Sink.Run(a);
    }

    public static void Run()
    {
        string b = Input.Read();
        b.Exec();
    }

    public static void Safe()
    {
        string c = Input.Read();
        System.Console.WriteLine(c.Count(1));
    }
}
