// A record's and a primary constructor's parameter list implies a constructor: it
// stores each positional parameter into its field, runs the `: Base(…)` call first and
// returns the object. Before this fixture's lowering existed these types produced no
// function at all, so a file of DTO records was "parsed but not lowered".
namespace Fixtures;

public record Money(long MinorUnits, string Currency);

public sealed record Payment(long Amount, string Currency) : Money(Amount, Currency);

public class Base(string tag)
{
    public string Tag { get; } = tag;
}

public sealed class Tagged(string tag) : Base(tag);

public readonly record struct Unit(string Code);
