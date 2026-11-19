using System;
using System.Diagnostics;

// Ported from Joern's TopLevelStatementTests (csharpsrc2cpg): a top-level statement
// belongs to a fictitious `<Main>$` in a `<file>_Program` class. scry has no such
// entry point, so the whole file is invisible to the analysis.
Console.WriteLine("Foo");
Process.Start("/bin/sh", Console.ReadLine());
