#region tokens
var x = 0x1F + 42L - 3.5e-2 * .5f; // comment
/* block
   comment */ string s = @"C:\a ""q""" + "t\"\n" + 'c' + '\'';
var i = $"a{x,3}b{{c}}{s.Length:N2}" + $@"\{s}\";
if (a >= b && c?.d ?? e) { List<List<int>> l; }
@class = a << 2 >>= 1;
#endregion
