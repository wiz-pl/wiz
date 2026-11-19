// A multibyte character before a token: the em dash (—) and the section sign (§)
// take three and two UTF-8 bytes, so tree-sitter's byte offsets run ahead of the
// character indices a Wiz String is sliced by.
class Unicode
{
    int Describe(int value)
    {
        int outcome = value + 1;
        // — § before the next token: `outcome` is declared above this line and used
        // below it, so a byte/character mix-up truncates the use but not the declaration.
        return outcome + Missing;
    }
}
