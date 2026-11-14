package dev.wiz.ide

import com.intellij.lexer.LexerBase
import com.intellij.psi.tree.IElementType

/** A hand-written lexer for Wiz. It is deliberately small: it only has to tokenise
 * enough for syntax highlighting and the no-op PSI tree, not to parse the language. */
class WizLexer : LexerBase() {
    private var buffer: CharSequence = ""
    private var endOffset: Int = 0
    private var tokenStart: Int = 0
    private var tokenEnd: Int = 0
    private var tokenType: IElementType? = null
    private var state: Int = 0
    private var declarationPending: Boolean = false

    override fun start(buffer: CharSequence, startOffset: Int, endOffset: Int, initialState: Int) {
        this.buffer = buffer
        this.endOffset = endOffset
        this.tokenStart = startOffset
        this.tokenEnd = startOffset
        this.tokenType = null
        this.state = initialState
        this.declarationPending = false
    }

    override fun getState(): Int = state

    override fun getTokenType(): IElementType? = tokenType

    override fun getTokenStart(): Int = tokenStart

    override fun getTokenEnd(): Int = tokenEnd

    override fun getBufferSequence(): CharSequence = buffer

    override fun getBufferEnd(): Int = endOffset

    override fun advance() {
        tokenStart = tokenEnd
        if (tokenStart >= endOffset) {
            tokenType = null
            return
        }
        tokenEnd = scanToken()
        val type = tokenType
        if (type == WizTokenTypes.WHITE_SPACE) {
            return
        }
        if (type == WizTokenTypes.COMMENT || type == WizTokenTypes.DOC_COMMENT) {
            declarationPending = false
            return
        }
        if (type == WizTokenTypes.COMMAND) {
            val text = buffer.subSequence(tokenStart, tokenEnd).toString()
            declarationPending = text in DECLARATION_KEYWORDS
            return
        }
        declarationPending = false
    }

    private fun scanToken(): Int {
        val from = tokenStart
        val c = peek(from)

        if (c.isWhitespace()) {
            var i = from + 1
            while (i < endOffset && peek(i).isWhitespace()) i++
            tokenType = WizTokenTypes.WHITE_SPACE
            return i
        }

        if (c == '-' && peek(from + 1) == '-') {
            var i = from + 2
            while (i < endOffset && peek(i) != '\n' && peek(i) != '\r') i++
            tokenType = WizTokenTypes.COMMENT
            return i
        }
        if (c == '/' && peek(from + 1) == '-') {
            val doc = peek(from + 2) == '-'
            tokenType = if (doc) WizTokenTypes.DOC_COMMENT else WizTokenTypes.COMMENT
            return scanBlockComment(from, if (doc) 3 else 2)
        }
        if (c == '"') {
            tokenType = WizTokenTypes.STRING
            return scanString(from)
        }
        if (c == '\'') {
            tokenType = WizTokenTypes.CHAR
            return scanChar(from)
        }
        if (c == 'r' && isRawStringStart(from)) {
            tokenType = WizTokenTypes.RAW_STRING
            return scanRawString(from)
        }
        if (c == '@' && peek(from + 1) == '[') {
            tokenType = WizTokenTypes.BRACKETS
            return from + 2
        }
        if (c == '#') {
            var i = from + 1
            while (i < endOffset && peek(i).isLetter()) i++
            val name = buffer.subSequence(from + 1, i).toString()
            tokenType = if (name in HASH_COMMANDS) WizTokenTypes.COMMAND else WizTokenTypes.OPERATOR
            return if (name in HASH_COMMANDS) i else from + 1
        }
        if (c == '?' && isIdentifierStart(peek(from + 1))) {
            var i = from + 2
            while (i < endOffset && isIdentifierPart(peek(i))) i++
            tokenType = WizTokenTypes.HOLE
            return i
        }
        if (c == '_' && !isIdentifierPart(peek(from + 1))) {
            tokenType = WizTokenTypes.HOLE
            return from + 1
        }
        if (c == '.' && isIdentifierStart(peek(from + 1))) {
            var i = from + 2
            while (i < endOffset && isIdentifierPart(peek(i))) i++
            tokenType = WizTokenTypes.CONSTRUCTOR
            return i
        }
        if (c.isDigit()) {
            tokenType = WizTokenTypes.NUMBER
            return scanNumber(from)
        }
        if (isIdentifierStart(c)) {
            var i = from + 1
            while (i < endOffset && isIdentifierPart(peek(i))) i++
            val text = buffer.subSequence(from, i).toString()
            tokenType = when {
                declarationPending -> WizTokenTypes.DECL_NAME
                text in COMMANDS -> WizTokenTypes.COMMAND
                text in MODIFIERS -> WizTokenTypes.MODIFIER
                text in SORTS -> WizTokenTypes.SORT
                text in TACTICS -> WizTokenTypes.TACTIC
                text in BOOLEANS -> WizTokenTypes.BOOLEAN
                text in KEYWORDS -> WizTokenTypes.KEYWORD
                text.firstOrNull()?.isUpperCase() == true -> WizTokenTypes.TYPE_NAME
                else -> WizTokenTypes.IDENTIFIER
            }
            return i
        }
        if (c in BRACKETS) {
            tokenType = WizTokenTypes.BRACKETS
            return from + 1
        }
        if (!c.isLetterOrDigit()) {
            tokenType = WizTokenTypes.OPERATOR
            return scanOperator(from)
        }
        tokenType = WizTokenTypes.BAD_CHARACTER
        return from + 1
    }

    private fun scanBlockComment(from: Int, startLength: Int): Int {
        var i = from + startLength
        var depth = 1
        while (i < endOffset) {
            if (peek(i) == '/' && peek(i + 1) == '-') {
                depth++
                i += 2
            } else if (peek(i) == '-' && peek(i + 1) == '/') {
                depth--
                i += 2
                if (depth == 0) return i
            } else {
                i++
            }
        }
        return endOffset
    }

    private fun scanString(from: Int): Int {
        var i = from + 1
        while (i < endOffset) {
            when (peek(i)) {
                '\\' -> i += 2
                '"' -> return i + 1
                else -> i++
            }
        }
        return endOffset
    }

    private fun scanChar(from: Int): Int {
        var i = from + 1
        while (i < endOffset) {
            when (peek(i)) {
                '\\' -> i += 2
                '\'' -> return i + 1
                else -> i++
            }
        }
        return endOffset
    }

    private fun isRawStringStart(from: Int): Boolean {
        if (peek(from) != 'r') return false
        var i = from + 1
        while (i < endOffset && peek(i) == '#') i++
        return i < endOffset && peek(i) == '"'
    }

    private fun scanRawString(from: Int): Int {
        var i = from + 1
        var hashes = 0
        while (i < endOffset && peek(i) == '#') {
            hashes++
            i++
        }
        if (i >= endOffset || peek(i) != '"') return i
        i++
        while (i < endOffset) {
            if (peek(i) == '"') {
                var j = i + 1
                var seen = 0
                while (j < endOffset && seen < hashes && peek(j) == '#') {
                    seen++
                    j++
                }
                if (seen == hashes) return j
                i = j
            } else {
                i++
            }
        }
        return endOffset
    }

    private fun scanNumber(from: Int): Int {
        var i = from
        if (peek(i) == '0' && (peek(i + 1) == 'x' || peek(i + 1) == 'X')) {
            i += 2
            while (i < endOffset && peek(i).isLetterOrDigit()) i++
            return i
        }
        while (i < endOffset && peek(i).isDigit()) i++
        if (i < endOffset && peek(i) == '.' && peek(i + 1).isDigit()) {
            i++
            while (i < endOffset && peek(i).isDigit()) i++
        }
        return i
    }

    private fun scanOperator(from: Int): Int {
        var i = from + 1
        while (i < endOffset) {
            val c = peek(i)
            if (c.isWhitespace() || isIdentifierStart(c) || isIdentifierPart(c) || c.isDigit()) break
            if (c == '"' || c == '\'' || c == '?' || c == '.' || c in BRACKETS) break
            if (c == '-' && peek(i + 1) == '-') break
            i++
        }
        return i
    }

    private fun peek(index: Int): Char = if (index in 0 until endOffset) buffer[index] else '\u0000'

    private fun isIdentifierStart(c: Char): Boolean = c == '_' || c.isLetter()

    private fun isIdentifierPart(c: Char): Boolean =
        c == '_' || c == '\'' || c == '!' || c == '?' || c.isLetterOrDigit()

    companion object {
        private val HASH_COMMANDS = setOf("eval", "check", "reduce", "print", "run")

        private val DECLARATION_KEYWORDS = setOf(
            "def", "theorem", "lemma", "abbrev", "axiom", "inductive", "coinductive",
            "codata", "structure", "class", "instance",
        )

        private val COMMANDS = DECLARATION_KEYWORDS + setOf(
            "mutual", "where", "deriving", "extends", "import", "open", "namespace",
            "section", "end", "variable", "universe", "syntax", "macro_rules", "macro",
            "notation", "infixl", "infixr", "infix", "prefix", "postfix",
            "declare_syntax_cat", "attribute", "extern", "export",
        )

        private val MODIFIERS = setOf("private", "partial", "unsafe", "noncomputable", "protected")

        private val SORTS = setOf("Type", "Prop", "Sort")

        private val TACTICS = setOf(
            "intro", "intros", "exact", "apply", "assumption", "rfl", "refl", "rewrite",
            "rw", "cases", "induction", "simp", "absurd", "cast", "transp", "ecase",
            "sorry",
        )

        private val BOOLEANS = setOf("true", "false")

        private val KEYWORDS = setOf(
            "fun", "let", "in", "match", "with", "do", "by", "if", "then", "else",
            "return", "for", "unless", "mut", "at", "have", "show", "from", "calc",
        )

        private val BRACKETS = setOf('(', ')', '[', ']', '{', '}', '⟨', '⟩', '⟦', '⟧')
    }
}
