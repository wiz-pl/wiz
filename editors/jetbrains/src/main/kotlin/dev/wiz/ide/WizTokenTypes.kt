package dev.wiz.ide

import com.intellij.psi.tree.IElementType

class WizTokenType(debugName: String) : IElementType(debugName, WizLanguage)

/** The tokens of editors/jetbrains/src/main/kotlin/dev/wiz/ide/WizLexer.kt. The lexer
 * assigns the categories; the syntax highlighter maps them to colours. */
object WizTokenTypes {
    @JvmField val WHITE_SPACE = WizTokenType("WHITE_SPACE")
    @JvmField val COMMENT = WizTokenType("COMMENT")
    @JvmField val DOC_COMMENT = WizTokenType("DOC_COMMENT")
    @JvmField val STRING = WizTokenType("STRING")
    @JvmField val RAW_STRING = WizTokenType("RAW_STRING")
    @JvmField val CHAR = WizTokenType("CHAR")
    @JvmField val NUMBER = WizTokenType("NUMBER")
    @JvmField val KEYWORD = WizTokenType("KEYWORD")
    @JvmField val COMMAND = WizTokenType("COMMAND")
    @JvmField val MODIFIER = WizTokenType("MODIFIER")
    @JvmField val SORT = WizTokenType("SORT")
    @JvmField val TACTIC = WizTokenType("TACTIC")
    @JvmField val BOOLEAN = WizTokenType("BOOLEAN")
    @JvmField val DECL_NAME = WizTokenType("DECL_NAME")
    @JvmField val IDENTIFIER = WizTokenType("IDENTIFIER")
    @JvmField val CONSTRUCTOR = WizTokenType("CONSTRUCTOR")
    @JvmField val TYPE_NAME = WizTokenType("TYPE_NAME")
    @JvmField val HOLE = WizTokenType("HOLE")
    @JvmField val OPERATOR = WizTokenType("OPERATOR")
    @JvmField val BRACKETS = WizTokenType("BRACKETS")
    @JvmField val TODO = WizTokenType("TODO")
    @JvmField val BAD_CHARACTER = WizTokenType("BAD_CHARACTER")
}
