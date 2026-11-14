package dev.wiz.ide

import com.intellij.lexer.Lexer
import com.intellij.openapi.editor.DefaultLanguageHighlighterColors
import com.intellij.openapi.editor.HighlighterColors
import com.intellij.openapi.editor.colors.TextAttributesKey
import com.intellij.openapi.fileTypes.SyntaxHighlighter
import com.intellij.openapi.fileTypes.SyntaxHighlighterBase
import com.intellij.openapi.fileTypes.SyntaxHighlighterFactory
import com.intellij.openapi.project.Project
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.psi.tree.IElementType

object WizTextAttributes {
    @JvmField
    val HOLE: TextAttributesKey =
        TextAttributesKey.createTextAttributesKey("WIZ_HOLE", DefaultLanguageHighlighterColors.INSTANCE_FIELD)

    @JvmField
    val CONSTRUCTOR: TextAttributesKey =
        TextAttributesKey.createTextAttributesKey("WIZ_CONSTRUCTOR", DefaultLanguageHighlighterColors.STATIC_FIELD)
}

class WizSyntaxHighlighter : SyntaxHighlighterBase() {
    override fun getHighlightingLexer(): Lexer = WizLexer()

    override fun getTokenHighlights(tokenType: IElementType?): Array<TextAttributesKey> =
        when (tokenType) {
            WizTokenTypes.KEYWORD,
            WizTokenTypes.COMMAND,
            WizTokenTypes.MODIFIER,
            WizTokenTypes.TACTIC -> arrayOf(DefaultLanguageHighlighterColors.KEYWORD)

            WizTokenTypes.SORT -> arrayOf(DefaultLanguageHighlighterColors.KEYWORD)
            WizTokenTypes.BOOLEAN -> arrayOf(DefaultLanguageHighlighterColors.CONSTANT)
            WizTokenTypes.DECL_NAME -> arrayOf(DefaultLanguageHighlighterColors.FUNCTION_DECLARATION)
            WizTokenTypes.CONSTRUCTOR -> arrayOf(WizTextAttributes.CONSTRUCTOR)
            WizTokenTypes.TYPE_NAME -> arrayOf(DefaultLanguageHighlighterColors.CLASS_NAME)
            WizTokenTypes.NUMBER -> arrayOf(DefaultLanguageHighlighterColors.NUMBER)
            WizTokenTypes.STRING,
            WizTokenTypes.RAW_STRING,
            WizTokenTypes.CHAR -> arrayOf(DefaultLanguageHighlighterColors.STRING)

            WizTokenTypes.COMMENT -> arrayOf(DefaultLanguageHighlighterColors.LINE_COMMENT)
            WizTokenTypes.DOC_COMMENT -> arrayOf(DefaultLanguageHighlighterColors.DOC_COMMENT)
            WizTokenTypes.OPERATOR -> arrayOf(DefaultLanguageHighlighterColors.OPERATION_SIGN)
            WizTokenTypes.HOLE -> arrayOf(WizTextAttributes.HOLE)
            WizTokenTypes.BRACKETS -> arrayOf(DefaultLanguageHighlighterColors.BRACES)
            WizTokenTypes.BAD_CHARACTER -> arrayOf(HighlighterColors.BAD_CHARACTER)
            else -> EMPTY_KEYS
        }

    private companion object {
        private val EMPTY_KEYS = emptyArray<TextAttributesKey>()
    }
}

class WizSyntaxHighlighterFactory : SyntaxHighlighterFactory() {
    override fun getSyntaxHighlighter(project: Project?, virtualFile: VirtualFile?): SyntaxHighlighter =
        WizSyntaxHighlighter()
}
