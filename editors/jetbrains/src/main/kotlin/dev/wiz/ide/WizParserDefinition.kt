package dev.wiz.ide

import com.intellij.extapi.psi.PsiFileBase
import com.intellij.lang.ParserDefinition
import com.intellij.lang.PsiParser
import com.intellij.lexer.Lexer
import com.intellij.openapi.fileTypes.FileType
import com.intellij.openapi.project.Project
import com.intellij.psi.FileViewProvider
import com.intellij.psi.PsiFile
import com.intellij.psi.tree.IFileElementType
import com.intellij.psi.tree.TokenSet

object WizFileElementType : IFileElementType(WizLanguage)

class WizPsiFile(viewProvider: FileViewProvider) : PsiFileBase(viewProvider, WizLanguage) {
    override fun getFileType(): FileType = WizLanguageFileType.INSTANCE
    override fun toString(): String = "Wiz file"
}

class WizParserDefinition : ParserDefinition {
    override fun createLexer(project: Project): Lexer = WizLexer()

    override fun createParser(project: Project): PsiParser = PsiParser { root, builder ->
        val marker = builder.mark()
        while (!builder.eof()) {
            builder.advanceLexer()
        }
        marker.done(root)
        builder.treeBuilt
    }

    override fun getFileNodeType(): IFileElementType = WizFileElementType

    override fun getCommentTokens(): TokenSet =
        TokenSet.create(WizTokenTypes.COMMENT, WizTokenTypes.DOC_COMMENT)

    override fun getStringLiteralElements(): TokenSet =
        TokenSet.create(WizTokenTypes.STRING, WizTokenTypes.RAW_STRING, WizTokenTypes.CHAR)

    override fun getWhitespaceTokens(): TokenSet = TokenSet.create(WizTokenTypes.WHITE_SPACE)

    override fun createFile(viewProvider: FileViewProvider): PsiFile = WizPsiFile(viewProvider)
}
