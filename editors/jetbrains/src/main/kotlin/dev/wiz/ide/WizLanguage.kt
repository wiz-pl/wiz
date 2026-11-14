package dev.wiz.ide

import com.intellij.lang.Language
import com.intellij.openapi.fileTypes.LanguageFileType
import com.intellij.openapi.util.IconLoader
import javax.swing.Icon

object WizLanguage : Language("Wiz")

class WizLanguageFileType : LanguageFileType(WizLanguage) {
    companion object {
        @JvmField
        val INSTANCE = WizLanguageFileType()
    }

    override fun getName(): String = "Wiz"
    override fun getDescription(): String = "Wiz source file"
    override fun getDefaultExtension(): String = "wiz"
    override fun getIcon(): Icon = WizIcons.FILE
}

object WizIcons {
    @JvmField
    val FILE: Icon = IconLoader.getIcon("/icons/wiz.svg", WizIcons::class.java)
}
