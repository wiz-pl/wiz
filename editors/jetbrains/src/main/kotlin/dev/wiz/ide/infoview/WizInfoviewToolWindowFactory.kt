package dev.wiz.ide.infoview

import com.intellij.openapi.project.Project
import com.intellij.openapi.util.Disposer
import com.intellij.openapi.wm.ToolWindow
import com.intellij.openapi.wm.ToolWindowFactory
import com.intellij.ui.content.ContentFactory
import dev.wiz.ide.settings.WizSettings

class WizInfoviewToolWindowFactory : ToolWindowFactory {
    override fun createToolWindowContent(project: Project, toolWindow: ToolWindow) {
        val panel = WizInfoviewPanel(project)
        val content = ContentFactory.getInstance().createContent(panel, "Infoview", false)
        Disposer.register(content, panel)
        toolWindow.contentManager.addContent(content)
        if (WizSettings.getInstance().current().infoviewAutoOpen) {
            toolWindow.show()
        }
        panel.requestRefresh()
    }
}
