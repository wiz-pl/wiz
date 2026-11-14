package dev.wiz.ide.actions

import com.intellij.openapi.actionSystem.AnAction
import com.intellij.openapi.actionSystem.AnActionEvent
import com.intellij.openapi.ui.Messages
import dev.wiz.ide.lsp.WizLsp

class WizRestartAction : AnAction() {
    override fun actionPerformed(event: AnActionEvent) {
        val project = event.project ?: return
        WizLsp.restart(project)
        Messages.showInfoMessage(project, "Wiz language server restarted.", "Wiz")
    }

    override fun update(event: AnActionEvent) {
        event.presentation.isEnabled = event.project != null
    }
}
