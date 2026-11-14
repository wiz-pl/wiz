package dev.wiz.ide.actions

import com.intellij.execution.configurations.GeneralCommandLine
import com.intellij.openapi.actionSystem.AnAction
import com.intellij.openapi.actionSystem.AnActionEvent
import com.intellij.openapi.actionSystem.CommonDataKeys
import com.intellij.openapi.ui.Messages
import dev.wiz.ide.WizRoots
import dev.wiz.ide.settings.WizSettings
import java.nio.file.Path

class WizFormatAction : AnAction() {
    override fun actionPerformed(event: AnActionEvent) {
        val project = event.project ?: return
        val file = event.getData(CommonDataKeys.VIRTUAL_FILE)
        if (file == null || file.extension != "wiz") {
            Messages.showInfoMessage(project, "Open a Wiz file first.", "Wiz")
            return
        }
        val command = WizSettings.getInstance().current().formatCommand.trim()
        if (command.isEmpty()) {
            Messages.showInfoMessage(
                project,
                "The Wiz language server does not provide textDocument/formatting yet. " +
                    "Set an external formatter in Settings | Tools | Wiz.",
                "Wiz",
            )
            return
        }
        val parts = command.split(Regex("\\s+")).map { it.replace("{file}", file.path) }
        val spec = WizRoots.launchForFile(Path.of(file.path), WizSettings.getInstance().snapshot())
        WizCommandRunner.run(
            project,
            "Wiz: Format ${file.name}",
            GeneralCommandLine(parts.first())
                .withParameters(parts.drop(1))
                .withWorkDirectory(spec.root.toString()),
        )
    }

    override fun update(event: AnActionEvent) {
        val file = event.getData(CommonDataKeys.VIRTUAL_FILE)
        event.presentation.isEnabled = event.project != null && file?.extension == "wiz"
    }
}
