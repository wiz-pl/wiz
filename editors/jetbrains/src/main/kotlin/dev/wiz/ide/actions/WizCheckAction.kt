package dev.wiz.ide.actions

import com.intellij.execution.configurations.GeneralCommandLine
import com.intellij.openapi.actionSystem.AnAction
import com.intellij.openapi.actionSystem.AnActionEvent
import com.intellij.openapi.actionSystem.CommonDataKeys
import com.intellij.openapi.ui.Messages
import dev.wiz.ide.WizRoots
import dev.wiz.ide.settings.WizSettings
import java.nio.file.Files
import java.nio.file.Path

class WizCheckAction : AnAction() {
    override fun actionPerformed(event: AnActionEvent) {
        val project = event.project ?: return
        val file = event.getData(CommonDataKeys.VIRTUAL_FILE)
        if (file == null || file.extension != "wiz") {
            Messages.showInfoMessage(project, "Open a Wiz file first.", "Wiz")
            return
        }
        val settings = WizSettings.getInstance().current()
        val spec = WizRoots.launchForFile(Path.of(file.path), WizSettings.getInstance().snapshot())
        val args = mutableListOf("check")
        val src = spec.root.resolve("src")
        if (Files.exists(spec.root.resolve("grail.wiz")) && Files.isDirectory(src)) {
            args += listOf("-I", src.toString())
        }
        args += file.path
        WizCommandRunner.run(
            project,
            "Wiz: Check ${file.name}",
            GeneralCommandLine(settings.wizPath)
                .withParameters(args)
                .withWorkDirectory(spec.root.toString()),
        )
    }

    override fun update(event: AnActionEvent) {
        val file = event.getData(CommonDataKeys.VIRTUAL_FILE)
        event.presentation.isEnabled = event.project != null && file?.extension == "wiz"
    }
}
