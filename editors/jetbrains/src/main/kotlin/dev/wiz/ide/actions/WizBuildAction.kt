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

class WizBuildAction : AnAction() {
    override fun actionPerformed(event: AnActionEvent) {
        val project = event.project ?: return
        val file = event.getData(CommonDataKeys.VIRTUAL_FILE)
        if (file == null || file.extension != "wiz") {
            Messages.showInfoMessage(project, "Open a Wiz file first.", "Wiz")
            return
        }
        val state = WizSettings.getInstance().current()
        val spec = WizRoots.launchForFile(Path.of(file.path), WizSettings.getInstance().snapshot())
        if (Files.exists(spec.root.resolve("grail.wiz"))) {
            WizCommandRunner.run(
                project,
                "Wiz: Build ${spec.root.fileName}",
                GeneralCommandLine(state.grailPath)
                    .withParameters(listOf("build"))
                    .withWorkDirectory(spec.root.toString()),
            )
            return
        }
        val name = file.name.removeSuffix(".wiz")
        WizCommandRunner.run(
            project,
            "Wiz: Build ${file.name}",
            GeneralCommandLine(state.wizPath)
                .withParameters(
                    listOf(
                        "build",
                        file.path,
                        "-o",
                        spec.root.resolve(".wiz-build").resolve(name).toString(),
                    ),
                )
                .withWorkDirectory(spec.root.toString()),
        )
    }

    override fun update(event: AnActionEvent) {
        val file = event.getData(CommonDataKeys.VIRTUAL_FILE)
        event.presentation.isEnabled = event.project != null && file?.extension == "wiz"
    }
}
