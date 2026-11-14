package dev.wiz.ide.lsp

import com.intellij.execution.configurations.GeneralCommandLine
import com.intellij.openapi.project.Project
import com.intellij.openapi.vfs.LocalFileSystem
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.platform.lsp.api.Lsp4jServer
import com.intellij.platform.lsp.api.LspClientDescriptor
import com.intellij.platform.lsp.api.LspIntegrationProvider
import dev.wiz.ide.LaunchSpec
import dev.wiz.ide.WizRoots
import dev.wiz.ide.settings.WizSettings
import java.nio.file.Path

/** Starts one server per root, with the rules in dev.wiz.ide.WizRoots (the same as
 * editors/nvim and the VS Code extension). */
class WizLspIntegrationProvider : LspIntegrationProvider {
    override fun fileOpened(
        project: Project,
        file: VirtualFile,
        clientStarter: LspIntegrationProvider.LspClientStarter,
    ) {
        if (file.extension != "wiz") {
            return
        }
        val spec = WizRoots.launchForFile(Path.of(file.path), WizSettings.getInstance().snapshot())
        val root = LocalFileSystem.getInstance()
            .findFileByPath(spec.root.toString().replace('\\', '/')) ?: return
        clientStarter.ensureClientStarted(WizLspClientDescriptor(project, spec, root))
    }
}

class WizLspClientDescriptor(
    project: Project,
    private val spec: LaunchSpec,
    root: VirtualFile,
) : LspClientDescriptor(project, "Wiz (${spec.root.fileName})", root) {
    override fun isSupportedFile(file: VirtualFile): Boolean {
        if (file.extension != "wiz") {
            return false
        }
        return Path.of(file.path).toAbsolutePath().normalize().startsWith(spec.cwd)
    }

    override fun createCommandLine(): GeneralCommandLine =
        GeneralCommandLine(spec.command)
            .withParameters(spec.args)
            .withWorkDirectory(spec.cwd.toString())

    override fun getLanguageId(file: VirtualFile): String = "wiz"

    override val lsp4jServerClass: Class<out Lsp4jServer> = WizLsp4jServer::class.java
}
