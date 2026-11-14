package dev.wiz.ide.lsp

import com.intellij.openapi.project.Project
import com.intellij.openapi.vfs.VfsUtilCore
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.platform.lsp.api.LspClient
import com.intellij.platform.lsp.api.LspClientManager

object WizLsp {
    /** The running client whose roots contain `file`, if any. */
    fun clientFor(project: Project, file: VirtualFile): LspClient? {
        val manager = LspClientManager.getInstance(project)
        return manager.getClients(WizLspIntegrationProvider::class.java).firstOrNull { client ->
            client.descriptor.roots.any { root ->
                root == file || VfsUtilCore.isAncestor(root, file, false)
            }
        }
    }

    fun restart(project: Project) {
        LspClientManager.getInstance(project)
            .stopAndRestartClientsIfNeeded(WizLspIntegrationProvider::class.java)
    }
}
