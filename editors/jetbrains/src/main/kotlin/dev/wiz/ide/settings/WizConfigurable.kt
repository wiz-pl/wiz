package dev.wiz.ide.settings

import com.intellij.openapi.options.BoundConfigurable
import com.intellij.openapi.project.ProjectManager
import com.intellij.openapi.ui.DialogPanel
import com.intellij.platform.lsp.api.LspClientManager
import com.intellij.ui.components.JBCheckBox
import com.intellij.ui.components.JBTextField
import com.intellij.util.ui.FormBuilder
import dev.wiz.ide.lsp.WizLspIntegrationProvider

class WizConfigurable : BoundConfigurable("Wiz") {
    private val wizPath = JBTextField()
    private val grailPath = JBTextField()
    private val rootMarkers = JBTextField()
    private val grailEnabled = JBCheckBox("Start grail lsp in a grail package")
    private val toolchains = JBCheckBox("One server per installed toolchain (its lib/)")
    private val autoOpen = JBCheckBox("Open the infoview with the first Wiz file")
    private val followCursor = JBCheckBox("The infoview follows the cursor")
    private val formatCommand = JBTextField()

    override fun createPanel(): DialogPanel = FormBuilder.createFormBuilder()
        .addLabeledComponent("wiz executable:", wizPath)
        .addLabeledComponent("grail executable:", grailPath)
        .addLabeledComponent("root markers (comma separated):", rootMarkers)
        .addComponent(grailEnabled)
        .addComponent(toolchains)
        .addComponent(autoOpen)
        .addComponent(followCursor)
        .addLabeledComponent("external formatter ({file} is replaced):", formatCommand)
        .addComponentFillVertically(javax.swing.JPanel(), 0)
        .panel

    override fun isModified(): Boolean {
        val state = WizSettings.getInstance().current()
        return wizPath.text != state.wizPath ||
            grailPath.text != state.grailPath ||
            rootMarkers.text != state.rootMarkers.joinToString(",") ||
            grailEnabled.isSelected != state.grailEnabled ||
            toolchains.isSelected != state.toolchains ||
            autoOpen.isSelected != state.infoviewAutoOpen ||
            followCursor.isSelected != state.infoviewFollowCursor ||
            formatCommand.text != state.formatCommand
    }

    override fun apply() {
        val state = WizSettings.getInstance().current()
        state.wizPath = wizPath.text.trim()
        state.grailPath = grailPath.text.trim()
        state.rootMarkers = rootMarkers.text.split(',').map { it.trim() }.filter { it.isNotEmpty() }
            .toMutableList()
        state.grailEnabled = grailEnabled.isSelected
        state.toolchains = toolchains.isSelected
        state.infoviewAutoOpen = autoOpen.isSelected
        state.infoviewFollowCursor = followCursor.isSelected
        state.formatCommand = formatCommand.text.trim()
        restartClients()
    }

    override fun reset() {
        val state = WizSettings.getInstance().current()
        wizPath.text = state.wizPath
        grailPath.text = state.grailPath
        rootMarkers.text = state.rootMarkers.joinToString(",")
        grailEnabled.isSelected = state.grailEnabled
        toolchains.isSelected = state.toolchains
        autoOpen.isSelected = state.infoviewAutoOpen
        followCursor.isSelected = state.infoviewFollowCursor
        formatCommand.text = state.formatCommand
    }

    private fun restartClients() {
        for (project in ProjectManager.getInstance().openProjects) {
            if (!project.isDefault) {
                LspClientManager.getInstance(project)
                    .stopAndRestartClientsIfNeeded(WizLspIntegrationProvider::class.java)
            }
        }
    }
}
