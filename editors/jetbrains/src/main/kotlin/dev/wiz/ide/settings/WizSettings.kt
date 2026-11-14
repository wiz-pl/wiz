package dev.wiz.ide.settings

import com.intellij.openapi.application.ApplicationManager
import com.intellij.openapi.components.PersistentStateComponent
import com.intellij.openapi.components.State
import com.intellij.openapi.components.Storage
import dev.wiz.ide.WizLaunchSettings

/** The persisted settings. The fields mirror the VS Code extension's `wiz.*`
 * settings, and the defaults are the same. */
@State(name = "WizSettings", storages = [Storage("wiz.xml")])
class WizSettings : PersistentStateComponent<WizSettings.State> {
    class State {
        var wizPath: String = "wiz"
        var wizArgs: MutableList<String> = mutableListOf("lsp")
        var grailPath: String = "grail"
        var grailArgs: MutableList<String> = mutableListOf("lsp")
        var grailEnabled: Boolean = true
        var toolchains: Boolean = true
        var rootMarkers: MutableList<String> =
            mutableListOf("grail.wiz", "wiz-toolchain", "lakefile.toml", ".git")
        var infoviewAutoOpen: Boolean = true
        var infoviewFollowCursor: Boolean = true
        var infoviewDebounce: Int = 150
        var formatCommand: String = ""
    }

    private var myState = State()

    override fun getState(): State = myState

    override fun loadState(state: State) {
        myState = state
    }

    /** The current state, for the UI and the launchers. */
    fun current(): State = myState

    fun snapshot(): WizLaunchSettings = WizLaunchSettings(
        wizPath = state.wizPath,
        wizArgs = state.wizArgs.toList(),
        grailPath = state.grailPath,
        grailArgs = state.grailArgs.toList(),
        grailEnabled = state.grailEnabled,
        toolchains = state.toolchains,
        rootMarkers = state.rootMarkers.toList(),
    )

    companion object {
        @JvmStatic
        fun getInstance(): WizSettings = ApplicationManager.getApplication().getService(WizSettings::class.java)
    }
}
