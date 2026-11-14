package dev.wiz.ide.run

import com.intellij.execution.ExecutionException
import com.intellij.execution.Executor
import com.intellij.execution.configurations.CommandLineState
import com.intellij.execution.configurations.ConfigurationFactory
import com.intellij.execution.configurations.ConfigurationType
import com.intellij.execution.configurations.GeneralCommandLine
import com.intellij.execution.configurations.RunConfiguration
import com.intellij.execution.configurations.RunConfigurationBase
import com.intellij.execution.configurations.RunConfigurationOptions
import com.intellij.execution.configurations.RunProfileState
import com.intellij.execution.process.OSProcessHandler
import com.intellij.execution.process.ProcessHandler
import com.intellij.execution.runners.ExecutionEnvironment
import com.intellij.openapi.options.SettingsEditor
import com.intellij.openapi.project.Project
import com.intellij.openapi.ui.TextBrowseFolderListener
import com.intellij.openapi.ui.TextFieldWithBrowseButton
import com.intellij.openapi.fileChooser.FileChooserDescriptor
import com.intellij.ui.components.JBTextField
import com.intellij.util.ui.FormBuilder
import dev.wiz.ide.WizIcons
import dev.wiz.ide.WizRoots
import dev.wiz.ide.settings.WizSettings
import java.nio.file.Files
import java.nio.file.Path
import javax.swing.JComponent
import javax.swing.JComboBox

class WizRunConfigurationType : ConfigurationType {
    override fun getDisplayName(): String = "Wiz"
    override fun getConfigurationTypeDescription(): String = "Run wiz check, or a grail/wiz build"
    override fun getIcon() = WizIcons.FILE
    override fun getId(): String = "WizRunConfiguration"
    override fun getConfigurationFactories(): Array<ConfigurationFactory> =
        arrayOf(WizConfigurationFactory(this))
}

class WizConfigurationFactory(type: ConfigurationType) : ConfigurationFactory(type) {
    override fun getId(): String = "Wiz"
    override fun createTemplateConfiguration(project: Project): RunConfiguration =
        WizRunConfiguration(project, this, "Wiz")
}

class WizRunConfigurationOptions : RunConfigurationOptions() {
    var mode: String? by string("check")
    var file: String? by string("")
    var target: String? by string("")
}

class WizRunConfiguration(
    project: Project,
    factory: ConfigurationFactory,
    name: String,
) : RunConfigurationBase<WizRunConfigurationOptions>(project, factory, name) {
    override fun getOptions(): WizRunConfigurationOptions =
        super.getOptions() as WizRunConfigurationOptions

    override fun getConfigurationEditor(): SettingsEditor<out RunConfiguration> =
        WizRunConfigurationEditor()

    override fun checkConfiguration() {
        // The command line is built in getState; a missing file is reported by the
        // process (wiz check/build prints usage).
    }

    override fun getState(executor: Executor, environment: ExecutionEnvironment): RunProfileState {
        val options = options
        val mode = options.mode ?: "check"
        val file = options.file?.takeIf { it.isNotBlank() }
        val commandLine = GeneralCommandLine()
        val state = WizSettings.getInstance().current()
        if (file == null) {
            throw ExecutionException("Wiz run configuration: choose a file")
        }

        if (mode == "build") {
            val root: Path = WizRoots.launchForFile(
                Path.of(file),
                WizSettings.getInstance().snapshot(),
            ).root
            if (Files.exists(root.resolve("grail.wiz"))) {
                val args = mutableListOf("build")
                options.target?.takeIf { it.isNotBlank() }?.let { args.add(it) }
                commandLine.withExePath(state.grailPath).withParameters(args)
            } else {
                val name = Path.of(file).fileName?.toString()?.removeSuffix(".wiz") ?: file
                commandLine.withExePath(state.wizPath).withParameters(
                    listOf("build", file, "-o", root.resolve(".wiz-build").resolve(name).toString()),
                )
            }
            commandLine.withWorkDirectory(root.toString())
        } else {
            val spec = WizRoots.launchForFile(Path.of(file), WizSettings.getInstance().snapshot())
            val args = mutableListOf("check")
            val src = spec.root.resolve("src")
            if (Files.exists(spec.root.resolve("grail.wiz")) && Files.isDirectory(src)) {
                args.addAll(listOf("-I", src.toString()))
            }
            args.add(file)
            commandLine.withExePath(state.wizPath).withParameters(args)
                .withWorkDirectory(spec.root.toString())
        }
        return WizRunProfileState(environment, commandLine)
    }
}

class WizRunProfileState(
    environment: ExecutionEnvironment,
    private val commandLine: GeneralCommandLine,
) : CommandLineState(environment) {
    @Throws(ExecutionException::class)
    override fun startProcess(): ProcessHandler = OSProcessHandler(commandLine)
}

class WizRunConfigurationEditor : SettingsEditor<WizRunConfiguration>() {
    private val mode: JComboBox<String> = JComboBox(arrayOf("check", "build"))
    private val file = TextFieldWithBrowseButton()
    private val target = JBTextField()
    private val panel: JComponent = FormBuilder.createFormBuilder()
        .addLabeledComponent("Mode:", mode)
        .addLabeledComponent("File:", file)
        .addLabeledComponent("grail target (build, empty: all):", target)
        .addComponentFillVertically(javax.swing.JPanel(), 0)
        .panel

    init {
        file.addBrowseFolderListener(
            TextBrowseFolderListener(
                FileChooserDescriptor(true, false, false, false, false, false)
                    .withTitle("Choose a Wiz file"),
            ),
        )
    }

    override fun createEditor(): JComponent = panel

    override fun resetEditorFrom(configuration: WizRunConfiguration) {
        mode.selectedItem = configuration.options.mode ?: "check"
        file.text = configuration.options.file ?: ""
        target.text = configuration.options.target ?: ""
    }

    override fun applyEditorTo(configuration: WizRunConfiguration) {
        configuration.options.mode = mode.selectedItem as? String ?: "check"
        configuration.options.file = file.text.trim()
        configuration.options.target = target.text.trim()
    }
}
