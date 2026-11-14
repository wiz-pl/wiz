package dev.wiz.ide.actions

import com.intellij.execution.configurations.GeneralCommandLine
import com.intellij.execution.process.OSProcessHandler
import com.intellij.execution.ui.RunContentDescriptor
import com.intellij.openapi.project.Project
import com.intellij.execution.ExecutionManager
import com.intellij.execution.filters.TextConsoleBuilderFactory

/** Run a command in a console tab (the same output the Run tool window shows). */
object WizCommandRunner {
    fun run(project: Project, title: String, commandLine: GeneralCommandLine) {
        val handler = OSProcessHandler(commandLine)
        val console = TextConsoleBuilderFactory.getInstance().createBuilder(project).console
        console.attachToProcess(handler)
        val descriptor = RunContentDescriptor(console, handler, console.component, title)
        ExecutionManager.getInstance(project).contentManager.showRunContent(descriptor)
        handler.startNotify()
    }
}
