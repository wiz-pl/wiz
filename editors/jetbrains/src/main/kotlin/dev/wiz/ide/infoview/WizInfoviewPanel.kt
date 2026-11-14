package dev.wiz.ide.infoview

import com.google.gson.JsonElement
import com.google.gson.JsonObject
import com.intellij.openapi.Disposable
import com.intellij.openapi.application.ApplicationManager
import com.intellij.openapi.editor.EditorFactory
import com.intellij.openapi.editor.event.CaretEvent
import com.intellij.openapi.editor.event.CaretListener
import com.intellij.openapi.editor.event.DocumentEvent
import com.intellij.openapi.editor.event.DocumentListener
import com.intellij.openapi.fileEditor.FileEditorManager
import com.intellij.openapi.fileEditor.FileDocumentManager
import com.intellij.openapi.fileEditor.OpenFileDescriptor
import com.intellij.openapi.project.Project
import com.intellij.openapi.util.TextRange
import com.intellij.openapi.vfs.VirtualFile
import com.intellij.openapi.vfs.VirtualFileManager
import com.intellij.platform.lsp.api.LspClient
import com.intellij.ui.components.JBScrollPane
import com.intellij.util.Alarm
import dev.wiz.ide.lsp.WizLsp
import dev.wiz.ide.lsp.WizLsp4jServer
import dev.wiz.ide.lsp.WizPosition
import dev.wiz.ide.lsp.WizSubtermParams
import dev.wiz.ide.lsp.WizTextDocumentIdentifier
import dev.wiz.ide.lsp.WizTextDocumentPositionParams
import dev.wiz.ide.settings.WizSettings
import java.awt.BorderLayout
import java.nio.charset.StandardCharsets
import java.util.Base64
import java.util.concurrent.CompletableFuture
import javax.swing.JEditorPane
import javax.swing.JPanel
import javax.swing.JSplitPane
import javax.swing.event.HyperlinkEvent
import javax.swing.text.html.HTMLEditorKit

/** The infoview tool window. It shows the same protocol results as the Neovim and
 * VS Code infoviews: goals, the expected type, messages, syntax/expansion/import/
 * instances/declarations, and widget titles. Widget HTML is not rendered yet (a gap
 * against the VS Code client). */
class WizInfoviewPanel(private val project: Project) : JPanel(BorderLayout()), Disposable {
    private val content = JEditorPane("text/html", "").apply {
        isEditable = false
        editorKit = HTMLEditorKit()
        addHyperlinkListener { onLink(it) }
    }
    private val detail = JEditorPane("text/html", "").apply {
        isEditable = false
        editorKit = HTMLEditorKit()
        addHyperlinkListener { onLink(it) }
    }
    private val alarm = Alarm(Alarm.ThreadToUse.SWING_THREAD, this)
    private var session: Int? = null
    private var lastFile: VirtualFile? = null
    private var disposed = false

    init {
        add(JSplitPane(
            JSplitPane.VERTICAL_SPLIT,
            JBScrollPane(content),
            JBScrollPane(detail),
        ).apply { resizeWeight = 0.78 }, BorderLayout.CENTER)
        EditorFactory.getInstance().eventMulticaster.addCaretListener(object : CaretListener {
            override fun caretPositionChanged(event: CaretEvent) {
                schedule()
            }
        }, this)
        EditorFactory.getInstance().eventMulticaster.addDocumentListener(object : DocumentListener {
            override fun documentChanged(event: DocumentEvent) {
                schedule(250)
            }
        }, this)
        renderMessage("Open a Wiz file.")
    }

    fun requestRefresh() {
        schedule(0)
    }

    private fun schedule(delay: Int = WizSettings.getInstance().current().infoviewDebounce) {
        if (disposed) return
        alarm.cancelAllRequests()
        alarm.addRequest({ refresh() }, delay)
    }

    private fun refresh() {
        if (disposed) return
        val editor = FileEditorManager.getInstance(project).selectedTextEditor
        if (editor == null) {
            renderMessage("Open a Wiz file.")
            return
        }
        val file = editor.virtualFile
        if (file == null || file.extension != "wiz") {
            renderMessage("Open a Wiz file.")
            return
        }
        val client = WizLsp.clientFor(project, file)
        if (client == null) {
            renderMessage("Starting the Wiz language server…")
            return
        }
        val document = editor.document
        val offset = editor.caretModel.offset.coerceIn(0, document.textLength)
        val line = document.getLineNumber(offset)
        val lineStart = document.getLineStartOffset(line)
        val character = Character.codePointCount(document.charsSequence, lineStart, offset)
        val position = WizPosition(line, character)
        val params = WizTextDocumentPositionParams(WizTextDocumentIdentifier(file.url), position)
        lastFile = file

        ApplicationManager.getApplication().executeOnPooledThread {
            val goals = request { it.interactiveGoals(params) }
            val term = request { it.interactiveTermGoal(params) }
            val info = request { it.interactiveInfo(params) }
            ApplicationManager.getApplication().invokeLater {
                if (disposed) return@invokeLater
                session = sessionOf(goals) ?: sessionOf(term) ?: sessionOf(info) ?: session
                render(file, position, goals, term, info)
            }
        }
    }

    private fun request(call: (WizLsp4jServer) -> CompletableFuture<JsonElement>): JsonElement? {
        return try {
            val client = lastFile?.let { WizLsp.clientFor(project, it) } ?: return null
            client.sendRequestSync { server -> call(server as WizLsp4jServer) }
        } catch (e: Exception) {
            null
        }
    }

    private fun sessionOf(element: JsonElement?): Int? {
        val obj = jsonObject(element) ?: return null
        val session = obj.get("session") ?: return null
        return if (session.isJsonPrimitive) session.asInt else null
    }

    private fun render(
        file: VirtualFile,
        position: WizPosition,
        goals: JsonElement?,
        term: JsonElement?,
        info: JsonElement?,
    ) {
        val html = StringBuilder()
        html.append("<html><body style='font-family:monospace;font-size:12px'>")
        html.append("<div style='color:gray'>")
            .append(esc(file.name))
            .append(":").append(position.line + 1).append(":").append(position.character + 1)
            .append("</div>")
        val goalsObj = jsonObject(goals)
        val termObj = jsonObject(term)
        val infoObj = jsonObject(info)
        if (goalsObj != null) {
            html.append("<b>Tactic state</b><br>")
            val list = arrayField(goalsObj, "goals")
            if (list == null || list.size() == 0) {
                html.append("<div>No goals</div>")
            } else {
                html.append("<div style='color:gray'>")
                html.append(if (list.size() == 1) "1 goal" else "${list.size()} goals")
                html.append("</div>")
                for (goal in list) {
                    if (goal.isJsonObject) html.append(goalHtml(goal.asJsonObject))
                }
            }
            arrayField(goalsObj, "messages")?.let { messages ->
                if (messages.size() > 0) {
                    html.append("<br><b>Messages</b><br>")
                    for (message in messages) {
                        html.append("<div style='margin-left:1em'>")
                            .append(esc(message.asString)).append("</div>")
                    }
                }
            }
            arrayField(goalsObj, "widgets")?.let { widgets ->
                if (widgets.size() > 0) {
                    html.append("<br><b>Widgets</b><br>")
                    for (widget in widgets) {
                        if (!widget.isJsonObject) continue
                        val title = string(widget.asJsonObject, "title") ?: "widget"
                        html.append("<div><b>").append(esc(title)).append("</b> ")
                            .append("<i>(widget HTML is not rendered in the JetBrains client yet)</i></div>")
                    }
                }
            }
        }
        if (objectField(termObj, "goal") != null) {
            html.append("<br><b>Expected type</b><br>")
            html.append(goalHtml(objectField(termObj, "goal")))
        }
        arrayField(infoObj, "items")?.let { items ->
            var section: String? = null
            for (item in items) {
                if (!item.isJsonObject) continue
                val obj = item.asJsonObject
                val kind = string(obj, "kind") ?: "info"
                val title = when (kind) {
                    "syntax", "expansion" -> "Syntax"
                    "import" -> "Import"
                    "instance" -> "Instances"
                    "declaration" -> "Declarations"
                    "message" -> "Messages"
                    else -> "Info"
                }
                if (title != section) {
                    html.append("<br><b>").append(title).append("</b><br>")
                    section = title
                }
                html.append(itemHtml(obj))
            }
        }
        if (goalsObj == null && objectField(termObj, "goal") == null &&
            (arrayField(infoObj, "items")?.size() ?: 0) == 0
        ) {
            html.append("<div style='color:gray'>No info.</div>")
        }
        html.append("</body></html>")
        content.text = html.toString()
        content.caretPosition = 0
    }

    private fun renderMessage(message: String) {
        content.text = "<html><body style='font-family:monospace'><i>${esc(message)}</i></body></html>"
    }

    private fun goalHtml(goal: JsonObject): String = buildString {
        append("<div style='margin:0.25em 0 0.25em 0.6em'>")
        string(goal, "userName")?.let { append("<div><i>case ").append(esc(it)).append("</i></div>") }
        arrayField(goal, "hyps")?.forEach { hyp ->
            if (!hyp.isJsonObject) return@forEach
            val h = hyp.asJsonObject
            val names = arrayField(h, "names")?.joinToString(" ") { it.asString } ?: ""
            append("<div>").append(esc(names)).append(" : ").append(tagged(h.get("type")))
            h.get("val")?.let { value ->
                if (!value.isJsonNull) append(" := ").append(tagged(value))
            }
            append("</div>")
        }
        val prefix = string(goal, "goalPrefix") ?: "⊢ "
        append("<div>").append(esc(prefix)).append(tagged(goal.get("type"))).append("</div>")
        append("</div>")
    }

    private fun itemHtml(item: JsonObject): String = buildString {
        val kind = string(item, "kind") ?: "info"
        val title = string(item, "title") ?: ""
        val head = link(objectField(item, "location"), esc(title))
        when (kind) {
            "declaration" -> {
                append("<div><b>").append(head).append("</b>")
                item.get("type")?.let { if (!it.isJsonNull) append(" : ").append(tagged(it)) }
                append("</div>")
            }
            "instance" -> {
                append("<div><b>").append(esc(string(item, "text") ?: "?")).append("</b>")
                item.get("type")?.let { if (!it.isJsonNull) append(" : ").append(tagged(it)) }
                append("</div>")
            }
            else -> {
                append("<div>").append(head).append("</div>")
                string(item, "text")?.let { text ->
                    for (line in text.split('\n')) {
                        append("<div style='margin-left:1.2em'>").append(esc(line)).append("</div>")
                    }
                }
            }
        }
    }

    private fun tagged(element: JsonElement?): String {
        if (element == null || element.isJsonNull || !element.isJsonObject) return ""
        val obj = element.asJsonObject
        obj.get("text")?.let { return esc(it.asString) }
        arrayField(obj, "append")?.let { parts ->
            return parts.joinToString("") { tagged(it) }
        }
        val tag = arrayField(obj, "tag") ?: return ""
        if (tag.size() < 2) return ""
        val info = tag[0] as? JsonObject ?: return tagged(tag[1])
        val body = tagged(tag[1])
        val ref = info.get("ref")?.takeIf { it.isJsonPrimitive }?.asInt ?: 0
        val kind = string(info, "kind") ?: "other"
        val name = string(info, "name")
        val color = when (kind) {
            "const", "data" -> "#7a3e9d"
            "var" -> "#1a5fb4"
            "sort" -> "#986a44"
            "lit" -> "#2a7b2a"
            else -> "#555555"
        }
        val title = if (name != null) " title='${attr(name)}'" else ""
        val colored = "<font color='$color'>$body</font>"
        return if (body.contains("<a ")) colored else "<a href='inspect:$ref'$title>$colored</a>"
    }

    private fun link(location: JsonObject?, text: String): String {
        if (location == null) return text
        val uri = string(location, "uri") ?: return text
        val start = objectField(objectField(location, "range"), "start")
        val line = start?.get("line")?.takeIf { it.isJsonPrimitive }?.asInt ?: 0
        val character = start?.get("character")?.takeIf { it.isJsonPrimitive }?.asInt ?: 0
        val encoded = Base64.getUrlEncoder().withoutPadding()
            .encodeToString(uri.toByteArray(StandardCharsets.UTF_8))
        return "<a href='goto:$encoded:$line:$character'>$text</a>"
    }

    private fun onLink(event: HyperlinkEvent) {
        if (event.eventType != HyperlinkEvent.EventType.ACTIVATED) return
        val description = event.description ?: return
        when {
            description.startsWith("goto:") -> {
                val parts = description.removePrefix("goto:").split(':')
                if (parts.size >= 3) {
                    val uri = String(Base64.getUrlDecoder().decode(parts[0]), StandardCharsets.UTF_8)
                    val line = parts[1].toIntOrNull() ?: 0
                    val character = parts[2].toIntOrNull() ?: 0
                    val file = VirtualFileManager.getInstance().findFileByUrl(uri)
                    if (file != null) {
                        val document = FileDocumentManager.getInstance().getDocument(file)
                        val offset = if (document != null && line < document.lineCount) {
                            val lineStart = document.getLineStartOffset(line)
                            val text = document.getText(TextRange(lineStart, document.getLineEndOffset(line)))
                            lineStart + utf16Length(text, character)
                        } else {
                            0
                        }
                        OpenFileDescriptor(project, file, offset).navigate(true)
                    }
                }
            }
            description.startsWith("inspect:") -> {
                val ref = description.removePrefix("inspect:").toIntOrNull() ?: return
                inspect(ref)
            }
        }
    }

    private fun inspect(ref: Int) {
        val file = lastFile ?: return
        val session = session ?: return
        val client = WizLsp.clientFor(project, file) ?: return
        val params = WizSubtermParams(WizTextDocumentIdentifier(file.url), session, ref)
        ApplicationManager.getApplication().executeOnPooledThread {
            val info = try {
                client.sendRequestSync { server -> (server as WizLsp4jServer).subtermInfo(params) }
            } catch (e: Exception) {
                null
            }
            ApplicationManager.getApplication().invokeLater {
                if (disposed) return@invokeLater
                if (info == null || !info.isJsonObject) {
                    refresh()
                } else {
                    detail.text = detailHtml(info.asJsonObject)
                    detail.caretPosition = 0
                }
            }
        }
    }

    private fun detailHtml(info: JsonObject): String = buildString {
        append("<html><body style='font-family:monospace;font-size:12px'>")
        append("<div>").append(esc(string(info, "text") ?: ""))
        info.get("type")?.let { if (!it.isJsonNull) append(" : ").append(tagged(it)) }
        append("</div>")
        append("<div style='color:gray'>-- ")
            .append(esc(string(info, "kind") ?: "?"))
        string(info, "name")?.let { append(" ").append(esc(it)) }
        append("</div>")
        val definition = objectField(info, "definition")
        if (definition != null) {
            val uri = string(definition, "uri") ?: ""
            append("<div>").append(link(definition, "defined in ${esc(uri.substringAfterLast('/'))}"))
                .append("</div>")
        }
        append("</body></html>")
    }

    /** The UTF-16 length of the first `codePoints` characters of `text`. */
    private fun utf16Length(text: String, codePoints: Int): Int {
        var index = 0
        var seen = 0
        while (index < text.length && seen < codePoints) {
            index += Character.charCount(text.codePointAt(index))
            seen++
        }
        return index
    }

    private fun jsonObject(element: JsonElement?): JsonObject? =
        if (element != null && element.isJsonObject) element.asJsonObject else null

    private fun objectField(obj: JsonObject?, key: String): JsonObject? = jsonObject(obj?.get(key))

    private fun arrayField(obj: JsonObject?, key: String): com.google.gson.JsonArray? {
        val value = obj?.get(key) ?: return null
        return if (value.isJsonArray) value.asJsonArray else null
    }

    private fun string(obj: JsonObject, key: String): String? {
        val value = obj.get(key) ?: return null
        return if (value.isJsonPrimitive) value.asString else null
    }

    private fun esc(text: String): String = text
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("\"", "&quot;")

    private fun attr(text: String): String = esc(text).replace("'", "&#39;")

    override fun dispose() {
        disposed = true
        alarm.cancelAllRequests()
    }
}
