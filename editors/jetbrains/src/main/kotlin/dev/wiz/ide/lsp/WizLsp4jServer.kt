package dev.wiz.ide.lsp

import com.google.gson.JsonElement
import com.intellij.platform.lsp.api.Lsp4jServer
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest
import java.util.concurrent.CompletableFuture

// The custom requests of wiz-notes/infoview-protocol.md. The results are kept as
// Gson JSON because the infoview only renders them; there is no need to mirror every
// tagged-text type in Kotlin.

data class WizPosition(val line: Int, val character: Int)

data class WizTextDocumentIdentifier(val uri: String)

data class WizTextDocumentPositionParams(
    val textDocument: WizTextDocumentIdentifier,
    val position: WizPosition,
)

data class WizSubtermParams(
    val textDocument: WizTextDocumentIdentifier,
    val session: Int,
    val ref: Int,
)

interface WizLsp4jServer : Lsp4jServer {
    @JsonRequest("wiz/interactiveGoals")
    fun interactiveGoals(params: WizTextDocumentPositionParams): CompletableFuture<JsonElement>

    @JsonRequest("wiz/interactiveTermGoal")
    fun interactiveTermGoal(params: WizTextDocumentPositionParams): CompletableFuture<JsonElement>

    @JsonRequest("wiz/interactiveInfo")
    fun interactiveInfo(params: WizTextDocumentPositionParams): CompletableFuture<JsonElement>

    @JsonRequest("wiz/subtermInfo")
    fun subtermInfo(params: WizSubtermParams): CompletableFuture<JsonElement>
}
