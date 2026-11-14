package dev.wiz.ide

import com.google.gson.JsonArray
import com.google.gson.JsonElement
import com.google.gson.JsonObject
import com.google.gson.JsonParser
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Rule
import org.junit.Test
import org.junit.rules.TemporaryFolder
import java.io.File
import java.nio.file.Files
import java.nio.file.Path

/** The shared launch/root cases, the same file the VS Code extension runs in
 * editors/vscode/test/root.test.mjs. */
class WizRootsTest {
    @Rule
    @JvmField
    val temp = TemporaryFolder()

    private class FakeProbe(private val executables: Set<String>) : FileProbe {
        override fun exists(path: Path): Boolean = Files.exists(path)
        override fun isDirectory(path: Path): Boolean = Files.isDirectory(path)
        override fun isExecutable(path: Path): Boolean {
            val name = path.toString()
            if (name.contains('/') || name.contains(File.separatorChar)) {
                return Files.isRegularFile(path) && Files.isExecutable(path)
            }
            return name in executables
        }
    }

    @Test
    fun sharedCases() {
        val casesFile = locateCases()
        val root = JsonParser.parseString(Files.readString(casesFile)).asJsonObject
        val defaults = root.getAsJsonObject("defaults")
        val cases = root.getAsJsonArray("cases")
        for (element in cases) {
            val case = element.asJsonObject
            runCase(case, defaults)
        }
    }

    private fun runCase(case: JsonObject, defaults: JsonObject) {
        val name = case.get("name").asString
        val base = temp.newFolder().toPath().toAbsolutePath().normalize()
        try {
            case.getAsJsonArray("dirs")?.forEach { dir ->
                Files.createDirectories(base.resolve(dir.asString))
            }
            case.getAsJsonArray("files")?.forEach { file ->
                val path = base.resolve(file.asString)
                Files.createDirectories(path.parent)
                Files.writeString(path, "fixture\n")
            }
            val executables = mutableSetOf<String>()
            case.getAsJsonArray("executables")?.forEach { executable ->
                val value = executable.asString
                if (value.contains('/') || value.contains(File.separatorChar)) {
                    base.resolve(value).toFile().setExecutable(true)
                } else {
                    executables += value
                }
            }
            val settingsObject = case.getAsJsonObject("settings")
            val settings = WizLaunchSettings(
                wizPath = stringSetting(settingsObject, defaults, "wizPath"),
                wizArgs = listSetting(settingsObject, defaults, "wizArgs"),
                grailPath = stringSetting(settingsObject, defaults, "grailPath"),
                grailArgs = listSetting(settingsObject, defaults, "grailArgs"),
                grailEnabled = boolSetting(settingsObject, defaults, "grailEnabled"),
                toolchains = boolSetting(settingsObject, defaults, "toolchains"),
                rootMarkers = listSetting(settingsObject, defaults, "rootMarkers"),
            )
            val file = base.resolve(case.get("file").asString)
            val spec = WizRoots.launchForFile(file, settings, FakeProbe(executables))
            val expected = case.getAsJsonObject("expect")
            val expectedRoot = base.resolve(expected.get("root").asString).toAbsolutePath().normalize()

            assertEquals("$name: root", expectedRoot, spec.root)
            assertEquals("$name: kind", expected.get("kind").asString, spec.kind.name.lowercase())
            assertEquals("$name: cwd", base.resolve(expected.get("cwd").asString).toAbsolutePath().normalize(), spec.cwd)
            assertEquals(
                "$name: command",
                expand(expected.get("command").asString, base, expectedRoot),
                spec.command,
            )
            val expectedArgs = expected.getAsJsonArray("args").map { expand(it.asString, base, expectedRoot) }
            assertEquals("$name: args", expectedArgs, spec.args)
            expected.getAsJsonArray("warnings")?.forEach { warning ->
                val text = warning.asString
                assertTrue(
                    "$name: expected a warning containing '$text', got $spec.warnings",
                    spec.warnings.any { it.contains(text) },
                )
            }
        } finally {
            base.toFile().deleteRecursively()
        }
    }

    private fun locateCases(): Path {
        val working = Path.of(System.getProperty("user.dir")).toAbsolutePath()
        val candidates = listOf(
            working.resolve("..").resolve("testdata").resolve("lsp-root-cases.json"),
            working.resolve("editors").resolve("testdata").resolve("lsp-root-cases.json"),
        )
        return candidates.firstOrNull { Files.exists(it) }
            ?: error("editors/testdata/lsp-root-cases.json not found from $working")
    }

    private fun setting(settings: JsonObject?, defaults: JsonObject, key: String): JsonElement? {
        val override = settings?.get(key)
        return if (override != null && !override.isJsonNull) override else defaults.get(key)
    }

    private fun stringSetting(settings: JsonObject?, defaults: JsonObject, key: String): String =
        setting(settings, defaults, key)?.asString ?: ""

    private fun boolSetting(settings: JsonObject?, defaults: JsonObject, key: String): Boolean =
        setting(settings, defaults, key)?.asBoolean ?: false

    private fun listSetting(settings: JsonObject?, defaults: JsonObject, key: String): List<String> {
        val array: JsonArray = setting(settings, defaults, key)?.asJsonArray ?: JsonArray()
        return array.map { it.asString }
    }

    private fun expand(value: String, base: Path, root: Path): String =
        value.replace("{base}", base.toString()).replace("{root}", root.toString())
}
