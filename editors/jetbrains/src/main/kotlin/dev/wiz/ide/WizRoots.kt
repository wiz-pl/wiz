package dev.wiz.ide

import java.io.File
import java.nio.file.Files
import java.nio.file.Path

/** Settings that affect the server launch; the persisted settings service snapshots
 * its state into this. The defaults are the same as editors/nvim's (and the VS Code
 * extension's). */
data class WizLaunchSettings(
    val wizPath: String = "wiz",
    val wizArgs: List<String> = listOf("lsp"),
    val grailPath: String = "grail",
    val grailArgs: List<String> = listOf("lsp"),
    val grailEnabled: Boolean = true,
    val toolchains: Boolean = true,
    val rootMarkers: List<String> = listOf("grail.wiz", "wiz-toolchain", "lakefile.toml", ".git"),
)

enum class LaunchKind { WIZ, GRAIL, TOOLCHAIN }

data class LaunchSpec(
    val root: Path,
    val kind: LaunchKind,
    val command: String,
    val args: List<String>,
    val cwd: Path,
    val warnings: List<String>,
)

data class Toolchain(val lib: Path, val wiz: Path)

/** The filesystem questions the root rules ask; a test can answer them without a
 * real installation. */
interface FileProbe {
    fun exists(path: Path): Boolean
    fun isDirectory(path: Path): Boolean
    fun isExecutable(path: Path): Boolean
}

object LocalFileProbe : FileProbe {
    override fun exists(path: Path): Boolean = Files.exists(path)
    override fun isDirectory(path: Path): Boolean = Files.isDirectory(path)

    override fun isExecutable(path: Path): Boolean {
        val name = path.toString()
        val looksLikePath = path.nameCount > 1 || name.contains(File.separatorChar)
        if (!looksLikePath) {
            return findOnPath(name) != null
        }
        return Files.isRegularFile(path) && Files.isExecutable(path)
    }

    private fun findOnPath(name: String): Path? {
        val path = System.getenv("PATH") ?: return null
        for (entry in path.split(File.pathSeparatorChar)) {
            if (entry.isEmpty()) continue
            val candidate = Path.of(entry).resolve(name)
            if (Files.isRegularFile(candidate) && Files.isExecutable(candidate)) {
                return candidate
            }
        }
        return null
    }
}

/** The launch and root rules, identical to editors/nvim/lua/wiz/lsp.lua and to the
 * VS Code extension's src/root.ts. The shared cases are in
 * editors/testdata/lsp-root-cases.json. */
object WizRoots {
    /** The installed toolchain whose standard library `file` lies in, if any. */
    fun findToolchain(file: Path, probe: FileProbe = LocalFileProbe): Toolchain? {
        var dir: Path? = file.toAbsolutePath().normalize().parent
        while (dir != null) {
            val current = dir
            if (current.fileName?.toString() == "lib") {
                val share = current.parent
                if (share != null) {
                    val binary = share.resolve(".lake/build/bin/wiz")
                    val marked = probe.exists(share.resolve("TOOLCHAIN")) ||
                        probe.exists(share.resolve("REVISION"))
                    if (probe.exists(current.resolve("Prelude.wiz")) && probe.exists(binary) && marked) {
                        val wrapper = share.parent?.parent?.resolve("bin/wiz")
                        val binaryOrWrapper =
                            if (wrapper != null && probe.isExecutable(wrapper)) wrapper else binary
                        return Toolchain(current, binaryOrWrapper)
                    }
                }
            }
            dir = current.parent
        }
        return null
    }

    /** The nearest ancestor directory of `file` (its own included) with a marker,
     * else the file's own directory. */
    fun findRoot(
        file: Path,
        markers: List<String> = WizLaunchSettings().rootMarkers,
        probe: FileProbe = LocalFileProbe,
    ): Path {
        val resolved = file.toAbsolutePath().normalize()
        val own = resolved.parent ?: resolved
        var dir: Path? = own
        while (dir != null) {
            val current = dir
            if (markers.any { probe.exists(current.resolve(it)) }) {
                return current
            }
            dir = current.parent
        }
        return own
    }

    fun launchForFile(
        file: Path,
        settings: WizLaunchSettings = WizLaunchSettings(),
        probe: FileProbe = LocalFileProbe,
    ): LaunchSpec {
        val resolved = file.toAbsolutePath().normalize()
        val warnings = mutableListOf<String>()

        if (settings.toolchains) {
            val toolchain = findToolchain(resolved, probe)
            if (toolchain != null) {
                return LaunchSpec(
                    root = toolchain.lib,
                    kind = LaunchKind.TOOLCHAIN,
                    command = toolchain.wiz.toString(),
                    args = listOf("lsp"),
                    cwd = toolchain.lib,
                    warnings = warnings,
                )
            }
        }

        val root = findRoot(resolved, settings.rootMarkers, probe)
        if (settings.grailEnabled && probe.exists(root.resolve("grail.wiz"))) {
            if (probe.isExecutable(Path.of(settings.grailPath))) {
                return LaunchSpec(
                    root = root,
                    kind = LaunchKind.GRAIL,
                    command = settings.grailPath,
                    args = settings.grailArgs + listOf("-C", root.toString()),
                    cwd = root,
                    warnings = warnings,
                )
            }
            warnings += "${settings.grailPath} is not on PATH; using ${settings.wizPath} lsp " +
                "without the package's modules"
        }

        return LaunchSpec(
            root = root,
            kind = LaunchKind.WIZ,
            command = settings.wizPath,
            args = settings.wizArgs,
            cwd = root,
            warnings = warnings,
        )
    }
}
