plugins {
    id("java")
    id("org.jetbrains.kotlin.jvm") version "2.2.20"
    id("org.jetbrains.intellij.platform") version "2.20.1"
}

group = "dev.wiz"
version = "0.1.0"

repositories {
    mavenCentral()
    intellijPlatform {
        defaultRepositories()
    }
}

dependencies {
    intellijPlatform {
        // The LSP API is part of IntelliJ IDEA (Ultimate) and the 2026.1.4+ renamed
        // classes (LspIntegrationProvider / LspClientDescriptor) are used here.
        intellijIdea("2026.2")
        testFramework(org.jetbrains.intellij.platform.gradle.TestFrameworkType.Platform)
    }
    testImplementation("junit:junit:4.13.2")
}

kotlin {
    jvmToolchain(21)
}

intellijPlatform {
    pluginConfiguration {
        id = "dev.wiz.ide"
        name = "Wiz"
        version = "0.1.0"
        description = """
            Wiz language support: the wiz/grail language server, syntax highlighting,
            commands and an infoview. The launch and root rules are the same as the
            Neovim plugin in editors/nvim.
        """.trimIndent()
        vendor {
            name = "wiz-pl"
            url = "https://github.com/wiz-pl/wiz"
        }
        ideaVersion {
            sinceBuild = "262"
            untilBuild = provider { null }
        }
    }
    buildSearchableOptions = false
}

tasks.test {
    useJUnit()
}
