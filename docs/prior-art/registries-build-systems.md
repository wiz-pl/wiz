# Package registries, dependency resolution and build systems

This is a survey of package registries and the machinery around them: index formats,
version syntax and resolution, lockfiles, artifact integrity, signing and transparency,
caches, offline builds and vendoring, namespaces, and toolchain pins. It was written in
November 2026 to inform the design of Grail's registry (stage 23m,
[23-grail.md](../stages/23-grail.md)), and compares Cargo, npm, Opam, Spack, Nix, Dune,
Bazel's Bzlmod, Go modules, Maven/Gradle, PyPI and Debian, plus the cross-cutting standards
(SemVer, PubGrub, MVS, TUF, Sigstore, SRI, reproducible builds). Its recommendations are
labelled R1 to R40; Grail's code and docs cite them by those labels. Each Grail paragraph
below says what Grail does now; several recommendations have since been implemented and
are marked as such.

Confidence markers:

* **[H]** high: canonical and stable, or checked against the upstream page when the survey
  was written.
* **[M]** medium: known from the project's own documentation, but the upstream page was
  not re-read; details may have moved.
* **[L]** low: an inference, flagged as such.
* **(V)** checked against the upstream page; **(S)** seen in a search snippet only;
  **(M)** from memory of a canonical document.

---

## 0. Summary

1. **Nothing in the Grail design is unprecedented, and that is good news.** Every layer has
   a close analogue: Opam (a git repository of text files as the index, one version per
   package name per switch, a real solver, `.opam.locked`), Cargo (static index, lock,
   highest satisfying version, `--locked`/`--offline`, `vendor`), Bzlmod (static HTTP
   registry, SRI hashes, `yanked_versions`, mirrors, `local_path`), Go (directory hashes in
   `go.sum`, a transparency log), TUF (rollback, freeze and mix-and-match protection),
   Debian (a signed `Release` over the index files).
2. **Three choices carry the design** and should not be traded away: (a) the index is text
   in git, and builds never read it; (b) the lock pins name, version, source and SHA-256,
   and holds the transitive closure; (c) archives are deterministic functions of a commit.
   Each is standard on its own; the combination is what makes a serverless registry
   possible.
3. **The riskiest single decision is the resolver, not the format.** A greedy "highest
   satisfying, one version per name, no backtracking" fixpoint is the one design in the
   family with a known bad failure mode, and Wiz's single global namespace removes the
   escape hatch every other ecosystem uses (install a second copy). Opam shows that the
   alternative is affordable.
4. **The first prototype had six cheap-to-fix defects**: the `^0`/`^0.0` caret bound; stale
   constraints in the resolver fixpoint; `update --locked` failing CI whenever the index
   published; a strict index decoder that forbade the format from growing; a
   non-recursive index reader that broke the documented `@org/name` layout; and no check
   that the index history fast-forwarded. All six have since been fixed (§2.2 to §2.7).
5. **The novel opportunity is module-prefix conflict detection at resolve time.** Because
   Wiz has one global namespace and "one name, one declaration", a registry that records
   each package's module names can reject two packages that would collide before a build.
   npm, Cargo and Opam cannot check this, because they have no global names to collide.
   Grail now does it (§2.10).
6. **Full TUF is the wrong cost/benefit here; two of its protections are not.** An ancestor
   check on the index commit (rollback protection) and a `(size …)` field (endless-data
   protection) are each a few lines. Signatures can come later behind a flag. Grail now has
   the ancestor check, records `size`, and verifies a signed index snapshot on request; the
   download cap is still missing.

---

## 1. Landscape

### 1.1 Table A: index, versions, selection, lock

| system | index form | version syntax | selection policy | lockfile | one version per name? |
|---|---|---|---|---|---|
| **Cargo** [H] | git repo of per-crate JSON-lines files + `config.json`, or **sparse** HTTP (`sparse+https://…/`, one file per crate) (V) | SemVer 2.0; `^`/`~`/`=`/comparisons/`*`; `1.2.*` | highest satisfying; **semver-compatible unification**, so 0.7 and 0.8 of one crate may coexist | `Cargo.lock`, `[[package]]` blocks, v3/v4 | no: one per semver-compatible range |
| **npm** [H] | HTTP registry (CouchDB-derived): `/<pkg>` packument, `/<pkg>/-/<pkg>-<v>.tgz` | semver + `\|\|`, `x`, hyphen ranges, tags (`latest`, `next`) | highest satisfying; **nested `node_modules`**, so N copies of a package may coexist | `package-lock.json` v2/v3; `npm ci` | no |
| **Opam** [H] | git repo `opam-repository`: `packages/<name>/<name>.<version>/opam` + `files/` | its own scheme (`~`, `+`, no epochs) | external solver over CUDF/CP (`aspcud`, `mccs`) with optimisation criteria | `.opam.locked` per package (`opam lock`, 2.1+); `opam install . --locked` (S) | **yes**: a switch is one coherent set |
| **Spack** [H] | recipes (`package.py`) in a repo; `spack repo add` | `@1.2:1.4`, `@:`, `@1.2:` | **clingo (ASP)** concretizer with optimisation over versions, compilers and variants | `spack.lock` (JSON, full DAG with hashes, inside an environment) | no (hash-distinct variants) |
| **Nix flakes** [H] | none for packages: git refs/URLs + the JSON `flake-registry` for names like `nixpkgs` | none (git rev; `narHash`) | input locks; `follows` deduplicates a transitive input | `flake.lock` (nodes with `locked.rev`, `narHash`, `lastModified`) | n/a: content-addressed store paths |
| **Dune** [H/M] | reuses Opam repositories; `(repositories …)` | opam versions | its own solver over opam metadata (`dune pkg lock`) | `dune.lock/` **directory**, one `*.pkg` per package (S) | yes |
| **Bazel/Bzlmod** [H] | **static HTTP or directory registry**: `/modules/$M/$V/{MODULE.bazel,source.json}`, `bazel_registry.json` (mirrors), `metadata.json` (`versions`, `yanked_versions`) (V) | its own ordering; `-pre` suffixes | **MVS-like**: highest required version wins per module; extensions locked separately | `MODULE.bazel.lock` (JSON: dependency graph + extension results; `--lockfile_mode`) | yes |
| **Go modules** [H] | module proxy protocol (`/@v/list`, `.info`, `.mod`, `.zip`); `GOPROXY` chain | SemVer 2.0 mandatory; `+incompatible` | **MVS**: the maximum of the minimums, never "highest available" | `go.mod` + `go.sum` (`go.mod` is the lock) | **yes** |
| **Maven** [H] | repo layout: `maven-metadata.xml` + POMs (+ `.sha1`, `.asc`) | its own ordering (`1.0-alpha-1` < `1.0`) | **nearest wins** (shortest path) + `dependencyManagement`; no backtracking | none (Gradle adds `gradle.lockfile`, `verification-metadata.xml`) | no (nearest wins picks one, silently) |
| **PyPI / pip** [H] | PEP 503 simple HTML or PEP 691 JSON per project, links + `#sha256=`; `.metadata` sidecars (PEP 658) | **PEP 440** (epoch, pre/post/dev, local versions) | pip: `resolvelib` **backtracking**; uv: PubGrub | none standardised: `requirements.txt` + `--require-hashes`, `uv.lock`, `poetry.lock`, `pdm.lock` | no |
| **Debian/apt** [H] | `dists/<suite>/<comp>/binary-<arch>/Packages` + `Sources`, hashed by a signed `Release`/`InRelease` | Debian version (`epoch:upstream-revision`) | apt's solver + **pin priorities** (`Preferences`, `apt-mark hold`) | none (the installed set is the state; `snapshot.debian.org` pins by date) | no, but `Provides`/`Conflicts`/`Replaces` model conflicts explicitly |

### 1.2 Table B: integrity, trust, offline, cache, names

| system | artifact integrity | signing / trust root | offline / vendoring | cache layout | namespace and conflict model |
|---|---|---|---|---|---|
| **Cargo** [H] | `sha256` of the `.crate` in the index **and** in the lock (`checksum`) | **none** for crates.io; `cargo-vet`/`crev` are community overlays [M] | `--offline`, `--locked`, `--frozen`; `cargo vendor` + `[source]` replacement | `$CARGO_HOME/registry/{index,cache,src}/…` | flat names, first publish wins; no scopes; two majors may coexist |
| **npm** [H] | **SRI** (`sha512-…`) in `package-lock.json` and `dist.integrity` | registry ECDSA signatures + `--provenance` (Sigstore) + `npm audit signatures` [M] | `npm ci --offline`, `npm pack`, `bundleDependencies` | `~/.npm/_cacache`, content-addressed (`index-v5` keys by URL+SRI) | scopes `@org/name`; nesting resolves conflicts |
| **Opam** [H] | `url { src: …; checksum: ["sha256=…"; "sha512=…"] }` | none in the repo (git history + review); `opam admin` checks checksums | `opam admin cache` (a local repo of tarballs), local pins | `~/.opam/download-cache/<2 hex>/<sha256>` | flat names; **one version per name**; `conflicts:` is a first-class field |
| **Spack** [H] | `sha256` per version in the recipe; **DAG hash** per spec | **GPG-signed buildcache**; configured trusted keys [M] | `spack mirror create` + `spack mirror add`; `concretizer:reuse` | `~/.spack/{cache,mirrors}` + the install tree | spec syntax `name@ver%compiler+variant`; variants coexist |
| **Nix** [H] | **`narHash`** (SHA-256 of a deterministic NAR serialisation) + store-path hash | `nix store sign` (ed25519) + `trusted-public-keys` on caches [M] | `nix flake archive`, `nix copy --to file://…`; the store is the cache | `/nix/store/<hash>-<name>`; `~/.cache/nix/…` | none (no names); collisions impossible by construction |
| **Dune** [H/M] | hashes in the lock's `*.pkg` sources | none beyond opam/git | `dune.lock/` committed; `~/.cache/dune` | `~/.cache/dune/db` + `_build` | opam names |
| **Bzlmod** [H] | **SRI** `integrity` in `source.json`; `sha256` for patches/overlays (V) | none in the registry (BCR = git + CI); `--distdir` digests | `--registry=file://…`, `--distdir`, repository cache | `~/.cache/bazel/…` (repository cache = CAS; action cache) | flat module names; **highest version wins**, `multiple_version_override` for exceptions [M] |
| **Go** [H] | `go.sum` `h1:` = SHA-256 over a canonical file tree (dirhash) + `/go.mod` hash | **checksum database**, a Trillian transparency log (`sum.golang.org`); `GONOSUMDB`/`GOPRIVATE` | `-mod=vendor` + `vendor/modules.txt`; `GOPROXY=off`; `GOMODCACHE` | `$GOMODCACHE/cache/download/<mod>/@v/*.zip`, `$GOCACHE` (content-addressed) | **module path = URL** (a real namespace); one version per path |
| **Maven/Gradle** [H] | `.sha1`/`.sha256` beside artifacts; Gradle `verification-metadata.xml` (checksums + PGP) | **PGP** per artifact; Central requires signatures and checksums [M] | `-o`/`--offline`; `~/.m2/repository`; Gradle `--offline` | `~/.m2/repository/<group>/<artifact>/<ver>/`; `~/.gradle/caches/modules-2` | `groupId:artifactId`; nearest wins silently picks one |
| **PyPI** [H] | `#sha256=` on every link; `--require-hashes`; PEP 658 metadata | **PEP 740** index-hosted attestations (Sigstore/in-toto) (S); **PEP 458** TUF for index metadata [M] | `pip download`, `--no-index --find-links`, wheel cache; `uv` lock | `~/.cache/pip` (HTTP + wheels, content-addressed); `uv`'s own CAS | flat, normalised names (PEP 503); **PEP 708** tracks against name takeover [M] |
| **Debian** [H] | `SHA256` per file in `Packages`/`Sources`; `Release` hashes the index files | **`InRelease` clearsigned** (OpenPGP); `apt-secure`; keyring in `trusted.gpg.d` | `--download-only`, local/partial mirrors, `snapshot.debian.org` | `/var/cache/apt/archives`, `/var/lib/apt/lists` | `Conflicts`/`Provides`/`Replaces`/`Breaks`, the richest conflict model here |

**Reading across the rows.** Three clusters:

* *Static text index in git*: Opam, Cargo (git protocol), Homebrew taps, Debian's own
  archive. *Static index over plain HTTP*: Cargo sparse, Bzlmod, PEP 503/691, Go proxies.
  Grail's choice (a git repository of S-expression files, plus directory and single-file
  forms for mirrors and tests) sits on the Opam/Cargo-git point, and the `sparse+`
  precedent says the same files can later be served over plain HTTP with no format change.
* *Lock holds the transitive closure*: Cargo, npm (the v2/v3 `packages` map), Opam (per
  package), Spack, Bzlmod (graph + extension results), Grail (lock v2 onwards). *Lock holds
  only roots*: `go.mod` is unusual in that the go command re-derives the closure from the
  module graph recorded there, with `go.sum` as the integrity sidecar.
* *One version per name*: Opam, Go, Bazel, Dune, and Grail. This is the majority among the
  build-tool registries and the minority among the web ones (npm, pip, Maven). Wiz is in
  good company.

### 1.3 Table C: cross-cutting standards worth reading before changing the format

| standard | what it fixes | relevance to Grail |
|---|---|---|
| **SemVer 2.0.0** [H] (V: semver.org) | precedence rules; build metadata ignored; pre-release ordering | Grail's `Version.cmp`/`Version.cmpPre` follow it, except that numeric identifiers with leading zeros are accepted |
| **PEP 440** [H/M] | a different, richer version algebra (epoch, post/dev, local) | a warning: do not grow epochs later; commit to SemVer now |
| **PubGrub (2018)** [H] (V) | CDCL over version *ranges*, with human-readable conflict explanations | the algorithm to adopt if the resolver is rewritten; uv, dart pub, bundler and poetry use it (V) |
| **ASP / clingo, SAT / libsolv** [H/M] | full CP/SAT solving with optimisation criteria | Spack (clingo), Opam (aspcud/mccs), dnf/zypper (libsolv): the "solve it properly" end of the spectrum |
| **MVS** [H] (M) | maximum of minimums; monotone, minimal upgrades | the cheap alternative to "highest satisfying" that avoids surprise upgrades |
| **TUF 1.0.37** [H] (V) | root/targets/snapshot/timestamp roles; rollback, freeze, mix-and-match, endless-data and extraneous-dependency defences | the checklist to audit the index against, even if only two roles are implemented |
| **PEP 458 / PEP 740 / Sigstore / Rekor / in-toto + SLSA** [H/M] | TUF for an index; index-hosted attestations; transparency log; provenance predicates | the roadmap for signed index state and for "the publisher verified the artifact" |
| **SRI** [H] | `sha256-<base64>` strings in HTML/JSON | Bzlmod uses it; hex `sha256` would be a needless deviation if Grail ever serves HTML/JSON |
| **SOURCE_DATE_EPOCH + reproducible-builds** [H/M] | one timestamp for every archive entry; `diffoscope` for diffs | `git archive \| gzip -n` is the git-specific instance; `tar --sort=name --mtime=@$SDE` is the recipe for non-git sources |
| **Cargo sparse index protocol** [H] (V) | plain HTTP per-crate files, `config.json`, caching headers | the upgrade path if `grail update` ever stops wanting a git clone |
| **Bazel registry** [H] (V) | `modules/$M/$V/source.json`, mirrors, `yanked_versions`, `local_path`, patches/overlays | the closest existing schema to Grail's index; borrow its field names |

---

## 2. Feature by feature

Notation: **Grail** = what Grail does now (code in `Grail/*.lean` and `lib/Grail.wiz`, docs
in [23-grail.md](../stages/23-grail.md) and
[index-repository.md](../stages/23-grail/index-repository.md)); **R** = recommendation;
**N** = novelty, judged plainly.

### 2.1 Manifest: `grail.wiz` as the single source of truth

**Grail.** `Package.version`, `Package.toolchain` and `Package.require NAME REQ` are
combinators in `lib/Grail.wiz`; the manifest is a Wiz program whose rendered S-expression
grail evaluates. Version, toolchain and requirements are optional, so older manifests
decode unchanged (`decodePackage` in `Grail/Config.lean` accepts the package node with or
without its last three fields).

**Prior art.** Cargo splits `Cargo.toml` (authored) from the index entry (published, but
generated from the manifest and tarball). npm has `package.json` plus a registry-side
packument. Opam's `opam` file *is* the registry entry (the repository contains the file the
author writes), which is why `opam pin` and `opam publish` are cheap. Bazel's registry
stores a `MODULE.bazel` per version in the registry, not in the archive (V): an explicit
decision to keep the registry authoritative.

**R1.** Keep one source of truth, with `grail publish` as the checker that the index entry
agrees with the archive's manifest. Grail does this (`publishEntry` and
`checkArchiveLayout` in `Grail/Registry.lean`). This is the Opam model, and it suits a small
ecosystem.

**R2.** Separate an informational "tested with" version (recorded in the lock) from the
`toolchain` range (a hard resolution filter). Cargo's MSRV field is advisory and only its
resolver v3 started considering it [M]; Opam's `ocaml` constraint is a real resolution
variable. Grail's `Package.toolchain` is documented as "the Wiz it was tested with (a
range)" and used as a filter, so it conflates the two; see §2.11.

**N.** None. Executable manifests are normal (Nix, Dhall, Starlark).

### 2.2 Versions and ranges

**Grail.** `Grail/Index.lean`: `Version` (major, minor, patch, pre), `Op` (`eq`, `ge`, `gt`,
`le`, `lt`, `caret`, `tilde`), `Clause` (op, version, number of components written), and
`Requirement = List Clause` (all must hold). Parsing accepts `1.2.3`, `1.2`, `1`,
`1.2.3-rc.1`, `^`, `~`, `>=`, `>`, `<=`, `<`, `=` and `*`.

Findings:

* **Caret bounds.** The first prototype ignored the number of components for `^`, so `^0`
  meant `<0.0.1` and `^0.0` meant `<0.0.1`, where Cargo and npm mean `<1.0.0` and `<0.1.0`.
  A `^0` is common in a young ecosystem. `Requirement.upper` now follows Cargo/npm: `^0` is
  `<1.0.0`, `^0.0` is `<0.1.0`, `^0.2.3` is `<0.3.0`, `^0.0.3` is `<0.0.4`.
* **`~` is right.** `~1` is `<2.0.0`; `~1.2` and `~1.2.3` are `<1.3.0`, matching npm.
* **Pre-releases** are excluded from any range whose comparator is not itself a
  pre-release (`Clause.holds`). Cargo and npm also admit a pre-release when some
  comparator has the same `major.minor.patch`. Grail's rule is stricter and simpler; with
  one version per name it stops an `-rc` leaking into everyone's build, so it is worth
  documenting rather than changing.
* **Build metadata is rejected, not ignored.** `Version.parse "1.2.3+abc"` fails (the `+`
  lands in a numeric field), and `1.2.3-rc.1+build` puts `rc.1+build` in the pre-release.
  SemVer says build metadata is ignored for precedence. Either strip `+…` when parsing or
  state "no build metadata".
* **No `||`, no `1.2.*`-style wildcards, no `!=`.** npm and Cargo have `||` and `1.2.*`.
  Adding `||` makes "one of these two incompatible worlds" expressible, which reduces
  resolution failures; it is the cheapest feature to add next. Representation:
  `Requirement` becomes `List (List Clause)` (disjunctive normal form), and `satisfies`
  becomes `any (all holds)`.
* **`=1.2` matches `1.2.0`**, because a short version fills the missing components with
  zero. That is correct; document it.

**N.** None; the syntax is deliberately npm's and Cargo's.

### 2.3 Index: schema, forward compatibility, static hosting

**Grail.** One file per package, `index/NAME.sexpr`:
`(index (package NAME (summary …) (repo …) (version V (source URL) (sha256 H) (size N)
(tree H) (commands H) (toolchain REQ) (modules …) (prefix …) (deps (dep N R)…)) (yanked V
WHY)))`. It is read from a directory, a single file, or a git URL cloned into
`<cache>/grail/index`. The lock records `(index URL COMMIT)`.

Findings and comparisons:

* **Forward compatibility.** The index is the shared artifact that old clients read: the day
  someone adds `(license …)`, an old client with a strict decoder refuses the whole
  package, and, since one bad file fails the read, the whole index. Cargo's index is
  JSON-lines where unknown keys are ignored; Bzlmod's `source.json` has typed optional
  fields and is versioned by path; Opam's format has a declared version and a documented
  deprecation cycle.
  **R3.** Ignore unknown *index* fields, stay strict for *lock* fields (a lock is a local
  trust anchor, so fail closed), and give the index an explicit format number so a future
  break is visible. Grail now does the first two (`Index.decodeVersion` and
  `Index.decodePackage` skip unknown fields; the lock decoder rejects them). An index
  repository's `registry.sexpr` and `index.wiz` carry a format number that
  `grail index check` checks; the client reader does not consult it.
* **Order-stable rendering.** A parse-then-render round trip should reproduce a canonical
  file, or every publish pull request shows a spurious diff and text comparison becomes
  fragile. Grail's `Index.render` sorts packages and `Index.decodePackage` sorts versions,
  so a decoded entry renders in version order.
  **R4.** Render versions and yanked entries in a canonical order and test that
  `render (parse s) == s` for a canonical fixture.
* **Scoped subdirectories.** The first prototype's reader did not recurse, so a documented
  `index/@org/name.sexpr` layout was silently skipped. **R5.** Recurse one level into
  scoped subdirectories, key each package by its path-derived name (`index/@org/name.sexpr`
  is `@org/name`), and add a fixture, so that "we left room for scopes" is true. Grail now
  does this: `readIndexDir` in `Grail/Registry.lean` reads one level of `@org/`
  subdirectories and the file name wins over the `(package …)` node inside. Scopes are not
  enforced in names or manifests yet.
* **Duplicate names across files are fatal.** That is right within one registry, but it
  forbids the two things static indexes are also for: an overlay (a company index
  shadowing or extending the public one) and sharded indexes. Bazel's `--registry` is an
  ordered list, earlier wins (V); Cargo allows source replacement; Opam allows several
  repositories with priorities. **R6.** Make `--index` repeatable, earlier wins per
  `name@version` (or per name), and keep the duplicate error within one registry. Grail
  lists repeatable `--index` overlays as deferred; `grail index check` warns about a
  dependency that another index provides.
* **One clone path for all indexes.** Grail clones every URL index into
  `<cache>/grail/index`, and `ensureClone` (`Grail/Deps.lean`) deletes and re-clones when
  the origin URL differs, so two projects using different indexes evict each other on every
  `grail update`. **R7.** Cache at `<cache>/grail/index/<sha256 of URL>/`, as Cargo hashes
  registry URLs. Still open (listed as deferred).
* **No default index.** A `require` without `--index` or `Package.set "index"` is an error:
  a deliberate no-magic stance, but the first run means reading a doc. **R8.** Compile in a
  default (the intended `https://github.com/wiz-pl/fate-index`), overridable by `--index`
  and `Package.set "index"`, as Cargo defaults to crates.io. Still open.
* **Schema gaps against Bzlmod**, the closest published schema (V): mirrors
  (`mirror_urls`), archive type, `strip_prefix`, patches/overlays with their own hashes,
  `presubmit.yml` (the BCR's "this version builds" evidence), `yanked_versions` as a map.
  Take `mirror_urls`, patches and `size`, and skip overlays and presubmit for now. `size`
  is a security fix rather than a feature (§2.6); Grail has added it.

**N.** S-expressions as the index wire format are mildly novel (Opam uses its own syntax,
Cargo JSON-lines, Bzlmod JSON, Debian RFC 822). The benefit is real (no new parser, line
diffs, the same reader as `grail.lock`), but it is a format choice of low strategic value,
and it costs interoperability (no `jq`, no existing registry tooling). Keep it; don't
oversell it.

### 2.4 Resolution

**Grail.** `Resolve.step` in `Grail/Index.lean` is a fixpoint. Each round it computes the
requirements on each name, picks for each name (in sorted order) the highest non-yanked
version that satisfies every requirement and the running toolchain, and stops when the
selection is unchanged; the fuel is 64 rounds. There is no backtracking; a conflict names
both requesters.

**Prior art, in increasing strength:**

1. **npm/Cargo greedy highest**: simple, fast, and the source of both ecosystems'
   most-complained-about failures. Cargo softens it by allowing two semver-incompatible
   versions; npm by nesting.
2. **MVS (Go, Bzlmod)**: take the maximum of the minimum requirements. No search, no
   backtracking, monotone in the manifests, and it makes `go mod tidy` explainable. The
   cost: "at least 1.4, because 1.3.9 has the bug" means bumping the requirement
   everywhere; Go's answer is "edit the requirement".
3. **Backtracking (pip/resolvelib)**: correct, but with the classic exponential blow-up and
   poor messages (`ResolutionImpossible` with a chain of causes).
4. **PubGrub**: CDCL over ranges, unit propagation, conflict-driven clause learning, and
   derived error messages of the form "because A ≥2 depends on B ≥2 and root needs B <2,
   A ≥2 is forbidden" (V). Used by uv, dart pub, bundler and poetry. The Rust
   implementation calls itself the designated replacement for Cargo's solver (V); whether
   Cargo's stable resolver uses it was not confirmed [M].
5. **ASP/SAT with optimisation (clingo, aspcud/mccs, libsolv)**: what Spack and Opam do.
   Correct and optimisable ("newest", "fewest changes"), with a heavy dependency (a solver
   binary) and error messages worse than PubGrub's.

**Two structural defects in the first prototype, both since fixed:**

* **Stale constraints.** The prototype's constraint map only grew. If round 1 picked
  `a 2.0` and round 2 forbade it, round 2 picked `a 1.5`, but `a 2.0`'s dependencies stayed
  in the map, so a package only `a 2.0` needed kept constraining the graph and could make a
  satisfiable graph fail. PubGrub retracts; MVS never has the problem, because its choice
  set is a join, not a search.
  **R9.** Rebuild the constraint map from scratch each round from the roots and the
  dependencies of the *current selection*,
  `cons' = roots ∪ ⋃_{n∈selection} deps(selection[n])`, pick, and repeat until the
  selection is unchanged. Grail now does this: `Resolve.constraintsOf` builds the map from
  the roots and the current selection, and `Resolve.step` iterates until the selection is
  stable, so requirements that only a replaced version introduced are retracted.
* **`--locked` re-resolved, so CI broke when the index published.** In the prototype,
  `grail update --locked` resolved afresh and compared the rendered text. As soon as a
  dependency published `1.2.1`, every project on `^1.2` produced a different lock, and
  `--locked` failed on a machine that had changed nothing. Cargo's `--locked` means "do not
  write the lock; fail if the manifest needs a change", not "re-query the registry"; npm's
  `npm ci` installs exactly the lock. **R10.** Split the operations: `grail update`
  re-resolves and writes; a separate command prints what would change; `--locked` only
  checks the lock (complete, requirements satisfied, hashes well-formed) with no index
  access. Grail now does this: `--locked` on `update`, `fetch` and `vendor` is a check
  (`checkLocked`) that reads no index, and `grail index resolve` prints what a fresh update
  would choose.

**R11 (algorithm).** Do not write CDCL now, but do not ship the greedy fixpoint as the final
answer either. Keep the current shape with R9, and add one escape hatch: a bounded
depth-first search over candidate versions only (each name's satisfying versions in
descending order, a node budget of a few thousand, memoised failure sets). That is roughly
60 lines, gives exact answers for the graphs a young ecosystem has (tens of packages,
fan-out below 10), and reproduces PubGrub's answers without its machinery. Adopt real
PubGrub when the first "why can't I install these two" report arrives; the index format
does not change either way. Still open: Grail's resolver does not backtrack.

**R12 (MVS option).** Offer `grail update --minimal` (pick the lowest satisfying version,
as Cargo's `-Z minimal-versions` and Go's default do) as a testing mode for library
authors. It is the only practical way to find that a lower bound in a manifest is false,
and it costs one flag. Do not make it the default. Listed as deferred.

**N.** "One version per name, so the resolver must satisfy every requirement with one
version" is Opam's and Go's position. Grail's *reason* (one global namespace in the
language, 23b) is unusual and worth stating: the resolver's rigidity follows from the
kernel's "one name, one declaration", not from preference.

### 2.5 Lockfile design

**Grail.** `grail.lock` holds `(version 3)`, `(toolchain VERSION [COMMIT])`,
`(index URL COMMIT)`, an optional `(index-signature …)`, git dependencies
`(dep NAME URL REV COMMIT CONTENT)`, registry packages
`(pkg NAME VERSION SOURCE SHA256 (size N) (tree H) (commands H) (deps "NAME REQ" …))` and
machine-local `(override NAME PATH HASH)` entries. Files without `(version …)` are read as
v1 (git only) or v2 (with `index`/`pkg`) by inspection; a newer version is refused.
`checkLocked` verifies completeness, hash shape, requirement satisfaction and the index pin.
`grail update` writes only when the text differs, and `fetch` never reads the index.

**Comparisons.** Cargo.lock: `[[package]]` with `name`, `version`, `source`, `checksum`,
`dependencies`, plus a top-level `version = 3|4` and the root packages (so `--locked` can
tell "the lock is stale for this workspace" from "the registry moved"). npm v3: a flat
`packages` map keyed by install path, with dependencies as a graph of paths: compact,
machine-readable, and hard to merge. Go: no lock beyond `go.mod` + `go.sum`, which works
because MVS is idempotent. Nix: `flake.lock` with one node per input and `narHash`, small
and stable. Bzlmod: a JSON lock that records not just versions but extension evaluation
results, to detect non-reproducible extensions. That last idea is instructive because it
treats "the build definition is a program" as something to pin, and `grail.wiz` is a
program too.

Findings, with their status:

* **R13 (schema version).** Add `(version 3)` as the first entry, keep reading header-less
  files as v1/v2 by inspection, and refuse a version newer than the binary with a clear
  message. Implemented.
* **R14 (toolchain record).** The lock's content depends on the running toolchain (the
  `toolchain` field filters versions), so the lock should say which toolchain resolved it,
  and a build should warn, not fail, when that differs. Implemented: the lock records
  `Wiz.version` and the release commit when known, and a build prints a note when the
  running grail differs.
* **R15 (merge-friendly text).** One line per entry, edges as a flat
  `(deps "std ^1" "text ~1.0")` list, entries sorted by name. Nix's one-node-per-line lock
  merges well in practice. Implemented (`Lock.renderPkg`); v2's nested `(deps (dep …))` is
  still read.
* **R16 (git dependency hashes).** A git dependency's `CONTENT` is a 64-bit
  non-cryptographic hash of the working tree (`contentHash` in `Grail/Deps.lean`): it
  detects accidents, not attacks. Use a SHA-256 over a sorted `(path, sha256)` list, as
  Go's dirhash does, and keep the 64-bit value as a fast path. Also exclude
  `grail.local.wiz` by basename, not by exact relative path. The basename exclusion is
  implemented (`packageFiles`); the SHA-256 tree hash for git dependencies is still open
  (registry packages have one, R20).
* **R17 (binding index pins).** A lock's index commit is audit metadata unless something
  makes it binding. Implemented: `--index URL#COMMIT` or `Package.set "index-commit"` makes
  `update` resolve from that commit and `checkLocked` refuse a lock from another one;
  without a pin, the recorded commit is audit metadata.

**N.** None. The shape is Cargo's, minus the root packages and plus the index URL and
commit (which Cargo lacks and Nix has in spirit).

### 2.6 Integrity: archives, determinism, tree hashes

**Grail.** `scripts/grail-archive.sh` makes the archive:
`git archive --format=tar --prefix=NAME-VERSION/ COMMIT | gzip -n`. `grail publish` checks
the layout (one `NAME-VERSION/` holding `grail.wiz`), hashes the file and prints the entry.
Fetch downloads to `<cache>/grail/downloads/<sha256>`, verifies the hash before unpacking,
unpacks with `tar -xzf --strip-components=1 --no-same-owner` into a temporary directory,
checks the lock's tree hash when there is one, stamps `.grail-pkg`, and renames it into the
shared store.

Why the archive is deterministic: `git archive` stamps every entry with the *commit*
timestamp and emits entries in tree order, and `gzip -n` omits the file name and mtime from
the gzip header. The bytes are a pure function of the commit, and anyone can re-derive the
hash. That is the same discipline as `SOURCE_DATE_EPOCH` with `tar --sort=name --mtime` in
reproducible-builds [H/M], and it is stronger than Cargo's `.crate` (a tar.gz of a staging
directory, reproducible only because Cargo normalises it) and PyPI sdists (frequently not
reproducible).

**R18 (verify, don't trust).** Have the index's CI rebuild the archive from the tag and
compare hashes before merging a publish pull request. That turns "the hash is what the
author uploaded" into "the hash is what the commit produces", which is what makes the
deterministic-archive claim load-bearing. `grail index check` recomputes the hash of every
local archive in an index; an automated rebuild from the tag is still listed as missing.

**R19 (endless data).** Add `(size BYTES)` to each version and cap the download
(`curl --max-filesize`, and a check after the fact for `file://`). TUF lists endless-data
attacks as a first-class threat (V): without a cap, a hostile `source` can stream until the
disk fills, and the SHA-256 check happens only at the end. Grail records `size` (publish
writes it, the lock and signed snapshot carry it, and it is checked against local
archives), but the download has no cap yet.

**R20 (tree hash).** Add `(tree SHA256)` to `pkg` entries, checked after unpacking. This
closes the gap "a hand-edited file inside a registry package is not detected". Go's `h1:`
dirhash and Nix's `narHash` are the two proven constructions; Go's is simpler (sorted
`path\0sha256` lines, hashed). Implemented: `treeHash` in `Grail/Registry.lean` hashes the
sorted paths and file hashes, and `ensurePkg` checks it before the tree enters the shared
store.

**R21 (extraction hygiene).** `--strip-components=1` will strip a *different* top
directory than `NAME-VERSION`; fetch should verify that the single top-level component is
`NAME-VERSION` (publish already does), so an index entry cannot smuggle in a differently
named tree. Also reject absolute and `..` members explicitly rather than relying on GNU
tar's defaults, and state the policy on hidden files (they are legitimate; keep them). A
hostile archive remains an attack surface (symlink-then-write, decompression bombs); 23m's
"Trust: fetch is not build" says so. Still open: fetch does not check the top-level name
(when the lock has a tree hash, a different tree is refused anyway).

**N.** "A deterministic tarball as the index's only artifact" is not novel (Homebrew
bottles, Nix `fetchurl`, Bzlmod `source.json`), but doing it without a server, a database
or an upload endpoint is a simplification worth a sentence in the docs.

### 2.7 Signing, TUF, transparency logs

**Grail.** The trust story is SHA-256 for bytes, review for names, git for history and
HTTPS for transport, plus, when requested, a signed index snapshot (below). Archives are
not signed individually.

**What TUF would add, mapped to this design** (V: the specification's own attack list), as
it stood for the first prototype:

| TUF attack | covered in the first prototype? | cheapest closure |
|---|---|---|
| arbitrary installation / wrong software | yes: the lock pins name, version, source and hash | none needed |
| extraneous dependencies | yes: the lock holds the closure and `checkLocked` refuses an incomplete graph | none needed |
| rollback (an older version served) | **no**: `update` took whatever the index tip said | ancestor check (R22) |
| freeze (a stale index served forever) | **no**: no timestamps, no expiry | an `(updated …)` field and a warning after N days, or a signed snapshot with a monotone counter |
| mix-and-match (metadata from different epochs) | partially: one commit hashes one tree | record the index commit *and* a hash of the index files read |
| endless data | **no** | R19 (`size` and a cap) |
| key compromise | n/a (no keys) | a multi-signature root when signing arrives |

The current coverage, after R19, R22 and the signed snapshot, is tabulated in
[index-repository.md](../stages/23-grail/index-repository.md): rollback and mix-and-match
are covered, freeze, endless data and key compromise partially.

**R22 (rollback protection from git ancestry).** The prototype's `grail update` ran
`git fetch` and `git reset --hard FETCH_HEAD`, so it accepted a rewritten index history (a
force-push that removes a version or rewrites an entry's hash) silently. Instead, when the
lock records an index commit, require `git merge-base --is-ancestor <locked> <new>` and fail
with "the index history was rewritten (locked at A, now at B)" unless `--allow-rewind` is
passed. This is TUF's rollback protection at the cost of git's own Merkle DAG, and it makes
"what did the index look like when this resolved?" exact. Implemented in
`Grail/Registry.lean`, with that message and flag.

**R23 (signing, staged).**

* *Signed index tags, no new format.* Tag index releases, sign them with an SSH or GPG key,
  and add `grail update --require-signature`, which runs `git verify-tag` and records the
  tag in the lock. Precedent: Debian's `InRelease`, a signature over the index's own
  metadata, and Homebrew's signed taps [M]. No new cryptography in Lean, and no key
  distribution beyond `allowed_signers`.
* *A signed snapshot file.* `index/snapshot.sexpr` lists every `name@version` with its
  SHA-256 and size, plus a monotone sequence number and an update time, and a detached
  signature beside it. Clients verify one signature, then read entries. This is TUF's
  targets and timestamp roles collapsed into two files; it keeps the "static text"
  property and gives freeze and rollback protection without a server. PEP 458 is the same
  idea applied to PyPI [H/M].
* *Provenance and transparency.* PEP 740-style attestations (Sigstore, an in-toto
  `Statement` with a `predicateType` per ecosystem) attached to the publish pull request,
  and an append-only publish log (Rekor is the public instance; a log over the index's git
  history is the minimal version). The repository's existing attestation vocabulary
  (`wiz-build-manifest/v1`) is the natural thing to reuse rather than inventing a second
  one.

Grail implements the signed-snapshot form, which its docs call Stage 1:
`index/snapshot.sexpr` with `(seq)`, `(updated)`, `(key)` and `(expires)`, signed with
`ssh-keygen -Y sign -n grail-index`; `grail update --require-signature --allowed-signers
FILE` verifies it offline and pins the key, sequence and digest in the lock's
`(index-signature …)` entry (`Grail/Signature.lean`). Signed tags and a transparency log
are not implemented.

**R24.** Do *not* sign individual archives. Ecosystems that did (Maven Central's PGP per
artifact) end up with a key per maintainer, an unusable revocation story, and users who
disable verification. Sign the index state (one key, one place) and let the hash chain bind
archives to it. That is TUF's core lesson: delegate trust to the metadata, not the
artifact. Grail follows this.

**N.** None of this is novel. Git ancestry as rollback protection over a static index is a
good fit that the survey did not find documented as such, but it is an application, not an
invention.

### 2.8 Cache layout

**Grail.** Archives live in `<cache>/grail/downloads/<sha256>` (the same cache root as the
elaboration cache, chosen by `--cache`), unpacked trees in `<cache>/grail/packages/<sha256>/`
with `.grail/packages/NAME` a symlink to one (or a copy where a symlink cannot be made), and
a URL index's clone in `<cache>/grail/index`. The build store is
`<project>/.grail/build/<key>/`, with installed outputs listed in `.grail/installed`.

**Prior art.**

* Cargo: `$CARGO_HOME/registry/{index/<hash>, cache/<hash>/*.crate, src/<hash>/<name>-<ver>/}`;
  the unpacked source lives in the shared home, not the project.
* npm: `_cacache` is a pure content-addressed blob store with a separate index
  (`index-v5/<sha256 of key>`), so two URLs serving identical bytes share one blob.
* pnpm: a global content-addressable store, hardlinked into `node_modules/.pnpm`.
* Nix: one store, paths computed from inputs; `nix copy` moves closures between stores.
* Go: `$GOMODCACHE/cache/download/<mod>/@v/{list,info,mod,zip,ziphash}`, a per-module-path
  layout with a content-addressed `.ziphash` sidecar.
* Bazel: a repository cache (CAS keyed by digest) and an action cache; `--disk_cache`.

**R25 (shared store).** Unpack registry packages into a shared, content-addressed store and
make the project's `.grail/packages/NAME` point into it: no duplicate unpacking across
projects or checkouts, and `grail clean` cannot destroy what another project is using.
Implemented (23n).

**R26 (crash safety).** Keep the archive store content-addressed by SHA-256 and make sure a
crash mid-download cannot leave a file that looks verified. Grail downloads and unpacks into
`.tmp<pid>` paths and renames them, and re-verifies a cached archive on every use, which is
equivalent to Go's sidecar habit.

**R27 (cache commands).** Hash the index URL into its cache path (R7) and add `grail cache`
subcommands (`path`, `list`, `verify`, `prune`), the analogue of `npm cache verify`. Without
`verify`, a corrupted store is found one package at a time. `grail cache path`, `list` and
`verify` are implemented (23n); `prune` and the per-URL index path are not.

### 2.9 Offline builds and vendoring

**Grail.** `--offline` on `update`, `fetch` and `vendor` refuses to clone the index or a git
dependency and requires the archive cache; `fetch --locked` never writes the lock; builds
need no index, and `--offline` on a build makes a missing archive or clone an error rather
than a download.

**Prior art.** Cargo: `--offline`, `--frozen` (`--locked` plus `--offline`), `cargo vendor`
(writes `vendor/` and a `.cargo/config.toml` with `[source]` replacement, so the lock is not
rewritten). Go: `-mod=vendor` with `vendor/modules.txt` (the lock is checked against the
vendor tree), `GOPROXY=off`. npm: `npm ci --offline`, `npm pack`, `bundleDependencies`.
Opam: `opam admin cache` builds a tarball repository; `--download-only`. Debian:
`--download-only`, a local mirror, and `snapshot.debian.org`.

**R28 (vendoring).** Add `grail vendor`: copy the lock's archives to `vendor/` named by
hash (so two packages with the same bytes share a file), write an index of
`name@version → file`, and make a `--vendor DIR` option look archives up there at fetch
time only. Do not rewrite the lock's `source`: that would break hash-identical locks across
machines. Cargo's source replacement and Go's `-mod=vendor` both keep the lock intact.
Implemented (23n): `vendor/<sha256>.tar.gz`, `vendor/index.sexpr` with
`(archive NAME VERSION SHA256 FILE)` lines, and `--vendor DIR` or `Package.set "vendor"`.

**R29 (strict `--offline`).** A missing archive under `--offline` is an error naming the
package, not a silent download. Implemented.

**R30 (hermetic CI prelude).** `grail fetch --locked --offline` is the CI prelude for
hermetic builds; document it next to the Nix setup. Documented in 23m, 23n and
[building.md](../building.md), with the `--vendor` variant.

### 2.10 Namespaces and conflicts

**Grail.** Global lowercase names `[a-z][a-z0-9-]{0,63}`; one file per name; one version
per name per build. The reader accepts the scoped layout `index/@org/name.sexpr` (R5), and
`grail index check` accepts `@org/name`, but scopes are not enforced in names or manifests.

**Prior art.** npm scopes (`@org/name`) exist partly against squatting and partly for
namespacing; PEP 708 tracks exist because flat names get taken over when a project is
abandoned; Cargo has no scopes and lives with squatting; Go makes the module path a URL, so
`github.com/org/repo` is the namespace (and typosquatting is a real attack); Debian's
`Conflicts`/`Provides` is the richest model and the most expensive to reason about; Nix
sidesteps names entirely.

**R31.** Choose explicitly between two approaches:

* *Scopes later, paths now.* Keep flat names, but make the reader recursive (R5) and key by
  path, so `index/@org/name.sexpr` works the day it is needed. Add a reserved-prefix rule
  so first-party packages cannot be squatted. The reader half is implemented; the
  reservation is not.
* *Module prefixes are the real namespace.* Wiz's module names are global, and a package's
  modules are `Ddr3.Ctrl` and so on, so two packages can have valid, distinct package names
  and still collide at `import`.
  **R32 (the novel part).** Have `grail publish` record the package's module names
  (computed from its `lib` roots and file paths) as `(modules "Ddr3" "Ddr3.Ctrl" …)` or a
  reserved `(prefix "Ddr3")`, and have resolution refuse a selection in which two packages
  claim overlapping module prefixes, naming both packages and the clashing modules. This
  turns "one global namespace" from a build-time surprise into a resolver error, and no
  surveyed system does it (npm, Cargo and Opam cannot; their namespaces are per package).
  It enforces 23b's "one name, one declaration" before a build. Implemented: `grail publish`
  records `(modules …)`, `Resolve.moduleConflicts` refuses an overlapping selection, and
  `grail index check` reports conflicts in an index (index-repository.md, "The
  module-prefix rule").
* *Yanking, not deletion.* Grail yanks and never deletes; old locks keep working because
  fetch never reads the index. This is npm's `deprecate` (rather than `unpublish`) and
  Cargo's `yank`, for the same reason.

### 2.11 Toolchain pins (tower) and the package registry

**Grail.** tower installs toolchains by spec (`nightly`, `stable`, `vX.Y.Z`,
`REF@COMMIT`, linked names), selected by `wiz-toolchain` or `wiz-toolchain.local` files
found walking up from the current directory (26a). The registry's `toolchain` field is a
range checked against `Wiz.version` (`Resolve.toolchainOk`); a checkout reports
`0.1.0-dev`, and the check strips the pre-release, so it counts as `0.1.0`.

**Prior art.** rustup: `rust-toolchain.toml` (channel, components, targets) pins the
compiler but never constrains dependency resolution. elan: `lean-toolchain`, one line, no
ranges. Opam: the `ocaml` package is a real resolution variable: a switch is built for one
compiler version, and the solver chooses packages compatible with it. Nix: the compiler is
part of the derivation's inputs, so "which toolchain" is just another locked input (the
strongest answer). Spack: `%gcc@12` is a spec dimension the concretizer solves over. Cargo:
`rust-version` (MSRV) is considered by resolver v3 [M].

**Findings.**

* Every checkout reports the same `0.1.0-dev`, so every development build looks like
  `0.1.0`, and `toolchain` filtering does little in exactly the environment where packages
  are developed and published. **R33.** Use the release commit when it is known, treat a
  checkout as "unknown: allow everything, warn once", and record what was used in the lock.
  Grail now records `Wiz.version` and the release commit in the lock (R14); the filter
  itself is unchanged.
* **Range against spec.** A range is right for the index (portable, independent of any
  installer), but resolving a range against a tower spec is impossible without a
  version-to-spec map. **R34.** Keep the range in the index and add to the lock the tower
  spec when the toolchain came from tower, so a locked fetch can say "this lock wants
  `v0.2.0`, you have `nightly`" and CI can install the right one. That is the elan/rustup
  contract with the registry's portability. Still open.
* **Two releases, one library.** Once a second release changes `lib/`, a package that says
  `>=0.1 <0.3` resolves differently on the two, and the same lock is "valid" on both. That
  is Opam's situation with compiler versions, and why Opam's solver treats the compiler as
  a variable. **R35.** If the ecosystem ever runs two toolchain lines, promote `toolchain`
  from a filter to a resolution variable (`grail update --toolchain 0.2.1` solves with it
  fixed). The current filter is the degenerate one-variable case; the data model already
  supports the general one. Still open.

### 2.12 `Package.command` recipes and non-hermetic builds

**Grail.** Commands (23i) are jobs with declared inputs and outputs, keyed over tool
identity, with arguments as data (never a shell line). Outputs are staged in
`.grail/tmp/<job>/out/`, renamed into the store, and installed back into the package with a
record in `.grail/installed`. 23i says plainly that nothing is sandboxed and declared
inputs cannot be checked for completeness: "This is make's and ninja's contract, not
Nix's."

**Prior art.** Bazel: hermetic, sandboxed actions with declared inputs enforced, remote
execution and CAS. Nix: derivations as pure functions, a sandbox on Linux, store paths as
identities. Dune: sandboxing modes (`copy`, `symlink`, `hardlink`) to catch undeclared
dependencies. Spack: builds in a controlled prefix with recorded dependencies. make/ninja:
exactly the contract grail documents.

**R36.** That honesty is right; do not chase Bazel. Two cheap improvements stay inside the
make/ninja contract:

1. **Best-effort `--sandbox`.** On Linux, run the command with a private `/tmp` and a
   read-only view of the package, or at least with `TMPDIR` redirected and the working
   directory holding only declared inputs. Dune's sandboxing shows the value: it is how
   you *discover* an undeclared input, not how you prevent malice. Not implemented.
2. **A command digest in the lock.** A `Package.command` is part of what a package does.
   Put a hash of the declared command set into the lock's `pkg` entry, so a version that
   silently gains a build-time command is a visible lock change, as Bzlmod's recorded
   extension results make a non-reproducible extension visible (V). Implemented:
   `commandDigest` in `Grail/Registry.lean` covers every field of every command, `grail
   publish` writes `(commands …)` and lock v3 records it.

**N.** Declared-input commands are Ninja's model. A lock that covers the command set is,
as far as the survey found, not done elsewhere (other ecosystems' locks record artifacts,
not build recipes). Modest, real and cheap.

### 2.13 Monorepos, workspaces and path dependencies

**Grail.** There is no workspace concept. When the survey was written, a downstream
package approximated a path dependency with `Package.lib "ddr3" "../wiz-ddr3/src"`: a
library target whose root is outside the package. That gives module roots and checking, but no version, no lock
and no fetch, and the modules join the consumer's target graph.

**Prior art.** Cargo workspaces: one lock for all members, `path` dependencies between
members, `[patch]` to override a registry dependency with a path, and `-p` to select a
member. npm/pnpm/yarn workspaces: the `workspace:*` protocol, one lock, hoisting. Go:
`go.work` (a workspace file, not committed by default) with `replace` directives. Bazel:
`local_path_override` for a module under development and the registry's `local_path` source
type (V). Nix: `follows`. Opam: `opam pin add . --kind=path` and dune's `vendored_dirs`.

**R37 (local overrides).** Add `Package.override NAME PATH`, usable only in the uncommitted
`grail.local.wiz`, like the toolchain settings. During resolution `NAME` is taken from
`PATH`; the lock records the override in a separate section; a plain build prints one line
saying the override is in use; and `--locked` refuses a lock with an override. This is
Cargo's `[patch]` power with npm's `link:` discipline and without Go's `replace` pitfalls
(which do get committed, and break `go install` for everyone else). Implemented (lock v3's
`(override NAME PATH HASH)`; an edited override no longer matches the locked tree and is
refused until `grail update`).

**R38.** Do not build workspace or lock sharing yet. One lock per package matches "one
package, one `grail.wiz`, one build graph". Revisit only when two first-party packages must
be released in lockstep; then copy `go.work` (an uncommitted workspace file), not Cargo's
shared lock (which makes `--locked` ambiguous about which member moved).

**N.** None.

### 2.14 Reproducibility and provenance, end to end

The chain that makes a build reproducible: deterministic archive, SHA-256 in the index,
lock pinning name, version, source and hash, fetch verifying before unpacking, the tree
hash checked after unpacking (R20), module keys hashing module text, job keys hashing tool
identity, and a store keyed by job key. The toolchain is now in the lock (R14). Two gaps
remain outside the registry: the C compiler and flags come from `grail.local.wiz`
(machine-local and uncommitted, which is right for portability, but the lock does not
record them, so "same lock, same sources, different C compiler" is invisible), and
`Package.command` outputs are only as reproducible as the tool (23i says so).

**R39.** A `grail build --manifest` that writes the exact inputs of a successful build
(toolchain identity and version, the `grail` binary's key, package tree hashes, command
identities) is almost the data the job keys already compute, and it is what the
repository's `wiz-build-manifest/v1` attestation format wants to sign. Emit that format;
do not invent another. Not implemented.

**R40.** Publish a `(reproducible true)` flag only when the index's CI has actually
rebuilt the archive from the tag and matched the hash (R18). Any other use of the word is
false, and a small ecosystem cannot afford that. Not implemented.

---

## 3. Novelty assessment

Scored 1 to 5: "novel" is how much would surprise someone who knows Cargo, Opam, Bzlmod and
TUF; "effort" is lower when cheaper; "value" is what it buys the project.

| element | prior art | novel | effort | value | verdict |
|---|---|---|---|---|---|
| static git index of text files | Opam, Cargo-git, Homebrew taps, Debian | 1 | n/a | n/a | standard; keep |
| S-expression index format | Opam's own syntax, RFC 822, JSON | 2 | n/a | low | a taste choice; fine, don't market it |
| deterministic `git archive \| gzip -n` + SHA-256 | reproducible-builds, Nix, Homebrew | 1 | n/a | high | standard and well chosen |
| lock with index URL + commit | Nix `flake.lock` (rev), Bzlmod | 2 | 1 | medium | slightly better than Cargo |
| lock holds the transitive closure | Cargo, npm, Spack, Bzlmod | 1 | n/a | high | right call |
| one version per name (forced by the language) | Opam, Go, Bazel | 2 | n/a | n/a | unusual reason, standard policy; say so |
| toolchain range as a resolution filter | Opam `ocaml`, Spack `%compiler`, Cargo MSRV | 3 | 2 | high | rare and well motivated; fix the development-version case |
| **module-prefix conflict check at resolve time** | none found | **4** | 2 | **high** | the one genuinely new idea here; small and defensible |
| **lock covers the `Package.command` set** | none found (locks pin artifacts, not recipes) | **4** | 2 | medium | novel because the build language is a program; cheap |
| signed index snapshot instead of signed artifacts | TUF, Debian `InRelease` | 2 | 3 | high | right shape, standard parts |
| git ancestry as rollback protection | TUF rollback (different mechanism) | 3 | 1 | high | an application, not an invention |
| command targets with declared I/O | Ninja, make, Bazel actions | 1 | n/a | n/a | explicitly make's contract |
| one-file-per-package index | Opam, Cargo, Bzlmod | 1 | n/a | n/a | standard |

**What is new, in one sentence each:**

1. *Resolve-time module-namespace checking*: possible only because Wiz has one global
   namespace; it makes the language's constraint a tool error instead of a build error.
2. *A lock that pins build recipes, not just source artifacts*: a consequence of
   `grail.wiz` being a program and of `Package.command` running arbitrary tools.
3. *A registry with no server, upload API, database or tokens, whose whole published state
   is a git tree of S-expressions plus immutable deterministic tarballs*: each ingredient
   exists (Opam, Cargo sparse, Nix), but the survey found no other instance of this
   combination with a language-level global namespace to protect.

**What is not new and should not be presented as such:** the resolver, `--locked` and
`--offline`, the `update`/`fetch` split, SHA-256 archives, yanking, the
manifest/index/lock split, vendoring, and the "fetch is not build" warning. Each is 5 to 15
years old elsewhere. The accurate claim is "the standard design, adapted to a language with
one global namespace".

**The main weakness.** One version per name, highest satisfying and no backtracking is the
combination with the worst failure mode in the survey: Go avoids it with MVS (no search,
monotone), Opam and Spack with real solvers, Cargo and npm with version splitting. Wiz has
removed the escape hatch and kept the weakest search. R9 is in place; the next steps are
the bounded search (R11) or PubGrub before the index is large, and treating the resolver's
error messages as a product surface (PubGrub's reputation rests on its messages).

---

## 4. Implications for Grail

Most of the format and correctness work this survey recommended has landed: lock v3 (R13,
R14, R15, R19's `size`, R20, R36's command digest, R37's overrides), index forward
compatibility and scoped paths (R3, R5), the caret fix, the resolver's retraction (R9),
`--locked` as a check (R10), binding index pins (R17), the ancestry check (R22), a signed
index snapshot (R23's snapshot form), module-prefix conflicts (R32), and the shared store,
vendoring and cache commands (R25, R28, R29, R30, most of R27).

What remains open, roughly in order of value:

1. **Resolver strength**: a bounded search or PubGrub (R11), `--minimal` (R12), and `||`
   in requirements (§2.2).
2. **Integrity gaps**: a download cap from `size` (R19), extraction hygiene (R21), a
   SHA-256 tree hash for git dependencies (R16), and an automated archive rebuild in the
   index's CI (R18, R40).
3. **Index hosting**: a default index (R8), per-URL index caches (R7), repeatable `--index`
   overlays (R6), a canonical-render test (R4), and the reserved first-party scope (R31).
4. **Toolchain**: a tower spec in the lock and a meaningful development version (R33,
   R34); a toolchain resolution variable only if two toolchain lines ever coexist (R35).
5. **Signing**: key rotation without re-locking, a freshness warning, and a transparency
   log or attestations (the later stages of R23).
6. **Build provenance**: `--sandbox` (R36) and a build manifest (R39).

Two policy questions are governance rather than engineering: whether `std` (which ships
with the toolchain) should ever appear in the index, and if so whether the toolchain's copy
always wins; and the rule of thumb for dependencies, *registry for packages you did not
write, a git `dep` for a source you chose, an override for a machine-local development
copy*. Git dependencies should stay supported indefinitely, as Bazel keeps `git_override`
and Cargo keeps `git` dependencies. Note the asymmetry: git dependencies are resolved from
their manifests, registry dependencies from the index; it is Cargo's asymmetry, and it is
why a registry-only build needs no manifest evaluation.

Compatibility rules that are cheap to keep now and impossible to add later:

* A lock written by a newer grail is refused with a clear message, never partly understood.
  Grail does this for `(version N)` above 3.
* An index read by an older grail degrades: unknown fields are ignored and the package
  stays usable. The two policies are deliberately opposite.
* `grail.lock` is sorted text, one entry per line; a resolution that changes nothing writes
  nothing.
* `source` URLs are immutable by contract; a moved archive is a new version, and the index
  never rewrites a `sha256`.
* `name@version` is immutable; a bad release is yanked, never replaced.
* Nothing in `.grail/` is authoritative; deleting it must stay safe as the store moves into
  the shared cache.
* Never rename a package in the index. A rename is a new package plus a yank note; aliases
  are how Homebrew's `brew migrate` and Debian's `Provides` became permanent complexity.

---

## 5. Bibliography

Format: what the source supports, the reference, a confidence marker, and whether it was
checked against the page (V), seen in a search snippet (S), or cited from memory of a
canonical document (M).

1. SemVer 2.0.0 precedence and syntax: https://semver.org/ [H] (M).
2. Cargo registry protocols (git and sparse, the `sparse+` prefix, `config.toml`
   registries): https://doc.rust-lang.org/cargo/reference/registries.html [H] (V).
3. Cargo, specifying dependencies (`^`, `~`, `*`, `1.2.*`, multiple versions):
   https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html [H] (M).
4. Cargo resolver, feature unification, `resolver = "2"`/`"3"`, MSRV-aware resolution:
   https://doc.rust-lang.org/cargo/reference/resolver.html [M] (M).
5. `Cargo.lock` against `Cargo.toml`, `--locked`/`--frozen`/`--offline`:
   https://doc.rust-lang.org/cargo/guide/cargo-toml-vs-cargo-lock.html and
   https://doc.rust-lang.org/cargo/commands/cargo-build.html [H] (M).
6. Cargo vendoring and source replacement:
   https://doc.rust-lang.org/cargo/reference/source-replacement.html and `cargo vendor`
   [H] (M).
7. PubGrub, the algorithm and its error messages: N. Weizenbaum, "PubGrub: Next-Generation
   Version Solving", April 2018,
   https://nex3.medium.com/pubgrub-next-generation-version-solving-2fb6470504f [H] (S)
   (originally at medium.com/@nex3/pubgrub-2fb6470504f).
8. PubGrub implementations and adopters (uv, dart pub, bundler, poetry; "designated
   replacement for cargo's solver"; CDCL; ASP lineage): https://github.com/pubgrub-rs/pubgrub
   [H] (V).
9. Bazel registries (index layout, `source.json`, SRI `integrity`, mirrors,
   `yanked_versions`, `local_path`, patches and overlays): https://bazel.build/external/registry
   [H] (V).
10. Bzlmod `MODULE.bazel.lock` and `--lockfile_mode`: https://bazel.build/external/module
    (and `bazel help mod`) [M] (M).
11. TUF specification 1.0.37 (roles; rollback, freeze, mix-and-match and endless-data
    attacks; consistent snapshots): https://theupdateframework.github.io/specification/latest/
    [H] (V).
12. Go modules reference (MVS, `go.sum`, the checksum database, `GOPROXY`, `GOMODCACHE`,
    `-mod=vendor`, `go.work`): https://go.dev/ref/mod [H] (M).
13. Go dirhash (`h1:` = SHA-256 over a canonical file list):
    https://pkg.go.dev/golang.org/x/mod/sumdb/dirhash [H] (M).
14. Opam repository layout, `opam lock`, `.opam.locked`, `opam install . --locked` (2.1+):
    https://opam.ocaml.org/doc/man/opam-lock.html and https://opam.ocaml.org/blog/opam-2-1-0/
    [H] (S).
15. Opam, CUDF and external solvers (aspcud, mccs), optimisation criteria:
    https://opam.ocaml.org/doc/External_solvers.html [M] (M).
16. Spack concretization with clingo, `spack.lock`, environments, buildcache signing:
    https://spack.readthedocs.io/en/latest/{concretization,environments,build_caches}.html
    [M] (M).
17. Nix flakes, `flake.lock`, `narHash`: https://nix.dev/concepts/flakes and
    https://nixos.org/manual/nix/stable/command-ref/new-cli/nix3-flake.html [H] (M).
18. Nix store-path signing (`nix store sign`, `trusted-public-keys`):
    https://nixos.org/manual/nix/stable/command-ref/nix-store.html [M] (M).
19. Dune package management (lock directory `dune.lock/`, `dune pkg lock`, repositories):
    https://dune.readthedocs.io/en/stable/explanation/package-management.html [H/M] (S)
    (the one-`*.pkg`-per-package detail is from a secondary source).
20. npm `package-lock.json` versions, `npm ci`, integrity fields:
    https://docs.npmjs.com/cli/configuring-npm/package-lock-json [M] (M).
21. npm registry signatures and provenance:
    https://docs.npmjs.com/generating-provenance-statements and `npm audit signatures`
    [M] (M).
22. `cacache` (npm's content-addressable cache, `index-v5`): https://github.com/npm/cacache
    [M] (M).
23. pnpm store and hardlinks: https://pnpm.io/symlinked-node-modules-structure [M] (M).
24. PyPI simple repository API (PEP 503 HTML, PEP 691 JSON), hashes on links:
    https://packaging.python.org/en/latest/specifications/simple-repository-api/ [H] (M).
25. PEP 658 (`.metadata` sidecars), PEP 700 (index fields), PEP 708 (tracks):
    https://peps.python.org/pep-0658/, https://peps.python.org/pep-0700/,
    https://peps.python.org/pep-0708/ [M] (M).
26. PEP 440 (version identification): https://peps.python.org/pep-0440/ [H] (M).
27. PEP 740 (index-hosted attestations, in-toto + Sigstore, the `provenance` key):
    https://peps.python.org/pep-0740/ [H] (S).
28. PEP 458 (TUF for PyPI): https://peps.python.org/pep-0458/ [M] (M).
29. pip's resolver (`resolvelib`, backtracking):
    https://pip.pypa.io/en/stable/topics/dependency-resolution/ [M] (M).
30. uv (PubGrub, universal lockfile): https://docs.astral.sh/uv/concepts/resolution/
    [M] (M).
31. Maven dependency mechanism, nearest wins, `dependencyManagement`:
    https://maven.apache.org/guides/introduction/introduction-to-dependency-mechanism.html
    [M] (M).
32. Gradle dependency locking, `verification-metadata.xml`, module metadata:
    https://docs.gradle.org/current/userguide/dependency_locking.html and
    https://docs.gradle.org/current/userguide/dependency_verification.html [M] (M).
33. Maven Central requirements (PGP signatures, checksums):
    https://central.sonatype.org/publish/requirements/ [M] (M).
34. Debian `Release`/`InRelease`, `apt-secure`, hash fields in `Packages`/`Sources`:
    https://www.debian.org/doc/manuals/debian-reference/ch02.en.html and `apt-secure(8)`
    [H] (M).
35. `snapshot.debian.org`: https://snapshot.debian.org/ [H] (M).
36. Reproducible builds, `SOURCE_DATE_EPOCH`:
    https://reproducible-builds.org/specs/source-date-epoch/ [H] (M).
37. `git archive` determinism (commit-timestamped entries) and `gzip -n`:
    https://git-scm.com/docs/git-archive and `gzip(1)` [H] (M); `scripts/grail-archive.sh`
    states the argument.
38. W3C Subresource Integrity (SRI): https://www.w3.org/TR/SRI/ [H] (M).
39. Sigstore and the Rekor transparency log: https://docs.sigstore.dev/logging/overview/
    [M] (M).
40. in-toto statements and SLSA provenance: https://slsa.dev/spec/v1.0/provenance [M] (M).
41. libsolv (the SAT solver behind libzypp/zypper and dnf):
    https://github.com/openSUSE/libsolv [M] (M).
42. CDCL and ASP background as cited by PubGrub's authors: Gebser, Kaminski, Kaufmann and
    Schaub, *Answer Set Solving in Practice* [M] (M) (cited in 8; not read for this survey).
43. Homebrew taps as a static index of formulae: https://docs.brew.sh/Taps [M] (M).
44. Cargo sparse-index HTTP details (`config.json`, per-crate file paths, caching):
    https://doc.rust-lang.org/cargo/reference/registry-index.html [M] (M).
45. Lean 4 Lake and `lake-manifest.json` as the in-family analogue of a lock:
    https://github.com/leanprover/lean4/blob/master/src/lake/README.md [M] (M). The Wiz
    repository itself uses `lake-manifest.json` and `lean-toolchain`, the closest
    structural precedent for `grail.lock` and `wiz-toolchain`.

### 5.1 Claims not verified

* **Whether Cargo's stable resolver ships PubGrub.** The pubgrub-rs README calls its Rust
  implementation the "designated replacement for cargo's solver" and names uv as a user
  (V); no Cargo release enabling it was confirmed. Treat "Cargo uses PubGrub" as unproven.
* **npm `lockfileVersion` defaults per npm major.** v2 is believed to be npm 7 and 8's
  default and v3 npm 9's, with v3 dropping the backward-compatible `dependencies` tree [M];
  the exact cutover is unverified.
* **Maven Central's current checksum algorithms** (SHA-1 historically; SHA-256/512 added
  later) [M].
* **Spack's clingo concretizer becoming the only option**, and the release [M].
* **apt 3.x's new solver** (`solver3`), and whether pin priorities are still the primary
  conflict mechanism [M].
* **Dune's lockfile being one `*.pkg` per package**: seen only in a secondary write-up (S),
  not in Dune's own reference.
* **PEP 458's rollout status on PyPI** (TUF metadata for the index; partial in practice)
  [M].
* **uv.lock's exact schema** (`resolution-markers`, universal lock semantics) [M].
