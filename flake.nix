{
  # The toolchain Wiz's tests need besides Lean: GMP (the C and LLVM backends), LLVM's
  # `llc`, Boehm GC (the self-hosted backend's runtime), a C compiler, and elan (which
  # installs the Lean version in `lean-toolchain`). CI runs every step in this shell
  # (`nix develop`); locally, `nix develop` gives the same environment as
  # /workspace/wiz-env.sh, and writes grail.local.wiz for grail.
  #
  # The packages: `wiz` (the default; it has `grail` too), built with Lake and the Lean
  # of nixpkgs (which must be the version in `lean-toolchain`), and wrapped with this
  # toolchain as flags; `wiz-nvim`, the Neovim plugin, and `nvim-wiz`, Neovim with it
  # and wiz (`nix run .#nvim-wiz`); `reference`, the standard library's reference
  # manual, generated with that wiz (never committed); `wiz-web`, `wiz-playground`,
  # `wiz-playground-ui` and `wiz-source-ui`, the Wasm page modules (`web/build*.sh`)
  # built by a derivation instead of in each CI job. CI pushes them to the Cachix cache
  # `badlydrawnwizards`; see docs/building.md for `nix run`.
  description = "Wiz: a didactic dependently typed language";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      # (R2, wiz-notes/sota-numerics.md §5.2) The bignum the kernel's `Nat` computes
      # with, pinned by version *and* source hash. Lean admits GMP into the kernel TCB
      # and requires >= 6.3.0. The two build paths carry the same upstream release in
      # different archives: nixpkgs builds GMP from the `.tar.bz2`, the release bundles
      # the `.tar.xz` (scripts/bundle-cc.sources); both hashes are recorded in
      # `docs/release/gmp-pin.json`, and the assert below names the actual and pinned
      # nix hashes (and both archives) when nixpkgs picks a different GMP. Changing the
      # bignum is a deliberate attestation update, never a flake-update side effect.
      gmpPin = {
        version = "6.3.0";
        nixSrcHash = "sha256-rCghGnz7YJuuLiyNYFjWbI/pZDT3QM9v4uR7AA0cIMs=";
        releaseSrcHash = "sha256-a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898";
      };
      gmpSrcHash = pkgs: let src = pkgs.gmp.src; in
        src.outputHash or (src.drvAttrs.outputHash or "unknown");

      # The toolchain `wiz build` and grail use: where GMP and Boehm GC live, and `llc`.
      toolchain = pkgs: {
        cflags = "-I${pkgs.gmp.dev}/include";
        ldflags = "-L${pkgs.gmp}/lib -Wl,-rpath,${pkgs.gmp}/lib";
        llc = "${pkgs.llvm}/bin/llc";
        gc-cflags = "-I${pkgs.boehmgc.dev}/include";
        gc-ldflags = "-L${pkgs.boehmgc}/lib -Wl,-rpath,${pkgs.boehmgc}/lib -lgc -lpthread";
      };

      # The empty seed `withLakeCache` starts from: a real store path, so the function's
      # argument is never nullable and the producer is an ordinary derivation whose cold
      # compile the sandbox enforces (no cache, no dev shell, no network).
      #
      # `.lake/build/.keep` is load-bearing: nixpkgs' fixupPhase prunes empty
      # directories, so an empty `.lake/build` disappears and the seed becomes an
      # empty store path. `lake-cache.sh build` then refuses it (`$seed/.lake is
      # missing`) and `withLakeCache` asserts the same. The file is what keeps the
      # directory, and it costs nothing in the build.
      emptyLake = pkgs:
        pkgs.runCommand "empty-lake" { } ''
          mkdir -p $out/.lake/build
          : > $out/.lake/build/.keep
          install -Dm644 ${./lean-toolchain} $out/toolchain
        '';

      packagesFor = pkgs: packagesWith pkgs null;

      # The same packages, built from a prebuilt `.lake` (`lakeCache`): a *different*
      # derivation from the pure build (the seed is an input, so the hash differs).
      # Applied to `empty-lake` it is the trusted producer (a cold build inside the
      # sandbox); applied to a restored seed it is a pull request's warm build. The
      # `unwrapped` derivation also has a `lake` output: the seed the producer saves.
      # A flake output cannot be a function in `packages`, but `lib` may hold one.
      withLakeCache = pkgs: lakeCache: packagesWith pkgs lakeCache;

      packagesWith = pkgs: lakeCache:
        let
          lib = pkgs.lib;
          fs = lib.fileset;
          lean = pkgs.lean4;
          pinned = lib.removePrefix "leanprover/lean4:v" (lib.trim (builtins.readFile ./lean-toolchain));
          tc = toolchain pkgs;
          # The commit this evaluation is from: the release's REVISION file, the
          # documentation's source links, and the epoch the archive metadata uses.
          revision = self.rev or self.dirtyRev or "unknown";
          epoch = toString self.lastModified;
          sourceUrl = "https://github.com/wiz-pl/wiz/blob/${revision}";

          # every file the build reads: a change elsewhere (README, tests, Wiz programs)
          # doesn't rebuild the compiler.
          buildSrc = fs.toSource {
            root = ./.;
            fileset = fs.unions [
              ./lakefile.lean ./lake-manifest.json ./lean-toolchain
              ./Main.lean ./Wiz.lean ./Wiz ./WizMeta.lean ./WizMeta ./Grail.lean ./Grail
              ./STC.lean ./STC # the metatheory library the STC bridge test imports
              ./Tests # the test driver (`packages.tests`)
              ./runtime # the C runtime (wiz_rt.h, rt_*.inc) and WizRuntime.lean, which embeds it (include_str)
              ./c # linked into the executables (moreLinkObjs)
            ];
          };

          # wiz and grail as Lake builds them (unwrapped) — the release path.
          pureUnwrapped =
            assert lib.assertMsg (lean.version == pinned)
              "flake.nix: nixpkgs has Lean ${lean.version} but lean-toolchain says ${pinned}: update the nixpkgs input (nix flake update) or lean-toolchain";
            # (R2) the release's GMP identity: the actual and pinned hashes are named
            assert lib.assertMsg (pkgs.gmp.version == gmpPin.version && gmpSrcHash pkgs == gmpPin.nixSrcHash)
              "flake.nix: GMP is ${pkgs.gmp.version} with nix source ${gmpSrcHash pkgs}, but the pin is GMP ${gmpPin.version} with nix source ${gmpPin.nixSrcHash} (release archive ${gmpPin.releaseSrcHash}); see docs/release/gmp-pin.json. Update the pin and the attestation deliberately, or the release's bignum identity has changed";
            pkgs.stdenv.mkDerivation {
              pname = "wiz-unwrapped";
              version = "0.1.0";
              src = buildSrc;
              nativeBuildInputs = [ lean ];
              buildPhase = ''
                runHook preBuild
                # no dependencies to fetch (lake-manifest.json); Lake's artifact cache in the sandbox
                # (`tests` is the test driver: `packages.tests` installs it from here)
                export HOME=$TMPDIR LAKE_CACHE_DIR=$TMPDIR/lake-cache
                lake build wiz grail tests
                runHook postBuild
              '';
              installPhase = ''
                runHook preInstall
                mkdir -p $out/bin
                install -m755 .lake/build/bin/wiz .lake/build/bin/grail .lake/build/bin/tests $out/bin/
                runHook postInstall
              '';
            };

          # The same three binaries from `lakeCache`'s compiled modules. Lake keys an
          # olean on its inputs' content hashes, so it recompiles exactly what the tree
          # changed and links the rest; the `toolchain` stamp refuses a seed built for
          # another lean-toolchain. This derivation has two outputs:
          #   `out`   the binaries, exactly as the pure build has them (a build from
          #           `empty-lake` is the same compile, so its bytes are identical);
          #   `lake`  what Lake wrote, for the next build: `.lake/build/lib` (oleans,
          #           `.ilean`, traces), `.lake/build/ir`, `.lake/config`, and the
          #           `toolchain` stamp. `build/bin` is left out (the consumer relinks
          #           in seconds) and `.lake/cache` never exists here (the build phase
          #           puts `LAKE_CACHE_DIR` in `$TMPDIR`).
          cachedUnwrapped =
            assert lib.assertMsg (lakeCache != null)
              "flake.nix withLakeCache: no lakeCache seed";
            assert lib.assertMsg (builtins.pathExists (lakeCache + "/toolchain"))
              "flake.nix withLakeCache: ${toString lakeCache} has no toolchain stamp (a seed is a withLakeCache `lake` output or `empty-lake`)";
            assert lib.assertMsg
              ((builtins.readFile (lakeCache + "/toolchain")) == (builtins.readFile ./lean-toolchain))
              "flake.nix withLakeCache: ${toString lakeCache} was built for another lean-toolchain; refusing a stale .lake";
            pkgs.stdenv.mkDerivation {
              pname = "wiz-unwrapped-lake-cache";
              version = "0.1.0";
              src = buildSrc;
              nativeBuildInputs = [ lean ];
              outputs = [ "out" "lake" ];
              buildPhase = ''
                runHook preBuild
                export HOME=$TMPDIR LAKE_CACHE_DIR=$TMPDIR/lake-cache
                if [ ! -d ${lakeCache}/.lake ]; then
                  echo "withLakeCache: ${lakeCache}/.lake is missing" >&2
                  exit 1
                fi
                cp -a ${lakeCache}/.lake .lake
                chmod -R u+w .lake
                lake build wiz grail tests
                runHook postBuild
              '';
              installPhase = ''
                runHook preInstall
                # the binaries, as the pure derivation installs them
                mkdir -p $out/bin
                install -m755 .lake/build/bin/wiz .lake/build/bin/grail .lake/build/bin/tests $out/bin/
                if [ ! -d .lake/build/lib ]; then
                  echo "withLakeCache: lake build wrote no .lake/build/lib" >&2
                  exit 1
                fi
                # the next build's seed, without the linked binaries
                mkdir -p $lake/.lake/build
                cp -a .lake/build/lib $lake/.lake/build/lib
                if [ -d .lake/build/ir ]; then cp -a .lake/build/ir $lake/.lake/build/ir; fi
                if [ -d .lake/config ]; then cp -a .lake/config $lake/.lake/config; fi
                install -Dm644 ${./lean-toolchain} $lake/toolchain
                runHook postInstall
              '';
            };

          unwrapped = if lakeCache == null then pureUnwrapped else cachedUnwrapped;

          # The toolchain as flags (stage 23a: nothing reads the environment). Flags on
          # the command line come later and win.
          tcFlags = [
            "--cc" "${pkgs.stdenv.cc}/bin/cc"
            "--cflags" tc.cflags "--ldflags" tc.ldflags "--llc" tc.llc
            "--gc-cflags" tc.gc-cflags "--gc-ldflags" tc.gc-ldflags
          ];
          addFlags = flags: lib.escapeShellArg (lib.escapeShellArgs flags);
          # The same flags as separate shell words, for a command line (the prewarm
          # below); `addFlags` is for `--add-flags`, which takes one escaped string.
          addArgs = flags: lib.concatMapStringsSep " " lib.escapeShellArg flags;

          # The site's own files `wiz doc` copies into OUT: the plain page's scripts and
          # the `--serve` client.
          # They are installed at `share/wiz/web`, which is where `wiz doc` looks beside
          # the toolchain's `lib/` (`Main.webDir`), and a fileset so only these files
          # enter the store: `scripts/check-release-web-assets.py` checks this list
          # covers everything `Wiz.Doc.run` copies, and a name without a file is a nix
          # evaluation error.
          # (The Wasm module and the infoview page come from `wiz-web`, which needs
          # `wiz`: a release gets them from `web/build.sh`; see scripts/release-tarball.sh.)
          docSiteAssets = [
            "scroll.css" "scroll.js" "scroll-search.js" "highlight.css"
            "lsp-client.js" "doc-live.js" "doc-live.css"
            "framework/mount.js" "framework/driver.js" "framework/runtime.js"
            "framework/adopt.js"
          ];
          docSiteSource = fs.toSource {
            root = ./web;
            fileset = fs.unions (map (f: ./web + "/${f}") docSiteAssets);
          };

          # $out/share/wiz is laid out like a checkout (lib/ next to .lake/build/bin/),
          # which is where grail looks for the standard library.
          wiz = pkgs.stdenv.mkDerivation {
            pname = "wiz";
            inherit (unwrapped) version;
            dontUnpack = true;
            nativeBuildInputs = [ pkgs.makeWrapper ];
            installPhase = ''
              share=$out/share/wiz
              mkdir -p $share/.lake/build/bin $out/bin $share/web
              cp -r ${fs.toSource { root = ./lib; fileset = ./lib; }} $share/lib
              # the site assets `wiz doc` reads (the release half of the asset lookup;
              # a checkout's `web/` is the other, and `--web` wins over both)
              cp -r ${docSiteSource}/. $share/web/
              # (F12) the Wasm backend's JS host, beside lib/ where `wiz run` looks for it
              mkdir -p $share/web
              install -m644 ${./web/wasm-host.mjs} $share/web/wasm-host.mjs
              # the marker editors look for (editors/nvim: a library file is served by its toolchain's wiz)
              echo 'A Wiz toolchain: lib/ is its standard library, .lake/build/bin/ its binaries, ../../bin/ its commands (editors use this file to find them).' > $share/TOOLCHAIN
              cp ${unwrapped}/bin/wiz ${unwrapped}/bin/grail $share/.lake/build/bin/
              # The packaged read-only elaboration cache: elaborate every module of the
              # standard library once, with the binary the wrapper runs (the same bytes,
              # the same toolchain flags and the same toolchain-library layout, so the
              # keys match a user's run; `Toolchain.tag` hashes the flags and is part of
              # every manifest's strong key, so omitting them would make the whole layer
              # a clean miss).
              # Check a one-line `import M` rather than M's file: checking the file
              # elaborates it as the main file, whose commands are keyed by the main
              # text and never hit by an importer. `import M` stores M's effect under
              # M's module key and writes its seen marker, which is what a user hits.
              # Run one check per module concurrently. The cache is content-addressed:
              # a key is the chained hash of the text (and of the imports' keys), and every
              # file is written to a temporary name and renamed into place
              # (`Cache.writeAtomic`), so two processes that elaborate one import write the
              # same bytes and a reader sees either the old file or the whole new one. Each
              # module is still checked exactly once; the order only decides how much of an
              # import's closure is already warm, not what is stored. `NIX_BUILD_CORES` is
              # the build's `--cores` (4 on the CI runner); the cap keeps a very wide host
              # from starting one wiz process per module.
              # A lib module that does not check is a real failure: xargs runs the rest and
              # exits non-zero, and the phase fails.
              export HOME=$TMPDIR
              cd $share
              cache=$share/cache
              mkdir -p "$cache"
              jobs=''${NIX_BUILD_CORES:-0}
              [ -n "$jobs" ] || jobs=0
              case "$jobs" in *[!0-9]*) jobs=0 ;; esac
              if [ "$jobs" -le 0 ]; then jobs=4; fi
              [ "$jobs" -le 8 ] || jobs=8
              echo "prewarm: $jobs concurrent wiz check processes"
              cat > "$TMPDIR/check-module.sh" <<'EOF'
#!/bin/sh
# check-module.sh WIZ CACHE LIB TMP FLAGS... MODULE: check `import MODULE` through a
# fresh root file (a module's own file would be keyed as a main file, never hit by an
# importer).
set -e
wiz=$1 cache=$2 lib=$3 tmp=$4 module=$5
shift 5
root=$(mktemp "$tmp/lib-import.XXXXXX.wiz")
trap 'rm -f "$root"' EXIT
printf 'import %s\n' "$module" > "$root"
"$wiz" "$@" --cache "$cache" -I "$lib" check "$root"
EOF
              find lib -name '*.wiz' | LC_ALL=C sort | while IFS= read -r f; do
                m=''${f#lib/}; m=''${m%.wiz}; m=''${m//\//.}
                printf '%s\n' "$m"
              done | xargs -P "$jobs" -I@ sh "$TMPDIR/check-module.sh" \
                "$PWD/.lake/build/bin/wiz" "$cache" "$share/lib" "$TMPDIR" @ ${addArgs tcFlags}
              # grail elaborates in-process under its *own* binary hash (the build file,
              # Grail and Prelude, before every command, and each `check` job), so it
              # hits none of the entries above: the two namespaces are disjoint by
              # design (Cache.binaryId). Warm grail's too, with a minimal package: its
              # `grail.wiz` elaborates Grail and Prelude, and the check target elaborates
              # Std's closure, which is the fixed cost of a first `grail build` (measured:
              # 437 entries, 3.3 MB, ~3 s here, against ~0 store hits without it). A
              # module outside Std's closure is elaborated once into the user's cache.
              # `grail build` reads the build file and runs the check job in one go.
              # Warm both with the same toolchain flags the wrappers add
              # (`addFlags tcFlags`): `Toolchain.tag` hashes exactly those fields and
              # enters the strong key of every manifest, so a cache warmed without them
              # is a clean miss for every wrapper invocation.
              warm=$TMPDIR/warm-pkg
              mkdir -p "$warm"
              printf '%s\n' 'import Grail' \
                'def package : Package := Package.new "warm"' \
                '  |> Package.check "std" "main.wiz"' > "$warm/grail.wiz"
              printf 'import Std\n' > "$warm/main.wiz"
              .lake/build/bin/grail ${addArgs tcFlags} -C "$warm" --cache "$cache" build
              # The binary's memo names the build-time executable path in its stamp, and the
              # per-root pointers name the build-time import files; both are write-cache
              # aids that a `--cache-ro` layer never reads, so the store ships neither.
              rm -rf "$cache/bin" "$cache/roots"
              chmod -R a-w "$cache"
              # wiz's module roots: ./lib (a checkout's), then the packaged standard library
              makeWrapper $share/.lake/build/bin/wiz $out/bin/wiz \
                --prefix PATH : ${lib.makeBinPath [ pkgs.coreutils ]} \
                --add-flags ${addFlags (tcFlags ++ [ "-I" "${placeholder "out"}/share/wiz/lib"
                  "--cache-ro" "${placeholder "out"}/share/wiz/cache" "--cache-ro-unsigned" ])}
              # grail: git fetches dependencies (stage 23h)
              makeWrapper $share/.lake/build/bin/grail $out/bin/grail \
                --prefix PATH : ${lib.makeBinPath [ pkgs.coreutils pkgs.git ]} \
                --add-flags ${addFlags (tcFlags ++ [ "--cache-ro" "${placeholder "out"}/share/wiz/cache"
                  "--cache-ro-unsigned" ])}
            '';
            meta = {
              description = "Wiz, a didactic dependently typed language, and grail, its build tool";
              mainProgram = "wiz";
              platforms = systems;
            };
          };
          # The test driver (`tests --list`, `tests --run GROUP INDEX`), from the same
          # build as wiz and grail (so `nix build .#wiz` builds it too). The driver looks
          # for `wiz`/`grail` beside itself (`IO.appPath.parent` in Tests/Grail.lean), so
          # the wrapped binaries are installed here too: their flags carry the packaged
          # library, cache and C toolchain, exactly what a `.lake/build/bin/wiz` in a
          # checkout has.
          tests = pkgs.stdenv.mkDerivation {
            pname = "wiz-tests";
            inherit (unwrapped) version;
            dontUnpack = true;
            installPhase = ''
              runHook preInstall
              mkdir -p $out/bin
              install -m755 ${unwrapped}/bin/tests $out/bin/tests
              install -m755 ${wiz}/bin/wiz $out/bin/wiz
              install -m755 ${wiz}/bin/grail $out/bin/grail
              runHook postInstall
            '';
            meta = {
              description = "The Wiz test driver";
              mainProgram = "tests";
              platforms = systems;
            };
          };
          # The standard library's reference manual (stage 11s; `wiz doc --lib --reference`):
          # built, not committed. It reads only the packaged wiz (its lib/ and its
          # read-only elaboration cache), so while the compiler and lib/ are unchanged a
          # rebuild is a Cachix hit. $out/index.md is the Markdown manual; $out/site is the
          # plain-HTML site it came with (reference.html among its pages).
          reference = pkgs.stdenv.mkDerivation {
            pname = "wiz-reference";
            inherit (unwrapped) version;
            dontUnpack = true;
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR
              ${wiz}/bin/wiz doc --lib -o site --reference manual
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              mkdir -p $out
              cp manual/index.md $out/index.md
              cp -r site $out/site
              runHook postInstall
            '';
            meta = {
              description = "The Wiz standard library reference manual (generated)";
              platforms = systems;
            };
          };
          # The Wiz→wasm page modules (stages 11n/11ab/11w) as derivations, so that Cachix
          # serves them: CI's `web` job used to run every Emscripten build inside its
          # single test step (95 % of it, ~10 min and an 8–10 GiB `wasm-opt -O2` tail),
          # and the `docs` job ran two of them again on every push. Each derivation runs the
          # same script a developer runs, with the packaged wiz, `emcc` on PATH (so the
          # script does not `nix shell`) and mini-gmp from `--gmp-src` (so it does not
          # `nix build`): no network at build time. `$out` is the script's OUT directory
          # — the module pair plus the page files it copies beside them — and the scripts
          # can copy it with `--from` (`WIZ_WEB_FROM`, `WIZ_PLAYGROUND_FROM`,
          # `WIZ_PLAYGROUND_UI_FROM`).
          #
          # The `src` filesets list exactly what each script reads: a change to a test or
          # a page it does not touch leaves the module in the cache. A script that starts
          # copying one more page file must add it here — the build fails loudly (a
          # `cp: cannot stat`) rather than publishing a site with a missing file.
          wiz-web = pkgs.stdenv.mkDerivation {
            pname = "wiz-web";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [
                # the program it compiles (`link_c "js.c"` is resolved beside Web.wiz)
                ./web/build.sh ./web/Web.wiz ./web/js.c
                # the page files the script copies into OUT
                ./web/infoview.html ./web/infoview.js ./web/playground-lsp.js
                ./web/lsp-client.js ./web/widgets.js ./web/widgets.css
                ./web/hover.js ./web/squiggles.js ./web/completions.js
                ./web/scroll.js ./web/scroll-search.js ./web/scroll.css ./web/highlight.css
                ./web/overlays.css
                ./web/doc-live.js ./web/doc-live.css
                ./web/framework/mount.js ./web/framework/driver.js ./web/framework/runtime.js
                ./web/framework/adopt.js ./web/framework/editor-text.js
                ./web/infoview-ui.wiz ./web/docs-ui.wiz ./web/doc-live-ui.wiz
                ./web/build-infoview-ui.sh ./web/build-docs-ui.sh ./web/build-doc-live-ui.sh
              ];
            };
            nativeBuildInputs = [ wiz pkgs.emscripten ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR EM_CACHE=$TMPDIR/emscripten-cache WIZ=${wiz}/bin/wiz
              sh web/build.sh out --gmp-src ${pkgs.gmp.src}
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              cp -r out $out
              runHook postInstall
            '';
            meta = {
              description = "The web documentation module (wiz-infoview.mjs/.wasm, web/build.sh)";
              platforms = systems;
            };
          };
          wiz-playground = pkgs.stdenv.mkDerivation {
            pname = "wiz-playground";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [
                # the engine (the self-hosted frontend) and the export
                ./web/build-playground.sh ./web/playground-exports.wiz
                # the module list the script reads from the Lean side, one source for both
                ./Wiz/Selfhost.lean
                ./selfhost/Lex.wiz ./selfhost/Parse.wiz ./selfhost/Kernel.wiz
                ./selfhost/CParse.wiz ./selfhost/CGlue.wiz ./selfhost/Frontend.wiz
                ./selfhost/Tables.wiz
                # the page files the script copies into OUT, and the generator that
                # fills the static-complete page (the same Loom renderer as the runtime)
                ./web/playground.html ./web/playground.js
                ./web/playground_static_gen.wiz ./web/playground_static.mjs
                ./web/playground.css ./web/overlays.css ./web/widgets.css
                ./web/lsp-client.js ./web/widgets.js
                ./web/playground-lsp.js ./web/selfhost-lsp-shim.js
                ./web/playground-engine.js
                # the entry point's mount contract (mount imports driver, which imports
                # runtime.js and adopt.js): build-playground.sh copies all of them
                ./web/framework/mount.js ./web/framework/driver.js
                ./web/framework/runtime.js ./web/framework/adopt.js
                ./web/framework/editor-text.js
                # the page's runtime (web/build-playground-ui.sh, built below): its Wiz
                # app, the FFI it links and the library modules it imports. The rest of
                # lib/ resolves from the packaged toolchain's own library.
                ./web/build-playground-ui.sh ./web/playground-ui.wiz ./web/js.c
                ./lib/Web/Loom.wiz ./lib/Web/Editor.wiz ./lib/Web/EditorModel.wiz
                ./lib/Web/Playground.wiz ./lib/Web/Examples.wiz
                ./lib/Web/Goals.wiz ./lib/Web/Hover.wiz
                ./web/squiggles.js ./web/completions.js ./web/hover.js
              ];
            };
            # node: web/playground_static.mjs fills the static-complete page.
            nativeBuildInputs = [ wiz pkgs.emscripten pkgs.nodejs ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR EM_CACHE=$TMPDIR/emscripten-cache WIZ=${wiz}/bin/wiz
              # -O1: emcc runs binaryen's `wasm-opt` at -O2 and up, and on this module that
              # stage peaks at 16.9 GiB (measured 2026-11-18) — it is SIGKILLed on a 16 GB
              # CI runner. -O1 (LLVM's, without binaryen) is 2.3 GiB and ~3 min faster, for
              # a module 47 % larger (11.4 MB against 7.75 MB). The script still defaults
              # to the compiler's -O2, so a local build is unchanged.
              sh web/build-playground.sh out --gmp-src ${pkgs.gmp.src} --opt 1
              # the page's runtime (the whole page as one Loom app), beside the engine:
              # the site requires it, so one store path carries both modules.
              sh web/build-playground-ui.sh out --gmp-src ${pkgs.gmp.src}
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              cp -r out $out
              runHook postInstall
            '';
            meta = {
              description = "The playground's Wasm modules (the engine and the Loom page, web/build-playground*.sh)";
              platforms = systems;
            };
          };
          # The playground page's Loom UI module (`?ui=loom`, stage 11w's page as one Loom
          # app): small, but built by `web/test.sh` and the web job only through this, so a
          # `web` job still needs no Emscripten. `lib/` is its `-I` root (the module is
          # `web/playground-ui.wiz` and imports Web.{Loom,Playground,Editor} and their
          # dependencies), so any library change rebuilds it — correct, and cheap.
          wiz-playground-ui = pkgs.stdenv.mkDerivation {
            pname = "wiz-playground-ui";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [
                ./web/build-playground-ui.sh ./web/playground-ui.wiz ./web/js.c
                ./web/framework/driver.js ./web/framework/runtime.js
                ./web/framework/adopt.js ./web/framework/mount.js
                ./lib
              ];
            };
            nativeBuildInputs = [ wiz pkgs.emscripten ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR EM_CACHE=$TMPDIR/emscripten-cache WIZ=${wiz}/bin/wiz
              sh web/build-playground-ui.sh out --gmp-src ${pkgs.gmp.src}
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              cp -r out $out
              runHook postInstall
            '';
            meta = {
              description = "The playground's Loom UI module (wiz-playground-ui.mjs, web/build-playground-ui.sh)";
              platforms = systems;
            };
          };
          # The landing page's quantity island (`web/landing_ui.wiz`, Web.Landing as a
          # Loom LiveApp): a tiny module, built here so neither the `web` nor the
          # `docs` job needs Emscripten. `lib/` is its `-I` root, so a library change
          # rebuilds it; the page's static first paint (web/build-landing.sh) is a
          # separate, compiler-only step.
          wiz-landing-ui = pkgs.stdenv.mkDerivation {
            pname = "wiz-landing-ui";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [
                ./web/build-landing-ui.sh ./web/landing_ui.wiz ./web/js.c
                ./web/framework/driver.js ./web/framework/runtime.js
                ./web/framework/adopt.js ./web/framework/mount.js
                ./lib
              ];
            };
            nativeBuildInputs = [ wiz pkgs.emscripten ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR EM_CACHE=$TMPDIR/emscripten-cache WIZ=${wiz}/bin/wiz
              sh web/build-landing-ui.sh out --gmp-src ${pkgs.gmp.src}
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              # build-landing-ui.sh writes OUT/landing/ (the page's asset directory);
              # the store path is that directory, so the page's --from/--ui copy finds
              # wiz-landing-ui.mjs at its root.
              mkdir -p $out
              cp -r out/landing/. $out/
              runHook postInstall
            '';
            meta = {
              description = "The landing page's quantity island (wiz-landing-ui.mjs, web/build-landing-ui.sh)";
              platforms = systems;
            };
          };
          # The source reader's Loom UI (`web/source-ui.wiz`: Web.Source.View as a
          # LiveApp). `scry web --ui` copies the module into a bundle and
          # `web/source-static.js` mounts it; the site's `/source/` page is the same
          # bytes. Built here for the same reason as `wiz-playground-ui`: one Cachix
          # entry, and neither the scry nor the docs job runs Emscripten. `lib/` is the
          # `-I` root, so a library change rebuilds it — correct, and small.
          wiz-source-ui = pkgs.stdenv.mkDerivation {
            pname = "wiz-source-ui";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [
                ./web/build-source-ui.sh ./web/source-ui.wiz ./web/js.c
                ./lib
              ];
            };
            nativeBuildInputs = [ wiz pkgs.emscripten ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR EM_CACHE=$TMPDIR/emscripten-cache WIZ=${wiz}/bin/wiz
              sh web/build-source-ui.sh out --gmp-src ${pkgs.gmp.src}
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              cp -r out $out
              runHook postInstall
            '';
            meta = {
              description = "The source reader's Loom UI module (wiz-source-ui.mjs, web/build-source-ui.sh)";
              platforms = systems;
            };
          };
          # tower, the toolchain manager (stage 26): the Wiz implementation in `tower/`,
          # built by grail (stage 26e/26h). It needs no Lean at build time; the binary
          # links GMP (the flags below), so the closure grows by GMP and glibc only.
          # Wrapped with the programs it runs (git, tar, curl; `nix` and `lake` are the
          # user's), and told its own path for the shims it writes.
          #
          # `towerFor wizPkg` builds it with a particular `wiz`: the pure `.#tower` is
          # `towerFor wiz`, and `lib.towerWith <store path>` is CI's seeded build. The
          # seeded path is a store input, not the `wiz` derivation, so Nix substitutes it
          # and never starts `wiz-unwrapped` (the cold compile the old job fell into).
          towerFor = wizPkg:
            let
              tower-unwrapped = pkgs.stdenv.mkDerivation {
                pname = "tower-unwrapped";
                inherit (unwrapped) version;
                src = fs.toSource {
                  root = ./.;
                  fileset = fs.unions [ ./tower ./scripts/build-tower-wiz.sh ];
                };
                nativeBuildInputs = [ wizPkg ];
                buildPhase = ''
                  runHook preBuild
                  export HOME=$TMPDIR
                  # only what tower uses: the C compiler, and GMP's headers and library (the
                  # generated C links no Boehm collector, so the closure stays GMP + glibc)
                  sh scripts/build-tower-wiz.sh tower-bin grail ${lib.escapeShellArgs [
                    "--cc" "${pkgs.stdenv.cc}/bin/cc" "--cflags" tc.cflags "--ldflags" tc.ldflags ]}
                  runHook postBuild
                '';
                installPhase = ''
                  runHook preInstall
                  install -Dm755 tower-bin $out/bin/tower
                  runHook postInstall
                '';
              };
            in
            pkgs.stdenv.mkDerivation {
              pname = "tower";
              inherit (unwrapped) version;
              dontUnpack = true;
              nativeBuildInputs = [ pkgs.makeWrapper ];
              installPhase = ''
                makeWrapper ${tower-unwrapped}/bin/tower $out/bin/tower \
                  --suffix PATH : ${lib.makeBinPath [ pkgs.coreutils pkgs.git pkgs.gnutar pkgs.gzip pkgs.curl ]} \
                  --add-flags ${addFlags [ "--self" "${placeholder "out"}/bin/tower" ]}
                # The `wiz` and `grail` shims, so installing the package puts them on PATH. They
                # call the `tower` on PATH (the user's), falling back to this package's own, and
                # use tower's default home, ~/.tower, where the toolchains live.
                for t in wiz grail; do
                  cat > $out/bin/$t <<EOF
              #!/bin/sh
              # tower shim: runs \`$t\` of the toolchain for this directory (\`tower show\`).
              # It asks the \`tower\` on PATH (the user's), else this package's own.
              tower=\$(command -v tower) || tower='$out/bin/tower'
              case "\$1" in
                +*) tc=\$("\$tower" resolve "\$1") || exit; shift ;;
                *) tc=\$("\$tower" resolve) || exit ;;
              esac
              exec "\$tc/bin/$t" "\$@"
              EOF
                  chmod +x $out/bin/$t
                done
              '';
              meta = {
                description = "tower, the Wiz toolchain manager, with the wiz and grail shims: installs toolchains, and the shims run the one a project asks for";
                mainProgram = "tower";
                platforms = systems;
              };
            };
          tower = towerFor wiz;

          # ---- the remaining CI-built artifacts as Nix outputs ---------------------
          #
          # Each output below is input-addressed by exactly the sources it reads (a
          # fileset, or the inputs it composes), so a pull request that changes the
          # docs does not rebuild the Wasm modules, and a change to one web module does
          # not rebuild the others. `passthru.subset` names that boundary for the CI
          # lane that splits the jobs. The release tarball is the one leaf that may
          # depend on all of them.

          # The Wasm test fixtures: `scripts/wasm-fixtures/*.wiz` compiled by the packaged wiz and
          # run through the checked-in `web/wasm-host.mjs`. The output is the module
          # pair, the host and the expected stdout; the check is the run.
          wasm-fixtures = pkgs.stdenv.mkDerivation {
            pname = "wiz-wasm-fixtures";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [ ./scripts/wasm-fixtures ./web/wasm-host.mjs ];
            };
            nativeBuildInputs = [ wiz pkgs.nodejs ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR
              mkdir -p $out
              while read -r name expected; do
                ${wiz}/bin/wiz build "scripts/wasm-fixtures/$name.wiz" -o "$out/$name.wasm" --target wasm
                printf '%s\n' "$expected" > "$out/$name.expected"
              done < scripts/wasm-fixtures/expected.tsv
              cp web/wasm-host.mjs $out/wasm-host.mjs
              runHook postBuild
            '';
            doCheck = true;
            checkPhase = ''
              runHook preCheck
              while read -r name expected; do
                got=$(node "$out/wasm-host.mjs" "$out/$name.wasm")
                if [ "$got" != "$expected" ]; then
                  echo "wasm-fixtures: $name: got '$got', expected '$expected'" >&2
                  exit 1
                fi
                echo "ok: $name: $got"
              done < scripts/wasm-fixtures/expected.tsv
              if grep -a -R '/nix/store' "$out" >/dev/null 2>&1; then
                echo "wasm-fixtures: a fixture names a build path" >&2
                exit 1
              fi
              runHook postCheck
            '';
            passthru.subset = "scripts/wasm-fixtures + web/wasm-host.mjs";
            meta = {
              description = "The Wasm backend's fixture modules, compiled from scripts/wasm-fixtures and run under web/wasm-host.mjs";
              platforms = systems;
            };
          };

          # One directory with every page module the site and the release use, exactly
          # the OUT of `web/build.sh` + `web/build-playground.sh` +
          # `web/build-playground-ui.sh`. It composes the three per-module derivations
          # (`wiz-web`, `wiz-playground`, `wiz-playground-ui`): each keeps its own
          # source fileset, so a change to one module does not rebuild the others, and
          # this bundle is only their union.
          web-bundle = pkgs.stdenv.mkDerivation {
            pname = "wiz-web-bundle";
            inherit (unwrapped) version;
            dontUnpack = true;
            nativeBuildInputs = [ pkgs.gnugrep ];
            installPhase = ''
              runHook preInstall
              mkdir -p $out
              cp -R --no-preserve=mode ${wiz-web}/. $out/
              cp -R --no-preserve=mode ${wiz-playground}/. $out/
              cp -R --no-preserve=mode ${wiz-playground-ui}/. $out/
              for f in wiz-infoview.mjs wiz-playground.mjs wiz-playground.wasm \
                       wiz-playground-ui.mjs wiz-playground-ui.wasm; do
                [ -f "$out/$f" ] || { echo "web-bundle: missing $f" >&2; exit 1; }
              done
              if grep -a -R '/nix/store' $out >/dev/null; then
                echo "web-bundle: a module names a build store path" >&2; exit 1
              fi
              runHook postInstall
            '';
            passthru.subset = "wiz-web + wiz-playground + wiz-playground-ui (their own filesets)";
            meta = {
              description = "Every Wasm page module and its page files in one directory (the site's web/out)";
              platforms = systems;
            };
          };

          # The published site's files, minus the source reader: `wiz doc --lib` plus
          # the landing page, guide, benchmark page and playground. `wiz-pages` adds
          # `/source/` and is the exact directory the Pages job uploads. The fileset
          # lists the site scripts and prose it reads, not all of `web/`; a change to
          # an Emscripten script does not rebuild the docs.
          siteAssetFiles = [
            "web/build-site.sh" "web/build-bench.py" "web/build-docs.py"
            "web/check-site.sh" "web/check-links.py" "web/bench/index.html"
            # the landing page is *generated* in the derivation now (build-site.sh
            # refuses a WEB without landing/index.html), so the generator, its template
            # and the snippets have to be inputs. `landing_highlight.py` is the
            # generator's `from landing_highlight import highlight` (it highlights the
            # snippet bytes at build time): without it build-landing.py dies with
            # ModuleNotFoundError in the sandbox, which is not a site bug but a missing
            # input here.
            "web/build-landing.sh" "web/build-landing.py" "web/landing_highlight.py"
            "web/landing"
            "web/playground.html" "web/playground.js" "web/playground.css"
            "web/overlays.css" "web/widgets.css" "web/lsp-client.js" "web/widgets.js"
            "web/playground-lsp.js" "web/hover.js" "web/selfhost-lsp-shim.js"
            "web/playground-engine.js" "web/squiggles.js" "web/completions.js"
            "web/framework/mount.js" "web/framework/driver.js"
            "web/framework/runtime.js" "web/framework/editor-text.js"
            "web/framework/adopt.js"
            "web/licenses/index.html" "web/licenses/LGPL-3.0.txt"
          ];
          docsSiteSource = fs.toSource {
            root = ./.;
            fileset = fs.unions ([
              ./docs ./bench ./examples ./tools ./editors ./drafts ./scry
              ./README.md ./ROADMAP.md ./CHANGELOG.md ./LICENSE
              ./COPYING.RUNTIME
            ] ++ map (f: ./. + "/${f}") siteAssetFiles);
          };
          # `wiz doc --lib` on its own: the API pages are the expensive, separately
          # cacheable half of the site (`--jobs 4` over every module), and the site
          # below consumes the result instead of re-running it. A `lib/` change rebuilds
          # this and then the site; a change to the site's chrome rebuilds only the site.
          docs-lib = pkgs.stdenv.mkDerivation {
            pname = "wiz-docs-lib";
            inherit (unwrapped) version;
            src = docsSiteSource;
            nativeBuildInputs = [ wiz pkgs.python3 pkgs.gnugrep ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR
              mkdir -p out
              ${wiz}/bin/wiz doc --lib --jobs 4 -o out/docs --web ${web-bundle} \
                --source-url ${lib.escapeShellArg "${sourceUrl}/lib/"}
              cp ${reference}/index.md out/docs/reference.md
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              cp -R out $out
              runHook postInstall
            '';
            passthru.subset = "lib/ + the docs tooling in siteAssetFiles + wiz + reference + web-bundle";
            meta = {
              description = "The API documentation: `wiz doc --lib` over lib/";
              platforms = systems;
            };
          };
          docs-site = pkgs.stdenv.mkDerivation {
            pname = "wiz-docs-site";
            inherit (unwrapped) version;
            src = docsSiteSource;
            nativeBuildInputs = [ wiz pkgs.python3 pkgs.gnugrep ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR
              mkdir -p site site-web
              # the API pages come from #docs-lib: `wiz doc --lib` is its own derivation
              # now, so a site-only change does not re-render 245 modules
              cp -R --no-preserve=mode ${docs-lib}/docs site/docs
              # The modules the site publishes (playground page and its Wasm) come from
              # #web-bundle; the LANDING page is generated, not templated: since the
              # landing merge, `web/build-site.sh` refuses a WEB without
              # `landing/index.html`, and nothing else in this derivation ran
              # `web/build-landing.sh` - so `.#pages` could not build (found by the
              # docs-truth lane; masked because the docs job never ran while `lean` was
              # red). The island's first paint needs `wiz`; the module itself is
              # #wiz-landing-ui.
              #
              # WEB is an explicit output directory (`#web-bundle` is "the site's
              # web/out"), not the checkout's `web/`: `build-landing.sh` writes the page
              # to `OUT/landing` and copies the template's `landing.css`, `carousel.js`
              # and `app.js` into it, so an OUT that *is* the template directory copies
              # `landing.css` onto itself and `cp` refuses
              # ("... landing.css and ... landing.css are the same file").
              cp -R --no-preserve=mode ${web-bundle}/. site-web/
              WIZ=${wiz}/bin/wiz sh web/build-landing.sh site-web
              mkdir -p site-web/landing
              cp -R --no-preserve=mode ${wiz-landing-ui}/. site-web/landing/
              WIZ_SOURCE_URL=${lib.escapeShellArg sourceUrl} \
                sh web/build-site.sh site site-web
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              cp -R site $out
              runHook postInstall
            '';
            doCheck = true;
            checkPhase = ''
              runHook preCheck
              sh web/check-site.sh site
              if grep -a -R -E '/nix/store/[0-9a-z]{32}-' site >/dev/null; then
                echo "docs-site: a page names a build store path" >&2; exit 1
              fi
              if grep -a -R "$PWD" site >/dev/null; then
                echo "docs-site: a page names the build root" >&2; exit 1
              fi
              runHook postCheck
            '';
            passthru.subset = "docs/ + bench/ + examples/ + tools/ + editors/ + drafts/ + scry/ (for the prose links) + README/ROADMAP/CHANGELOG/LICENSE/COPYING.RUNTIME + the site scripts in siteAssetFiles + wiz + reference + web-bundle";
            meta = {
              description = "The documentation site: wiz doc --lib and the landing, guide, benchmark and playground pages";
              platforms = systems;
            };
          };

          # The source reader's own inputs: scry's package (built with grail) and the
          # browser bundle's host files. `pages` is docs-site plus this `/source/`; a
          # scry change rebuilds only the reader, and a docs change rebuilds both (the
          # reader is added to the docs tree it publishes).
          pagesSource = fs.toSource {
            root = ./.;
            fileset = fs.unions [
              ./scry
              ./web/source-bundle.sh ./web/source-app.js ./web/source.css
              ./web/source-static.js
              ./web/framework/mount.js ./web/framework/driver.js
              ./web/framework/runtime.js ./web/framework/adopt.js
            ];
          };
          pages = pkgs.stdenv.mkDerivation {
            pname = "wiz-pages";
            inherit (unwrapped) version;
            src = pagesSource;
            nativeBuildInputs = [ wiz pkgs.python3 pkgs.gnugrep ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR
              mkdir -p site
              cp -R --no-preserve=mode ${docs-site}/. site/
              # scry is a derivation now (`.#scry`): the sandbox no longer copies the
              # package, links the grammar and runs `grail build scry` here
              mkdir -p bundle
              sh web/source-bundle.sh ${scry}/bin/scry bundle \
                --ui ${wiz-source-ui} --target scry/tests/fixtures/report
              mkdir -p site/source
              cp -R --no-preserve=mode bundle/. site/source/
              SITE_REQUIRE_SOURCE=1 sh ${docsSiteSource}/web/check-site.sh site
              if grep -a -R -E '/nix/store/[0-9a-z]{32}-' site >/dev/null; then
                echo "pages: a page names a build store path" >&2; exit 1
              fi
              if grep -a -R "$PWD" site >/dev/null; then
                echo "pages: a page names the build root" >&2; exit 1
              fi
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              cp -R site $out
              runHook postInstall
            '';
            passthru.subset = "docs-site + scry/ + web/source-{bundle.sh,app.js,css,static.js} + web/framework/ + wiz-source-ui + tree-sitter-c-sharp";
            meta = {
              description = "The exact doc-site tree GitHub Pages deploys: the docs site plus the scry source reader";
              platforms = systems;
            };
          };

          # ---- the portable release toolchain -------------------------------------
          #
          # `wiz`, `grail` and `tower` in a release must run on a machine that has
          # glibc and nothing else from this build. The normal packages link GMP,
          # libuv, OpenSSL, libstdc++ and libgcc dynamically (and a Nix RUNPATH names
          # their store paths). The release build links every one of those statically:
          #
          #   gmp      `withStatic` (the release archive's link line already uses -lgmp)
          #   libuv    a static-only autotools build
          #   openssl  `static = true`
          #   libstdc++/libgcc  the compiler driver's -static-libstdc++ -static-libgcc
          #
          # The .a files are collected in one -L directory with no .so beside them, so
          # the linker's -luv/-lssl/-lgmp resolve to the archives no matter what other
          # -L paths the stdenv adds. glibc (libc, libm, libdl, libpthread) stays
          # dynamic, as the portability rule requires. `releaseCC` is the explicit
          # alternate-tool seam: `LEAN_CC` and grail's `--cc` take it, and a caller may
          # still pass its own --cc/--ldflags to build a different release.
          release-gmp = pkgs.gmp.override { withStatic = true; };
          release-libuv = pkgs.libuv.overrideAttrs (old: {
            # static only, with the normal (glibc) stdenv; do not spend the build on
            # libuv's own test suite for an archive we only link
            configureFlags = (old.configureFlags or []) ++ [ "--disable-shared" "--enable-static" ];
            dontDisableStatic = true;
            doCheck = false;
          });
          release-openssl = pkgs.openssl.override { static = true; };
          release-static-libs = pkgs.runCommand "wiz-release-static-libs" { } ''
            mkdir -p $out/lib
            cp -L ${release-gmp}/lib/libgmp.a $out/lib/libgmp.a
            cp -L ${release-libuv}/lib/libuv.a $out/lib/libuv.a
            cp -L ${release-openssl.out}/lib/libssl.a $out/lib/libssl.a
            cp -L ${release-openssl.out}/lib/libcrypto.a $out/lib/libcrypto.a
          '';
          releaseCC = pkgs.writeShellScript "wiz-release-cc" ''
            # The release's C compiler. Compile-only calls just get the release's
            # static archive directory first on the search path. At link time the
            # dynamic C++/GCC runtimes Lean's link line names are dropped and added
            # back as static archives after every object (order matters for archives),
            # and the link is non-PIE (the archives are not built PIC). glibc stays
            # dynamic: -lm/-ldl/-pthread are the only libraries after -Bdynamic.
            compile=no
            args=()
            for a in "$@"; do
              case "$a" in
                -c|-E|-S|-M|-MM) compile=yes ;;
                -lgmp|-luv|-lssl|-lcrypto|-lstdc++|-lc++|-lc++abi|-lgcc|-lgcc_s|-latomic) continue ;;
              esac
              args+=("$a")
            done
            if [ "$compile" = yes ]; then
              exec ${pkgs.stdenv.cc}/bin/cc -L${release-static-libs}/lib "''${args[@]}"
            fi
            # All non-glibc libraries, after every object that uses them. appending
            # them (rather than only trusting -L order) is what makes the result static
            # even if a later -L path or the driver's own specs name a .so first.
            exec ${pkgs.stdenv.cc}/bin/cc -no-pie -static-libstdc++ -static-libgcc \
              -L${release-static-libs}/lib "''${args[@]}" \
              -Wl,-Bstatic -lgmp -luv -lssl -lcrypto -lstdc++ -lgcc -lgcc_eh -latomic \
              -Wl,-Bdynamic -lm -ldl -pthread
          '';
          releaseInterp =
            if pkgs.stdenv.hostPlatform.isAarch64
            then "/lib/ld-linux-aarch64.so.1"
            else "/lib64/ld-linux-x86-64.so.2";
          releaseArch = pkgs.stdenv.hostPlatform.parsed.cpu.name;
          release-unwrapped = pkgs.stdenv.mkDerivation {
            pname = "wiz-unwrapped-release";
            inherit (unwrapped) version;
            # Lake reads the package definition (including the Tests/STC targets) even
            # when asked for only wiz and grail; the release is a leaf, so it uses the
            # full compiler source subset rather than staking a cold build on Lake not
            # touching a target it was not asked for.
            src = buildSrc;
            nativeBuildInputs = [ lean ];
            # an intermediate store path keeps its RUNPATH and debug info; the tarball's
            # leaf step is the only place that touches them
            dontStrip = true;
            dontPatchELF = true;
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR LAKE_CACHE_DIR=$TMPDIR/lake-cache \
                LEAN_CC=${releaseCC} CC=${releaseCC} CXX=${releaseCC}
              # Lake's executable link can pick the ambient cc/gcc/g++ even when
              # LEAN_CC is set; put the release wrapper under every driver name first.
              mkdir -p cc-bin
              for t in cc gcc g++ c++ clang clang++; do
                ln -sf ${releaseCC} cc-bin/$t
              done
              export PATH=$PWD/cc-bin:$PATH
              lake build wiz grail
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              mkdir -p $out/bin
              install -m755 .lake/build/bin/wiz .lake/build/bin/grail $out/bin/
              runHook postInstall
            '';
            passthru.subset = "buildSrc (the compiler/tests subset: lakefile.lean, lake-manifest.json, lean-toolchain, Main.lean, Wiz/, Grail/, WizMeta/, STC/, Tests/, runtime/, c/)";
          };
          release-tower = pkgs.stdenv.mkDerivation {
            pname = "tower-unwrapped-release";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [ ./tower ./scripts/build-tower-wiz.sh ./lib ];
            };
            nativeBuildInputs = [ release-unwrapped ];
            dontStrip = true;
            dontPatchELF = true;
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR
              # grail finds the standard library beside its launcher
              # (share/wiz/.lake/build/bin/grail with share/wiz/lib); the release
              # unwrapped output has only bin/grail, so give it the layout it reads.
              mkdir -p grail-root/share/wiz/.lake/build/bin
              cp ${release-unwrapped}/bin/grail grail-root/share/wiz/.lake/build/bin/grail
              cp -R lib grail-root/share/wiz/lib
              sh scripts/build-tower-wiz.sh tower-bin \
                "$PWD/grail-root/share/wiz/.lake/build/bin/grail" \
                --cc ${releaseCC} \
                --cflags ${lib.escapeShellArg "-I${release-gmp.dev}/include"} \
                --ldflags ${lib.escapeShellArg "-L${release-static-libs}/lib"}
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              install -Dm755 tower-bin $out/bin/tower
              runHook postInstall
            '';
            passthru.subset = "tower/ + scripts/build-tower-wiz.sh + lib/ (the grail layout) + release-unwrapped + release-static-libs";
          };

          # The binary release tarball (scripts/release-tarball.sh): the portable
          # wiz/grail/tower, the standard library, editors, licences and the infoview
          # module. This is the leaf: the only place that points the ELF interpreter at
          # the conventional path, removes the build RUNPATH, strips, and scrubs store
          # paths, so the archive runs on a machine with no /nix/store. Do not copy that
          # step into an intermediate derivation. The leaf deliberately has no
          # `share/wiz/cc`: `wiz build` falls back to the host `cc`/GMP, and
          # `scripts/bundle-cc.sh` remains the release pipeline's portable compiler
          # bundle.
          releaseSrc = fs.toSource {
            root = ./.;
            fileset = fs.unions [
              ./lib ./editors ./scripts/release-licenses
              ./LICENSE ./COPYING.RUNTIME ./web/wasm-host.mjs
              ./scripts/release-tarball.sh
            ];
          };
          release-bin = pkgs.stdenv.mkDerivation {
            pname = "wiz-release-bin";
            inherit (unwrapped) version;
            src = releaseSrc;
            nativeBuildInputs = [
              pkgs.binutils pkgs.patchelf pkgs.python3 pkgs.lean4
              pkgs.coreutils pkgs.diffutils pkgs.gnutar pkgs.gzip
              pkgs.gnugrep pkgs.findutils
            ];
            dontStrip = true;
            dontPatchELF = true;
            buildPhase = ''
              runHook preBuild
              mkdir -p bin
              cp ${release-unwrapped}/bin/wiz ${release-unwrapped}/bin/grail bin/
              cp ${release-tower}/bin/tower bin/
              chmod u+w bin/wiz bin/grail bin/tower
              # Lean's executable link does not take the static-runtime flags, so
              # bundle the matching C++ runtime from the GCC that releaseCC wraps
              # and give it (and the commands) a relative RUNPATH. This keeps the
              # tarball dependent on glibc alone without patching Lean's linker.
              mkdir -p release-libs
              cp -L ${pkgs.stdenv.cc.cc.lib}/lib/libstdc++.so.6 release-libs/
              cp -L ${pkgs.stdenv.cc.cc.lib}/lib/libgcc_s.so.1 release-libs/
              chmod u+w release-libs/libstdc++.so.6 release-libs/libgcc_s.so.1
              patchelf --set-rpath '$ORIGIN' release-libs/libstdc++.so.6 release-libs/libgcc_s.so.1
              strip --strip-unneeded release-libs/libstdc++.so.6 release-libs/libgcc_s.so.1
              python3 ${./scripts}/scrub-store-paths.py release-libs/libstdc++.so.6 release-libs/libgcc_s.so.1
              # ------------------------------------------------------------------
              # LEAF ONLY. This deliberately breaks Nix convention: a normal store
              # path keeps its interpreter, RUNPATH and references, and Nix tracks
              # them. The final tarball leaves the store and must run on a machine
              # with only glibc, so here (and nowhere else) the ELF interpreter is
              # the conventional one, the build RUNPATH is replaced by the bundled
              # C++ runtime's relative one later, debug data is dropped, and the
              # build's absolute store paths are overwritten. The binaries were
              # linked statically against GMP/libuv/OpenSSL; the C++ runtime is in
              # lib/, so nothing outside this derivation is patched or stripped.
              # ------------------------------------------------------------------
              for b in bin/wiz bin/grail bin/tower; do
                patchelf --set-interpreter ${releaseInterp} "$b"
                patchelf --remove-rpath "$b"
                strip --strip-unneeded "$b"
                python3 ${./scripts}/scrub-store-paths.py "$b"
              done
              # Package in buildPhase: stdenv runs checkPhase before installPhase, and
              # the check compares the packaged archive.
              mkdir -p package
              RELEASE_SOURCE_DATE_EPOCH=${epoch} SOURCE_DATE_EPOCH=${epoch} \
                sh ${./scripts}/release-tarball.sh \
                  "package/wiz-${releaseArch}-linux.tar.gz" bin "${revision}" "" \
                  ${wiz-web} ${releaseSrc} "$PWD/release-libs"
              # GPLv3 Corresponding Source for the bundled GCC runtime: the
              # upstream tarball, the nixpkgs patches and expression, and the
              # revision, beside the tarball in the same Nix output.
              mkdir -p gcc-source
              cp ${pkgs.gcc.cc.src} gcc-source/
              for p in ${lib.concatStringsSep " " pkgs.gcc.cc.patches}; do
                cp "$p" gcc-source/
              done
              cp -R ${nixpkgs}/pkgs/development/compilers/gcc gcc-source/nixpkgs-gcc
              echo ${nixpkgs.rev} > gcc-source/NIXPKGS_REVISION
              tar --sort=name --mtime=@${epoch} --owner=0 --group=0 \
                --numeric-owner -cf - -C gcc-source . | gzip -n \
                > package/gcc-16.2.0-nixpkgs-source.tar.gz
              ( cd package && sha256sum gcc-16.2.0-nixpkgs-source.tar.gz \
                  > gcc-16.2.0-nixpkgs-source.tar.gz.sha256 )
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              mkdir -p $out
              cp package/wiz-${releaseArch}-linux.tar.gz \
                 package/wiz-${releaseArch}-linux.tar.gz.sha256 \
                 package/gcc-16.2.0-nixpkgs-source.tar.gz \
                 package/gcc-16.2.0-nixpkgs-source.tar.gz.sha256 $out/
              runHook postInstall
            '';
            doCheck = true;
            checkPhase = ''
              runHook preCheck
              name=wiz-${releaseArch}-linux
              # The archive layer is reproducible: the same patched binaries, commit
              # epoch and members from a second environment are byte-identical.
              for side in a b; do
                mkdir -p repro/$side/bin repro/$side/out repro/$side/home repro/$side/tmp
                cp bin/* repro/$side/bin/
              done
              ( umask 022; HOME=$PWD/repro/a/home TMPDIR=$PWD/repro/a/tmp \
                  LC_ALL=C TZ=UTC SOURCE_DATE_EPOCH=1111111111 \
                  RELEASE_SOURCE_DATE_EPOCH=${epoch} \
                  sh ${./scripts}/release-tarball.sh repro/a/out/$name.tar.gz \
                    repro/a/bin "${revision}" "" ${wiz-web} ${releaseSrc} "$PWD/release-libs" )
              ( umask 077; HOME=$PWD/repro/b/home TMPDIR=$PWD/repro/b/tmp \
                  LC_ALL=C.UTF-8 TZ=Asia/Tokyo SOURCE_DATE_EPOCH=1700000000 \
                  RELEASE_SOURCE_DATE_EPOCH=${epoch} \
                  sh ${./scripts}/release-tarball.sh repro/b/out/$name.tar.gz \
                    repro/b/bin "${revision}" "" ${wiz-web} ${releaseSrc} "$PWD/release-libs" )
              cmp repro/a/out/$name.tar.gz repro/b/out/$name.tar.gz
              cmp repro/a/out/$name.tar.gz.sha256 repro/b/out/$name.tar.gz.sha256
              cmp package/$name.tar.gz repro/a/out/$name.tar.gz
              # The source archive is part of the release: build it again and
              # compare, with the same deterministic tar/gzip -n inputs.
              mkdir -p repro/gcc-source
              cp ${pkgs.gcc.cc.src} repro/gcc-source/
              for p in ${lib.concatStringsSep " " pkgs.gcc.cc.patches}; do
                cp "$p" repro/gcc-source/
              done
              cp -R ${nixpkgs}/pkgs/development/compilers/gcc repro/gcc-source/nixpkgs-gcc
              echo ${nixpkgs.rev} > repro/gcc-source/NIXPKGS_REVISION
              tar --sort=name --mtime=@${epoch} --owner=0 --group=0 \
                --numeric-owner -cf - -C repro/gcc-source . | gzip -n \
                > repro/gcc-source.tar.gz
              cmp package/gcc-16.2.0-nixpkgs-source.tar.gz repro/gcc-source.tar.gz
              [ "$(cut -d' ' -f1 package/gcc-16.2.0-nixpkgs-source.tar.gz.sha256)" = \
                "$(cd repro && sha256sum gcc-source.tar.gz | cut -d' ' -f1)" ]
              sh ${./scripts}/test-release-portability.sh \
                "package/$name.tar.gz" --glibc ${pkgs.glibc} --max-glibc 2.43
              runHook postCheck
            '';
            passthru.subset = "release leaf: lib/ + editors/ + scripts/release-licenses + LICENSE + COPYING.RUNTIME + web/wasm-host.mjs, composed with release-unwrapped + release-tower + wiz-web";
            meta = {
              description = "The portable binary release tarball (wiz, grail, tower, library, editors and the infoview module)";
              platforms = systems;
            };
          };

          # A deterministic source tarball with a manifest and a CycloneDX SBOM
          # (scripts/source-tarball.py, docs/building.md "Reproducible source tarball"):
          # sorted entries, epoch mtimes, uid/gid 0, normalised modes, no
          # .git/caches/build outputs. The epoch is the flake's commit time (0 for a
          # source archive) and the revision the commit, so two builds of one commit are
          # byte-identical. `source-tarball` is the same derivation under the name the
          # docs use.
          release-tarball =
            pkgs.runCommand "wiz-release-tarball" {
              nativeBuildInputs = [ pkgs.python3 ];
            } ''
              mkdir -p $out
              python3 ${./scripts}/source-tarball.py --root ${./.} --mode tree \
                --out $out --revision ${lib.escapeShellArg revision} --epoch ${epoch}
            '';

          # The Neovim plugin (editors/nvim, docs/stages/11-tooling.md 11p), without its tests.
          wiz-nvim = pkgs.vimUtils.buildVimPlugin {
            pname = "wiz-nvim";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./editors/nvim;
              fileset = fs.difference ./editors/nvim ./editors/nvim/tests;
            };
            meta = {
              description = "Wiz in Neovim: wiz lsp, Lean-style unicode input, and an infoview";
              platforms = lib.platforms.all;
            };
          };

          # Neovim with wiz.nvim and this wiz on PATH (`nix run .#nvim-wiz -- file.wiz`).
          # Its own configuration: your init.lua is not read.
          nvim-wiz =
            let
              nvim = pkgs.neovim.override {
                configure = {
                  packages.wiz.start = [ wiz-nvim ];
                  customRC = "";
                };
              };
            in
            pkgs.writeShellApplication {
              name = "nvim-wiz";
              runtimeInputs = [ wiz ];
              text = ''exec ${nvim}/bin/nvim "$@"'';
              meta = {
                description = "Neovim with wiz.nvim and wiz";
                mainProgram = "nvim-wiz";
                platforms = systems;
              };
            };

          # scry's C# grammar (scry/CSHARP.md, scry/native/README.md): tree-sitter-c-sharp
          # v0.23.5, fetched rather than vendored, because its src/parser.c (29.7 MB) is
          # generated by tree-sitter. scry's `link_c` lines compile it from
          # scry/native/tree-sitter-c-sharp, an uncommitted out-link to this path:
          #   nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp
          #
          # One local patch fixes two grammar gaps (backports from upstream master,
          # scry/CSHARP.md §8.2): `with`, `partial` and `required` are contextual keywords
          # and valid identifiers outside their keyword position, but v0.23.5's
          # `_reserved_identifier` omits them (`var with = …`, `partial.Member`); and a
          # list-pattern slice with a designation (`['[', .. var middle, ']']`) needs
          # master's `slice_pattern` rule. The patch touches grammar.js only; the parser is
          # regenerated at build time by the tree-sitter in nixpkgs (ABI 15).
          tree-sitter-c-sharp = pkgs.stdenv.mkDerivation {
            pname = "tree-sitter-c-sharp";
            version = "0.23.5";
            src = pkgs.fetchFromGitHub {
              owner = "tree-sitter";
              repo = "tree-sitter-c-sharp";
              rev = "cac6d5fb595f5811a076336682d5d595ac1c9e85"; # tag v0.23.5
              hash = "sha256-N5AAlwQFGGi47cj0m7Te08bA486gwY6NBOx4Qcy4lpo=";
            };
            patches = [ ./scry/native/tree-sitter-c-sharp-v0.23.5-fixes.patch ];
            nativeBuildInputs = [ pkgs.tree-sitter ];
            dontConfigure = true;
            buildPhase = ''
              runHook preBuild
              tree-sitter generate --js-runtime native --abi 15
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              mkdir -p $out
              cp -r src grammar.js tree-sitter.json LICENSE queries $out/
              runHook postInstall
            '';
            meta = {
              description = "tree-sitter-c-sharp v0.23.5 with scry's contextual-keyword and slice-pattern fixes";
              platforms = systems;
            };
          };

          # scry's native parse library, built once here and substituted from Cachix: the
          # tree-sitter runtime, the C grammar (both vendored under scry/native), the C#
          # grammar above, and ts_shim.c, as lib/libscry-ts.a. The check parses one C and
          # one C# file through `scry_parse`, so a grammar the shim can't load fails here.
          scry-native = pkgs.stdenv.mkDerivation {
            pname = "scry-native";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./scry/native;
              fileset = fs.unions [ ./scry/native/ts_shim.c ./scry/native/tree-sitter ./scry/native/tree-sitter-c ];
            };
            buildPhase = ''
              runHook preBuild
              ln -s ${tree-sitter-c-sharp} tree-sitter-c-sharp
              cc=''${CC:-cc}
              $cc -O2 -c -I tree-sitter/lib/include -I tree-sitter/lib/src tree-sitter/lib/src/lib.c -o ts-lib.o
              $cc -O2 -c -I tree-sitter-c/src tree-sitter-c/src/parser.c -o ts-c.o
              $cc -O2 -c -I tree-sitter-c-sharp/src tree-sitter-c-sharp/src/parser.c -o ts-cs-parser.o
              $cc -O2 -c -I tree-sitter-c-sharp/src tree-sitter-c-sharp/src/scanner.c -o ts-cs-scanner.o
              $cc -O2 -c -I . ts_shim.c -o ts-shim.o
              ar rcs libscry-ts.a ts-lib.o ts-c.o ts-cs-parser.o ts-cs-scanner.o ts-shim.o
              runHook postBuild
            '';
            doCheck = true;
            checkPhase = ''
              runHook preCheck
              cat > smoke.c <<'C'
              #include <stdint.h>
              #include <stdio.h>
              #include <string.h>
              typedef struct ScryStore ScryStore;
              ScryStore *scry_parse(const char *lang, const char *src, uint64_t len);
              uint64_t scry_store_ok(ScryStore *s);
              const char *scry_store_error(ScryStore *s);
              uint64_t scry_node_count(ScryStore *s);
              uintptr_t wiz_warray_of_c(uint32_t width, const void *p, size_t n) { return 0; }
              static int check(const char *lang, const char *src) {
                ScryStore *s = scry_parse(lang, src, strlen(src));
                if (!s || !scry_store_ok(s) || scry_node_count(s) < 3) {
                  fprintf(stderr, "scry_parse %s: %s\n", lang, s ? scry_store_error(s) : "null");
                  return 1;
                }
                return 0;
              }
              int main(void) {
                return check("c", "int main(void) { return 0; }")
                     | check("c_sharp", "class A { static void Main() { var x = $\"{1}\"; } }");
              }
              C
              ''${CC:-cc} smoke.c libscry-ts.a -o smoke
              ./smoke
              runHook postCheck
            '';
            installPhase = ''
              runHook preInstall
              install -Dm644 libscry-ts.a $out/lib/libscry-ts.a
              runHook postInstall
            '';
            meta = {
              description = "scry's tree-sitter parse library: the runtime, the C and C# grammars, and the shim";
              platforms = systems;
            };
          };
          # `scry`, the analysis CLI, as a derivation: the same `grail build scry` the
          # `docs` job and `scry.yml` run today (68 imperative jobs in a job step), but
          # with a store path as the result, so the docs job can take it as an input and a
          # future `.#source-bundle` can depend on it. The one thing the dev shell does
          # that this must repeat is write `grail.local.wiz` (the GMP flags), because that
          # file is generated and not committed.
          # The two self-hosted programs, as derivations. The tests build them in a
          # `/tmp` cache keyed on their source plus the *mtime of the test binary*, so
          # every fresh runner rebuilds them and concurrent cases can build twice (perf
          # review H2: ~9,257 s of a suite run, 9.8%). A derivation is the same program
          # with a content key, substitutable, and the test flags
          # (`--selfhost-compiler/--selfhost-checker`) take the store path.
          #
          # The composition lives in `Wiz/Selfhost.lean` (which files, in which order),
          # so the driver prints it: `tests --selfhost-source compiler|checker`.
          # `selfhostProgramWith { wizPkg, testsPkg }` is the same derivation built with
          # those packages (the shape `towerFor` uses): CI passes the `lean` job's
          # seeded store paths on a pull request, where the pure `wiz`/`tests` do not
          # exist. `selfhostProgram` is the pure default.
          selfhostProgramWith = { wizPkg, testsPkg }: name: from: pkgs.stdenv.mkDerivation {
            pname = "wiz-selfhost-${name}";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [ ./selfhost ./lib ];
            };
            nativeBuildInputs = [ wizPkg testsPkg ];
            buildInputs = [ pkgs.gmp pkgs.boehmgc ];
            buildPhase = ''
              runHook preBuild
              export HOME=$TMPDIR
              ${testsPkg}/bin/tests --selfhost-source ${name} > ${from}.wiz
              # No --cflags/--ldflags/--gmp here: the wrapped `wiz` already carries the
              # toolchain's full flags (GMP, and Boehm's -lgc through --gc-ldflags), and
              # these options REPLACE the wrapper's rather than adding to them - spelling
              # them here was a second, drifting copy that worked only by flag order.
              ${wizPkg}/bin/wiz --cc cc build ${from}.wiz -o ${name}
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              install -Dm755 ${name} $out/bin/${name}
              # (No `<exe>.selfhost-id` yet: the harness flag that reads it,
              # `tests --selfhost-identity`, is on `agent/ci-sim` and not in this line;
              # writing it here made every build fail with "unknown flag". Re-add this
              # together with that branch, so the identity check and the file land in
              # the same commit.)
              runHook postInstall
            '';
            passthru.subset = "selfhost/ + lib/ (the composed program and its prelude)";
            meta = {
              description = "The self-hosted ${name} of the Wiz frontend (Wiz.Selfhost, as a store path)";
              platforms = systems;
            };
          };
          selfhostProgram = name: from:
            selfhostProgramWith { wizPkg = wiz; testsPkg = tests; } name from;
          selfhost-compiler = selfhostProgram "compiler" "selfhost-compiler";
          selfhost-checker = selfhostProgram "checker" "selfhost-checker";
          scry = pkgs.stdenv.mkDerivation {
            pname = "scry";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [ ./scry ./lib ];
            };
            nativeBuildInputs = [ wiz ];
            buildInputs = [ pkgs.gmp ];
            buildPhase = ''
              runHook preBuild
              cat > grail.local.wiz <<EOF
import Grail
def settings : Settings := Settings.empty
  |> Settings.set "cflags" "-I${lib.getDev pkgs.gmp}/include"
  |> Settings.set "ldflags" "-L${pkgs.gmp}/lib -Wl,-rpath,${pkgs.gmp}/lib"
EOF
              # the C/C# grammar the vendored shim links; the job did this with
              # `nix build .#tree-sitter-c-sharp -o scry/native/tree-sitter-c-sharp`
              ln -s ${tree-sitter-c-sharp} scry/native/tree-sitter-c-sharp
              ( cd scry && HOME=$TMPDIR ${wiz}/bin/grail build scry )
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              install -Dm755 scry/.grail/bin/scry $out/bin/scry
              runHook postInstall
            '';
            meta = {
              description = "scry, the C/C# analysis CLI (grail build scry, as a store path)";
              platforms = systems;
            };
          };
          # The self-hosted toolchain chain (docs/bootstrap-chain.md): a prototype, not built
          # by CI and not pinned by any commit until the chain's root is declared.
          # `wizc` is the fixpoint compiler built from the Lean host's seed, `wizc-release`
          # its self-contained release tarball; `legacyPackages.SYSTEM.bootstrapChain` has
          # the functions (`step`, `fetchToolchain`).
          bootstrapChain = import ./nix/bootstrap-chain.nix {
            inherit pkgs lib;
            hostWiz = wiz;
            selfhostSrc = fs.toSource { root = ./.; fileset = ./selfhost; };
            inherit (unwrapped) version;
          };
        in {
          inherit wiz unwrapped tower tests reference wiz-nvim nvim-wiz tree-sitter-c-sharp scry-native scry
                   wiz-web wiz-playground wiz-playground-ui wiz-landing-ui wiz-source-ui release-tarball
                   wasm-fixtures web-bundle docs-lib docs-site pages release-bin
                   selfhost-compiler selfhost-checker
                   release-unwrapped release-tower;
          # a function, not a package: `tower` is `towerFor wiz`, and `lib.towerWith`
          # is CI's seeded build. `packages` removes it (see below).
          inherit towerFor;
          # Likewise a function: `lib.selfhostWith { wiz, tests }` is the seeded build
          # of the two self-hosted programs, and it needs the builder itself to be an
          # attribute of this set (a `let` binding is not reachable from `lib`).
          inherit selfhostProgramWith;
          # The trusted Lake seed as a package: `withLakeCache empty-lake`'s `lake`
          # output (the compiled `.lake` directory without the linked binaries). A master
          # push builds this and publishes the store path to the trusted Cachix; a pull
          # request names its base commit's output, substitutes it and passes it to
          # `withLakeCache` (scripts/lake-cache.sh `trusted`). The seed is a derivation
          # output, not a tarball in an Actions cache.
          lake-seed = (packagesWith pkgs (emptyLake pkgs)).unwrapped.lake;
          source-tarball = release-tarball;
          default = wiz;
          wizc = bootstrapChain.wizc;
          wizc-seed = bootstrapChain.seed;
          wizc-release = bootstrapChain.release { };
          inherit bootstrapChain;
        };
    in {
      # (packages without the function set, which is not a derivation)
      packages = forAll (pkgs: builtins.removeAttrs (packagesFor pkgs) [ "bootstrapChain" "towerFor" ]);
      legacyPackages = forAll (pkgs: { inherit (packagesFor pkgs) bootstrapChain towerFor; });

      # The function set (a flake output cannot be a function, so `packages` cannot hold
      # `withLakeCache`). CI's producer and consumer both call it through
      # scripts/lake-cache.sh:
      #   nix build --impure --expr \
      #     'let f = builtins.getFlake "/path/to/checkout"; in
      #      (f.lib."x86_64-linux".withLakeCache f.lib."x86_64-linux"."empty-lake").unwrapped.lake'
      lib = forAll (pkgs: {
        withLakeCache = lakeCache: packagesWith pkgs lakeCache;
        empty-lake = emptyLake pkgs;
        # `lib.selfhostWith { wiz, tests }` is `.#selfhost-compiler`/`.#selfhost-checker`
        # built with those packages. CI passes the lean job's seeded store paths through
        # `builtins.storePath`, so a pull request does not cold-build the pure compiler.
        selfhostWith = { wiz, tests }: {
          compiler = (packagesWith pkgs null).selfhostProgramWith
            { wizPkg = wiz; testsPkg = tests; } "compiler" "selfhost-compiler";
          checker = (packagesWith pkgs null).selfhostProgramWith
            { wizPkg = wiz; testsPkg = tests; } "checker" "selfhost-checker";
        };
        # `lib.towerWith wizPkg` is `.#tower` built with that `wiz` package. CI passes
        # the lean job's store path through `builtins.storePath`, so the seeded compiler
        # is a build input and `wiz-unwrapped` is never instantiated.
        towerWith = wizPkg: (packagesWith pkgs null).towerFor wizPkg;
      });

      apps = forAll (pkgs:
        let
          pkg = self.packages.${pkgs.stdenv.hostPlatform.system}.wiz;
          app = name: { type = "app"; program = "${pkg}/bin/${name}"; meta = pkg.meta; };
          towerPkg = self.packages.${pkgs.stdenv.hostPlatform.system}.tower;
          nvim = self.packages.${pkgs.stdenv.hostPlatform.system}.nvim-wiz;
        in {
          wiz = app "wiz"; grail = app "grail"; default = app "wiz";
          tower = { type = "app"; program = "${towerPkg}/bin/tower"; meta = towerPkg.meta; };
          nvim-wiz = { type = "app"; program = "${nvim}/bin/nvim-wiz"; meta = nvim.meta; };
        });

      devShells = forAll (pkgs: {
        # CI's publish step: `cachix` from this flake's locked nixpkgs, so no global
        # registry (`nixpkgs#cachix`) is consulted by a job with the push token.
        ci = pkgs.mkShell {
          packages = [ pkgs.cachix ];
        };
        default = pkgs.mkShell {
          # neovim: the `nvim` test group (editors/nvim); z3 and cadical: the `smt` and `sat`
          # groups (stage 28b: `sat_decide` finds it on PATH); yosys: the synthesis cases
          # (the `hdl` group and the HDL protocol hooks), so CI runs them instead of
          # skipping; nodejs: the WebAssembly backend's modules run under Node with
          # web/wasm-host.mjs (stage 8f) and skip without it
          packages = [
            # the Lean toolchain and the C/LLVM backend's libraries
            pkgs.elan pkgs.gmp pkgs.boehmgc pkgs.llvm
            # the test suite's tools (each one had a `skipMissing` before CI's image
            # happened to provide it: node, yosys, iverilog/vvp, z3/cadical, ssh-keygen)
            pkgs.python3 pkgs.git pkgs.neovim pkgs.nodejs
            pkgs.z3 pkgs.cadical pkgs.yosys pkgs.iverilog pkgs.openssh
            # the scripts' tools (release/tarball, fetch/vendor, docs, patches)
            pkgs.curl pkgs.jq pkgs.rsync pkgs.gnumake pkgs.tree-sitter
            pkgs.coreutils pkgs.diffutils pkgs.patch pkgs.which pkgs.file
            pkgs.gnutar pkgs.gzip pkgs.xz pkgs.zip pkgs.unzip pkgs.time
          ];
          # `wiz` and `grail` take the toolchain as flags (stage 23a); grail and the test
          # driver read this machine's paths from the uncommitted grail.local.wiz written
          # here (when run from the repository root). Nothing reads the environment.
          shellHook = let tc = toolchain pkgs; in ''
            WIZ_CFLAGS="${tc.cflags}"
            WIZ_LDFLAGS="${tc.ldflags}"
            WIZ_LLC="${tc.llc}"
            WIZ_GC_CFLAGS="${tc.gc-cflags}"
            WIZ_GC_LDFLAGS="${tc.gc-ldflags}"
            if [ -f grail.wiz ]; then
              local_wiz=$(printf '%s\n' \
                '-- This machine'"'"'s toolchain, written by the nix dev shell (flake.nix); not committed.' \
                'import Grail' \
                'def settings : Settings := Settings.empty' \
                "  |> Settings.set \"cflags\" \"$WIZ_CFLAGS\"" \
                "  |> Settings.set \"ldflags\" \"$WIZ_LDFLAGS\"" \
                "  |> Settings.set \"llc\" \"$WIZ_LLC\"" \
                "  |> Settings.set \"gc-cflags\" \"$WIZ_GC_CFLAGS\"" \
                "  |> Settings.set \"gc-ldflags\" \"$WIZ_GC_LDFLAGS\"")
              [ "$(cat grail.local.wiz 2>/dev/null)" = "$local_wiz" ] || printf '%s\n' "$local_wiz" > grail.local.wiz
            fi
          '';
        };
      });
    };
}
