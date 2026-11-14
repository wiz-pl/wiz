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
  # and wiz (`nix run .#nvim-wiz`). CI pushes them to the Cachix cache `badlydrawnwizards`; see
  # docs/building.md for `nix run`.
  description = "Wiz: a didactic dependently typed language";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      # The toolchain `wiz build` and grail use: where GMP and Boehm GC live, and `llc`.
      toolchain = pkgs: {
        cflags = "-I${pkgs.gmp.dev}/include";
        ldflags = "-L${pkgs.gmp}/lib -Wl,-rpath,${pkgs.gmp}/lib";
        llc = "${pkgs.llvm}/bin/llc";
        gc-cflags = "-I${pkgs.boehmgc.dev}/include";
        gc-ldflags = "-L${pkgs.boehmgc}/lib -Wl,-rpath,${pkgs.boehmgc}/lib -lgc -lpthread";
      };

      packagesFor = pkgs:
        let
          lib = pkgs.lib;
          fs = lib.fileset;
          lean = pkgs.lean4;
          pinned = lib.removePrefix "leanprover/lean4:v" (lib.trim (builtins.readFile ./lean-toolchain));
          tc = toolchain pkgs;

          # wiz and grail as Lake builds them (unwrapped), from only the files the build
          # reads: a change elsewhere (README, tests, Wiz programs) doesn't rebuild them.
          unwrapped =
            assert lib.assertMsg (lean.version == pinned)
              "flake.nix: nixpkgs has Lean ${lean.version} but lean-toolchain says ${pinned}: update the nixpkgs input (nix flake update) or lean-toolchain";
            pkgs.stdenv.mkDerivation {
              pname = "wiz-unwrapped";
              version = "0.1.0";
              src = fs.toSource {
                root = ./.;
                fileset = fs.unions [
                  ./lakefile.lean ./lake-manifest.json ./lean-toolchain
                  ./Main.lean ./Wiz.lean ./Wiz ./Grail.lean ./Grail
                  ./runtime # the C runtime (wiz_rt.h, rt_*.inc) and WizRuntime.lean, which embeds it (include_str)
                  ./c # linked into the executables (moreLinkObjs)
                ];
              };
              nativeBuildInputs = [ lean ];
              buildPhase = ''
                runHook preBuild
                # no dependencies to fetch (lake-manifest.json); Lake's artifact cache in the sandbox
                export HOME=$TMPDIR LAKE_CACHE_DIR=$TMPDIR/lake-cache
                lake build wiz grail
                runHook postBuild
              '';
              installPhase = ''
                runHook preInstall
                mkdir -p $out/bin
                install -m755 .lake/build/bin/wiz .lake/build/bin/grail $out/bin/
                runHook postInstall
              '';
            };

          # The toolchain as flags (stage 23a: nothing reads the environment). Flags on
          # the command line come later and win.
          tcFlags = [
            "--cc" "${pkgs.stdenv.cc}/bin/cc"
            "--cflags" tc.cflags "--ldflags" tc.ldflags "--llc" tc.llc
            "--gc-cflags" tc.gc-cflags "--gc-ldflags" tc.gc-ldflags
          ];
          addFlags = flags: lib.escapeShellArg (lib.escapeShellArgs flags);

          # $out/share/wiz is laid out like a checkout (lib/ next to .lake/build/bin/),
          # which is where grail looks for the standard library.
          wiz = pkgs.stdenv.mkDerivation {
            pname = "wiz";
            inherit (unwrapped) version;
            dontUnpack = true;
            nativeBuildInputs = [ pkgs.makeWrapper ];
            installPhase = ''
              share=$out/share/wiz
              mkdir -p $share/.lake/build/bin $out/bin
              cp -r ${fs.toSource { root = ./lib; fileset = ./lib; }} $share/lib
              # the marker editors look for (editors/nvim: a library file is served by its toolchain's wiz)
              echo 'A Wiz toolchain: lib/ is its standard library, .lake/build/bin/ its binaries, ../../bin/ its commands (editors use this file to find them).' > $share/TOOLCHAIN
              cp ${unwrapped}/bin/wiz ${unwrapped}/bin/grail $share/.lake/build/bin/
              # wiz's module roots: ./lib (a checkout's), then the packaged standard library
              makeWrapper $share/.lake/build/bin/wiz $out/bin/wiz \
                --prefix PATH : ${lib.makeBinPath [ pkgs.coreutils ]} \
                --add-flags ${addFlags (tcFlags ++ [ "-I" "${placeholder "out"}/share/wiz/lib" ])}
              # grail: git fetches dependencies (stage 23h)
              makeWrapper $share/.lake/build/bin/grail $out/bin/grail \
                --prefix PATH : ${lib.makeBinPath [ pkgs.coreutils pkgs.git ]} \
                --add-flags ${addFlags tcFlags}
            '';
            meta = {
              description = "Wiz, a didactic dependently typed language, and grail, its build tool";
              mainProgram = "wiz";
              platforms = systems;
            };
          };
          # tower, the toolchain manager (stage 26): the Wiz implementation in `tower/`,
          # built by grail (stage 26e/26h). It needs no Lean at build time; the binary
          # links GMP (the flags below), so the closure grows by GMP and glibc only.
          # Wrapped with the programs it runs (git, tar, curl; `nix` and `lake` are the
          # user's), and told its own path for the shims it writes.
          tower-unwrapped = pkgs.stdenv.mkDerivation {
            pname = "tower-unwrapped";
            inherit (unwrapped) version;
            src = fs.toSource {
              root = ./.;
              fileset = fs.unions [ ./tower ./scripts/build-tower-wiz.sh ];
            };
            nativeBuildInputs = [ wiz ];
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
          tower = pkgs.stdenv.mkDerivation {
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
        in { inherit wiz unwrapped tower wiz-nvim nvim-wiz; default = wiz; };
    in {
      packages = forAll packagesFor;

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
        default = pkgs.mkShell {
          # neovim: the `nvim` test group (editors/nvim); z3 and cadical: the `smt` and `sat` groups
          # (stage 28b: `sat_decide` finds it on PATH)
          packages = [ pkgs.elan pkgs.gmp pkgs.boehmgc pkgs.llvm pkgs.python3 pkgs.git pkgs.neovim pkgs.z3 pkgs.cadical ];
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
