# The self-hosted toolchain chain: a prototype (docs/bootstrap-chain.md).
#
# NOT ACTIVE. Nothing in CI builds these packages, and no commit pins a toolchain yet:
# the chain starts once the root is declared (docs/bootstrap-chain.md, "The start
# condition"). Until then they exist to be built locally and measured.
#
# Terms (all in docs/bootstrap-chain.md):
#   self.wiz   the toolchain's source as one program, the input of every stage
#   wizc       the self-hosted compiler as a static executable: reads input.wiz in its
#              working directory, prints C
#   C*         the fixpoint C: the C that wizc built from C* prints for self.wiz
#   release    wizc built from C*, checked to reproduce C*, packed reproducibly
#
# Everything here is a function of (selfhost/ sources, nixpkgs) plus, for `step`, the
# predecessor toolchain; the release's bytes do not depend on the predecessor.
{ pkgs, lib, hostWiz, selfhostSrc, version, rc ? true }:
let
  static = pkgs.pkgsStatic;
  gc = static.boehmgc;
  # The memory mode of every stage. Reference counting (stage 21k) is the default: the
  # executable then links libc only (no collector), a self-compile peaks near 1.7 GB
  # instead of 5.7 GB and takes minutes instead of a quarter of an hour, and a leak is a
  # hard error. `rc = false` gives the collector's chain (Boehm GC, static).
  modeFlag = lib.optionalString rc "--rc";
  gcFlags = lib.optionalString (!rc) "-I${lib.getDev gc}/include";
  gcLibs = if rc then "" else "-L${lib.getLib gc}/lib -lgc -lpthread";

  # Build wizc from a C file (the output of some compiler for self.wiz), statically, with
  # the self-hosted runtime (selfhost/rt.c, #included by the C), and Boehm GC when
  # `rc` is false. The source
  # is copied to the fixed name wizc.c first: cc records the base name in the symbol
  # table, so equal C gives an equal executable only under one name. Then run it on
  # self.wiz: $out/self.c is what this compiler makes of the toolchain.
  stage = { name, c, selfWiz }: static.stdenv.mkDerivation {
    inherit name;
    dontUnpack = true;
    dontStrip = true; # the bytes are what they are; stripping is a separate, later choice
    dontPatchELF = true;
    buildPhase = ''
      runHook preBuild
      cp ${c} wizc.c
      $CC -O2 -w -static -I${selfhostSrc}/selfhost ${gcFlags} wizc.c -o wizc ${gcLibs}
      mkdir run
      cp ${selfWiz} run/input.wiz
      (cd run && ../wizc ${modeFlag}) > self.c
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      install -Dm755 wizc $out/bin/wizc
      install -Dm644 self.c $out/self.c
      install -Dm644 wizc.c $out/wizc.c
      runHook postInstall
    '';
    # A static executable must not refer to the store (a release cannot carry references).
    disallowedReferences = [ static.stdenv.cc.libc ] ++ lib.optionals (!rc) [ gc (lib.getDev gc) ];
  };

  # The input of the chain at this commit, assembled by the Lean host: self.wiz (and
  # compiler.wiz, the same program for the Lean `wiz build`), and seed.c, the C that
  # the Lean-built compiler prints for self.wiz. Today assembly needs the Lean host
  # (Wiz/Selfhost.lean: strip imports, concatenate, a toolchain id from Lean's string
  # hash); a Lean-free chain step needs that assembly in Wiz or in this file (the
  # design's prerequisite P2).
  seed = pkgs.stdenv.mkDerivation {
    name = "wiz-selfhost-seed-${version}";
    src = selfhostSrc;
    nativeBuildInputs = [ hostWiz ];
    buildPhase = ''
      runHook preBuild
      export HOME=$TMPDIR
      cat > grail.wiz <<'EOF'
      import Grail
      def package : Package := Package.new "wiz-selfhost"
        |> Package.selfhost "selfhost-compiler" "compiler"
      EOF
      grail build selfhost-compiler
      mkdir run
      cp .grail/gen/compiler-self.wiz run/input.wiz
      (cd run && ../.grail/bin/selfhost-compiler ${modeFlag}) > seed.c
      runHook postBuild
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p $out
      cp .grail/gen/compiler.wiz $out/compiler.wiz
      cp .grail/gen/compiler-self.wiz $out/self.wiz
      cp seed.c $out/seed.c
      runHook postInstall
    '';
  };

  # The fixpoint check and the release's executable: wizc built from `c`, which must
  # print `c` again for self.wiz. Fails (no release) when it does not.
  fixpoint = { c, selfWiz }:
    let s = stage { name = "wizc-fixpoint-${version}"; inherit c selfWiz; }; in
    pkgs.runCommand "wizc-${version}" { } ''
      if ! cmp -s ${c} ${s}/self.c; then
        echo "no fixpoint: wizc built from ${c} prints different C:" >&2
        cmp ${c} ${s}/self.c >&2 || true
        exit 1
      fi
      mkdir -p $out/bin
      cp ${s}/bin/wizc $out/bin/wizc
    '';

  # One link of the chain from a predecessor toolchain `pred` (a directory with bin/wizc,
  # e.g. `fetchToolchain …` of the previous release): pred compiles self.wiz (c1), the
  # compiler that C builds compiles it again (c2 = C*, whatever pred was, as long as pred
  # compiles correctly), and the fixpoint check builds the release from c2. Three
  # self-compiles; the Lean root needs one (`fromLean`), because the Lean-built
  # compiler's seed.c is already C*.
  step = { pred, selfWiz ? seed + "/self.wiz" }:
    let
      c1 = pkgs.runCommand "wiz-selfhost-c1-${version}" { } ''
        mkdir run; cp ${selfWiz} run/input.wiz
        (cd run && ${pred}/bin/wizc ${modeFlag}) > $out
      '';
      s1 = stage { name = "wizc-stage1-${version}"; c = c1; inherit selfWiz; };
      # c1, s1 and c2 (= s1/self.c) are attributes of the result, so a check can compare
      # them (scripts/chain-step-check.sh); `//` on a derivation keeps its drvPath.
    in fixpoint { c = "${s1}/self.c"; inherit selfWiz; } // { inherit c1 s1; };

  fromLean = fixpoint { c = "${seed}/seed.c"; selfWiz = "${seed}/self.wiz"; };

  # The release artifact: a reproducible tarball of the executable (the same tar flags
  # as scripts/release-tarball.sh), self-contained (no store paths). Its MANIFEST holds
  # only facts about the bytes (so the tarball stays a function of the sources and
  # nixpkgs); the commit, the source's narHash and the nixpkgs lock are bound by the
  # attestation, outside the artifact. Its sha256 is what a pin names.
  release = { toolchain ? fromLean, c ? "${seed}/seed.c" }:
    pkgs.runCommand "wizc-release-${version}" { nativeBuildInputs = [ pkgs.gnutar pkgs.gzip ]; } ''
      top=wizc-${pkgs.stdenv.hostPlatform.system}
      mkdir -p $top/bin
      cp ${toolchain}/bin/wizc $top/bin/wizc
      if grep -q /nix/store $top/bin/wizc; then
        echo "release: wizc names a store path, so it is not self-contained:" >&2
        grep -ao '/nix/store/[a-z0-9]*-[^/[:space:]]*' $top/bin/wizc | sort -u | head >&2
        exit 1
      fi
      {
        echo "format 1"
        echo "version ${version}"
        echo "system ${pkgs.stdenv.hostPlatform.system}"
        echo "mode ${if rc then "rc" else "gc"}"
        echo "wizc-sha256 $(sha256sum $top/bin/wizc | cut -d' ' -f1)"
        echo "fixpoint-c-sha256 $(sha256sum ${c} | cut -d' ' -f1)"
      } > $top/MANIFEST
      mkdir -p $out
      tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner \
          --mode='u+rwX,go+rX,go-w' -cf - $top | gzip -n > $out/$top.tar.gz
      (cd $out && sha256sum $top.tar.gz > $top.tar.gz.sha256)
    '';

  # Fetch a released toolchain by commit and content hash, from any of `urls` (GitHub
  # Releases by default) or from any substituter that has the path: a fixed-output
  # derivation's store path depends only on its name and hash, so a Cachix copy, a
  # local `nix store add-file`, or a mirror are all the same object. The commit is only
  # in the name and the default URL; the hash is the identity.
  fetchToolchain = { commit, hash, urls ? [ ], system ? pkgs.stdenv.hostPlatform.system }:
    assert lib.assertMsg (builtins.match "[0-9a-f]{40}" commit != null)
      "fetchToolchain: commit must be a full 40-hex commit, got '${commit}'";
    assert lib.assertMsg (builtins.match "sha256-[A-Za-z0-9+/]{43}=" hash != null)
      "fetchToolchain: hash must be an SRI sha256 (sha256-…=), got '${hash}'";
    let
      tarball = pkgs.fetchurl {
        name = "wizc-${system}-${commit}.tar.gz";
        urls = urls ++ [
          "https://github.com/wiz-pl/wiz/releases/download/toolchain-${commit}/wizc-${system}.tar.gz"
        ];
        inherit hash;
      };
    in
    pkgs.runCommand "wizc-${builtins.substring 0 12 commit}" { } ''
      mkdir -p $out
      tar -xzf ${tarball} -C $out --strip-components=1
      # static: it runs as is, nothing to patch or wrap
    '';
in
{
  inherit stage seed fixpoint step fromLean release fetchToolchain;
  wizc = fromLean;
}
