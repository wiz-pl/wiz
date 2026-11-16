# The chain's step check at one commit (scripts/chain-step-check.sh, docs/bootstrap-chain.md):
# the release built from the Lean host, and the same commit rebuilt by `bootstrapChain.step`
# from that release fetched by hash. Every attribute is a derivation; the script compares
# their bytes.
#
#   nix build -f scripts/chain-step.nix --argstr root "$PWD" --argstr commit SHA \
#     [--argstr hash sha256-…=] [--argstr predCommit SHA] ATTR
#
# The predecessor is the release of `predCommit` (default: `commit` itself) with sha256
# `hash`, fetched by fetchToolchain (it must be in the store or a substituter).
{ root, commit, hash ? null, predCommit ? commit, system ? builtins.currentSystem }:
let
  flake = builtins.getFlake "git+file://${root}?rev=${commit}";
  chain = flake.legacyPackages.${system}.bootstrapChain;
  pred = chain.fetchToolchain { commit = predCommit; inherit hash system; };
  step = chain.step { inherit pred; };
in
{
  # path A: the Lean host's seed.c, compiled statically, checked to reproduce itself
  seed = flake.packages.${system}.wizc-seed;
  lean-release = flake.packages.${system}.wizc-release;
  # path B: a release (fetched by commit and hash) compiles this commit's source
  inherit pred step;
  c1 = step.c1; # pred's C for self.wiz
  stage1 = step.s1; # wizc built from c1; stage1/self.c is c2
  # path B's executable packed like path A's, with c2 as its fixpoint C
  step-release = chain.release { toolchain = step; c = "${step.s1}/self.c"; };
}
