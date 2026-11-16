# Generated documentation and test data: built here, never committed (docs/building.md,
# "Generated files"). Each derivation reads only its generator and inputs, so an
# unrelated change does not rebuild it, and each is deterministic: the same inputs give
# the same bytes (the generators add no timestamps or absolute paths).
#
#   nix build .#semantics-matrix     result/cells.tsv, result/semantics-matrix.md
#   nix build .#notebook-pages       result/*.html (the site's /notebooks/)
#   nix build .#grail-index-fixture  result/{registry.sexpr,index/,packages/}
{ pkgs }:
let
  lib = pkgs.lib;
  fs = lib.fileset;
  src = files: fs.toSource { root = ../.; fileset = fs.unions files; };
in
{
  # The value-level semantics matrix (stage 22): the document and the TSV the
  # `=semantics` test reads (the test runs the same generator itself).
  semantics-matrix = pkgs.runCommand "wiz-semantics-matrix"
    {
      src = src [ ../scripts/gen-semantics-matrix.py ];
      nativeBuildInputs = [ pkgs.python3 ];
    } ''
    python3 $src/scripts/gen-semantics-matrix.py --out $out
  '';

  # The notebooks in docs/notebooks/ exported to static pages, plus their index.
  notebook-pages = pkgs.runCommand "wiz-notebook-pages"
    {
      src = src [
        ../tools/jupyter/export.py
        ../tools/jupyter/export-notebooks.sh
        (fs.fileFilter (f: f.hasExt "py") ../tools/jupyter/wiz_kernel)
        (fs.fileFilter (f: f.hasExt "ipynb") ../docs/notebooks)
        ../docs/notebooks/index.html
      ];
      nativeBuildInputs = [ pkgs.python3 ];
    } ''
    sh $src/tools/jupyter/export-notebooks.sh $out
  '';

  # The grail-index test fixture rendered (Tests/fixtures/grail-index/make.sh): the
  # tests render their own copy; this is the same output, for inspection and for the
  # reproducibility check.
  grail-index-fixture = pkgs.runCommand "wiz-grail-index-fixture"
    {
      src = src [ ../Tests/fixtures/grail-index ];
      nativeBuildInputs = [ pkgs.gnutar pkgs.gzip pkgs.coreutils pkgs.gnused ];
    } ''
    sh $src/Tests/fixtures/grail-index/make.sh $out
  '';
}
