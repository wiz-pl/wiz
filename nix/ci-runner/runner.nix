{ pkgs }:
pkgs.writeShellApplication {
  name = "wiz-ci-runner";
  runtimeInputs = with pkgs; [
    bash
    coreutils
    curl
    jq
    util-linux
    github-runner
  ];
  text = builtins.readFile ./runner.sh;
  meta = {
    description = "Ephemeral GitHub Actions runner for the Wiz CI";
    mainProgram = "wiz-ci-runner";
    platforms = [ "x86_64-linux" "aarch64-linux" ];
  };
}
