{
  # The controls for scripts/check-repro-build.sh --self-test.
  #
  # `reproducible` writes a constant. `nonreproducible` writes a timestamp (the kernel's
  # uptime), its shell's PID and NIX_BUILD_TOP, so a second build of the same derivation
  # produces different bytes. The gate must accept the first and reject the second; see
  # "Reproducible builds" in docs/building.md.
  #
  # No inputs: the self-test needs no network and no nixpkgs, and /bin/sh comes from the
  # sandbox path every Nix installation has.
  description = "Control derivations for the Wiz reproducible-build gate";

  outputs = { self }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      mk = system: name: script: derivation {
        inherit name system;
        builder = "/bin/sh";
        args = [ "-c" script ];
      };
      forSystem = system: {
        reproducible = mk system "repro-gate-reproducible" ''
          echo fixed > $out
        '';
        nonreproducible = mk system "repro-gate-nonreproducible" ''
          if read -r uptime rest < /proc/uptime 2>/dev/null; then :; else uptime=$$; fi
          printf '%s %s %s\n' "$uptime" "$$" "''${NIX_BUILD_TOP:-}" > $out
        '';
      };
    in {
      packages = builtins.listToAttrs (map
        (system: { name = system; value = forSystem system; })
        systems);
    };
}
