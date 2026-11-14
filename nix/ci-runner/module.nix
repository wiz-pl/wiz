# An optional, ephemeral self-hosted GitHub Actions runner for the Wiz CI.
#
# Import this module (the flake exports it as `nixosModules.ci-runner`) and set
# `services.wiz-ci-runner.enable = true`; it is inert otherwise.  See
# docs/ci-runner.md for the host setup, the token, and the security caveats.
{ config, lib, pkgs, ... }:

let
  cfg = config.services.wiz-ci-runner;
  runner = import ./runner.nix { inherit pkgs; };

  # The base under /var/lib: systemd's StateDirectory= creates it, and the
  # runner's private state and work directories live below it.
  stateRoot = "/var/lib/wiz-ci-runner";
  stateDir = "${stateRoot}/runner";

  # `wiz-pl/wiz` -> "repo:wiz-pl/wiz"; `wiz-pl` -> "org:wiz-pl".  GitHub
  # Enterprise hosts (and explicit scopes) set services.wiz-ci-runner.scope.
  scope =
    if cfg.scope != null then
      cfg.scope
    else
      let
        prefix = "https://github.com/";
        parts = lib.filter (part: part != "") (lib.splitString "/" (lib.removePrefix prefix cfg.url));
      in
      if lib.hasPrefix prefix cfg.url && lib.length parts == 2 then
        "repo:${lib.concatStringsSep "/" parts}"
      else if lib.hasPrefix prefix cfg.url && lib.length parts == 1 then
        "org:${lib.head parts}"
      else
        throw ''
          services.wiz-ci-runner.scope must be set (for example "repo:owner/name") when
          services.wiz-ci-runner.url is not a github.com repository or organisation URL.
        '';

  runnerEnv = {
    WIZ_CI_RUNNER_URL = cfg.url;
    WIZ_CI_RUNNER_NAME = cfg.name;
    WIZ_CI_RUNNER_LABELS = lib.concatStringsSep "," cfg.labels;
    WIZ_CI_RUNNER_TOKEN_TYPE = cfg.tokenType;
    WIZ_CI_RUNNER_API_URL = cfg.apiUrl;
    WIZ_CI_RUNNER_SCOPE = scope;
    WIZ_CI_RUNNER_STATE_DIR = stateDir;
    WIZ_CI_RUNNER_WORK_DIR = cfg.workDir;
    WIZ_CI_RUNNER_USER = cfg.user;
    WIZ_CI_RUNNER_GROUP = cfg.group;
    WIZ_CI_RUNNER_GITHUB_RUNNER = "${cfg.package}";
  };

  # Registration needs the token, so the service starts as root and the
  # runner script drops to cfg.user before the listener runs.  A token file
  # (rather than the service environment) keeps the secret out of `ps` and
  # out of the Nix store.
  credential =
    if cfg.tokenFile != null then
      "token:${toString cfg.tokenFile}"
    else if cfg.tokenCredential != null then
      "token:${cfg.tokenCredential}"
    else
      # The assertion below reports the real problem; keep the unit evaluable.
      "token:/run/wiz-ci-runner-token-missing";
in
{
  options.services.wiz-ci-runner = {
    enable = lib.mkEnableOption ''
      an ephemeral GitHub Actions runner for the Wiz CI.  It takes one job,
      unregisters, and starts again with an empty state and work directory.
    '';

    url = lib.mkOption {
      type = lib.types.str;
      default = "https://github.com/wiz-pl/wiz";
      description = ''
        The repository (or organisation) whose Actions jobs the runner serves.
        This is what `actions/runner`'s `config.sh --url` takes.
      '';
    };

    apiUrl = lib.mkOption {
      type = lib.types.str;
      default = "https://api.github.com";
      description = ''
        The GitHub REST API base.  Change it for GitHub Enterprise (for
        example `https://github.example.com/api/v3`).
      '';
    };

    scope = lib.mkOption {
      type = lib.types.nullOr lib.types.str;
      default = null;
      description = ''
        The registration scope, `repo:owner/name` or `org:owner`.  Derived from
        `url` for `https://github.com/...`; set it explicitly for GitHub
        Enterprise or an organisation URL that is not under github.com.
      '';
      example = "repo:wiz-pl/wiz";
    };

    name = lib.mkOption {
      type = lib.types.str;
      default = "wiz-heavy-${config.networking.hostName}";
      defaultText = lib.literalExpression ''"wiz-heavy-''${config.networking.hostName}"'';
      description = ''
        The runner's name in GitHub.  The default makes it recognisable in
        `gh api repos/wiz-pl/wiz/actions/runners`; use a distinct name for each
        machine running the runner.
      '';
    };

    labels = lib.mkOption {
      type = lib.types.listOf lib.types.str;
      default = [ "wiz-heavy" ];
      description = ''
        Extra labels advertised by the runner.  The Wiz workflow selects this
        label through the repository variable `WIZ_RUNNER_HEAVY`.
      '';
    };

    tokenFile = lib.mkOption {
      type = lib.types.nullOr lib.types.path;
      default = null;
      description = ''
        A file containing a fine-grained personal access token (Administration:
        read and write on this repository's self-hosted runners) or a runner
        registration token.  It is read by systemd's `LoadCredential=`, never
        copied into the Nix store, and never put in the service's environment.
        Exactly one of `tokenFile` and `tokenCredential` is required.
      '';
      example = "/run/secrets/wiz-ci-runner-token";
    };

    tokenCredential = lib.mkOption {
      type = lib.types.nullOr lib.types.str;
      default = null;
      description = ''
        A systemd credential name in `/etc/credstore`, `/run/credstore`, or
        `/usr/lib/credstore` (see systemd-creds(1)), used instead of
        `tokenFile`.  Exactly one of `tokenFile` and `tokenCredential` is
        required.
      '';
      example = "wiz-ci-runner-token";
    };

    tokenType = lib.mkOption {
      type = lib.types.enum [ "auto" "access" "registration" ];
      default = "auto";
      description = ''
        How to use the token.  `access` exchanges a personal access token for a
        fresh one-use registration token on every start; `registration` uses
        the file as a registration token (valid for one hour, so it has to be
        rotated); `auto` detects a personal access token by its prefix.
      '';
    };

    user = lib.mkOption {
      type = lib.types.str;
      default = "wizci";
      description = ''
        The unprivileged user the runner (and therefore every job) runs as.
        The service starts as root only long enough to register and then drops
        to this user.  `root` is rejected.
      '';
    };

    group = lib.mkOption {
      type = lib.types.str;
      default = "wizci";
      description = "The group of the runner user.";
    };

    package = lib.mkOption {
      type = lib.types.package;
      default = pkgs.github-runner;
      defaultText = lib.literalExpression "pkgs.github-runner";
      description = "The `actions/runner` package.";
    };

    workDir = lib.mkOption {
      type = lib.types.str;
      default = "${stateRoot}/work";
      description = ''
        The runner's work directory (`$GITHUB_WORKSPACE`, and the home directory
        for the job).  It is emptied before every job and on every stop, and
        must stay under `/var/lib/wiz-ci-runner`; mount a filesystem there to
        put it on another disk.  Allow room for the build caches (tens of GB).
      '';
    };

    restartSec = lib.mkOption {
      type = lib.types.str;
      default = "10s";
      description = "How long to wait before registering the next ephemeral runner.";
    };

    cachix = {
      enable = lib.mkOption {
        type = lib.types.bool;
        default = true;
        description = "Add the Wiz Cachix cache as a system-wide Nix substituter.";
      };

      name = lib.mkOption {
        type = lib.types.str;
        default = "badlydrawnwizards";
        description = "The Cachix cache name.";
      };

      publicKey = lib.mkOption {
        type = lib.types.str;
        default = "badlydrawnwizards.cachix.org-1:TxG+RHY8RMC/AXc0LJbYtYm9LW/XRjfQwgz+EEaAjBI=";
        description = "The cache's trusted public key.";
      };
    };

    warm = {
      enable = lib.mkOption {
        type = lib.types.bool;
        default = true;
        description = ''
          Pre-fetch the Wiz dev shell once at boot, so the first job does not
          download the toolchain.  The download is best-effort: a failure does
          not stop the runner.
        '';
      };

      flake = lib.mkOption {
        type = lib.types.str;
        default = "github:wiz-pl/wiz";
        description = "The flake whose dev shell is pre-fetched.";
      };

      timeout = lib.mkOption {
        type = lib.types.str;
        default = "20min";
        description = "How long the pre-fetch may take before the runner starts without it.";
      };
    };

    extraPackages = lib.mkOption {
      type = lib.types.listOf lib.types.package;
      default = [ ];
      description = "Extra packages on the runner's (and so every job's) PATH.";
    };

    extraEnvironment = lib.mkOption {
      type = lib.types.attrsOf lib.types.str;
      default = { };
      description = "Extra environment variables for the runner service.";
    };

    serviceOverrides = lib.mkOption {
      type = lib.types.attrs;
      default = { };
      description = ''
        Extra systemd `Service` settings, merged last.  Use with care: the
        service's default hardening is what keeps the registration token away
        from jobs.
      '';
    };
  };

  config = lib.mkIf cfg.enable {
    assertions = [
      {
        assertion = (cfg.tokenFile != null) != (cfg.tokenCredential != null);
        message = "services.wiz-ci-runner: set exactly one of tokenFile and tokenCredential";
      }
      {
        assertion = cfg.tokenFile == null || !(lib.hasPrefix "/nix/store/" (toString cfg.tokenFile));
        message = "services.wiz-ci-runner.tokenFile must not be in the Nix store; deploy it as a runtime secret";
      }
      {
        assertion = cfg.user != "root";
        message = "services.wiz-ci-runner.user must not be root; jobs run as this user";
      }
      {
        assertion = cfg.group != "root";
        message = "services.wiz-ci-runner.group must not be root";
      }
      {
        assertion = cfg.labels != [ ];
        message = "services.wiz-ci-runner.labels must not be empty";
      }
      {
        assertion = !cfg.cachix.enable || cfg.cachix.name != "";
        message = "services.wiz-ci-runner.cachix.name must not be empty";
      }
      {
        assertion = lib.hasPrefix "${stateRoot}/" cfg.workDir;
        message = "services.wiz-ci-runner.workDir must be under ${stateRoot} (mount a filesystem there to use another disk)";
      }
    ];

    users.groups = lib.mkIf (cfg.group != "root") {
      ${cfg.group} = { };
    };

    users.users = lib.mkIf (cfg.user != "root") {
      ${cfg.user} = {
        isSystemUser = true;
        group = cfg.group;
        home = stateRoot;
        createHome = false;
        description = "Wiz CI runner";
      };
    };

    # The runner user is trusted so `cachix-action` (which writes the user's
    # nix.conf on a self-hosted runner) can add the cache; the cache is also
    # configured system-wide so jobs can substitute from it immediately.
    nix.settings = lib.mkMerge [
      {
        experimental-features = [ "nix-command" "flakes" ];
        trusted-users = lib.mkAfter [ cfg.user ];
      }
      (lib.mkIf cfg.cachix.enable {
        substituters = lib.mkAfter [ "https://${cfg.cachix.name}.cachix.org" ];
        trusted-public-keys = lib.mkAfter [ cfg.cachix.publicKey ];
      })
    ];

    systemd.tmpfiles.rules = [
      "d ${cfg.workDir} 0700 ${cfg.user} ${cfg.group} - -"
    ];

    systemd.services.wiz-ci-runner = {
      description = "Wiz ephemeral GitHub Actions runner";
      wantedBy = [ "multi-user.target" ];
      wants = [ "network-online.target" ];
      after = [ "network-online.target" "nix-daemon.service" ]
        ++ lib.optional cfg.warm.enable "wiz-ci-runner-warm.service";
      path = with pkgs; [
        bashInteractive
        cacert
        coreutils
        curl
        diffutils
        findutils
        gawk
        git
        gnused
        gnutar
        gzip
        jq
        openssh
        python3
        which
        xz
        config.nix.package
        cfg.package
      ] ++ cfg.extraPackages;

      environment = {
        HOME = stateRoot;
        SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
        NIX_SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
      } // runnerEnv // cfg.extraEnvironment;

      unitConfig = {
        # StartLimit* live in [Unit]; a wrong token must not loop forever.
        StartLimitIntervalSec = 300;
        StartLimitBurst = 5;
      };

      serviceConfig = {
        Type = "simple";
        # Registration and cleanup need root (to read the credential and to
        # chown the state); the script drops to cfg.user for the listener.
        User = "root";
        Group = "root";
        WorkingDirectory = stateRoot;
        StateDirectory = "wiz-ci-runner";
        StateDirectoryMode = "0700";
        LoadCredential = [ credential ];
        ExecStart = "${runner}/bin/wiz-ci-runner run";
        ExecStopPost = "-${runner}/bin/wiz-ci-runner cleanup";
        Restart = "always";
        RestartSec = cfg.restartSec;
        TimeoutStartSec = "5min";
        TimeoutStopSec = "60s";
        KillSignal = "SIGINT";
        UMask = "0077";

        # The listener is unprivileged, but the unit starts as root to register.
        # CAP_SETUID/CAP_SETGID are only used by setpriv before the listener
        # starts; dropping the user clears the capabilities.
        CapabilityBoundingSet = [
          "CAP_CHOWN"
          "CAP_DAC_OVERRIDE"
          "CAP_FOWNER"
          "CAP_SETGID"
          "CAP_SETUID"
        ];
        AmbientCapabilities = [ ];
        NoNewPrivileges = true;
        PrivateDevices = true;
        PrivateMounts = true;
        PrivateTmp = true;
        ProtectClock = true;
        ProtectControlGroups = true;
        ProtectHome = true;
        ProtectHostname = true;
        ProtectKernelLogs = true;
        ProtectKernelModules = true;
        ProtectKernelTunables = true;
        ProtectProc = "invisible";
        ProtectSystem = "strict";
        ProcSubset = "all";
        ReadWritePaths = [ "-${cfg.workDir}" ];
        RestrictAddressFamilies = [ "AF_INET" "AF_INET6" "AF_NETLINK" "AF_UNIX" ];
        RestrictNamespaces = true;
        RestrictRealtime = true;
        RestrictSUIDSGID = true;
        SystemCallArchitectures = "native";
        # PrivateTmp= covers /tmp and /var/tmp; /dev/shm is a separate tmpfs.
        # Give each job an empty one too, so nothing survives a restart.
        TemporaryFileSystem = [ "/dev/shm:mode=1777" ];
        SystemCallFilter = [
          "~@clock"
          "~@cpu-emulation"
          "~@module"
          "~@mount"
          "~@obsolete"
          "~@raw-io"
          "~@reboot"
          "~setdomainname"
          "~sethostname"
        ];
        # .NET (the runner) and nix commands need these; they are the same
        # exceptions the NixOS github-runners module makes.
        LockPersonality = false;
        MemoryDenyWriteExecute = false;
      } // cfg.serviceOverrides;
    };

    systemd.services.wiz-ci-runner-warm = lib.mkIf cfg.warm.enable {
      description = "Pre-fetch the Wiz CI dev shell";
      wantedBy = [ "multi-user.target" ];
      wants = [ "network-online.target" ];
      after = [ "network-online.target" "nix-daemon.service" ];
      path = with pkgs; [ cacert coreutils git nix openssh ];
      environment = {
        HOME = "/root";
        SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
        NIX_SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
      };
      serviceConfig = {
        Type = "oneshot";
        RemainAfterExit = true;
        TimeoutStartSec = cfg.warm.timeout;
        # A network or cache hiccup must not keep the runner from starting.
        ExecStart = "-${lib.getExe config.nix.package} develop ${lib.escapeShellArg cfg.warm.flake} --command true";
      };
    };
  };
}
