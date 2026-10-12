{
  description = "Functional Programming in Lean — build environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = {
    self,
    nixpkgs,
  }: let
    systems = [
      "x86_64-linux"
      "aarch64-linux"
      "x86_64-darwin"
      "aarch64-darwin"
    ];

    forAllSystems = f:
      nixpkgs.lib.genAttrs systems (system: f (import nixpkgs {inherit system;}));

    # Some of what the build needs is not captured by a Lean toolchain alone:
    # the book compiles and runs a C program (book/expect/native/pty.c) and
    # executes a Python interpreter, rendering its output into the text.
    #
    # elan is what makes the two projects' different Lean versions work. It reads
    # the lean-toolchain files and installs `book`'s (v4.34.0-rc1) and
    # `examples`' (4.33.0) toolchains as they are needed.
    sharedInputs = pkgs:
      with pkgs;
        [
          elan
          git
          curl
          cacert
          gnumake
          which
        ]
        ++ [
          stdenv.cc
          python3
        ];

    # Runs a command from the repository root so that the scripts behave the
    # same whether they are started at the top of the tree or in a subdirectory.
    repoRoot = ''
      if root="$(git rev-parse --show-toplevel 2>/dev/null)"; then
        :
      else
        root="$PWD"
      fi
      if [ ! -e "$root/book/lakefile.lean" ]; then
        echo "error: $root does not look like the fp-lean repository" >&2
        exit 1
      fi
      export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
    '';

    mkScript = pkgs: name: text:
      pkgs.writeShellApplication {
        inherit name text;
        runtimeInputs = (sharedInputs pkgs) ++ [pkgs.coreutils];
      };

    mkScripts = pkgs: {
      build-examples = mkScript pkgs "build-examples" ''
        ${repoRoot}
        cd "$root/examples"
        lake build
        lake build subverso-extract-mod
      '';
      build-book = mkScript pkgs "build-book" ''
        ${repoRoot}
        cd "$root/examples"
        lake build
        lake build subverso-extract-mod
        cd "$root/book"
        lake exe fp-lean "$@"
      '';
      serve-book = mkScript pkgs "serve-book" ''
        ${repoRoot}
        cd "$root/book"
        lake exe verso-serve "$@"
      '';
    };
  in {
    devShells = forAllSystems (pkgs: {
      default = pkgs.mkShell {
        packages =
          sharedInputs pkgs
          ++ pkgs.lib.attrValues (mkScripts pkgs)
          ++ [pkgs.bashInteractive];

        shellHook = ''
          # elan installs toolchains here and exposes its lean/lake proxies
          # through this directory.
          export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
          export PATH="$ELAN_HOME/bin:$PATH"

          cat <<'EOF'
          Functional Programming in Lean

            build-examples   lake build in examples/ (incl. subverso-extract-mod)
            build-book       build the HTML into book/_out
            serve-book       serve book/_out/html-multi over HTTP

          The toolchains named in book/lean-toolchain and
          examples/lean-toolchain are installed by elan on first use, so the
          first build needs network access.
          EOF
        '';
      };
    });

    packages = forAllSystems (pkgs: let
      scripts = mkScripts pkgs;
    in
      scripts
      // {
        default = scripts.build-book;
      });

    apps = forAllSystems (pkgs: let
      scripts = mkScripts pkgs;
    in {
      build-examples = {
        type = "app";
        program = "${scripts.build-examples}/bin/build-examples";
        meta.description = "Build the example code in examples/";
      };
      build-book = {
        type = "app";
        program = "${scripts.build-book}/bin/build-book";
        meta.description = "Build the book HTML into book/_out";
      };
      serve-book = {
        type = "app";
        program = "${scripts.serve-book}/bin/serve-book";
        meta.description = "Serve the built book over HTTP";
      };
      default = self.apps.${pkgs.stdenv.hostPlatform.system}.build-book;
    });

    formatter = forAllSystems (pkgs: pkgs.alejandra);
  };
}
