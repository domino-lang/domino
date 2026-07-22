{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.fenix = {
    url = "github:nix-community/fenix";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.treefmt-nix.url = "github:numtide/treefmt-nix";

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      fenix,
      treefmt-nix,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system}.extend fenix.overlays.default;

        dominoToolchain = fenix.packages.${system}.stable.withComponents [
          "cargo"
          "rustc"
          "clippy"
          "rustfmt"
          "rust-std"
        ];

        src = pkgs.lib.sources.sourceByRegex ./. [
          "^Cargo.(lock|toml)$"
          "^crates$"
          "^crates/.*"
          "^src$"
          "^src/.*"
          "^testdata$"
          "^testdata/.*"
          "^example-projects$"
          "^example-projects/.*"
          "^test-projects$"
          "^test-projects/.*"
          "^scripts"
          "^scripts/.*"
        ];

        crateCargotoml = pkgs.lib.importTOML ./crates/domino/Cargo.toml;
        workspaceCargoToml = pkgs.lib.importTOML ./Cargo.toml;

        rustPlatform = pkgs.makeRustPlatform {
          cargo = dominoToolchain;
          rustc = dominoToolchain;
        };

        domino = rustPlatform.buildRustPackage {
          name = crateCargotoml.package.name;
          version = workspaceCargoToml.workspace.package.version;
          src = src;
          doCheck = true;
          cargoLock.lockFile = ./Cargo.lock;
          buildAndTestSubdir = "crates/domino/";
          cargoBuildFlags = [ "--workspace" ];
          # NOTE: cargo check / clippy / fmt used to live here too. They are
          # now separate checks (checks.cargo-check, checks.clippy,
          # checks.treefmt) so they can be run independently and don't run
          # twice under `nix flake check`. This phase is now the full test
          # suite only.
          checkPhase = ''
            echo "==== BEGIN TOOL VERSIONS ===="
            rustc --version
            cargo --version
            cargo clippy -- --version
            echo "==== END TOOL VERSIONS ===="
            cargo test --verbose --workspace --all-targets
            cargo test --verbose --workspace --doc
          '';
          meta.license = with pkgs.lib.licenses; [
            mit
            asl20
          ];
          meta.platforms = pkgs.lib.platforms.all;
        };

        # Lightweight, toolchain-exercising checks. They reuse domino's build
        # setup (src, toolchain, vendored Cargo.lock) but skip the optimized
        # build and the full test suite, so they're cheap enough to run
        # against freshly-updated flake inputs. Build individually in CI with:
        #   nix build .#checks.<system>.cargo-check
        #   nix build .#checks.<system>.clippy
        mkQuickCheck =
          { name, command }:
          domino.overrideAttrs (_: {
            name = "domino-${name}";
            doCheck = false;
            buildPhase = ''
              runHook preBuild
              echo "==== BEGIN TOOL VERSIONS ===="
              rustc --version
              cargo --version
              cargo clippy -- --version
              echo "==== END TOOL VERSIONS ===="
              ${command}
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              touch "$out"
              runHook postInstall
            '';
          });

        cargoCheck = mkQuickCheck {
          name = "cargo-check";
          command = "cargo check --verbose --workspace --all-targets";
        };

        clippyCheck = mkQuickCheck {
          name = "clippy";
          command = "cargo clippy --verbose --workspace --all-targets -- --deny warnings";
        };

        dominoTreefmt = treefmt-nix.lib.evalModule pkgs {
          projectRootFile = "flake.nix";
          programs.nixfmt.enable = true;
          programs.rustfmt.enable = true;
          programs.rustfmt.edition = workspaceCargoToml.workspace.package.edition;
          programs.prettier.enable = true;
          programs.taplo.enable = true;
          programs.taplo.excludes = [
            "**/ssp.toml"
            # skip this one - it is very old and uses an outdated syntax. probably should delete this.
            "example-projects/yao"
          ];
          programs.shfmt.enable = true;
          programs.prettier.includes = [
            "*.md"
            "*.yaml"
            "*.yml"
          ];
        };

        devShellBasePackages = [
          dominoToolchain
          pkgs.cargo-release
          pkgs.rustfmt
        ];

        devShellPackages = devShellBasePackages ++ [
          domino
          pkgs.cvc5
          pkgs.z3
          texlive
        ];

        defaultDevShell = pkgs.mkShellNoCC {
          packages = devShellPackages;
        };

        # for doing dev on domino
        devDevShell = pkgs.mkShellNoCC {
          packages = devShellBasePackages;
        };

        texlive = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-small
            collection-plaingeneric
            collection-latexextra
            collection-fontsrecommended
            cryptocode
            pgfplots
            ;
        };

        knownWorkingExamplesCheck = pkgs.stdenv.mkDerivation {
          name = "domino-knownWorkingExamples";
          src = src;
          buildInputs = [ domino ];
          nativeCheckInputs = [
            pkgs.cvc5
            pkgs.z3
            texlive
          ];
          doCheck = true;
          buildPhase = ''
            cp -R "$src" src/
            chmod -R u+w src/
          '';
          checkPhase = ''
            DOMINO="$(type -p domino)" ${pkgs.bash}/bin/bash ./scripts/test-known-examples.sh
          '';
          installPhase = "touch $out";
        };
      in
      {
        packages.default = domino;
        packages.domino = domino;
        packages.dominoToolchain = dominoToolchain;

        formatter = dominoTreefmt.config.build.wrapper;

        checks.default = domino;
        checks.domino = domino;
        checks.treefmt = dominoTreefmt.config.build.check self;
        checks.cargo-check = cargoCheck;
        checks.clippy = clippyCheck;
        checks.knownWorkingExamples = knownWorkingExamplesCheck;

        devShells.default = defaultDevShell;
        devShells.dev = devDevShell;
      }
    );
}
