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
          checkPhase = ''
            echo "==== BEGIN TOOL VERSIONS ===="
            rustc --version
            cargo --version
            cargo clippy -- --version
            echo "==== END TOOL VERSIONS ===="
            export RUSTFLAGS="-D warnings"
            cargo test --verbose --workspace --all-targets
            cargo test --verbose --workspace --doc
            cargo check --verbose --workspace --all-targets
            cargo clippy --verbose --workspace --all-targets -- --deny warnings
            cargo fmt --all --verbose --check
          '';
          meta.license = with pkgs.lib.licenses; [
            mit
            asl20
          ];
          meta.platforms = pkgs.lib.platforms.all;
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
        checks.knownWorkingExamples = knownWorkingExamplesCheck;

        devShells.default = defaultDevShell;
        devShells.dev = devDevShell;
      }
    );
}
