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

        toml = pkgs.lib.importTOML ./crates/domino/Cargo.toml;
        workspaceToml = pkgs.lib.importTOML ./Cargo.toml;

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

        rustPlatform = pkgs.makeRustPlatform {
          cargo = dominoToolchain;
          rustc = dominoToolchain;
        };

        domino = rustPlatform.buildRustPackage {
          name = toml.package.name;
          version = workspaceToml.workspace.package.version;
          src = src;
          doCheck = true;
          cargoLock.lockFile = ./Cargo.lock;
          buildAndTestSubdir = "crates/domino/";
          cargoBuildFlags = [ "--workspace" ];
          checkPhase = ''
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
          programs.rustfmt.edition = workspaceToml.workspace.package.edition;
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

        devShellPackages = [
          dominoToolchain
          pkgs.cargo-release
          pkgs.rustfmt
        ];

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
      in
      {
        packages.default = domino;
        packages.domino = domino;
        packages.dominoToolchain = dominoToolchain;

        formatter = dominoTreefmt.config.build.wrapper;

        checks.default = domino;
        checks.domino = domino;
        checks.treefmt = dominoTreefmt.config.build.check self;

        checks.knownWorkingExamples = pkgs.stdenv.mkDerivation {
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

        devShells.default = pkgs.mkShellNoCC {
          packages = devShellPackages ++ [
            domino
            pkgs.cvc5
            texlive
          ];
        };
        devShells.dev = pkgs.mkShellNoCC {
          packages = devShellPackages;
        };
      }
    );
}
