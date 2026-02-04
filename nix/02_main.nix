ctx: ctx.scoped rec {
  inherit (builtins) fromTOML readFile trace;

  inherit (ctx.flake.inputs) nixpkgs;
  inherit (nixpkgs.lib.fileset) toSource;
  inherit (nixpkgs.lib.sources) sourceByRegex cleanSourceWith;

  # TODO: This is really ugly – use flake-parts?
  fenix = ctx.flake.inputs.fenix.packages.${ctx.system.name};
  pkgs = ctx.flake.inputs.nixpkgs.legacyPackages.${ctx.system.name}.extend ctx.flake.inputs.fenix.overlays.default;

  inherit (pkgs) mkShellNoCC;
  inherit (pkgs.testers) runNixOSTest;
  inherit (pkgs.stdenv) mkDerivation;
  inherit (pkgs.writers) writePython3Bin;


  # TODO: The overlay is now working as it should
  inherit (pkgs.makeRustPlatform {
    cargo = packages.dominoToolchain;
    rustc = packages.dominoToolchain;
  }) buildRustPackage;

  packages.dominoToolchain = fenix.default.withComponents [
    "cargo"
    "rustc"
    "clippy"
    "rustfmt"
    "rust-std"
  ];


  git = {
    revision = ctx.flake.self.rev or ctx.flake.self.dirtyRev;
  };

  result.packages = packages;
  result.devShells = devShells;
  result.apps = apps;
  result.checks = checks;

  apps = {};

  # TODO: Path should be a config variable
  workspace.path = ../.;
  workspace.toml = readToml (workspace.path + "/Cargo.toml");
  workspace.src = sourceByRegex workspace.path [
     "^Cargo.(lock|toml)$"
     "^crates$"
     "^crates/.*"
     "^src$"
     "^src/.*"
     "^testdata$"
     "^testdata/.*"
     "^example-projects$"
     "^example-projects/.*"
     "^scripts"
     "^scripts/.*"
  ];

  toml = readToml (workspace.path + "/Cargo.toml");

  packages.default = packages.domino;

  packages.domino = buildRustPackage {
    name = toml.package.name;
    version = toml.package.version;
    src = workspace.src;
    doCheck = true;
    cargoLock.lockFile = workspace.path + "/Cargo.lock";
    buildAndTestSubdir = "crates/domino/";
    #meta.description = toml.package.description;
    #meta.homepage = toml.package.description;
    meta.license = with pkgs.lib.licenses; [ mit asl20 ];
    meta.platforms = pkgs.lib.platforms.all;
    cargoBuildFlags = ["--workspace"];
    checkPhase = "
      cargo test --workspace
      cargo clippy --workspace --all-targets -- --deny warnings
    ";
  };

  checks.default = packages.domino;
  checks.domino = packages.domino;
  checks.knownWorkingExamples = mkDerivation {
    name = "domino-knownWorkingExamples";
    src = workspace.src;
    buildInputs = with pkgs; [
      packages.domino
      cvc5
      z3
      cvc4
    ];
    buildCommand = ''
      cp -R "$src" src/
      chmod -R u+w src/
      cd src
      DOMINO="$(type -p domino)" ${pkgs.bash}/bin/bash ./scripts/test-known-examples.sh
      touch $out
    '';
  };

  devShellPackages = []
    ++ [packages.dominoToolchain]
    ++ (with pkgs; [
      cargo-release
      rustfmt
    ]);

  devShells.default = mkShellNoCC {
    packages = devShellPackages ++ [packages.domino];
  };

  devShells.noDominoItself = mkShellNoCC {
    packages = devShellPackages;
  };

  readToml = (file: fromTOML (readFile file));
}
