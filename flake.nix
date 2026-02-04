{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.fenix = {
    url = "github:nix-community/fenix";
    inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = (inputs:
    let scoped = (scope: scope.result);
    in scoped rec {
      inherit (builtins) removeAttrs;

      result = (import ./nix/01_init.nix) {
        scoped = scoped;
        flake.self = inputs.self;
        flake.inputs = removeAttrs inputs ["self"];
      };
    }
  );
}
