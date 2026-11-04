{
  description = "Pinned development environment for the beeping-machine proofs";

  inputs = {
    lean4-nix.url = "github:lenianiva/lean4-nix";
    nixpkgs.follows = "lean4-nix/nixpkgs";
  };

  outputs = { nixpkgs, lean4-nix, ... }:
    let
      systems = [ "aarch64-darwin" "aarch64-linux" "x86_64-darwin" "x86_64-linux" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
    in {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ (lean4-nix.readToolchainFile { toolchain = ./lean-toolchain; binary = true; }) ];
          };
        in {
          default = pkgs.mkShell {
            packages = [ pkgs.lean.lean-all pkgs.python312 pkgs.git pkgs.curl pkgs.zstd ];
          };
        });
    };
}
