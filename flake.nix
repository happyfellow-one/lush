{
  description = "Lean 4 project lush";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.lean4
            pkgs.git
          ];

          shellHook = ''
            echo "🟣 Lean 4 development environment loaded"
            echo "🟣 Available commands:"
            echo "   lake build     - Build the project"
            echo "   lake test      - Run tests"
            echo "   lake serve     - Start Lake server"
            echo "   lean --version - Check Lean version"
          '';
        };
      });
}
