{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/22.11";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        hpkgs = pkgs.haskell.packages.ghc902;
      in {
        formatter = pkgs.nixfmt;
        devShells = let
          buildInputs = (with pkgs; [
            git # Required to build in pure nix shells
            cacert # git SSL
            cabal-install
            hpack # Needed by the CI
            ormolu # Needed by the CI
            z3
          ]) ++ [ hpkgs.ghc ];
          LD_LIBRARY_PATH = pkgs.lib.strings.makeLibraryPath [ pkgs.z3 ];
        in {
          ## A minimal development shell
          ci = pkgs.mkShell {
            inherit buildInputs;
            inherit LD_LIBRARY_PATH;
          };
          ## A development shell with more features
          default = pkgs.mkShell {
            buildInputs = buildInputs ++ (with pkgs; [
              cabal-install
              hlint

              # graphmod is a nice tool to visualize the project module
              # structure; run:
              # $ graphmod -p --no-cluster | xdot -
              # to see it in action!
              xdot
              haskellPackages.graphmod
            ]) ++ [ hpkgs.haskell-language-server ];
            inherit LD_LIBRARY_PATH;
          };
        };
      });
}
