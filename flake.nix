{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/22.11";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.pre-commit-hooks.url = "github:cachix/pre-commit-hooks.nix";

  outputs = { self, nixpkgs, flake-utils, pre-commit-hooks }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        hpkgs = pkgs.haskell.packages.ghc902;

        pre-commit = pre-commit-hooks.lib.${system}.run {
          src = ./.;
          hooks = {
            nixfmt.enable = true;
            ormolu.enable = true;

            ## FIXME: The upstream `hpack` hook is completely broken, so we
            ## write our own, heavily inspired by theirs but introducing some
            ## fixes. The bugs have been reported at
            ##
            ## https://github.com/cachix/pre-commit-hooks.nix/issues/235
            ##
            ## and we should simply update pre-commit-hooks, remove all this and
            ## replace it by `hpack.enable = true` once they are fixed.
            hpack-fixed = {
              enable = true;
              entry = let
                hpack-dir = pkgs.writeShellApplication {
                  name = "hpack-dir";
                  text = ''
                    find . -type f -name package.yaml | while read -r file; do
                        ${pkgs.hpack}/bin/hpack --force "$file"
                    done
                  '';
                };
              in "${hpack-dir}/bin/hpack-dir";
              files = "(\\.l?hs(-boot)?$)|(\\.cabal$)|((^|/)package\\.yaml$)";
              pass_filenames = false;
            };
          };
        };
      in {
        formatter = pkgs.nixfmt;

        devShells = let
          buildInputs = (with pkgs; [
            git # Required to build in pure nix shells
            cacert # git SSL
            cabal-install
            hpack # Needed by the CI
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
            inherit (pre-commit) shellHook;
            inherit LD_LIBRARY_PATH;
          };
        };

        checks = { inherit pre-commit; };
      });
}
