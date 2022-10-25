{
  description = "Pirouette";
  inputs.haskellNix.url = "github:input-output-hk/haskell.nix";
  inputs.nixpkgs.follows = "haskellNix/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  outputs = { self, nixpkgs, flake-utils, haskellNix }:
    let
      supportedSystems = with flake-utils.lib.system; [
        x86_64-linux
        # FIXME systems that are different from the host architecture
        # cause `nix develop` to fail.
        # x86_64-darwin
        # aarch64-linux
        # aarch64-darwin
      ];
    in
      flake-utils.lib.eachSystem supportedSystems (system:
      let
        overlays = [ haskellNix.overlay
          (final: prev: {
            pirouetteProject =
              final.haskell-nix.project {
                name = "Pirouette";
                compiler-nix-name = "ghc8107"; # Version of GHC to use
                src = ./.;

                shell = {
                  # Tools to include in the development shell
                  tools = {
                    cabal = {};
                    haskell-language-server = {};
                    hpack = {};
                    ormolu = {};
                  };
                  # graphmod is a nice tool to visualize the project module
                  # structure; run: $ graphmod -p --no-cluster | xdot - to see
                  # it in action!
                  buildInputs = with pkgs; [ xdot haskellPackages.graphmod z3.lib ];

                  # Add `libz3.so` to the library path
                  shellHook =
                    ''
                      export LD_LIBRARY_PATH=${pkgs.z3.lib}/lib:$\{LD_LIBRARY_PATH:+:}$\{LD_LIBRARY_PATH}
                    '';
                };
              };
          })
        ];
        pkgs = import nixpkgs { inherit system overlays; inherit (haskellNix) config; };
        flake = pkgs.pirouetteProject.flake {};
      in flake // {
        legacyPackages = pkgs;
      });

  # --- Flake Local Nix Configuration ----------------------------
  nixConfig = {
    # This sets the flake to use the IOG nix cache.
    # Nix should ask for permission before using it,
    # but remove it here if you do not want it to.
    extra-substituters = ["https://cache.iog.io"];
    extra-trusted-public-keys = ["hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="];
    allow-import-from-derivation = "true";
  };
}
