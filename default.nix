########################################################################
# default.nix -- The top-level nix build file for plutus-starter.
#
# This file defines various attributes that are used for building and
# developing plutus-starter.
#
########################################################################

let
  # Here a some of the various attributes for the variable 'packages':
  #
  # { pkgs
  #   plutus-starter: {
  #     haskell: {
  #       project # The Haskell project created by haskell-nix.project
  #       packages # All the packages defined by our project, including dependencies
  #       projectPackages # Just the packages in the project
  #     }
  #     hlint
  #     cabal-install
  #     stylish-haskell
  #     haskell-language-server
  #   }
  # }
  packages = import ./nix;

  inherit (packages) pkgs pirouette;
  project = pirouette.haskell.project;
in
{
  inherit pkgs pirouette;

  inherit project;
}
