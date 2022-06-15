{ packages ? import ./nix { inherit enableHaskellProfiling; }
, enableHaskellProfiling ? false
}:
let
  inherit (packages) pkgs pirouette;
  project = pirouette.haskell.project;
in
{
  inherit pkgs pirouette;

  inherit project;
}
