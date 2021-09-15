{ nixpkgs ? import <nixpkgs> {}
, enableHaskellProfiling ? false
, packages ? import ./. { inherit enableHaskellProfiling; }
}:
let
  inherit (packages) pkgs pirouette;
  inherit (pirouette) haskell;

in
  haskell.project.shellFor {
    withHoogle = false;

    nativeBuildInputs = with pirouette; [
      nixpkgs.hpack
      hlint
      cabal-install
      haskell-language-server
      stylish-haskell
      pkgs.niv
      cardano-repo-tool
    ];
  }
