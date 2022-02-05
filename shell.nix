{ pkgs ? import (import ./nix/sources.nix {}).nixpkgs {} }:
let
  ourpkgs = import ./nix/packages.nix {};
  runtime-deps = [ ourpkgs.nixPkgsProxy.cvc4 ];
in pkgs.mkShell {
    buildInputs = ourpkgs.build-deps ++ ourpkgs.dev-deps ++ runtime-deps;
}
