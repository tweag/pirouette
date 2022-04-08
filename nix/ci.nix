# This file is almos a copy of our shell.nix, with the difference
# that it only loads up the build dependencies, not the development deps.
{ pkgs ? import (import ./sources.nix {}).nixpkgs {} }:
let
  ourpkgs = import ./packages.nix {};
  runtime-deps = [
      ourpkgs.nixPkgsProxy.cvc4
    ];
in pkgs.mkShell {
    buildInputs = ourpkgs.build-deps ++ runtime-deps;
}
