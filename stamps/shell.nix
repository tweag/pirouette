{ pkgs ? import (builtins.fetchTarball {
  url =
    # https://lazamar.co.uk/nix-versions/?package=z3&version=4.8.12&fullName=z3-4.8.12&keyName=python38Packages.z3&revision=05ae8b52071ff158a4d3c7036e13a2e932b2549b&channel=nixos-21.11#instructions
    "https://github.com/NixOS/nixpkgs/archive/05ae8b52071ff158a4d3c7036e13a2e932b2549b.tar.gz";
}) { } }:

pkgs.mkShell {
  packages = with pkgs; [
    hyperfine
    z3
    (haskellPackages.ghcWithPackages (hp: with hp; [ typed-process (z3.override { z3 = pkgs.z3; }) ]))
  ];
}
