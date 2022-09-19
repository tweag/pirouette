{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  packages = with pkgs; [ hyperfine z3 (haskellPackages.ghcWithPackages (pkgs: [ pkgs.typed-process pkgs.z3 ]))];
}
