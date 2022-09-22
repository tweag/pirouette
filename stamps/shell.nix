{ pkgs ? import <nixpkgs> { } }:

let
  haskell-z3 = hp:
    hp.callPackage ({ mkDerivation, base, containers, hspec, lib, QuickCheck
      , transformers, fetchzip }:
      mkDerivation {
        pname = "z3";
        version = "master";
        src = fetchzip {
          url =
            "https://github.com/IagoAbal/haskell-z3/archive/df0773a6012a57df5a0a3d2f0cf83c518c9a925f.tar.gz";
          sha256 = "sha256:gLz7xYx8i4d70R+yYySOaLcYB0/qSInlwOnsNt3eZjY=";
        };
        sha256 = "1fjf9pfj3fhhcd0ak8rm6m5im2il8n5d21z8yv5c32xnsgj7z89a";
        isLibrary = true;
        isExecutable = true;
        libraryHaskellDepends = [ base containers transformers ];
        librarySystemDepends = with pkgs; [ gomp z3 ];
        testHaskellDepends = [ base hspec QuickCheck ];
        homepage = "https://github.com/IagoAbal/haskell-z3";
        description = "Bindings for the Z3 Theorem Prover";
        license = lib.licenses.bsd3;
      }) { };
in pkgs.mkShell {
  propagatedBuildInputs = [ pkgs.z3.lib ];
  packages = with pkgs; [
    hyperfine
    z3
    gcc
    (haskellPackages.ghcWithHoogle
      (hp: with hp; [ typed-process (haskell-z3 hp) haskell-language-server ]))
    cmake
  ];
}
