{ 
  sources ? import ./sources.nix {},
  rawpkgs ? import sources.nixpkgs {},
}:
{ 
  # We will split our dependencies into those deps that are needed for
  # building and testing; and those that are needed for development
  # the purpose is to keep CI happier and make it as fast as possible.
  build-deps = with rawpkgs; [
        # libs required to build plutus
        libsodium
        lzma
        zlib

        # required to build in a pure nix shell
        git
        cacert # git SSL
        pkg-config # required by libsystemd-journal

        # haskell development tools pulled from regular nixpkgs
        hpack
        ormolu
        haskellPackages.cabal-install
        haskellPackages.happy
        haskell.compiler.ghc902
        cvc4 # required to run pirouette once its built
     ] ++ lib.optional (stdenv.isLinux) systemd.dev;

  dev-deps = with rawpkgs; [
        haskellPackages.haskell-language-server
      ];

  # Export the raw nixpkgs to be accessible to whoever imports this.
  nixPkgsProxy = rawpkgs;
}
