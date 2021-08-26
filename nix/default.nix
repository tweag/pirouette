let
  # Pratically, the only needed dependency is the plutus repository.
  sources = import ./sources.nix { inherit pkgs; };

  # We're going to get everything from the main plutus repository. This ensures
  # we're using the same version of multiple dependencies such as nipxkgs,
  # haskell-nix, cabal-install, compiler-nix-name, etc.
  plutus = import sources.plutus {};
  pkgs = plutus.pkgs.extend (self: super: {
    R = self.lib.overrideDerivation super.R (s: {
      doCheck = false;
    });
  });

  haskell-nix = pkgs.haskell-nix;

  pirouette = import ./pkgs {
    inherit pkgs haskell-nix sources plutus;
  };

in
{
  inherit pkgs pirouette;
}
