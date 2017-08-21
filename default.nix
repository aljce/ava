{ nixpkgs ? (import <nixpkgs> {}) }:
let
  hrecursion-schemes-json = builtins.fromJSON (builtins.readFile ./nix/hrecursion-schemes.json);
  hrecursion-schemes-src = nixpkgs.fetchFromGitHub {
    repo = "hrecursion-schemes";
    owner = "mckeankylej";
    inherit (hrecursion-schemes-json) rev sha256;
  };
  overrides = nixpkgs.haskell.packages.ghc821.override {
    overrides = self: super: {
      th-desugar = self.callPackage ./nix/th-desugar.nix {};
      singletons = nixpkgs.haskell.lib.dontCheck (self.callPackage ./nix/singletons.nix {});
      hrecursion-schemes = self.callPackage hrecursion-schemes-src {};
      ava = self.callCabal2nix "ava" ./. {};
    };
  };
  drv = overrides.ava;
in
if nixpkgs.lib.inNixShell then
  drv.env
else
  drv
