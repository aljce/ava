{ nixpkgs ? (import <nixpkgs> {}) }:
let
  overrides = nixpkgs.haskell.packages.ghc821.override {
    overrides = self: super: with nixpkgs.haskell.lib; {
      th-desugar = self.callPackage ./nix/th-desugar.nix {};
      singletons = nixpkgs.haskell.lib.dontCheck (self.callPackage ./nix/singletons.nix {});
      text-show = dontCheck (super.text-show);
      ava = self.callCabal2nix "ava" ./. {};
    };
  };
  drv = overrides.ava;
in
if nixpkgs.lib.inNixShell then
  drv.env
else
  drv
