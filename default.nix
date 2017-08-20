{ nixpkgs ? (import <nixpkgs> {}) }:
let
  overrides = nixpkgs.haskell.packages.ghc821.override {
    overrides = self: super: {
      singletons = self.callPackage ./nix/singletons.nix {};
      ava = self.callCabal2nix "ava" ./. {};
    };
  };
  drv = overrides.ava;
in
if nixpkgs.lib.inNixShell then
  drv.env
else
  drv
