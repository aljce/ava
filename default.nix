{ nixpkgs ? (import <nixpkgs> {}) }:
let
  overrides = nixpkgs.haskellPackages.override {
    overrides = self: super: with self; with nixpkgs.haskell.lib; {
      ava = callCabal2nix "ava" ./. {};
    };
  };
  drv = overrides.ava;
in
if nixpkgs.lib.inNixShell then
  drv.env
else
  drv
