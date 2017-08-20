{ mkDerivation, base, containers, hspec, HUnit, mtl, stdenv, syb
, template-haskell, th-expand-syns, th-lift, th-orphans
}:
mkDerivation {
  pname = "th-desugar";
  version = "1.7";
  sha256 = "1iqlqadax1ahgv9h1vdyddf55v2h4ghqrxfyqirrvk97iyk1rcsj";
  libraryHaskellDepends = [
    base containers mtl syb template-haskell th-expand-syns th-lift
    th-orphans
  ];
  testHaskellDepends = [
    base containers hspec HUnit mtl syb template-haskell th-expand-syns
    th-lift th-orphans
  ];
  homepage = "https://github.com/goldfirere/th-desugar";
  description = "Functions to desugar Template Haskell";
  license = stdenv.lib.licenses.bsd3;
}
