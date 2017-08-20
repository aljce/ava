{ mkDerivation, base, Cabal, containers, directory, filepath, mtl
, process, stdenv, syb, tasty, tasty-golden, template-haskell, text
, th-desugar
}:
mkDerivation {
  pname = "singletons";
  version = "2.3.1";
  sha256 = "1i5fmz2fqk3ijcv38ig1wmbjlva5r4imlwgindir63nmhpgy93fa";
  libraryHaskellDepends = [
    base containers mtl syb template-haskell text th-desugar
  ];
  testHaskellDepends = [
    base Cabal directory filepath process tasty tasty-golden
  ];
  homepage = "http://www.github.com/goldfirere/singletons";
  description = "A framework for generating singleton types";
  license = stdenv.lib.licenses.bsd3;
}
