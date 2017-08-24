{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Language.Ava where

import Prelude hiding (pi)
import Data.Kind (Type)
import Data.String (IsString(..))
import Data.Monoid ((<>))
import Flow ((.>))
import Control.Lens.TH (makeLenses,makePrisms)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as LT
import TextShow (TextShow(..))
import Data.Singletons.Prelude (PNum(..))

import Data.Nat (Nat(..))
import Data.Fin (Fin,fzero,fsucc)

newtype Name
  = Name { _getName :: T.Text }
  deriving (Eq, Ord)
makeLenses ''Name

instance Show Name where
  showsPrec p (Name t) = showsPrec p t

instance TextShow Name where
  showb (Name t) = LT.fromText t

instance IsString Name where
  fromString = T.pack .> Name

data Var b n
  = Bound b n
  | Free n
  deriving (Eq, Ord, Show)
makePrisms ''Var

data Kind
  = Elim
  | Term

data AST :: Nat -> Type -> Type -> Type -> Kind -> Type where
  Universe :: u -> AST n v u c Term
  Constant :: c -> AST n v u c Term
  Embed    :: AST n v u c Elim -> AST n v u c Term
  Pi       :: Var () v -> AST n v u c Term -> AST (Succ n) v u c Term -> AST n v u c Term
  Lam      :: Var () v -> AST (Succ n) v u c Term -> AST n v u c Term
  Ref      :: Var (Fin n) v -> AST n v u c Elim
  (:::)    :: AST n v u c Term -> AST n v u c Term -> AST n v u c Elim
  (:@:)    :: AST n v u c Elim -> AST n v u c Term -> AST n v u c Elim

data Star
  = Star
  deriving Show

instance TextShow Star where
  showb _ = "*"

star :: AST n v Star c Term
star = Universe Star

lam :: v -> AST (Succ n) v u c Term -> AST n v u c Term
lam x = Lam (Bound () x)

data Vec :: Type -> Nat -> Type where
  Nil :: Vec a Zero
  Cons :: a -> Vec a n -> Vec a (Succ n)

lams :: Vec v n -> AST (n :+ m) v u c Term -> AST m v u c Term
lams Nil e = e
lams (Cons v vs) e = lams vs (lam v e)

pi :: v -> AST n v u c Term -> AST (Succ n) v u c Term -> AST n v u c Term
pi x = Pi (Bound () x)

ref :: v -> Fin n -> AST n v u c Elim
ref x i = Ref (Bound i x)

refE :: v -> Fin n -> AST n v u c Term
refE x = ref x .> Embed

iComb :: AST (Succ (Succ Zero)) Name Star () Elim
iComb = expr ::: typ
  where
    expr :: AST (Succ (Succ Zero)) Name Star () Term
    expr = lam "a" $ lam "x" $ refE "x" fzero
    typ :: AST (Succ (Succ Zero)) Name Star () Term
    typ = pi "a" star $ pi "_" a a
      where a = refE "a" (fsucc fzero)

kComb :: AST (FromInteger 4) Name Star () Elim
kComb = expr ::: typ
  where
    expr :: AST (FromInteger 4) Name Star () Term
    expr = lam "a" $ lam "b" $ lam "x" $ lam "y" $ refE "x" (fsucc fzero)
    typ :: AST (FromInteger 4) Name Star () Term
    typ =
      pi "a" star $
      pi "b" star $
      pi "_" (refE "a" (fsucc (fsucc fzero))) $
      pi "_" (refE "b" (fsucc (fzero))) $
      refE "a" (fsucc (fsucc (fsucc (fsucc fzero))))

sComb :: AST (FromInteger 3) Name Star () Elim
sComb = expr ::: typ
  where
    expr :: AST (FromInteger 3) Name Star () Term
    expr = lam "a" $ lam "b" $ lam "c" $ lam "x" $ lam "y" $ lam "z" $
      Embed $
      ref "x" two :@:
      refE "z" fzero :@:
      Embed (ref "y" (fsucc fzero) :@: refE "z" fzero)
    typ :: AST (FromInteger 3) Name Star () Term
    typ =
      pi "a" star $
      pi "b" star $
      pi "c" star $
      pi "_" (pi "_" (refE "a" two) $
              pi "_" (refE "b" two) $
              refE "c" two) $
      pi "_" (pi "_" (refE "a" (fsucc two)) $
              refE "b" (fsucc two)) $
      refE "c" two
    two :: Fin (Succ (Succ (Succ n)))
    two = fsucc (fsucc fzero)

skk :: AST (FromInteger 2) Name Star () Elim
skk = expr ::: typ
  where
    expr = lam "a" $ Embed $ sComb :@: refE "a" fzero :@: refE "a" fzero :@: refE "a" fzero
    typ = pi "a" star $ pi "_" (refE "a" fzero) $ refE "a" fzero

printAscii :: forall n v u c k. (TextShow v, TextShow u, TextShow c) => AST n v u c k -> T.Text
printAscii = go .> LT.toLazyText .> LT.toStrict
  where
    go :: AST m v u c kind -> LT.Builder
    go = \case
      Universe u -> showb u
      Constant c -> showb c
      Embed e -> mconcat [ "{", go e, "}" ]
      Pi x typeX b -> mconcat
        [ parens (var x <> " : " <> parensWhenBinder typeX)
        , " -> "
        , go b ]
      Lam x b -> mconcat [ "\\", var x, " -> ", go b ]
      Ref v -> case v of
        Bound f n  -> showb n <> "@" <> LT.fromString (show f)
        Free n -> showb n
      x ::: typeX -> mconcat [ go x, " : ", parensWhenBinder typeX ]
      e1 :@: e2 -> mconcat [ parensWhenAnn e1, " ", parensWhenBinder e2 ]
    parens :: LT.Builder -> LT.Builder
    parens e = "(" <> e <> ")"
    parensWhenBinder :: AST m v u c kind -> LT.Builder
    parensWhenBinder e = case e of
      Lam _ _ -> parens (go e)
      Pi _ _ _ -> parens (go e)
      _ -> go e
    parensWhenAnn :: AST m v u c Elim -> LT.Builder
    parensWhenAnn e = case e of
      _ ::: _ -> parens (go e)
      _ -> go e
    var :: Var () v -> LT.Builder
    var = \case
      Bound () v -> showb v
      Free v -> showb v

test :: AST n Name Star () k -> IO ()
test = printAscii .> T.putStrLn
