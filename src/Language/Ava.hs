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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Language.Ava where

import Prelude hiding (pi)
import Data.Kind (Type)
import Data.String (IsString(..))
import Flow ((.>),(|>))
import Control.Lens.TH (makeLenses,makePrisms)
import qualified Data.Text as T
import qualified Data.Text.Lazy.Builder as LT
import TextShow (TextShow(..))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Type.Equality ((:~:)(..))
import Data.Singletons (SingI)
import Data.Singletons.Prelude (PNum(..),POrd(..))

import Data.Nat (Nat(..))
import Data.Nat.Properties (plusSuccRightSucc)
import Data.Nat.LTE (LTE,lteI)
import Data.Fin (Fin,fzero,fsucc)

newtype Name
  = Name { _getName :: T.Text }
  deriving (Eq, Ord)
makeLenses ''Name

instance Show Name where
  showsPrec p (Name t) = showsPrec p t

instance TextShow Name where
  showb (Name t) = LT.fromText t

instance PP.Pretty Name where
  pretty = _getName .> T.unpack .> PP.text

instance IsString Name where
  fromString = T.pack .> Name

data Var b n
  = Bound b n
  | Free n
  deriving (Eq, Ord, Show)
makePrisms ''Var

data Cat
  = Elim
  | Term

data AST :: Nat -> Type -> Type -> Type -> Cat -> Type where
  Universe :: u -> AST n v u c Term
  Constant :: c -> AST n v u c Term
  Lift     :: LTE n m -> AST n v u c k -> AST m v u c k
  Embed    :: AST n v u c Elim -> AST n v u c Term
  Pi       :: Var () v -> AST n v u c Term -> AST (Succ n) v u c Term -> AST n v u c Term
  Lam      :: Var () v -> AST (Succ n) v u c Term -> AST n v u c Term
  Ref      :: Var (Fin n) v -> AST n v u c Elim
  (:::)    :: AST n v u c Term -> AST n v u c Term -> AST n v u c Elim
  (:@:)    :: AST n v u c Elim -> AST n v u c Term -> AST n v u c Elim

instance (PP.Pretty v, PP.Pretty u, PP.Pretty c) =>
  PP.Pretty (AST n v u c s) where
  pretty = \case
    Universe u -> PP.pretty u
    Constant c -> PP.pretty c
    Lift _ t -> PP.pretty t
    Embed e -> PP.sep [ PP.lbrace, PP.pretty e , PP.rbrace ]
    Pi x typeX b -> PP.vcat
      [ PP.sep [ PP.parens (PP.sep [var x, PP.colon, PP.pretty typeX]), "-> " ]
      , PP.pretty b
      ]
    Lam x b -> PP.vcat
      [ PP.hcat [ PP.backslash, var x, " -> " ]
      , PP.pretty b
      ]
    Ref r -> case r of
      Bound i x -> PP.hcat [ PP.pretty x, PP.char '@', PP.text (show i) ]
      Free x -> PP.pretty x
    x ::: typeX -> PP.sep [ parensWhenBinder x, PP.colon, parensWhenBinder typeX ]
    e1 :@: e2 -> parensWhenAnn e1 PP.<+> parensWhenBinder e2
    where
      var :: Var () v -> PP.Doc
      var = \case
        Bound () v -> PP.pretty v
        Free v -> PP.pretty v
      parensWhenAnn :: AST m v u c Elim -> PP.Doc
      parensWhenAnn e = case e of
        _ ::: _ -> PP.pretty e |> vparens
        _ -> PP.pretty e
      parensWhenBinder :: AST m v u c Term -> PP.Doc
      parensWhenBinder e = case e of
        Pi _ _ _ -> ps
        Lam _ _ -> ps
        _ -> PP.pretty e
        where ps = PP.pretty e |> vparens
      vparens :: PP.Doc -> PP.Doc
      vparens e = PP.sep [ PP.lparen, e, PP.rparen ]

lift :: (SingI n, SingI m, (n :<= m) ~ True) => AST n v u c k -> AST m v u c k
lift = Lift lteI

lam :: v -> AST (Succ n) v u c Term -> AST n v u c Term
lam x = Lam (Bound () x)

infixr 5 :|
data Vec :: Type -> Nat -> Type where
  Nil :: Vec a Zero
  (:|) :: a -> Vec a n -> Vec a (Succ n)

lams :: forall n m v u c. Vec v n -> AST (n :+ m) v u c Term -> AST m v u c Term
lams Nil e = e
lams (v :| vs) e = case plusSuccRightSucc @n @m of
  Refl -> lam v (lams vs e)

pi :: v -> AST n v u c Term -> AST (Succ n) v u c Term -> AST n v u c Term
pi x = Pi (Bound () x)

ref :: v -> Fin n -> AST n v u c Elim
ref x i = Ref (Bound i x)

refE :: v -> Fin n -> AST n v u c Term
refE x = ref x .> Embed

data Star
  = Star
  deriving Show

instance TextShow Star where
  showb _ = "*"

instance PP.Pretty Star where
  pretty Star = "*"

star :: AST n v Star c Term
star = Universe Star

data Base
  = IntT
  | IntV Int

instance TextShow Base where
  showb = \case
    IntT -> "Int"
    IntV i -> showb i

instance PP.Pretty Base where
  pretty = \case
    IntT -> "Int"
    IntV i -> PP.pretty i

iComb :: AST Zero Name Star c Elim
iComb = expr ::: typ
  where
    expr :: AST Zero Name Star c Term
    expr = lam "a" $ lam "x" $ refE "x" fzero
    typ :: AST Zero Name Star c Term
    typ = pi "a" star $ pi "_" (refE "a" fzero) (refE "a" (fsucc fzero))

kComb :: AST Zero Name Star c Elim
kComb = expr ::: typ
  where
    expr :: AST Zero Name Star c Term
    expr = lam "a" $ lam "b" $ lam "x" $ lam "y" $ refE "x" (fsucc fzero)
    typ :: AST Zero Name Star c Term
    typ =
      pi "a" star $
      pi "b" star $
      pi "_" (refE "a" (fsucc fzero)) $
      pi "_" (refE "b" (fsucc fzero)) $
      refE "a" (fsucc (fsucc (fsucc fzero)))

sComb :: AST Zero Name Star c Elim
sComb = expr ::: typ
  where
    expr :: AST Zero Name Star c Term
    expr = lam "a" $ lam "b" $ lam "c" $ lam "x" $ lam "y" $ lam "z" $
      Embed $
      ref "x" two :@:
      refE "z" fzero :@:
      Embed (ref "y" (fsucc fzero) :@: refE "z" fzero)
    typ :: AST Zero Name Star c Term
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

skk :: AST Zero Name Star c Elim
skk = expr ::: typ
  where
    expr :: AST Zero Name Star c Term
    expr =
      lam "a" $ Embed $
      lift sComb :@: a :@: a :@: a :@:
      Embed (lift kComb :@: a :@: a) :@:
      Embed (lift iComb :@: a)
      where
        a :: AST (Succ Zero) Name Star c Term
        a = refE "a" fzero
    typ :: AST Zero Name Star c Term
    typ = pi "a" star $ pi "_" (refE "a" fzero) $ refE "a" (fsucc fzero)

test :: AST n Name Star Base s -> IO ()
test = PP.pretty .> print
