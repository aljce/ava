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
import Data.Semigroup ((<>))
import qualified Data.Text as T
import qualified Data.Text.Lazy.Builder as LT
import TextShow (TextShow(..))
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Type.Equality ((:~:)(..))
import Data.Singletons (SingI)
import Data.Singletons.Prelude (PNum(..),POrd(..))

import Data.Nat (Nat(..))
import Data.Nat.Properties (plusSuccRightSucc)
import Data.Nat.LTE (LTE,lteI)
import Data.Fin (Fin,fzero,fsucc)

import Debug.Trace (trace)

newtype Name
  = Name { _getName :: T.Text }
  deriving (Eq, Ord)
makeLenses ''Name

instance Show Name where
  showsPrec p (Name t) = showsPrec p t

instance TextShow Name where
  showb (Name t) = LT.fromText t

instance PP.Pretty Name where
  pretty = _getName .> PP.pretty

instance IsString Name where
  fromString = T.pack .> Name

data Var n v
  = Bound (Fin n) v
  | Free v
  deriving (Eq, Ord, Show)
makePrisms ''Var

data Binding
  = Ignore
  | Remember

type family BindingLevel (b :: Binding) (n :: Nat) :: Nat where
  BindingLevel Ignore n = n
  BindingLevel Remember n = Succ n

data Bind :: Binding -> Type -> Type where
  Irrelevant :: Bind Ignore v
  Bind :: v -> Bind Remember v

deriving instance Show v => Show (Bind b v)

instance PP.Pretty v => PP.Pretty (Bind b v) where
  pretty = \case
    Irrelevant -> "_"
    Bind v -> PP.pretty v

data Cat
  = Elim
  | Term

infixl 1 :::
infixl 2 :@:
data AST :: Nat -> Type -> Type -> Type -> Cat -> Type where
  Universe :: u -> AST n v u c Term
  Constant :: c -> AST n v u c Term
  Lift     :: LTE n m -> AST n v u c k -> AST m v u c k
  Embed    :: AST n v u c Elim -> AST n v u c Term
  Pi       :: Bind b v -> AST n v u c Term -> AST (BindingLevel b n) v u c Term -> AST n v u c Term
  Lam      :: Bind b v -> AST (BindingLevel b n) v u c Term -> AST n v u c Term
  Ref      :: Var n v -> AST n v u c Elim
  (:::)    :: AST n v u c Term -> AST n v u c Term -> AST n v u c Elim
  (:@:)    :: AST n v u c Elim -> AST n v u c Term -> AST n v u c Elim

deriving instance (Show v, Show u, Show c) => Show (AST n v u c k)

instance (PP.Pretty v, PP.Pretty u, PP.Pretty c) =>
  PP.Pretty (AST n v u c s) where
  pretty = \case
    Universe u -> PP.pretty u
    Constant c -> PP.pretty c
    Lift _ t -> PP.pretty t
    Embed e -> PP.sep [ PP.lbrace, PP.pretty e , PP.rbrace ]
    Pi x typeX b -> PP.vcat
      [ PP.sep [ PP.parens (PP.sep [PP.pretty x, PP.colon, PP.pretty typeX]), "-> " ]
      , PP.pretty b
      ]
    Lam x b -> PP.vcat
      [ PP.hcat [ PP.backslash, PP.pretty x, " -> " ]
      , PP.pretty b
      ]
    Ref r -> case r of
      Bound i x -> PP.hcat [ PP.pretty x, PP.pretty '@', PP.pretty (show i) ]
      Free x -> PP.pretty x
    x ::: typeX -> PP.sep [ parensWhenBinder x, PP.colon, parensWhenBinder typeX ]
    e1 :@: e2 -> parensWhenAnn e1 PP.<+> parensWhenBinder e2
    where
      parensWhenAnn :: AST m v u c Elim -> PP.Doc a
      parensWhenAnn e = case e of
        _ ::: _ -> PP.pretty e |> vparens
        _ -> PP.pretty e
      parensWhenBinder :: AST m v u c Term -> PP.Doc a
      parensWhenBinder e = case e of
        Pi _ _ _ -> ps
        Lam _ _ -> ps
        _ -> PP.pretty e
        where ps = PP.pretty e |> vparens
      vparens :: PP.Doc a -> PP.Doc a
      vparens e = PP.lparen <> (PP.vcat [ PP.nest 1 e, PP.rparen ])

lift :: (SingI n, SingI m, (n :<= m) ~ True) => AST n v u c k -> AST m v u c k
lift = Lift lteI

lam :: v -> AST (Succ n) v u c Term -> AST n v u c Term
lam x = Lam (Bind x)

infixr 5 :|
data Vec :: Type -> Nat -> Type where
  Nil :: Vec a Zero
  (:|) :: a -> Vec a n -> Vec a (Succ n)

lams :: forall n m v u c. Vec v n -> AST (n :+ m) v u c Term -> AST m v u c Term
lams Nil e = e
lams (v :| vs) e = case plusSuccRightSucc @n @m of
  Refl -> lam v (lams vs e)

pi :: v -> AST n v u c Term -> AST (Succ n) v u c Term -> AST n v u c Term
pi x = Pi (Bind x)

infixr 0 ~>
(~>) :: AST n v u c Term -> AST n v u c Term -> AST n v u c Term
(~>) = Pi Irrelevant

ref :: v -> Fin n -> AST n v u c Elim
ref x i = Ref (Bound i x)

refE :: v -> Fin n -> AST n v u c Term
refE x = ref x .> Embed

lemma :: LTE (Succ n) (Succ n) -> LTE n n
lemma = undefined

substitute
  :: forall b n v u c
  .  Bind b v
  -> AST n v u c Term
  -> AST (BindingLevel b n) v u c Term
  -> AST n v u c Term
substitute var x expr = case var of
  Irrelevant -> expr
  Bind _ -> go fzero expr
  where
    go :: Fin (Succ m) -> AST (Succ m) v u c k -> AST m v u c k
    go m e = case e of
      Universe u -> Universe u
      Constant c -> Constant c
      Lift lte l -> undefined
      Embed em -> Embed (go m em)
      Pi v typeV b -> case v of
        Irrelevant -> Pi v (go m typeV) (go m b)
        Bind _ -> Pi v (go m typeV) (go (fsucc m) b)
      Lam v b -> case v of
        Irrelevant -> Lam v (go m b)
        Bind _ -> Lam v (go (fsucc m) b)
      Ref v -> case v of
        Bound f _ -> case m == f of
          True -> undefined
          False -> undefined
        Free freeVar -> Ref (Free freeVar)
      b ::: typeB -> go m b ::: go m typeB
      f :@: a -> go m f :@: go m a

normalize :: AST n v u c k -> AST n v u c k
normalize e = case e of
  f :@: a -> case trace "f" (normalize f) of
    l ::: typeL -> case normalize l of
      Lam var b -> case normalize typeL of
        Pi typeVar _ typeB -> normalize (substitute var a b) ::: normalize (substitute typeVar a typeB)
        _ -> e
      _ -> e
    _ -> e
  _ -> e

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
  deriving Show

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
    typ = pi "a" star $ refE "a" fzero ~> refE "a" fzero

kComb :: AST Zero Name Star c Elim
kComb = expr ::: typ
  where
    expr :: AST Zero Name Star c Term
    expr =
      lams ("a" :| "b" :| "x" :| "y" :| Nil) $
      refE "x" (fsucc fzero)
    typ :: AST Zero Name Star c Term
    typ =
      pi "a" star $
      pi "b" star $
      refE "a" (fsucc fzero) ~>
      refE "b" fzero ~>
      refE "a" (fsucc fzero)

sComb :: AST Zero Name Star c Elim
sComb = expr ::: typ
  where
    expr :: AST Zero Name Star c Term
    expr =
      lams ("a" :| "b" :| "c" :| "x" :| "y" :| "z" :| Nil) $
      Embed $
      ref "x" two :@:
      refE "z" fzero :@:
      Embed (ref "y" (fsucc fzero) :@: refE "z" fzero)
    typ :: AST Zero Name Star c Term
    typ =
      pi "a" star $
      pi "b" star $
      pi "c" star $
      (refE "a" two ~> refE "b" (fsucc fzero) ~> refE "c" fzero) ~>
      (refE "a" two ~> refE "b" (fsucc fzero)) ~>
      refE "c" fzero
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
    typ = pi "a" star $ refE "a" fzero ~> refE "a" fzero

test :: AST n Name Star Base s -> IO ()
test = PP.pretty .> print

normTest :: String -> AST n Name Star Base s -> IO ()
normTest name e = do
  putStrLn (name ++ " before normalization:")
  test e
  putStrLn (name ++ " after normalization:")
  test (normalize e)

tests :: IO ()
tests = do
  normTest "Identity function" iComb
  normTest "Identity function on Ints" (iComb :@: Constant IntT)
  normTest "Zero" (iComb :@: Constant IntT :@: Constant (IntV 0))
