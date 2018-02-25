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

import Prelude hiding (pi,id,(.),succ)
import Data.Kind (Type)
import Data.String (IsString(..))
import Flow ((.>),(|>))
import Control.Lens.TH (makeLenses)
import Data.Semigroup ((<>))
import qualified Data.Text as T
import qualified Data.Text.Lazy.Builder as LT
import TextShow (TextShow(..))
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Type.Equality ((:~:)(..))
import Data.Singletons (Sing(..),SingI(..),withSingI)
import Data.Singletons.TH (genSingletons)
import Data.Singletons.Prelude (PNum(..),POrd(..))
import Data.Singletons.Decide (Decision(..),(%~))

import Data.Nat (Nat(..),succ)
import Data.Nat.Properties (plusSuccRightSucc)
import Data.Nat.LTE (LTE,lteI,lsucc,lteN)
import Data.Fin (Fin,fzero,fsucc)
import Data.Fin.Internal (Fin(..)) -- TODO: Do not abuse unsafe internals

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

data Binding
  = Ignore
  | Remember

type family BindingLevel (b :: Binding) (n :: Nat) :: Nat where
  BindingLevel Ignore n = n
  BindingLevel Remember n = Succ n

bindingLevel :: Bind b v -> Sing n -> Sing (BindingLevel b n)
bindingLevel Irrelevant n = n
bindingLevel (Bind _) n = succ n

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

$(genSingletons [''Cat])

infixl 1 :::
infixl 2 :@:
data AST :: Type -> Type -> Type -> Cat -> Nat -> Type where
  Universe :: u -> AST v u c Term n
  Constant :: c -> AST v u c Term n
  Lift     :: LTE n m -> AST v u c k n -> AST v u c k m
  Embed    :: AST v u c Elim n -> AST v u c Term n
  Pi       :: Bind b v -> AST v u c Term n -> AST v u c Term (BindingLevel b n) -> AST v u c Term n
  Lam      :: Bind b v -> AST v u c Term (BindingLevel b n) -> AST v u c Term n
  Ref      :: v -> Fin n -> AST v u c Elim n
  (:::)    :: AST v u c Term n -> AST v u c Term n -> AST v u c Elim n
  (:@:)    :: AST v u c Elim n -> AST v u c Term n -> AST v u c Elim n

deriving instance (Show v, Show u, Show c) => Show (AST v u c k n)

instance (Eq u, Eq c, SingI n) => Eq (AST v u c k n) where
  (==) = alphaEq

instance (PP.Pretty v, PP.Pretty u, PP.Pretty c) =>
  PP.Pretty (AST v u c k n) where
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
    Ref x i -> PP.hcat [ PP.pretty x, PP.pretty '@', PP.pretty (show i) ]
    x ::: typeX -> PP.sep [ parensWhenBinder x, PP.colon, parensWhenBinder typeX ]
    e1 :@: e2 -> parensWhenAnn e1 PP.<+> parensWhenBinder e2
    where
      parensWhenAnn :: AST v u c Elim m -> PP.Doc a
      parensWhenAnn e = case e of
        _ ::: _ -> PP.pretty e |> vparens
        _ -> PP.pretty e
      parensWhenBinder :: AST v u c Term m -> PP.Doc a
      parensWhenBinder e = case e of
        Pi _ _ _ -> ps
        Lam _ _ -> ps
        _ -> PP.pretty e
        where ps = PP.pretty e |> vparens
      vparens :: PP.Doc a -> PP.Doc a
      vparens e = PP.lparen <> (PP.vcat [ PP.nest 1 e, PP.rparen ])

data ASTLen :: Type -> Type -> Type -> Cat -> Type where
  ASTLen :: SingI n => AST v u c k n -> ASTLen v u c k

deriving instance (Show v, Show u, Show c) => Show (ASTLen v u c k)

data ASTCat :: Type -> Type -> Type -> Nat -> Type where
  ASTCat :: AST v u c k n -> ASTCat v u c n

data ASTAny :: Type -> Type -> Type -> Type where
  ASTAny :: (SingI k, SingI n) => AST v u c k n -> ASTAny v u c

lift :: (SingI n, SingI m, (n :<= m) ~ True) => AST v u c k n -> AST v u c k m
lift = Lift lteI

lam :: v -> AST v u c Term (Succ n) -> AST v u c Term n
lam x = Lam (Bind x)

infixr 5 :|
data Vec :: Type -> Nat -> Type where
  Nil :: Vec a Zero
  (:|) :: a -> Vec a n -> Vec a (Succ n)

lams :: forall n m v u c. Vec v n -> AST v u c Term (n :+ m) -> AST v u c Term m
lams Nil e = e
lams (v :| vs) e = case plusSuccRightSucc @n @m of
  Refl -> lam v (lams vs e)

pi :: v -> AST v u c Term n -> AST v u c Term (Succ n) -> AST v u c Term n
pi x = Pi (Bind x)

infixr 0 ~>
(~>) :: AST v u c Term n -> AST v u c Term n -> AST v u c Term n
(~>) = Pi Irrelevant

refE :: v -> Fin n -> AST v u c Term n
refE x = Ref x .> Embed

alphaEq
  :: forall v u c k n m
  .  (Eq u, Eq c, SingI n, SingI m)
  => AST v u c k n
  -> AST v u c k m -> Bool
alphaEq e1 e2 = go sing sing e1 e2
  where
    go :: Sing o -> Sing p -> AST v u c kind o -> AST v u c kind p -> Bool
    go _ _ (Universe u1) (Universe u2) = u1 == u2
    go _ _ (Constant c1) (Constant c2) = c1 == c2
    go o p (Lift lte1 l1) (Lift lte2 l2) =
      go (withSingI o (lteN lte1)) (withSingI p (lteN lte2)) l1 l2
    go o p (Embed x1) (Embed x2) = go o p x1 x2
    go o p (Pi x1 typeX1 b1) (Pi x2 typeX2 b2) =
      go o p typeX1 typeX2 &&
      go (bindingLevel x1 o) (bindingLevel x2 p) b1 b2
    go o p (Lam x1 b1) (Lam x2 b2) =
      go (bindingLevel x1 o) (bindingLevel x2 p) b1 b2
    go o p (Ref _ i1) (Ref _ i2) = case o %~ p of
      Proved Refl -> i1 == i2
      Disproved _ -> False
    go o p (x1 ::: typeX1) (x2 ::: typeX2) =
      go o p x1 x2 && go o p typeX1 typeX2
    go o p (f1 :@: a1) (f2 :@: a2) =
      go o p f1 f2 && go o p a1 a2
    go _ _ _ _ = False

lemma :: Fin (Succ m) -> Fin (Succ m) -> Maybe (Fin m)
lemma (Fin i) (Fin j) = case i <= j of
  True -> Nothing
  False -> Just (Fin j)

liftVar :: AST v u c k n -> AST v u c k (Succ n)
liftVar = \case
  Universe u -> Universe u
  Constant c -> Constant c
  Lift lte l -> Lift (lsucc lte) (liftVar l)
  Embed em -> Embed (liftVar em)
  Pi v typeV b -> case v of
    Irrelevant -> Pi v (liftVar typeV) (liftVar b)
    Bind _ -> Pi v (liftVar typeV) (liftVar b)
  Lam v b -> case v of
    Irrelevant -> Lam v (liftVar b)
    Bind _ -> Lam v (liftVar b)
  Ref x i -> Ref x (fsucc i)
  x ::: typeX -> liftVar x ::: liftVar typeX
  f :@: a -> liftVar f :@: liftVar a

-- | substitute v x typeX e ~ e[v := x ::: typeX]
substitute
  :: forall b n v u c
  .  Bind b v
  -> AST v u c Term n
  -> AST v u c Term n
  -> AST v u c Term (BindingLevel b n)
  -> AST v u c Term n
substitute var sub typeSub expr = case var of
  Irrelevant -> expr
  Bind _ -> go fzero sub typeSub expr
  where
    go :: Fin (Succ m) -> AST v u c Term m -> AST v u c Term m -> AST v u c k (Succ m) -> AST v u c k m
    go m x typeX e = case e of
      Universe u -> Universe u
      Constant c -> Constant c
      Lift lte l -> undefined lte l -- Lift _ _ -- (go m l)
      Embed em -> Embed (go m x typeX em)
      Pi v typeV b -> case v of
        Irrelevant -> Pi v (go m x typeX typeV) (go m x typeX b)
        Bind _ -> Pi v (go m x typeX typeV) (go (fsucc m) (liftVar x) (liftVar typeX) b)
      Lam v b -> case v of
        Irrelevant -> Lam v (go m x typeX b)
        Bind _ -> Lam v (go (fsucc m) (liftVar x) (liftVar typeX) b)
      Ref name f -> case lemma m f of
        Nothing -> x ::: typeX
        Just decF -> Ref name decF
      b ::: typeB -> go m x typeX b ::: go m x typeX typeB
      f :@: a -> go m x typeX f :@: go m x typeX a

-- normalize :: AST n v u c k -> AST n v u c k
-- normalize e = case e of
--   f :@: a -> case normalize f of
--     l ::: typeL -> case normalize l of
--       Lam var b -> case normalize typeL of
--         Pi typeVar _ typeB ->
--           normalize (substitute var a b) :::
--           normalize (substitute typeVar a typeB)
--         _ -> e
--       _ -> e
--     _ -> e
--   _ -> e

data Star
  = Star
  deriving (Eq, Show)

instance TextShow Star where
  showb _ = "*"

instance PP.Pretty Star where
  pretty Star = "*"

star :: AST v Star c Term n
star = Universe Star

data Base
  = IntT
  | IntV Int
  deriving (Eq, Show)

instance TextShow Base where
  showb = \case
    IntT -> "Int"
    IntV i -> showb i

instance PP.Pretty Base where
  pretty = \case
    IntT -> "Int"
    IntV i -> PP.pretty i

iComb :: AST Name Star c Elim Zero
iComb = expr ::: typ
  where
    expr :: AST Name Star c Term Zero
    expr = lam "a" $ lam "x" $ refE "x" fzero
    typ :: AST Name Star c Term Zero
    typ = pi "a" star $ refE "a" fzero ~> refE "a" fzero

kComb :: AST Name Star c Elim Zero
kComb = expr ::: typ
  where
    expr :: AST Name Star c Term Zero
    expr =
      lams ("a" :| "b" :| "x" :| "y" :| Nil) $
      refE "x" (fsucc fzero)
    typ :: AST Name Star c Term Zero
    typ =
      pi "a" star $
      pi "b" star $
      refE "a" (fsucc fzero) ~>
      refE "b" fzero ~>
      refE "a" (fsucc fzero)

sComb :: AST Name Star c Elim Zero
sComb = expr ::: typ
  where
    expr :: AST Name Star c Term Zero
    expr =
      lams ("a" :| "b" :| "c" :| "x" :| "y" :| "z" :| Nil) $
      Embed $
      Ref "x" two :@:
      refE "z" fzero :@:
      Embed (Ref "y" (fsucc fzero) :@: refE "z" fzero)
    typ :: AST Name Star c Term Zero
    typ =
      pi "a" star $
      pi "b" star $
      pi "c" star $
      (refE "a" two ~> refE "b" (fsucc fzero) ~> refE "c" fzero) ~>
      (refE "a" two ~> refE "b" (fsucc fzero)) ~>
      refE "c" fzero
    two :: Fin (Succ (Succ (Succ n)))
    two = fsucc (fsucc fzero)

skk :: AST Name Star c Elim Zero
skk = expr ::: typ
  where
    expr :: AST Name Star c Term Zero
    expr =
      lam "a" $ Embed $
      lift sComb :@: a :@: a :@: a :@:
      Embed (lift kComb :@: a :@: a) :@:
      Embed (lift iComb :@: a)
      where
        a :: AST Name Star c Term (Succ Zero) 
        a = refE "a" fzero
    typ :: AST Name Star c Term Zero
    typ = pi "a" star $ refE "a" fzero ~> refE "a" fzero

test :: AST Name Star Base s n -> IO ()
test = PP.pretty .> print

-- normTest :: String -> AST n Name Star Base s -> IO ()
-- normTest name e = do
--   putStrLn (name ++ " before normalization:")
--   test e
--   putStrLn (name ++ " after normalization:")
--   test (normalize e)

-- tests :: IO ()
-- tests = do
--   normTest "Identity function" iComb
--   normTest "Identity function on Ints" (iComb :@: Constant IntT)
--   normTest "Zero" (iComb :@: Constant IntT :@: Constant (IntV 0))
