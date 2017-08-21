{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Language.Ava where

import Data.Kind (Type)
import Data.String (IsString(..))
import Flow ((.>))
import Control.Lens.TH (makeLenses,makePrisms)
import qualified Data.Text as T
import Data.Singletons ()
import Data.HFunctor.Foldable (HFunctor(..),Recursive(..),Base)

import Data.Nat (Nat(..))
import Data.Fin (Fin,fzero,fsucc)

newtype Name
  = Name { _getName :: T.Text }
  deriving (Eq, Ord, Show)
makeLenses ''Name

instance IsString Name where
  fromString = T.pack .> Name

data Var b f
  = Bound b
  | Free f
  deriving (Eq, Ord, Show)
makePrisms ''Var

data Named b f
  = Named
  { _namedName :: Name
  , _namedVar :: Var b f
  }
  deriving (Eq, Ord, Show)
makeLenses ''Named

data Kind
  = Elim
  | Term

data AST :: Nat -> Type -> Type -> Type -> Kind -> Type where
  Universe :: u -> AST n v u c Term
  Constant :: c -> AST n v u c Term
  Embed    :: AST n v u c Elim -> AST n v u c Term
  Pi       :: Named () v -> AST n v u c Term -> AST (Succ n) v u c Term -> AST n v u c Term
  Lam      :: Named () v -> AST (Succ n) v u c Term -> AST n v u c Term
  Ref      :: Named (Fin n) v -> AST n v u c Elim
  (:::)    :: AST n v u c Term -> AST n v u c Term -> AST n v u c Elim
  (:@:)    :: AST n v u c Elim -> AST n v u c Term -> AST n v u c Elim

data ASTF v u c f (k :: Kind) where
  UniverseF :: u                           -> ASTF v u c f Term
  ConstantF :: c                           -> ASTF v u c f Term
  EmbedF    :: f Elim                      -> ASTF v u c f Term
  PiF       :: Named v -> f Term -> f Term -> ASTF v u c f Term
  LamF      :: Named v -> f Term           -> ASTF v u c f Term
  RefF      :: Named v                     -> ASTF v u c f Elim
  (:.:.:)   :: f Term  -> f Term           -> ASTF v u c f Elim
  (:.@.:)   :: f Elim  -> f Term           -> ASTF v u c f Elim

deriving instance (Show v, Show u, Show c, Show (f Term), Show (f Elim)) => Show (ASTF v u c f k)

instance HFunctor (ASTF v u c) where
  hfmap eta = (\case UniverseF u  -> UniverseF u
                     ConstantF c  -> ConstantF c
                     EmbedF e     -> EmbedF (eta e)
                     PiF v vT bT  -> PiF v (eta vT) (eta bT)
                     LamF v b     -> LamF v (eta b)
                     RefF v       -> RefF v
                     tm :.:.: ty  -> eta tm :.:.: eta ty
                     el :.@.: tm  -> eta el :.@.: eta tm)

type instance Base (AST v u c) = ASTF v u c

instance Recursive (AST v u c) where
  project = (\case Universe u -> UniverseF u
                   Constant c -> ConstantF c
                   Embed e    -> EmbedF e
                   Pi v vT bT -> PiF v vT bT
                   Lam v b    -> LamF v b
                   Ref v      -> RefF v
                   tm ::: ty  -> tm :.:.: ty
                   el :@: tm  -> el :.@.: tm)

lam :: Name -> AST (Succ n) v u c Term -> AST n v u c Term
lam var = Lam (Named var (Bound ()))

ref :: Name -> Fin n -> AST n v u c Elim
ref var i = Ref (Named var (Bound i))

refE :: Name -> Fin n -> AST n v u c Term
refE var = ref var .> Embed

iComb :: AST (Succ n) T.Text () () Term
iComb = lam "x" $ refE "x" fzero

kComb :: AST (Succ (Succ n)) T.Text () () Term
kComb = lam "x" $ lam "y" $ refE "x" fzero

sComb :: AST (Succ (Succ (Succ n))) T.Text () () Term
sComb = lam "x" $ lam "y" $ lam "z" $ Embed $
  ref "x" (fsucc (fsucc fzero)) :@:
  refE "z" fzero :@:
  Embed (ref "y" (fsucc fzero) :@: refE "z" fzero)

