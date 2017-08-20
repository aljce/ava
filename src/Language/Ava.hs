{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Language.Ava where

import Data.Kind (Type)
import Flow ()
import Control.Lens.TH (makeLenses,makePrisms)
import qualified Data.Text as T
import Data.Singletons ()

import Data.Nat (Nat(..))
import Data.Fin (Fin)

newtype Name
  = Name { _getName :: T.Text }
  deriving (Eq, Ord, Show)
makeLenses ''Name

data Var (n :: Nat) a
  = Bound (Fin n)
  | Free a
  deriving (Eq, Ord, Show)
makePrisms ''Var

data Named (n :: Nat) a
  = Named
  { _namedName :: Name
  , _namedVar :: Var n a
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
  Pi       :: Named n v -> AST n v u c Term -> AST (Succ n) v u c Term -> AST n v u c Term
  -- Lam      :: Named v -> AST v u c Term -> AST v u c Term
  -- Ref      :: Named v -> AST v u c Elim
  -- (:::)    :: AST v u c Term -> AST v u c Term -> AST v u c Elim
  -- (:@:)    :: AST v u c Elim -> AST v u c Term -> AST v u c Elim
