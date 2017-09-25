{-# LANGUAGE LambdaCase#-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Language.Ava.TypeCheck where

import Prelude hiding (succ)
-- import qualified Data.HashMap.Strict as HM
import qualified Control.Monad.Trans as MT
import Control.Monad.Reader (ReaderT,MonadReader(..))
import Control.Monad.Except (Except,MonadError(..))
-- import Data.Type.Equality ((:~:)(..))
import Data.Singletons (SingI(..),withSingI)
-- import Data.Singletons.Prelude (Sing(..),SOrd(..))
-- import Data.Singletons.Decide (Decision(..),(%~))

import Data.Nat (succ)
import Data.Fin (Fin)
import Data.Nat.LTE (lteN)
import Language.Ava

data TypeError v u c where
  UnboundVariable :: v -> Fin n -> TypeError v u c
  NotAFunction :: AST v u c Elim n -> AST v u c k m -> TypeError v u c
  TypeMismatch :: AST v u c k n -> AST v u c k n -> TypeError v u c
  NotAUniverse :: AST v u c k n -> TypeError v u c

data Context v u c where

lookupVar :: forall v u c n. SingI n => Fin n -> Context v u c -> Maybe (AST v u c Term n)
lookupVar = undefined

insert :: AST v u c Term n -> Context v u c -> Context v u c
insert = undefined

data Basis v u c
  = Basis
  { incrementUniverse :: forall n. u -> TCM v u c (AST v u c Term n)
  , lookupUniverse :: forall n. AST v u c Term n -> TCM v u c u
  , universeRelation :: u -> u -> TCM v u c ()
  , constantChecker :: forall n. c -> TCM v u c (AST v u c Term n)
  }

newtype TCM v u c a
  = TCM { unTCM :: ReaderT (Context v u c) (ReaderT (Basis v u c) (Except (TypeError v u c))) a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadError (TypeError v u c)
    , MonadReader (Context v u c)
    )

getBasis :: TCM v u c (Basis v u c)
getBasis = TCM (MT.lift ask)

check
  :: forall v u c n
  .  (Eq u, Eq c, SingI n)
  => AST v u c Term n
  -> TCM v u c (AST v u c Term n)
check = \case
  Universe u -> do
    basis <- getBasis
    incrementUniverse basis u
  Constant c -> do
    basis <- getBasis
    constantChecker basis c
  Lift lte l -> withSingI (lteN lte) (Lift lte <$> check l)
  Embed e -> synthesize e
  Pi x typeX b -> do
    basis <- getBasis
    typeXU <- check typeX
    case typeXU of
      Universe xU -> case x of
        Irrelevant -> check b >>= \case
          Universe bU -> do
            universeRelation basis xU bU
            return typeXU
          typeB -> throwError (NotAUniverse typeB)
        Bind _ -> withSingI (succ (sing @_ @n)) $
          local (insert typeX) (check b) >>= \case
            Universe bU -> do
              universeRelation basis xU bU
              return typeXU
            typeB -> throwError (NotAUniverse typeB)
      _ -> throwError (NotAUniverse typeXU)
  Lam _x _b -> undefined

synthesize
  :: forall v u c n
  .  (Eq u, Eq c, SingI n)
  => AST v u c Elim n
  -> TCM v u c (AST v u c Term n)
synthesize = \case
  Lift lte l -> withSingI (lteN lte) (Lift lte <$> synthesize l)
  Ref x i -> do
    ctx <- ask
    case lookupVar i ctx of
      Nothing -> throwError (UnboundVariable x i)
      Just ast -> pure ast
  _ ::: typeX -> pure typeX
  f :@: a -> do
    typeA <- check a
    synthesize f >>= \case
      Pi x typeX b -> case typeA == typeX of
        True -> pure (substitute x a typeA b)
        False -> throwError (TypeMismatch typeA typeX)
      typeF -> throwError (NotAFunction f typeF)
