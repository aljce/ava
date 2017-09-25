{-# LANGUAGE LambdaCase#-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Language.Ava.TypeCheck where

import qualified Data.HashMap.Strict as HM
import Control.Monad.Reader (ReaderT,MonadReader(..))
import Control.Monad.State (StateT,MonadState(..))
import Control.Monad.Except (Except,MonadError(..))
import Data.Singletons (SingI(..))

import Data.Fin (Fin,finToInt)
import Language.Ava

data TypeError v u c where
  UnboundVariable :: v -> Fin n -> TypeError v u c
  NotAFunction :: AST v u c Elim n -> AST v u c k m -> TypeError v u c

data Constraint v u c

newtype Context v u c
  = Context { getContext :: HM.HashMap Int (ASTAny v u c) }

data Basis v u c
  = Basis
  { incrementUniverse :: u -> TCM v u c (ASTAny v u c)
  , lookupUniverse :: ASTAny v u c -> TCM v u c u
  , constantChecker :: c -> TCM v u c (ASTAny v u c)
  }

newtype TCM v u c a
  = TCM { unTCM :: ReaderT (Basis v u c) (StateT (Context v u c) (Except (TypeError v u c))) a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader (Basis v u c)
    , MonadState (Context v u c)
    , MonadError (TypeError v u c)
    )

check :: SingI n => AST v u c Term n -> TCM v u c (ASTAny v u c)
check = \case
  Universe u -> do
    basis <- ask
    incrementUniverse basis u
  Constant c -> do
    basis <- ask
    constantChecker basis c
  Lift lte l -> undefined -- check l
  Embed e -> synthesize e
  Pi x typeX b -> return undefined

synthesize :: SingI n => AST v u c Elim n -> TCM v u c (ASTAny v u c)
synthesize = \case
  Ref x i -> do
    ctx <- get
    case HM.lookup (finToInt i) (getContext ctx) of
      Nothing -> throwError (UnboundVariable x i)
      Just ast -> pure ast
  x ::: typeX -> pure (ASTAny typeX)
  f :@: a -> synthesize f >>= \case
      ASTAny (Pi x typeX b) -> undefined
      ASTAny typeF -> throwError (NotAFunction f typeF)
