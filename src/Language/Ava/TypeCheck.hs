{-# LANGUAGE LambdaCase#-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Language.Ava.TypeCheck where

import Prelude hiding (succ)
-- import qualified Data.HashMap.Strict as HM
import qualified Control.Monad.Trans as MT
import Control.Monad.Reader (ReaderT,MonadReader(..),runReaderT)
import Control.Monad.Except (Except,MonadError(..),runExcept)
-- import Data.Type.Equality ((:~:)(..))
import Data.Singletons (SingI(..),withSingI)
-- import Data.Singletons.Prelude (Sing(..),SOrd(..))
-- import Data.Singletons.Decide (Decision(..),(%~))

import Data.Nat (succ)
import Data.Fin (Fin,finToInt)
import Data.Nat.LTE (lteN)
import Language.Ava

import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace

data TypeError v u c where
  UnboundVariable :: v -> Fin n -> TypeError v u c
  NotAFunction :: AST v u c Elim n -> AST v u c k m -> TypeError v u c
  TypeMismatch :: AST v u c k n -> AST v u c k m -> TypeError v u c
  NotReduceable :: AST v u c k n -> AST v u c k m -> TypeError v u c
  NotAUniverse :: AST v u c k n -> AST v u c k m -> TypeError v u c
  LamRequiresTypePi :: AST v u c k n -> AST v u c k m -> TypeError v u c

deriving instance (Show v, Show u, Show c) => Show (TypeError v u c)

data Context v u c where
  Context :: [ASTLen v u c Term] -> Context v u c
  deriving Show

empty :: Context v u c
empty = Context []

insert :: SingI n => AST v u c Term n -> Context v u c -> Context v u c
insert ast (Context ctx) = Context (ASTLen ast : ctx)

lookupVar :: forall v u c n. SingI n => Fin n -> Context v u c -> Maybe (AST v u c Term n)
lookupVar f (Context ctx) = go 0 ctx
  where
    go :: Int -> [ASTLen v u c Term] -> Maybe (AST v u c Term n)
    go _ [] = Nothing
    go i (ASTLen c:cs) = case finToInt f == i of
      True -> Just (unsafeCoerce c)
      False -> go (i + 1) cs

data Basis v u c
  = Basis
  { checkUniverse :: u -> u -> TCM v u c ()
  , checkConstant :: forall n. c -> AST v u c Term n -> TCM v u c ()
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

runTCM :: TCM v u c a -> Basis v u c -> Either (TypeError v u c) a
runTCM (TCM tc) basis = runExcept (runReaderT (runReaderT tc empty) basis)

getBasis :: TCM v u c (Basis v u c)
getBasis = TCM (MT.lift ask)

typeMismatch :: AST v u c Term n -> AST v u c Term m -> TCM v u c void
typeMismatch e1 e2 = throwError (TypeMismatch e1 e2)

notAUniverse :: AST v u c Term n -> AST v u c Term m -> TCM v u c void
notAUniverse e1 e2 = throwError (NotAUniverse e1 e2)

bindingLevelI :: forall n b v r. SingI n => Bind b v -> (SingI (BindingLevel b n) => r) -> r
bindingLevelI b cb = case b of
  Irrelevant -> cb
  Bind _ -> withSingI (succ (sing @_ @n)) cb

check
  :: forall v u c n m
  .  (Eq u, Eq c, SingI n, SingI m, Show v, Show u, Show c)
  => AST v u c Term n
  -> AST v u c Term m
  -> TCM v u c ()
check e typeE = case trace (show e ++ " : " ++ show typeE) e of
  Universe eU -> case typeE of
    Universe typeEU -> do
      basis <- getBasis
      checkUniverse basis eU typeEU
    _ -> notAUniverse e typeE
  Constant c -> do
      basis <- getBasis
      checkConstant basis c typeE
  Lift lte l -> withSingI (lteN lte) (check l typeE)
  Embed d -> do
    s <- synthesize d
    case alphaEq s typeE of
      True -> pure ()
      False -> throwError (NotReduceable s typeE)
  Pi x typeX b -> case typeE of
    Universe _ -> do
      check typeX typeE
      case x of
        Irrelevant -> check b typeE
        Bind _ ->
          local (insert typeX)
                (withSingI (succ (sing @_ @n))
                           (check b typeE))
    _ -> notAUniverse e typeE
  Lam x b -> case typeE of
    Pi a typeA typeB ->
      bindingLevelI @n x
        (case a of
           Irrelevant -> check b typeB
           Bind _ -> local (insert typeA)
                           (withSingI (succ (sing @_ @m)) (check b typeB)))
    _ -> throwError (LamRequiresTypePi e typeE)

synthesize
  :: forall v u c n
  .  (Eq u, Eq c, SingI n, Show v, Show u, Show c)
  => AST v u c Elim n
  -> TCM v u c (AST v u c Term n)
synthesize = \case
  Lift lte l -> withSingI (lteN lte) (Lift lte <$> synthesize l)
  Ref x i -> do
    ctx <- ask
    case lookupVar i (traceShowId ctx) of
      Nothing -> throwError (UnboundVariable x i)
      Just ast -> pure ast
  x ::: typeX -> do
    check x typeX
    pure typeX
  f :@: a -> synthesize f >>= \case
    Pi x typeX b -> do
      check a typeX
      pure (substitute x a typeX b)
    typeF -> throwError (NotAFunction f typeF)

-- normalize :: AST v u c k n -> TCM v u c (AST v u c )

basic :: Basis v Star Base
basic = Basis (\_ _ -> pure ()) base
  where
    base :: Base -> AST v u Base Term n -> TCM v u Base ()
    base IntT (Universe _) = pure ()
    base (IntV _) (Constant IntT) = pure ()
    base b e = typeMismatch (Constant b) e
