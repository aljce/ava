{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Fin (Fin, elimFin) where

import Data.Kind (Type)

import Data.Singletons (Sing)
import Data.Nat (Nat(..))

import Unsafe.Coerce (unsafeCoerce)

data Fin :: Nat -> Type where
  Fin :: Sing n -> Int -> Fin n

instance Eq (Fin n) where
  (Fin _ x) == (Fin _ y) = x == y

instance Ord (Fin n) where
  compare (Fin _ x) (Fin _ y) = compare x y

instance Show (Fin n) where
  show (Fin _ i) = show i

elimFin
  :: forall p n
  .  (forall m. p (Succ m))
  -> (forall m. Fin m -> p m -> p (Succ m))
  -> Fin n
  -> p n
elimFin z s (Fin n f) = go f
  where
    go :: Int -> p n
    go 0 = unsafeCoerce z
    go i = unsafeCoerce (s (Fin n i) (go i))
