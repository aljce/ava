{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Nat
  ( type Nat(..)
  , Sing(SNat)
  , zero
  , succ
  , slit
  , natToInt
  , elimNat
  ) where

import Prelude hiding (succ)
import Data.Singletons (SingI(..))
import Unsafe.Coerce (unsafeCoerce)

import Data.Nat.Internal (type Nat(..),Sing(..),FromKnownNat)

zero :: Sing Zero
zero = SNat 0

succ :: Sing n -> Sing (Succ n)
succ (SNat i) = SNat (1 + i)

slit :: SingI (FromKnownNat n) => Sing (FromKnownNat n)
slit = sing

natToInt :: Sing (n :: Nat) -> Int
natToInt (SNat i) = i

elimNat
  :: forall p n
  .  p Zero
  -> (forall m. p m -> p (Succ m))
  -> Sing n
  -> p n
elimNat z s (SNat i)
  | i == 0 = unsafeCoerce z
  | otherwise = unsafeCoerce (s (elimNat z s (SNat (i - 1))))
