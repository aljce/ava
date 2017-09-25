{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Fin
  ( Fin
  , fzero
  , fsucc
  , finToInt
  , bound
  , elimFin
  , finZeroAbsurd
  , finZeroElim
  , weaken
  , weakenN
  , weakenLTE
  , strengthen
  , shift
  , shiftLTE
  , last
  , natToFin
  , intToFin
  ) where

import Prelude hiding (last)
import Data.Void (Void,absurd)

import Data.Singletons (SingI(..))
import Data.Singletons.Prelude (Sing(..),PNum(..),SOrd(..))
import Unsafe.Coerce (unsafeCoerce)

import Data.Nat (Nat(..),slit,natToInt)
import Data.Nat.LTE (LTE,lteToInt)
import Data.Fin.Internal (Fin(..),fzero,fsucc,last,finToInt,intToFin)

bound :: SingI n => Fin n -> Sing n
bound _ = sing

elimFin
  :: forall p n
  .  (forall m. p (Succ m))
  -> (forall m. Fin m -> p m -> p (Succ m))
  -> Fin n
  -> p n
elimFin z s (Fin f) = go f
  where
    go :: Int -> p n
    go 0 = unsafeCoerce z
    go i = unsafeCoerce (s (Fin i) (go (i - 1)))

finZeroAbsurd :: Fin Zero -> Void
finZeroAbsurd _ = error "Data.Fin.finZAbsurd: Fin Zero is uninhabited"

finZeroElim :: Fin Zero -> a
finZeroElim = absurd . finZeroAbsurd

weaken :: Fin n -> Fin (Succ n)
weaken (Fin i) = Fin i

weakenN :: forall n m. Fin m -> Fin (n :+ m)
weakenN (Fin i) = Fin i

weakenLTE :: forall n m. LTE n m -> Fin n -> Fin m
weakenLTE _ (Fin i) = Fin i

strengthen :: forall n. SingI n => Fin (Succ n) -> Maybe (Fin n)
strengthen (Fin i) = case sing @_ @n %:<= slit @1 of
  STrue -> Nothing
  SFalse -> Just (Fin i)

shift :: Sing n -> Fin m -> Fin (n :+ m)
shift n (Fin i) = Fin (natToInt n + i)

shiftLTE :: LTE n m -> Fin n -> Fin m
shiftLTE lte (Fin i) = Fin (lteToInt lte + i)

natToFin :: Sing (n :: Nat) -> Sing m -> Maybe (Fin (Succ m))
natToFin n m = case n %:<= m of
  STrue -> Just (Fin (natToInt n))
  SFalse -> Nothing
