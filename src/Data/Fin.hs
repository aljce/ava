{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
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
  , strengthen
  , shift
  , last
  , natToFin
  , intToFin
  ) where

import Prelude hiding (last)
import Data.Void (Void,absurd)
import Data.Maybe (fromMaybe)

import Data.Singletons (SingI(..))
import Data.Singletons.Prelude (Sing(..),PNum(..),SOrd(..))
import Data.Nat (Nat(..),slit,natToInt)

import Unsafe.Coerce (unsafeCoerce)

newtype Fin (n :: Nat) = Fin Int
  deriving (Eq,Ord)

instance SingI n => Enum (Fin (Succ n)) where
  succ (Fin i)
    | i < 1 + natToInt (sing @_ @n) = Fin (i + 1)
    | otherwise = error "Prelude.Enum.Fin.succ: bad argument"
  pred (Fin _)
    | otherwise = error "Prelude.Enum.Fin.pred: bad argument"
  toEnum i = fromMaybe (error "Prelude.Enum.Fin.toEnum: bad argument") (intToFin i sing)
  fromEnum = finToInt

instance SingI n => Bounded (Fin (Succ n)) where
  minBound = fzero
  maxBound = last

instance Show (Fin n) where
  show (Fin i) = show i

fzero :: Fin (Succ n)
fzero = Fin 0

fsucc :: Fin n -> Fin (Succ n)
fsucc (Fin i) = Fin (1 + i)

finToInt :: Fin n -> Int
finToInt (Fin i) = i

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

strengthen :: forall n. SingI n => Fin (Succ n) -> Maybe (Fin n)
strengthen (Fin i) = case sing @_ @n %:<= slit @1 of
  STrue -> Nothing
  SFalse -> Just (Fin i)

shift :: Sing n -> Fin m -> Fin (n :+ m)
shift n (Fin i) = Fin (natToInt n + i)

last :: forall n. SingI n => Fin (Succ n)
last = Fin (natToInt (sing @_ @n))

natToFin :: Sing (n :: Nat) -> Sing m -> Maybe (Fin (Succ m))
natToFin n m = case n %:<= m of
  STrue -> Just (Fin (natToInt n))
  SFalse -> Nothing

intToFin :: Int -> Sing n -> Maybe (Fin (Succ n))
intToFin i n
  | 0 <= i && i <= natToInt n = Just (Fin i)
  | otherwise = Nothing
