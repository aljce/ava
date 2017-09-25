{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Fin.Internal where

import Prelude hiding (last)
import Data.Maybe (fromMaybe)
import Data.Singletons (SingI(..),Sing(..))

import Data.Nat (type Nat(..),natToInt)

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

last :: forall n. SingI n => Fin (Succ n)
last = Fin (natToInt (sing @_ @n))

intToFin :: Int -> Sing n -> Maybe (Fin (Succ n))
intToFin i n
  | 0 <= i && i <= natToInt n = Just (Fin i)
  | otherwise = Nothing
