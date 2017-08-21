{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Fin where

import Data.Kind (Type)
import Data.Void (Void,absurd)

import Data.Singletons (SingI(..))
import Data.Singletons.Prelude (Sing(..),PNum(..),SNum(..),SOrd(..))
import Data.Singletons.Prelude.Enum (SEnum(..))
import Data.Nat (Nat(..),slit,natToInt)

import Unsafe.Coerce (unsafeCoerce)

data Fin :: Nat -> Type where
  Fin :: Sing n -> !Int -> Fin n

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

finToInt :: Fin n -> Int
finToInt (Fin _ i) = i

bound :: Fin n -> Sing n
bound (Fin n _) = n

finZeroAbsurd :: Fin Zero -> Void
finZeroAbsurd _ = error "Data.Fin.finZAbsurd: Fin Zero is uninhabited"

finZeroElim :: Fin Zero -> a
finZeroElim = absurd . finZeroAbsurd

weaken :: Fin n -> Fin (Succ n)
weaken (Fin n i) = Fin (sSucc n) i

weakenN :: Sing n -> Fin m -> Fin (n :+ m)
weakenN n (Fin m i) = Fin (n %:+ m) i

strengthen :: Fin (Succ n) -> Maybe (Fin n)
strengthen (Fin n i) = case n %:<= slit @1 of
  STrue -> Nothing
  SFalse -> Just (Fin (sPred n) i)

shift :: Sing n -> Fin m -> Fin (n :+ m)
shift n (Fin m i) = Fin (n %:+ m) (natToInt n + i)

last :: forall n. SingI n => Fin (Succ n)
last = Fin (sSucc n) (natToInt n)
  where
    n :: Sing n
    n = sing

natToFin :: Sing (n :: Nat) -> Sing m -> Maybe (Fin (Succ m))
natToFin n m = case n %:<= m of
  STrue -> Just (Fin (sSucc m) (natToInt n))
  SFalse -> Nothing

intToFin :: Int -> Sing n -> Maybe (Fin (Succ n))
intToFin i n
  | 0 <= i && i < natToInt n = Just (Fin (sSucc n) i)
  | otherwise = Nothing
