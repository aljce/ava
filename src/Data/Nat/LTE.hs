{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Nat.LTE
  ( LTE
  , lteToInt
  , lteI
  , lte
  , lteLit
  ) where

import Prelude hiding (id,(.))
import Control.Category (Category(..))
import Data.Singletons (SingI(..))
import Data.Singletons.Prelude (Sing(..),PNum(..),POrd(..),SOrd(..))
import Data.Nat (Nat,slit,natToInt)

newtype LTE (n :: Nat) (m :: Nat) = LTE Int

instance Category LTE where
  id = LTE 0
  (LTE ab) . (LTE bc) = LTE (ab + bc)

lteToInt :: LTE n m -> Int
lteToInt (LTE nm) = nm

lte :: Sing (n :: Nat) -> Sing (m :: Nat) -> Maybe (LTE n m)
lte n m = case n %:<= m of
  STrue -> Just (LTE (natToInt m - natToInt n))
  SFalse -> Nothing

lteI :: forall n m. (SingI n, SingI m, (n :<= m) ~ True) => LTE n m
lteI = LTE (natToInt (sing @_ @m) - natToInt (sing @_ @n))

lteLit
  :: forall n m n' m'.
     ( n' ~ FromInteger n
     , m' ~ FromInteger m
     , SingI n'
     , SingI m'
     , (n' :<= m') ~ True)
  => LTE n' m'
lteLit = LTE (natToInt (slit @n) - natToInt (slit @m))
