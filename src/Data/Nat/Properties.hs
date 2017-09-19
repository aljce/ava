{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Data.Nat.Properties
  ( plusSuccRightSucc
  ) where

import Data.Singletons.Prelude (PNum(..))
import Data.Type.Equality ((:~:)(..))
import Data.Nat (Nat(..))

import Unsafe.Coerce (unsafeCoerce)

plusSuccRightSucc :: forall n m. n :+ Succ m :~: Succ (n :+ m)
plusSuccRightSucc = unsafeCoerce Refl

