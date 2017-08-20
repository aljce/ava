{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Language.Ava.Nat where

import Data.Singletons (Sing)
import Data.Singletons.Prelude (PNum(..))

data Nat
  = Zero
  | Succ Nat

instance PNum Nat where

data instance Sing (n :: Nat) = SNat Int

