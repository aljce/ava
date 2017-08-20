{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Nat where

import Data.Proxy (Proxy(..))
import qualified GHC.TypeLits as GHC
import Data.Singletons (SingI(..),SingKind(..),SomeSing(..),Apply)
import Data.Singletons.Prelude
  (Sing(..),PNum(..),SNum(..),FromIntegerSym0,PEq(..),SEq(..),POrd(..),SOrd(..))
import Data.Singletons.TypeLits (withKnownNat)

import Unsafe.Coerce (unsafeCoerce)

data Nat
  = Zero
  | Succ Nat

type family FromKnownNat (n :: GHC.Nat) :: Nat where
  FromKnownNat 0 = Zero
  FromKnownNat n = Succ (FromKnownNat (n :- 1))

type family ToKnownNat (n :: Nat) :: GHC.Nat where
  ToKnownNat Zero = 0
  ToKnownNat (Succ n) = 1 :+ ToKnownNat n

instance PNum Nat where
  type Zero :+ n = n
  type (Succ n) :+ m = Succ (n :+ m)
  type n :- Zero = n
  type Zero :- _ = Zero
  type (Succ n) :- (Succ m) = n :- m
  type Zero :* m = Zero
  type (Succ n) :* m = m :+ (n :* m)
  type Negate m = GHC.TypeError (GHC.Text "Cannot negate a natural number")
  type Abs n = n
  type Signum Zero = Zero
  type Signum (Succ _) = Succ Zero
  type FromInteger n = FromKnownNat n

instance PEq Nat where
  type Zero :== Zero = True
  type Zero :== (Succ _) = False
  type (Succ _) :== Zero = False
  type (Succ n) :== (Succ m) = n :== m
  type Zero :/= Zero = False
  type Zero :/= (Succ _) = True
  type (Succ _) :/= Zero = True
  type (Succ n) :/= (Succ m) = n :/= m

instance POrd Nat where
  type Compare Zero Zero = EQ
  type Compare (Succ _) Zero = GT
  type Compare Zero (Succ _) = LT
  type Compare (Succ n) (Succ m) = Compare n m
  type Zero :< Zero = False
  type Zero :< (Succ _) = True
  type (Succ _) :< Zero = False
  type (Succ n) :< (Succ m) = n :< m
  type Zero :<= Zero = True
  type Zero :<= (Succ _) = True
  type (Succ _) :<= Zero = False
  type (Succ n) :<= (Succ m) = n :< m
  type Zero :> Zero = False
  type Zero :> (Succ _) = False
  type (Succ _) :> Zero = True
  type (Succ n) :> (Succ m) = n :> m
  type Zero :>= Zero = True
  type Zero :>= (Succ _) = False
  type (Succ _) :>= Zero = True
  type (Succ n) :>= (Succ m) = n :> m
  type Max Zero m = m
  type Max (Succ n) Zero = Succ n
  type Max (Succ n) (Succ m) = Succ (Max n m)
  type Min Zero _ = Zero
  type Min _ Zero = Zero
  type Min (Succ n) (Succ m) = Succ (Min n m)

data instance Sing (n :: Nat) = SNat Int

instance Show (Sing (n :: Nat)) where
  showsPrec p (SNat i) = showsPrec p i

instance SingI Zero where
  sing = SNat 0

instance GHC.KnownNat (ToKnownNat (Succ n)) => SingI (Succ n) where
  sing = (SNat . fromIntegral . GHC.natVal) (Proxy @(ToKnownNat (Succ n)))

instance SingKind Nat where
  type Demote Nat = Word
  fromSing (SNat i) = fromIntegral i
  toSing w = SomeSing (SNat (fromIntegral w))

instance SNum Nat where
  SNat n %:+ SNat m = SNat (n + m)
  SNat n %:- SNat m
    | n >= m = SNat (n - m)
    | otherwise = SNat 0
  SNat n %:* SNat m = SNat (n * m)
  sNegate _ = error "Cannot negate a natural number"
  sAbs n = n
  sSignum (SNat n) = SNat (signum n)
  sFromInteger :: forall n. Sing n -> Sing (Apply FromIntegerSym0 n :: Nat)
  sFromInteger n = withKnownNat n nat
    where
      nat :: GHC.KnownNat n => Sing (FromKnownNat n)
      nat = SNat (fromInteger (GHC.natVal (Proxy @n)))

instance SEq Nat where
  (SNat n) %:== (SNat m)
    | n == m = unsafeCoerce STrue
    | otherwise = unsafeCoerce SFalse
  (SNat n) %:/= (SNat m)
    | n == m = unsafeCoerce SFalse
    | otherwise = unsafeCoerce STrue

instance SOrd Nat where
  sCompare (SNat n) (SNat m) = case compare n m of
    LT -> unsafeCoerce SLT
    EQ -> unsafeCoerce SEQ
    GT -> unsafeCoerce SGT
  (SNat n) %:< (SNat m)
    | n < m = unsafeCoerce STrue
    | otherwise = unsafeCoerce SFalse
  (SNat n) %:<= (SNat m)
    | n <= m = unsafeCoerce STrue
    | otherwise = unsafeCoerce SFalse
  (SNat n) %:> (SNat m)
    | n > m = unsafeCoerce STrue
    | otherwise = unsafeCoerce SFalse
  (SNat n) %:>= (SNat m)
    | n >= m = unsafeCoerce STrue
    | otherwise = unsafeCoerce SFalse
  sMax (SNat n) (SNat m) = SNat (max n m)
  sMin (SNat n) (SNat m) = SNat (min n m)

elimNat
  :: forall p n
  .  p Zero
  -> (forall m. p m -> p (Succ m))
  -> Sing n
  -> p n
elimNat z s (SNat i)
  | i == 0 = unsafeCoerce z
  | otherwise = unsafeCoerce (s (elimNat z s (SNat (i - 1))))

