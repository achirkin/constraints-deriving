{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RoleAnnotations      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}

module Lib.VecBackend
  -- ( VecBackend(..)
  -- , inferEq, inferOrd, inferShow, inferSemigroup, inferMonoid
  -- )
  where


import           Data.Constraint
import           Data.Constraint.Deriving
import           Data.Constraint.Unsafe
import           GHC.Base
import           GHC.TypeLits             (KnownNat, Nat)
import           Unsafe.Coerce
#if __GLASGOW_HASKELL__ < 804
import           Data.Semigroup
#endif


import           Lib.BackendFamily


{-# ANN type VecBackend DeriveAll #-}
{-# ANN type VecBackend DeriveAll #-}
{-# ANN VecBackend DeriveAll #-}
type role VecBackend phantom phantom representational
-- I need two layers of wrappers to provide default overlappable instances to
-- all type classes using KnownBackend mechanics.
-- Type arguments are redundant here;
-- nevertheless, they improve readability of error messages.
newtype VecBackend (t :: Type) (n :: Nat) (backend :: Type)
  = VecBackend { _getBackend :: backend }
type instance DataElemType (VecBackend t _ _) = t
type instance DataDims (VecBackend _  n _) = n
-- I use this type instance to inform `DeriveAll` core plugin that backend is an instance
-- of type family `Backend t n`.
-- This allows the plugin to find all possible instances of the type family and
-- then lookup corresponding class instances.
-- Otherwise, the plugin would have to derive all instances for all types in scope,
-- because the newtype declaration is too general without these additional constraints.
type instance DeriveContext (VecBackend t n b) = b ~ Backend t n

{-# ANN type TestData DeriveAll #-}
{-# ANN type TestNewtype DeriveAll #-}
{-# ANN type TestNewtype2 DeriveAll #-}
{-# ANN TestNewtype2C DeriveAll #-}
{-# ANN TestNewtype2C DeriveAll #-}

data TestData a = TData a a Int
newtype TestNewtype t n = TestNewtypeC (Backend t n)
newtype TestNewtype2 t n b = TestNewtype2C (Backend t n)
type instance DeriveContext (TestNewtype2 t n b) = Backend t n ~ b

{-# ANN type TestNewtype3 DeriveAll #-}
newtype TestNewtype3 a = TestNewtype3C a
-- Enumerate specific instances
type instance DeriveContext (TestNewtype3 Bool) = ()
type instance DeriveContext (TestNewtype3 Int)  = ()
type instance DeriveContext (TestNewtype3 (Maybe a)) = ()
type instance DeriveContext (TestNewtype3 (VecBackend t n b)) = b ~ Backend t n


{-# ANN type Newclass DeriveAll #-}
class Newclass a where
  hereAmI :: a

{-# ANN type Properclass DeriveAll #-}
class Properclass a where
  p1 :: a
  p2 :: (a, a)

{-# ANN type TestTypeType DeriveAll #-}
type TestTypeType t n = TestNewtype t n

{-# ANN type TestTF DeriveAll #-}
type family TestTF t (n :: Nat)
type instance TestTF t n = TestNewtype t n

-- invalid annotation for testing purposes
{-# ANN type TestTF (ToInstance NoOverlap) #-}


{-# ANN inferEq (ToInstance Overlappable) #-}
inferEq :: forall t n b . ( KnownBackend b, Eq t) => Dict (Eq (VecBackend t n b))
inferEq = mapDict toVecBackend
        . mapDict (Sub inferBackendInstance)
        $ inferBase @t @n @b undefined

{-# ANN inferShow (ToInstance Overlappable) #-}
inferShow :: forall t n b . ( KnownBackend b, Show t)
          => Dict (Show (VecBackend t n b))
inferShow = mapDict toVecBackend
          . mapDict (Sub inferBackendInstance)
          $ inferBase @t @n @b undefined

{-# ANN inferOrd (ToInstance Overlappable) #-}
inferOrd :: forall t n b . ( KnownBackend b, Ord t)
         => Dict (Ord (VecBackend t n b))
inferOrd = mapDict toVecBackend
         . mapDict (Sub inferBackendInstance)
         $ inferBase @t @n @b undefined

{-# ANN inferSemigroup (ToInstance Overlappable) #-}
inferSemigroup :: forall t n b . ( KnownBackend b, Num t)
               => Dict (Semigroup (VecBackend t n b))
inferSemigroup = mapDict toVecBackend
               . mapDict (Sub inferBackendInstance)
               $ inferBase @t @n @b undefined

{-# ANN inferMonoid (ToInstance Overlappable) #-}
inferMonoid :: forall t n b . ( KnownBackend b, Num t, KnownNat n)
            => Dict (Monoid (VecBackend t n b))
inferMonoid = mapDict toVecBackend
            . mapDict (Sub inferBackendInstance)
            $ inferBase @t @n @b undefined

inferBase :: VecBackend t n b -> Dict (b ~ Backend t n, t ~ DataElemType b, n ~ DataDims b)
inferBase _ = unsafeCoerce
  (Dict :: Dict (b ~ b, t ~ t, n ~ n) )
{-# INLINE inferBase #-}

toVecBackend :: forall c t n b . c b :- c (VecBackend t n b)
toVecBackend = unsafeDerive VecBackend
{-# INLINE toVecBackend #-}