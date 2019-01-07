{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RoleAnnotations            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Lib.Vector
  ( -- * Data types
    Vector (..), pattern Vec
  , SomeVector (..)
  , VecBackend (..), Backend
  , Nat
  ) where


#if __GLASGOW_HASKELL__ < 804
import           Data.Semigroup
#endif
import           GHC.Base          (Type)
import           GHC.TypeLits      (KnownNat, Nat)

import           Lib.BackendFamily
import           Lib.VecBackend




newtype Vector (t :: Type) (n ::Nat) = Vector (VecBackend t n (Backend t n))

pattern Vec :: Backend (t :: Type) (n :: Nat) -> Vector t n
pattern Vec x = (Vector (VecBackend x))

data SomeVector (t :: Type) where
  SomeVector :: (KnownNat (n :: Nat), KnownBackend (Backend t n))
             => Vector t n -> SomeVector t


type instance DataElemType (Vector t n) = t
type instance DataDims (Vector t n) = n


-- instance KnownBackend (Backend t n) => KnownBackend (DataFrame t n) where
--  bSing = unsafeCoerce# (bSing :: BackendSing (Backend t n))
--  {-# INLINE bSing #-}
deriving instance Eq (VecBackend t n (Backend t n)) => Eq (Vector t n)
deriving instance Ord (VecBackend t n (Backend t n)) => Ord (Vector t n)
deriving instance Show (VecBackend t n (Backend t n)) => Show (Vector t n)
deriving instance Semigroup (VecBackend t n (Backend t n)) => Semigroup (Vector t n)
deriving instance Monoid (VecBackend t n (Backend t n)) => Monoid (Vector t n)
