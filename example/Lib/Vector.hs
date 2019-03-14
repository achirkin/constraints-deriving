{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RoleAnnotations            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
{- |
  This is an example of using constraints-deriving plugin for optimization.

  This module presents a "front-end"  Vector data type visible to a user.
  It is a simple newtype wrapper over a "backend" data type family.
  Behind the scenes, the compiler chooses the most efficient representations
  for the backend based on a type family `Backend t n`.
  For example, if the compiler knows that the size of a vector is 1,
  than the `Vector t 1` type is a newtype wrapper over `t`,
  and GHC statically uses all type class instances for `t`, sidestepping dynamic instance elaboration.
  But, if GHC does not know the dimensionality of the vector statically,
  it selects class instances dynamically at runtime.  
 -}
module Lib.Vector
  ( -- * Data types
    Vector (Z, (:*))
  , SomeVector (..), KnownBackend (), Backend
  , Nat
  ) where


#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif
import Data.Constraint
import GHC.Base        (Type, unsafeCoerce#)
import GHC.TypeLits    (type (+), type (-), KnownNat, Nat)

import Lib.BackendFamily
import Lib.VecBackend


newtype Vector (t :: Type) (n ::Nat) = Vector (VecBackend t n (Backend t n))

pattern Z :: forall t n
           . KnownBackend (Vector t n)
          => n ~ 0
          => Vector t n
pattern Z <- (vUncons -> Left Dict)
  where
    Z = Vector (VecBackend bNil)

pattern (:*) :: forall t n
              . KnownBackend (Vector t n)
             => forall m
              . (KnownBackend (Vector t m), n ~ (m + 1), m ~ (n - 1))
             => t -> Vector t m -> Vector t n
pattern (:*) x xs <- (vUncons -> Right (Dict, x, xs))
  where
    (:*) = vCons
infixr 7 :*
#if __GLASGOW_HASKELL__ >= 802
{-# Complete Z, (:*) #-}
#endif

vUncons :: forall t n m
         . KnownBackend (Vector t n)
        => Vector t n
        -> Either ( Dict ( n ~ 0
                         , n ~ DataDims (Vector t n)
                         , t ~ DataElemType (Vector t n)
                         ))
                  ( Dict ( KnownBackend (Vector t m)
                         , n ~ (m + 1)
                         , m ~ (n - 1)
                         , n ~ DataDims (Vector t n)
                         , m ~ DataDims (Vector t m)
                         , t ~ DataElemType (Vector t n)
                         , t ~ DataElemType (Vector t m)
                         )
                  , t, Vector t m )
vUncons = case underiveKB @t @n of Dict -> unsafeCoerce# (bUncons @t @n @m)

vCons :: forall t n
       . KnownBackend (Vector t n)
      => t -> Vector t n -> Vector t (n + 1)
vCons = case underiveKB @t @n of Dict -> unsafeCoerce# (bCons @t @n)


data SomeVector (t :: Type) where
  SomeVector :: (KnownNat (n :: Nat), KnownBackend (Backend t n))
             => Vector t n -> SomeVector t


type instance DataElemType (Vector t n) = t
type instance DataDims (Vector t n) = n

instance (KnownBackend (Vector t n), Show t) => Show (Vector t n) where
  show Z         = "Z"
  show (x :* xs) = show x ++ " :* " ++ show xs

instance KnownBackend (Backend t n) => KnownBackend (Vector t n)
deriving instance Eq (VecBackend t n (Backend t n)) => Eq (Vector t n)
deriving instance Ord (VecBackend t n (Backend t n)) => Ord (Vector t n)
deriving instance Semigroup (VecBackend t n (Backend t n)) => Semigroup (Vector t n)
deriving instance Monoid (VecBackend t n (Backend t n)) => Monoid (Vector t n)

underiveKB :: forall t n . KnownBackend (Vector t n) => Dict (KnownBackend (Backend t n))
underiveKB = unsafeCoerce# (Dict @(KnownBackend (Vector t n)))
