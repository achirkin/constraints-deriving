{-# LANGUAGE CPP                    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

{- |
  This module contains actual implementation of the `Backend` type family.

  The idea is that this module does not expose any implementation details;
  one can even implement multiple copies of this file depending on the compiler or package flags,
  (such as the presence of SIMD extensions).

  In this example, I provide four implementations, depending on the dimensionality of the vector.
  Note, that no evidence of the implementation details is exported.
 -}
module Lib.BackendFamily
  ( Backend, DataElemType, DataDims
  , KnownBackend ()
  , inferBackendInstance
    -- constructing data
  , bCons, bUncons, bNil
  ) where


import Data.Constraint
import Debug.Trace
import GHC.Base
import GHC.TypeLits
import Unsafe.Coerce
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif


-- backend type level definitions
data UnitBase (t :: Type) = UnitBase
  deriving (Eq, Ord, Show)

newtype ScalarBase (t :: Type) = ScalarBase { _unScalarBase :: t }
  deriving (Eq, Ord, Show)

data Vec2Base (t :: Type) = Vec2Base t t
  deriving (Eq, Ord, Show)

newtype ListBase (t :: Type) (n :: Nat) = ListBase { _unListBase :: [t] }
  deriving (Eq, Ord, Show)

-- backend mappings
type family Backend (t :: Type) (n :: Nat) = (v :: Type) | v -> t n where
    Backend t  0 = UnitBase t
    Backend t  1 = ScalarBase t
    Backend t  2 = Vec2Base t
    Backend t  n = ListBase t n

-- ideally, bijection in the backend mapping allows to identify t and n,
-- but compiler does not like it.

type family DataElemType (backend :: Type) :: Type
type instance DataElemType (UnitBase t)   = t
type instance DataElemType (ScalarBase t) = t
type instance DataElemType (Vec2Base t)   = t
type instance DataElemType (ListBase t _) = t

type family DataDims (backend :: Type) :: Nat
type instance DataDims (UnitBase _)   = 0
type instance DataDims (ScalarBase _) = 1
type instance DataDims (Vec2Base _)   = 2
type instance DataDims (ListBase _ n) = n

-- backend term level definition (GADT)
data BackendSing (backend :: Type) where
  BS0 :: (Backend t 0 ~ UnitBase t  , n ~ 0) => BackendSing (UnitBase t)
  BS1 :: (Backend t 1 ~ ScalarBase t, n ~ 1) => BackendSing (ScalarBase t)
  BS2 :: (Backend t 2 ~ Vec2Base t  , n ~ 2) => BackendSing (Vec2Base t)
  BSn :: (Backend t n ~ ListBase t n, CmpNat n 2 ~ 'GT) => BackendSing (ListBase t n)


deriving instance Eq (BackendSing backend)
deriving instance Ord (BackendSing backend)
deriving instance Show (BackendSing backend)


-- | A framework for using Array type family instances.
class KnownBackend (t :: Type) where
    -- | Get Array type family instance
    bSing :: BackendSing t
    default bSing :: ( Coercible (Backend (DataElemType t) (DataDims t)) t
                     , KnownBackend (Backend (DataElemType t) (DataDims t))
                     )
                  => BackendSing t
    bSing = unsafeCoerce (bSing @(Backend (DataElemType t) (DataDims t)))



instance Semigroup (UnitBase t) where
  UnitBase <> UnitBase = UnitBase

instance Monoid (UnitBase t) where
  mempty = UnitBase
  mappend = (<>)


instance Num t => Semigroup (ScalarBase t) where
  ScalarBase a <> ScalarBase b = ScalarBase (a + b)

instance Num t => Monoid (ScalarBase t) where
  mempty = ScalarBase 0
  mappend = (<>)

instance Num t => Semigroup (Vec2Base t) where
  Vec2Base a1 a2 <> Vec2Base b1 b2 = Vec2Base (a1 + b1) (a2 + b2)

instance Num t => Monoid (Vec2Base t) where
  mempty = Vec2Base 0 0
  mappend = (<>)

instance Num t => Semigroup (ListBase t n) where
  ListBase as <> ListBase bs = ListBase $ zipWith (+) as bs

instance (Num t, KnownNat n) => Monoid (ListBase t n) where
  mempty = r
    where
      r = ListBase $ replicate (fromInteger $ natVal r) 0
  mappend = (<>)

instance KnownBackend (UnitBase t) where
    bSing = BS0
instance KnownBackend (ScalarBase t) where
    bSing = BS1
instance KnownBackend (Vec2Base t) where
    bSing = BS2
instance CmpNat n 2 ~ 'GT => KnownBackend (ListBase t n) where
    bSing = case ( unsafeCoerce
                     (Dict :: Dict (ListBase t n ~ ListBase t n) )
                           :: Dict (ListBase t n ~ Backend  t n)
                 ) of
      Dict -> BSn


-- This function determines the logic of instance selection
-- for the type  b
inferBackendInstance
  :: forall b c
   . ( KnownBackend b
     , c (UnitBase (DataElemType b))
     , c (ScalarBase (DataElemType b))
     , c (Vec2Base (DataElemType b))
     , c (ListBase (DataElemType b) (DataDims b))
     )
  => Dict (c b)
inferBackendInstance = case (bSing :: BackendSing b) of
    BS0 -> trace "---------- Selecting UnitBase" Dict
    BS1 -> trace "---------- Selecting ScalarBase" Dict
    BS2 -> trace "---------- Selecting Vec2Base" Dict
    BSn -> trace "---------- Selecting ListBase" Dict
{-# INLINE inferBackendInstance #-}


bUncons :: forall t n m
         . KnownBackend (Backend t n)
        => Backend t n
        -> Either ( Dict ( n ~ 0
                         , n ~ DataDims (Backend t n)
                         , t ~ DataElemType (Backend t n)
                         ))
                  ( Dict ( KnownBackend (Backend t m)
                         , n ~ (m + 1)
                         , m ~ (n - 1)
                         , n ~ DataDims (Backend t n)
                         , m ~ DataDims (Backend t m)
                         , t ~ DataElemType (Backend t n)
                         , t ~ DataElemType (Backend t m)
                         )
                  , t, Backend t m )
bUncons x = case dataTypeDims x of
  Dict -> case bSing @(Backend t n) of
    BS0 -> Left Dict
    BS1 -> case unsafeDict @(n ~ n, m ~ m) @(n ~ 1, m ~ 0) Dict of
      Dict -> case x of ScalarBase a -> Right (Dict, a, UnitBase)
    BS2 -> case unsafeDict @(n ~ n, m ~ m) @(n ~ 2, m ~ 1) Dict of
      Dict -> case x of Vec2Base a b -> Right (Dict, a, ScalarBase b)
    BSn -> case x of
      ListBase [a,b,c] -> case unsafeDict @(n ~ n, m ~ m) @(n ~ 3, m ~ 2) Dict of
        Dict -> Right (Dict, a, Vec2Base b c)
      ListBase (a:as) -> case unsafeDict
                                @(n ~ n, m ~ m, CmpNat 3 2 ~ 'GT, Backend t m ~ Backend t m)
                                @(n ~ (m + 1), m ~ (n - 1), CmpNat m 2 ~ 'GT, Backend t m ~ ListBase t m)
                                Dict of
        Dict -> Right (Dict, a, ListBase @t @m as)
      ListBase _      -> error "Unexpected-length vector"

unsafeDict :: forall a b . a => Dict a -> Dict b
unsafeDict _ = unsafeCoerce (Dict @a)

dataTypeDims :: forall t n . Backend t n -> Dict (t ~ DataElemType (Backend t n), n ~ DataDims (Backend t n))
dataTypeDims _ = unsafeCoerce (Dict @(t ~ t, n ~ n))

--  Hmm, would be interesting to "provide" KnownBackend (Backend t (n+1))
bCons :: forall t n
       . KnownBackend (Backend t n)
      => t -> Backend t n -> Backend t (n + 1)
bCons a as = case dataTypeDims @t @n as of
  Dict -> case bSing @(Backend t n) of
    BS0 -> ScalarBase a
    BS1 -> case as of ScalarBase b -> Vec2Base a b
    BS2 -> case as of Vec2Base b c -> ListBase [a,b,c]
    BSn -> case as of ListBase as' -> unsafeCoerce (ListBase (a : as'))

bNil :: Backend t 0
bNil = UnitBase
