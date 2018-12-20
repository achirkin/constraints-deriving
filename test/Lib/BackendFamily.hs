{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Lib.BackendFamily
  ( UnitBase (..), ScalarBase (..), Vec2Base (..), ListBase (..)
  , Backend, DataElemType, DataDims
  , KnownBackend (..)
  , BackendSing ()
  , InferBackendInstance (..)
  ) where


import           Data.Constraint
import           Data.Constraint.Bare
import           Data.Semigroup
import           Debug.Trace
import           GHC.Base
import           GHC.TypeLits         (KnownNat, Nat, natVal)

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
    BS0 :: Backend t 0 ~ UnitBase t   => BackendSing (UnitBase t)
    BS1 :: Backend t 1 ~ ScalarBase t => BackendSing (ScalarBase t)
    BS2 :: Backend t 2 ~ Vec2Base t   => BackendSing (Vec2Base t)
    BSn :: Backend t n ~ ListBase t n => BackendSing (ListBase t n)

deriving instance Eq (BackendSing backend)
deriving instance Ord (BackendSing backend)
deriving instance Show (BackendSing backend)


-- | A framework for using Array type family instances.
class KnownBackend (t :: Type) where
    -- | Get Array type family instance
    bSing :: BackendSing t



















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
  Vec2Base a1 a2 <> Vec2Base b1 b2 = Vec2Base (a1 + b1) (a2 * b2)

instance Num t => Monoid (Vec2Base t) where
  mempty = Vec2Base 0 1
  mappend = (<>)

instance Num t => Semigroup (ListBase t n) where
  ListBase as <> ListBase bs = ListBase $ zipWith (*) as bs

instance (Num t, KnownNat n) => Monoid (ListBase t n) where
  mempty = r
    where
      r = ListBase $ replicate (fromInteger $ natVal r) 1
  mappend = (<>)




instance HasDict (KnownBackend backend) (BackendSing backend) where
  evidence ds = reifyBackendSing ds Dict
  {-# INLINE evidence #-}

reifyBackendSing :: forall backend r
                  . BackendSing backend -> ( KnownBackend backend => r) -> r
reifyBackendSing as k
  = unsafeCoerce# (MagicBackendSing k :: MagicBackendSing backend r) as
{-# INLINE reifyBackendSing #-}
newtype MagicBackendSing (backend :: Type) (r :: Type)
  = MagicBackendSing (KnownBackend backend => r)



instance KnownBackend (UnitBase t) where
    bSing = BS0
instance KnownBackend (ScalarBase t) where
    bSing = BS1
instance KnownBackend (Vec2Base t) where
    bSing = BS2
instance KnownBackend (ListBase t n) where
    bSing = case ( unsafeCoerce#
                     (Dict :: Dict (ListBase t n ~ ListBase t n) )
                           :: Dict (ListBase t n ~ Backend  t n)
                 ) of
      Dict -> BSn



class InferBackendInstance (backend :: Type) (c :: Type -> Constraint) where
    inferBackendInstance :: BareConstraint (c backend)

instance {-# OVERLAPPABLE #-}
         ( KnownBackend b
         , c (UnitBase (DataElemType b))
         , c (ScalarBase (DataElemType b))
         , c (Vec2Base (DataElemType b))
         , c (ListBase (DataElemType b) (DataDims b))
         ) => InferBackendInstance b c where
    inferBackendInstance = dictToBare $ case (bSing :: BackendSing b) of
          BS0 -> trace "---------- Selecting UnitBase" Dict
          BS1 -> trace "---------- Selecting ScalarBase" Dict
          BS2 -> trace "---------- Selecting Vec2Base" Dict
          BSn -> trace "---------- Selecting ListBase" Dict
    {-# INLINE inferBackendInstance #-}

