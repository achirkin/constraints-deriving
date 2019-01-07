{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
module Spec.DeriveAll01 where

import Data.Constraint.Deriving


data family FooFam a b
data instance FooFam Int b = FooInt b Int
data instance FooFam Double b = FooDouble Double b b
data instance FooFam Float Float = FooFloats Float Float
data instance FooFam Float String = FooString Float String



{-# ANN type TestData DeriveAll #-}
{-# ANN type TestNewtype1 DeriveAll #-}
{-# ANN type TestNewtype2 DeriveAll #-}
{-# ANN TestNewtype2C DeriveAll #-}
{-# ANN TestNewtype2C DeriveAll #-}

data TestData a = TData a a Int
newtype TestNewtype1 a b = TestNewtype1C (FooFam a b)
newtype TestNewtype2 a b r = TestNewtype2C (FooFam a b)
type instance DeriveContext (TestNewtype2 a b r) = FooFam a b ~ r

{-# ANN type TestNewtype3 DeriveAll #-}
newtype TestNewtype3 a = TestNewtype3C a
-- Enumerate specific instances
type instance DeriveContext (TestNewtype3 Bool) = ()
type instance DeriveContext (TestNewtype3 Int)  = ()
type instance DeriveContext (TestNewtype3 (Maybe a)) = ()


{-# ANN type Newclass DeriveAll #-}
class Newclass a where
  hereAmI :: a

{-# ANN type Properclass DeriveAll #-}
class Properclass a where
  p1 :: a
  p2 :: (a, a)

{-# ANN type TestTypeType DeriveAll #-}
type TestTypeType t n = TestNewtype1 t n




