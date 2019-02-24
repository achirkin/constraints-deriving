{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
module Spec.DeriveAll01 where

import Data.Constraint.Deriving


data family FooFam a b
data instance FooFam Int b = FooInt b Int
  deriving Eq
data instance FooFam Double b = FooDouble Double b b
  deriving Read
data instance FooFam Float Float = FooFloats Float Float
  deriving (Eq, Ord)
data instance FooFam Float String = FooString Float String
  deriving Show

{-# ANN type TestNewtype1 DeriveAll #-}
newtype TestNewtype1 a b = TestNewtype1C (FooFam a b)

{-# ANN type TestNewtype2 DeriveAll #-}
newtype TestNewtype2 a b r = TestNewtype2C r
type instance DeriveContext (TestNewtype2 a b r) = FooFam a b ~ r
