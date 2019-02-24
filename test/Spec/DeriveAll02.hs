{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
module Spec.DeriveAll02 where

import Data.Constraint.Deriving


type family FooFam a b c

type instance FooFam Int Int Double = D
type instance FooFam a Float a = Float
type instance FooFam String String b = String

newtype D = D Double
  deriving (Eq, Ord, Show, Read)

{-# ANN type TestNewtypeDirect DeriveAll #-}
newtype TestNewtypeDirect a b c = ConDirect (FooFam a b c)

{-# ANN type TestNewtypeContextual DeriveAll #-}
newtype TestNewtypeContextual a b c r = ConContextual r
type instance DeriveContext (TestNewtypeContextual a b c r) = FooFam a b c ~ r
