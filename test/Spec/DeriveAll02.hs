{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
module Spec.DeriveAll02 where

import Data.Constraint.Deriving


data FooData a b c = FooDataCon Float b
  deriving (Eq, Ord)

instance (a ~ Int, Show b) => Show (FooData a b c) where
  show (FooDataCon f b) = "FooDataCon " ++ show f ++ " " ++ show b


type family FooFam a b c d e f
type instance FooFam a b c Double e f = FooData Int b c

class Ord b => FooClass a b c where
  fooFun :: a -> b -> c
  barFun :: a -> c -> b

instance (a ~ Int, Ord b, Show a) => FooClass (FooData a b c) b Float where
  fooFun (FooDataCon f _) _ = f
  barFun (FooDataCon _ b) _ = b


{-# ANN type BazTy DeriveAll #-}
newtype BazTy a b c d e f = BazCon (FooFam a b c d e f)

-- Type class constraints are prepended to the instance arguments.
-- Thus, they can be used to impose additional (fictional) constraints
-- on the generated instances.
type instance DeriveContext (BazTy a b c d e f ) = Show e
