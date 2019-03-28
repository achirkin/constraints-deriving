{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
module Spec.DeriveAll06 where

import Data.Constraint.Deriving

data Bar = Bar | Baz
  deriving (Eq, Ord, Show, Read, Enum)

{-# ANN type Foo (DeriveAllBut ["Show", "Read"]) #-}
newtype Foo a b = Foo Bar
