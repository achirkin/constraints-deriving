{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
module Spec.ClassDict02 where

import Data.Constraint
import Data.Constraint.Deriving

-- Here check test/out/ClassDict02.stderr to see what happens if the type of this
-- function does not correspond to the class declaration
{-# ANN defineOrd ClassDict #-}
defineOrd :: Eq a
          => (a -> a -> Ordering)
          -> Dict (Ord a)
defineOrd = defineOrd
