{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
module Spec.DeriveAll05 where

import Data.Constraint.Deriving

data family AB x
data instance AB _ = B deriving Eq

{-# ANN type BazTy DeriveAll #-}
newtype BazTy a = BazCon (AB a)

