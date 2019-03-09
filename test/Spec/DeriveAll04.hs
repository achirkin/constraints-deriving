{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
module Spec.DeriveAll04 where

import Data.Constraint.Deriving

{-
  Here, I want to test overlapping type families
 -}
data ListTy
data MaybeTy

data A = ACon deriving Eq
data B = BCon deriving Eq

type family AB x where
  AB A = A
  AB _ = B

{-# ANN type BazTy DeriveAll #-}
newtype BazTy a = BazCon (AB a)
