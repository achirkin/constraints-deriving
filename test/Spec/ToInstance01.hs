{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
module Spec.ToInstance01 where

{-
This is a minimal example for deriving multiple instances
for a newtype over a type family.

The plugin provides two advantages over manually implementing instances using singletons:

  * No need to implement every class function manually

  * Instance elaboration at the call site happens only once for many used functions,
    rather than once for every fuction usage.
 -}
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Constraint.Deriving

newtype Number t = Number (NumberFam t)

type family NumberFam t where
  NumberFam Int = Int
  NumberFam Double = Double

data NumberSing t where
  NumInt    :: NumberSing Int
  NumDouble :: NumberSing Double

class    KnownNumber t      where numberSing :: NumberSing t
instance KnownNumber Int    where numberSing = NumInt
instance KnownNumber Double where numberSing = NumDouble

{-# ANN deriveEq (ToInstance NoOverlap) #-}
deriveEq :: KnownNumber t => Dict (Eq (Number t))
deriveEq = deriveIt numberSing

{-# ANN deriveOrd (ToInstance NoOverlap) #-}
deriveOrd :: KnownNumber t => Dict (Ord (Number t))
deriveOrd = deriveIt numberSing

{-# ANN deriveNum (ToInstance NoOverlap) #-}
deriveNum :: KnownNumber t => Dict (Num (Number t))
deriveNum = deriveIt numberSing

deriveIt :: (c Double, c Int) => NumberSing t -> Dict (c (Number t)) 
deriveIt NumInt    = mapDict (unsafeDerive Number) Dict
deriveIt NumDouble = mapDict (unsafeDerive Number) Dict