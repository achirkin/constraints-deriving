{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
module Spec.ToInstance02 where

{-
Testing that variables, such as deriveEqOrig, may have TyVars (forall t);
ToInstance pass should be able to go through the vars and theta types and match
the RHS of the arrow (deriveEqOrig signature).
 -}
import Data.Constraint
import Data.Constraint.Deriving
import Data.Constraint.Unsafe

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
deriveEq :: forall t . KnownNumber t => Dict (Eq (Number t))
deriveEq = deriveEqOrig

deriveEqOrig :: forall t . KnownNumber t => Dict (Eq (Number t))
deriveEqOrig = deriveIt numberSing
{-# NOINLINE deriveEqOrig #-}

deriveIt :: (c Double, c Int) => NumberSing t -> Dict (c (Number t))
deriveIt NumInt    = mapDict (unsafeDerive Number) Dict
deriveIt NumDouble = mapDict (unsafeDerive Number) Dict
