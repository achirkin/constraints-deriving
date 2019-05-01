{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
module Spec.DeriveAll03 where

import Data.Constraint.Deriving

{-
  Here I test three different things:

  * Deriving instances for the types defined elsewhere
    (including the base library);
    it should produce a lot of instances for all transitively
    reachable modules.

  * Closed, injective type families - should not be a problem.

  * Higher-kinded types;
    The following should produce instances for kind `Type`
     (e.g. Show, Monoid)
    as well as for kind `Type -> Type`
     (e.g. Functor, Monad)
 -}
data ListTy
data MaybeTy

type family FooFam m = r | r -> m where
  FooFam ListTy = []
  FooFam MaybeTy = Maybe

{-# ANN type BazTy DeriveAll #-}
newtype BazTy m a = BazCon (FooFam m a)
