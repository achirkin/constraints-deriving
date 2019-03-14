{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RoleAnnotations      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
{- |
  This is where the magic happens.

  Via combination of DeriveAll and ToInstance plugin passes
  I create a system of overlapping type class instances for `VecBackend` type.
  This way, if GHC knows which backend (type instance of `Backend`) is behind `VecBackend`,
  it can select overlapping class instance for it;
  overwise, it selects overlappable instance based on `KnownBackend` constraint.
  -}
module Lib.VecBackend where


import Data.Constraint
import Data.Constraint.Deriving
import Data.Constraint.Unsafe
import GHC.Base
import GHC.TypeLits             (KnownNat, Nat)
import Unsafe.Coerce
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif

import Lib.BackendFamily

-- Try to comment out the annotation;
-- You will see that the compiler has to select type class instances at runtime more often.
{-# ANN type VecBackend DeriveAll #-}
type role VecBackend phantom phantom representational
-- I need two layers of wrappers to provide default overlappable instances to
-- all type classes using KnownBackend mechanics.
-- Type arguments are redundant here;
-- nevertheless, they improve readability of error messages.
newtype VecBackend (t :: Type) (n :: Nat) (backend :: Type)
  = VecBackend { _getBackend :: backend }
type instance DataElemType (VecBackend t _ _) = t
type instance DataDims (VecBackend _  n _) = n
-- I use this type instance to inform `DeriveAll` core plugin that backend is an instance
-- of type family `Backend t n`.
-- This allows the plugin to find all possible instances of the type family and
-- then lookup corresponding class instances.
-- Otherwise, the plugin would have to derive all instances for all types in scope,
-- because the newtype declaration is too general without these additional constraints.
type instance DeriveContext (VecBackend t n b) = b ~ Backend t n



{-# ANN inferEq (ToInstance Overlappable) #-}
inferEq :: forall t n b . ( KnownBackend b, Eq t) => Dict (Eq (VecBackend t n b))
inferEq = mapDict toVecBackend
        . mapDict (Sub inferBackendInstance)
        $ inferBase @t @n @b undefined

{-# ANN inferShow (ToInstance Overlappable) #-}
inferShow :: forall t n b . ( KnownBackend b, Show t)
          => Dict (Show (VecBackend t n b))
inferShow = mapDict toVecBackend
          . mapDict (Sub inferBackendInstance)
          $ inferBase @t @n @b undefined

{-# ANN inferOrd (ToInstance Overlappable) #-}
inferOrd :: forall t n b . ( KnownBackend b, Ord t)
         => Dict (Ord (VecBackend t n b))
inferOrd = mapDict toVecBackend
         . mapDict (Sub inferBackendInstance)
         $ inferBase @t @n @b undefined

{-# ANN inferSemigroup (ToInstance Overlappable) #-}
inferSemigroup :: forall t n b . ( KnownBackend b, Num t)
               => Dict (Semigroup (VecBackend t n b))
inferSemigroup = mapDict toVecBackend
               . mapDict (Sub inferBackendInstance)
               $ inferBase @t @n @b undefined

{-# ANN inferMonoid (ToInstance Overlappable) #-}
inferMonoid :: forall t n b . ( KnownBackend b, Num t, KnownNat n)
            => Dict (Monoid (VecBackend t n b))
inferMonoid = mapDict toVecBackend
            . mapDict (Sub inferBackendInstance)
            $ inferBase @t @n @b undefined

-- This is the rule that cannot be encoded in the type system, but enforced
-- as an invariant: VecBackend t n b implies DeriveContext t n b
inferBase :: VecBackend t n b
          -> Dict (b ~ Backend t n, t ~ DataElemType b, n ~ DataDims b)
inferBase _ = unsafeCoerce
  (Dict :: Dict (b ~ b, t ~ t, n ~ n) )
{-# INLINE inferBase #-}

-- VecBackend is the newtype wrapper over b.
-- It has the same represenation and I expect it to have the same instance behavior.
toVecBackend :: forall c t n b . c b :- c (VecBackend t n b)
toVecBackend = unsafeDerive VecBackend
{-# INLINE toVecBackend #-}
