{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RoleAnnotations            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}

module Lib.VecBackend
  ( VecBackend(..)
  , inferEq, inferOrd, inferShow, inferSemigroup, inferMonoid
  )
where


import           Data.Constraint
import           Data.Constraint.Bare
import           Data.Constraint.Deriving
import           Data.Semigroup
import           GHC.Base
import           GHC.TypeLits         (KnownNat, Nat)
import           Unsafe.Coerce

import           Lib.BackendFamily


type role VecBackend phantom phantom representational
-- I need two layers of wrappers to provide default overlappable instances to
-- all type classes using KnownBackend mechanics.
-- Type arguments are redundant here;
-- nevertheless, they improve readability of error messages.
newtype VecBackend (t :: Type) (n :: Nat) (backend :: Type)
  = VecBackend { _getBackend :: backend }
type instance DataElemType (VecBackend t _ _) = t
type instance DataDims (VecBackend _  n _) = n

-- -- Note, deriving KnownBackend goes in a not intuitive way:
-- -- VecBackend t n b ==> DataFrame t n ==> Backend t n;
-- -- this way, I may be able to not expose VecBackend in user error messages.
-- instance KnownBackend (DataFrame t n) => KnownBackend (VecBackend t n b) where
--   bSing = unsafeCoerce# (bSing :: BackendSing (DataFrame t n))
--   {-# INLINE bSing #-}



{-# ANN inferEq ToInstanceOverlappable #-}
inferEq :: forall t n b . ( KnownBackend b, Eq t) => BareConstraint (Eq (VecBackend t n b))
inferEq = case inferBase @t @n @b undefined of
  Dict -> toVecBackend @Eq @t @n @b $ inferBackendInstance

{-# ANN inferShow ToInstanceOverlappable #-}
inferShow :: forall t n b . ( KnownBackend b, Show t)
          => BareConstraint (Show (VecBackend t n b))
inferShow = case inferBase @t @n @b undefined of
  Dict -> toVecBackend @Show @t @n @b $ inferBackendInstance


{-# ANN inferOrd ToInstanceOverlappable #-}
inferOrd :: forall t n b . ( KnownBackend b, Ord t)
          => BareConstraint (Ord (VecBackend t n b))
inferOrd = case inferBase @t @n @b undefined of
  Dict -> toVecBackend @Ord @t @n @b $ inferBackendInstance

{-# ANN inferSemigroup ToInstanceOverlappable #-}
inferSemigroup :: forall t n b . ( KnownBackend b, Num t)
          => BareConstraint (Semigroup (VecBackend t n b))
inferSemigroup = case inferBase @t @n @b undefined of
  Dict -> toVecBackend @Semigroup @t @n @b $ inferBackendInstance


{-# ANN inferMonoid ToInstanceOverlappable #-}
inferMonoid :: forall t n b . ( KnownBackend b, Num t, KnownNat n)
          => BareConstraint (Monoid (VecBackend t n b))
inferMonoid = case inferBase @t @n @b undefined of
  Dict -> toVecBackend @Monoid @t @n @b $ inferBackendInstance



inferBase :: VecBackend t n b -> Dict (b ~ Backend t n, t ~ DataElemType b, n ~ DataDims b)
inferBase _ = unsafeCoerce
  (Dict :: Dict (b ~ b, t ~ t, n ~ n) )
{-# INLINE inferBase #-}


toVecBackend :: forall c t n b . BareConstraint (c b) -> BareConstraint (c (VecBackend t n b))
toVecBackend = unsafeCoerce
{-# INLINE toVecBackend #-}
