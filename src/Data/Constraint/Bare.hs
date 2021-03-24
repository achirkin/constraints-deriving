{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint.Bare
-- Copyright   :  (c) 2019 Artem Chirkin
-- License     :  BSD3
-- Portability :  non-portable
--
-- Extract a Constraint from a Dict to manipulate it as a plain value.
-- It is supposed to be used in compiler plugins
--   -- to move around instances of type classes.
--
-----------------------------------------------------------------------------
module Data.Constraint.Bare
  ( BareConstraint, pattern DictValue
  , dictToBare, bareToDict
  , withBareConstraint
  ) where


import Data.Constraint (Dict (..))
import GHC.Base        (Constraint, Type)
import GHC.Exts        (unsafeCoerce#)

-- | An unsafeCoerced pointer to a Constraint, such as a class function dictionary.
data BareConstraint :: Constraint -> Type

-- | Extract the constraint inside the Dict GADT as if it was
--   an ordinary value of kind `Type`.
--
--   It exploits the feature of the GHC core language
--    -- representing constraints as ordinary type arguments of a function.
--   Thus, I unsafeCoerce between a function with one argument and a function
--    with no arguments and one constraint.
--
--   This pattern has never been tested with multiple constraints.
pattern DictValue :: BareConstraint c -> Dict c
pattern DictValue c <- (dictToBare -> c)
  where
    DictValue c = bareToDict c

#if __GLASGOW_HASKELL__ >= 802
{-# COMPLETE DictValue #-}
#endif

-- | Extract a `Constraint` from a `Dict`
dictToBare :: forall c . Dict c -> BareConstraint c
dictToBare Dict = case (unsafeCoerce# id :: Magic c (BareConstraint c)) of Magic c -> c
{-# INLINE dictToBare #-}

-- | Wrap a `Constraint` into a `Dict`
bareToDict :: forall c . BareConstraint c -> Dict c
bareToDict = unsafeCoerce# (Magic Dict :: Magic c (Dict c))
{-# INLINE bareToDict #-}

-- | Provide a constraint to a function using `BareConstraint`.
--   This allows to provide constraints on-demand (lazily), rather than eagerly
--   pattern-matching against `Dict` before executing the function.
withBareConstraint :: forall c r . BareConstraint c -> (c => r) -> r
withBareConstraint bc f = unsafeCoerce# (Magic f :: Magic c r) bc

newtype Magic c r = Magic (c => r)
