{-
Copyright 2011-2015 Edward Kmett

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS OR
IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED.  IN NO EVENT SHALL THE AUTHORS OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.
 -}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Unsafe #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint.Unsafe
-- Copyright   :  (C) 2011-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module is taken from
-- <https://github.com/ekmett/constraints/blob/963c0e904ad48a5cec29a0cb649622d8c1872af4/src/Data/Constraint/Unsafe.hs constraints:Data.Constraint.Unsafe>
-- A few things have been cut from the module.
--
----------------------------------------------------------------------------
module Data.Constraint.Unsafe
  ( Coercible
  , unsafeCoerceConstraint
  , unsafeDerive
  , unsafeUnderive
  ) where

import Data.Coerce
import Data.Constraint
import Unsafe.Coerce

-- | Coerce a dictionary unsafely from one type to another
unsafeCoerceConstraint :: a :- b
unsafeCoerceConstraint = unsafeCoerce refl

-- | Coerce a dictionary unsafely from one type to a newtype of that type
unsafeDerive :: Coercible n o => (o -> n) -> t o :- t n
unsafeDerive _ = unsafeCoerceConstraint

-- | Coerce a dictionary unsafely from a newtype of a type to the base type
unsafeUnderive :: Coercible n o => (o -> n) -> t n :- t o
unsafeUnderive _ = unsafeCoerceConstraint
