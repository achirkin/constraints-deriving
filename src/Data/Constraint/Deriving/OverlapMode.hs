{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveDataTypeable  #-}
module Data.Constraint.Deriving.OverlapMode
  ( OverlapMode (..)
  , toOverlapFlag, instanceOverlapMode
  ) where

import           Data.Data           (Data)
import           Data.Semigroup      as Sem (Semigroup (..))
import           Data.Monoid         as Mon (Monoid (..))

#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Types.Basic as BasicTypes
import qualified GHC.Core.InstEnv as InstEnv
#else
import qualified BasicTypes
import qualified InstEnv
#endif

-- | Define the behavior for the instance selection.
--   Mirrors `BasicTypes.OverlapMode`, but does not have a `SourceText` field.
data OverlapMode
  = NoOverlap
    -- ^ This instance must not overlap another `NoOverlap` instance.
    --   However, it may be overlapped by `Overlapping` instances,
    --   and it may overlap `Overlappable` instances.
  | Overlappable
    -- ^ Silently ignore this instance if you find a
    --   more specific one that matches the constraint
    --   you are trying to resolve
  | Overlapping
    -- ^ Silently ignore any more general instances that may be
    --   used to solve the constraint.
  | Overlaps
    -- ^ Equivalent to having both `Overlapping` and `Overlappable` flags.
  | Incoherent
    -- ^ Behave like Overlappable and Overlapping, and in addition pick
    --   an an arbitrary one if there are multiple matching candidates, and
    --   don't worry about later instantiation
  deriving (Eq, Show, Read, Data)

instance Sem.Semigroup OverlapMode where
    NoOverlap <> m = m
    m <> NoOverlap = m
    Incoherent <> _ = Incoherent
    _ <> Incoherent = Incoherent
    Overlaps <> _   = Overlaps
    _ <> Overlaps   = Overlaps
    Overlappable <> Overlappable = Overlappable
    Overlapping  <> Overlapping  = Overlapping
    Overlappable <> Overlapping  = Overlaps
    Overlapping  <> Overlappable = Overlaps

instance Mon.Monoid OverlapMode where
    mempty = NoOverlap
#if !(MIN_VERSION_base(4,11,0))
    mappend = (<>)
#endif


toOverlapFlag :: OverlapMode -> BasicTypes.OverlapFlag
toOverlapFlag m = BasicTypes.OverlapFlag (getOMode m) False
  where
    getOMode NoOverlap    = BasicTypes.NoOverlap noSourceText
    getOMode Overlapping  = BasicTypes.Overlapping noSourceText
    getOMode Overlappable = BasicTypes.Overlappable noSourceText
    getOMode Overlaps     = BasicTypes.Overlaps noSourceText
    getOMode Incoherent   = BasicTypes.Incoherent noSourceText

#if __GLASGOW_HASKELL__ >= 802
    noSourceText = BasicTypes.NoSourceText
#else
    noSourceText = "[plugin-generated code]"
#endif

instanceOverlapMode :: InstEnv.ClsInst -> OverlapMode
instanceOverlapMode i = case BasicTypes.overlapMode (InstEnv.is_flag i) of
    BasicTypes.NoOverlap {}    -> NoOverlap
    BasicTypes.Overlapping {}  -> Overlapping
    BasicTypes.Overlappable {} -> Overlappable
    BasicTypes.Overlaps {}     -> Overlaps
    BasicTypes.Incoherent {}   -> Incoherent
