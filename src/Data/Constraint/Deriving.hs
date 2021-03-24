{-# LANGUAGE CPP #-}
module Data.Constraint.Deriving
  ( plugin
    -- * DeriveAll pass
  , DeriveAll (..)
  , DeriveContext
    -- * ToInstance pass
  , ToInstance (..)
  , OverlapMode (..)
    -- * ClassDict pass
  , ClassDict (..)
  ) where

import Data.List (sortOn)

import Data.Constraint.Deriving.ClassDict
import Data.Constraint.Deriving.DeriveAll
import Data.Constraint.Deriving.Import
import Data.Constraint.Deriving.ToInstance


-- | To use the plugin, add
--
-- @
-- {\-\# OPTIONS_GHC -fplugin Data.Constraint.Deriving \#-\}
-- @
--
-- to the header of your file.
--
-- For debugging, add a plugin option @dump-instances@
--
-- @
-- {\-\# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances \#-\}
-- @
--
-- to the header of your file; it will print all instances declared in the module
-- (hand-written and auto-generated).
--
plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
#if __GLASGOW_HASKELL__ >= 860
  , pluginRecompile = purePlugin
#endif
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install cmdopts todo = do
    eref <- initCorePluginEnv
    return ( deriveAllPass eref
           : classDictPass eref
           : toInstancePass eref
           : if "dump-instances" `elem` cmdopts
             then dumpInstances:todo
             else todo
           )


-- | Just print all instance signatures in this module
dumpInstances :: CoreToDo
dumpInstances = CoreDoPluginPass "Data.Constraint.Deriving.DumpInstances"
              $ \guts -> guts <$ go (mg_insts guts)
  where
    locdoc i = ( ( getOccString $ is_cls i
                 , map (fmap getOccString . tyConAppTyCon_maybe)
                   $ is_tys i
                 ), ppr i)
    go is = do
      let is' = sortOn fst $ map locdoc is
      putMsg $
        blankLine
        $+$
        hang
          (text "============ Class instances declared in this module ============")
          2 (vcat $ map snd is')
        $+$
        blankLine
