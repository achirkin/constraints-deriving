{-# LANGUAGE CPP #-}
module Data.Constraint.Deriving
  ( plugin
    -- * DeriveAll pass
  , DeriveAll (..)
  , DeriveContext
    -- * ToInstance pass
  , ToInstance (..)
  , OverlapMode (..)
  ) where


#if MIN_VERSION_ghc(8,6,0)
import GhcPlugins (CoreM, CoreToDo, Plugin (..), defaultPlugin, purePlugin)
#else
import GhcPlugins (CoreM, CoreToDo, Plugin (..), defaultPlugin)
#endif


import Data.Constraint.Deriving.DeriveAll
import Data.Constraint.Deriving.ToInstance



-- | To use the plugin, add
--
-- @
-- {\-\# OPTIONS_GHC -fplugin Data.Constraint.Deriving \#-\}
-- @
--
-- To the header of your file.
plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = const install
#if MIN_VERSION_ghc(8,6,0)
  , pluginRecompile = purePlugin
#endif
  }

install :: [CoreToDo] -> CoreM [CoreToDo]
install todo = do
  eref <- initCorePluginEnv
  return ( deriveAllPass eref
         : toInstancePass eref
         : todo)

