{-# LANGUAGE CPP #-}
module Data.Constraint.Deriving.Import (module Reexport) where

#if __GLASGOW_HASKELL__ >= 900
import GHC.Core.Class            as Reexport (Class, classTyCon)
import GHC.Core.Coercion.Axiom   as Reexport
import GHC.Core.FamInstEnv       as Reexport
import GHC.Core.InstEnv          as Reexport hiding (OverlapMode (..))
import GHC.Core.Predicate        as Reexport
import GHC.Core.Unify            as Reexport
import GHC.Driver.Finder         as Reexport
import GHC.Iface.Env             as Reexport
import GHC.Iface.Load            as Reexport
import GHC.Plugins               as Reexport hiding (OverlapMode (..), UniqFM, empty, varName)
import GHC.Tc.Utils.Monad        as Reexport (TcM, getEps, initTc)
import GHC.Tc.Utils.TcType       as Reexport (tcSplitDFunTy)
import GHC.Types.Avail           as Reexport (AvailInfo (..), availName, filterAvails)
import GHC.Types.Name.Occurrence as Reexport (varName)
import GHC.Utils.Error           as Reexport (Severity (..), pprErrMsgBagWithLoc)
import GHC.Utils.Monad           as Reexport (MonadIO (..))
import GHC.Utils.Panic           as Reexport (panicDoc)
#else
import Avail      as Reexport
import Class      as Reexport (Class, classTyCon)
import CoAxiom    as Reexport
import ErrUtils   as Reexport (Severity (..), pprErrMsgBagWithLoc)
import FamInstEnv as Reexport
import Finder     as Reexport (findImportedModule)
import GhcPlugins as Reexport hiding (OverlapMode (..), empty, varName)
import IfaceEnv   as Reexport
import InstEnv    as Reexport hiding (OverlapMode (..))
import LoadIface  as Reexport (loadModuleInterface, loadModuleInterfaces)
import MonadUtils as Reexport (MonadIO (..))
import Name       as Reexport (varName)
import Panic      as Reexport (panicDoc)
import TcRnMonad  as Reexport (getEps, initTc)
import TcRnTypes  as Reexport (TcM)
import TcType     as Reexport (tcSplitDFunTy)
import Unify      as Reexport
#if __GLASGOW_HASKELL__ >= 810
import Predicate as Reexport
#endif
#if __GLASGOW_HASKELL__ < 802
import GHC.Stack as Reexport (HasCallStack)
#endif
#endif

import Data.Constraint.Deriving.Compat as Reexport
