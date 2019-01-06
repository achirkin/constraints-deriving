{-# LANGUAGE CPP        #-}
{-# LANGUAGE LambdaCase #-}
module Data.Constraint.Deriving.CorePluginM
  ( CorePluginM (), runCorePluginM
  , CorePluginEnv (), initCorePluginEnv
  , liftCoreM, liftIO, lookupName
    -- * Error handling
  , try, exception
    -- * Accessing read-only on-demand variables
  , ask
  , tyConDict, tyConBareConstraint, tyConDeriveContext
  , funDictToBare, tyEmptyConstraint, classTypeEq
    -- * Reporting
  , pluginWarning, pluginLocatedWarning
  , pluginError, pluginLocatedError
  ) where


import           Class         (Class)
import           Control.Monad (join)
import           Data.IORef    (IORef, modifyIORef', newIORef, readIORef)
import qualified ErrUtils
import qualified Finder
import           GhcPlugins
import qualified IfaceEnv
import           MonadUtils    (MonadIO (..))
#if __GLASGOW_HASKELL__ < 806
import qualified TcRnMonad     (initTcForLookup)
#endif


-- | Since I do not have access to the guts of CoreM monad,
--   I implement a wrapper on top of it here.
--
--   It provides two pieces of functionality:
--
--     * Possibility to fail a computation
--       (to show a nice error to a user and continue the work if possible);
--
--     * An environment with things that computed on demand, once at most.
--
data CorePluginM a = CorePluginM
  { runCorePluginM :: IORef CorePluginEnv -> CoreM (Maybe a) }

instance Functor CorePluginM where
  fmap f m = CorePluginM $ \e -> fmap f <$> runCorePluginM m e

instance Applicative CorePluginM where
  pure = CorePluginM . const . pure . Just
  mf <*> ma = CorePluginM $ \e -> (<*>) <$> runCorePluginM mf e <*> runCorePluginM ma e

instance Monad CorePluginM where
  return = pure
  ma >>= k = CorePluginM $ \e -> runCorePluginM ma e >>= \case
    Nothing -> pure Nothing
    Just a  -> runCorePluginM (k a) e

instance MonadIO CorePluginM where
  liftIO = liftCoreM . liftIO

instance MonadThings CorePluginM where
  lookupThing = liftCoreM . lookupThing

instance MonadUnique CorePluginM where
  getUniqueSupplyM = CorePluginM $ const $ Just <$> getUniqueSupplyM


-- | Wrap CoreM action
liftCoreM :: CoreM a -> CorePluginM a
liftCoreM = CorePluginM . const . fmap Just

-- | Synonym for `fail`
exception :: CorePluginM a
exception = CorePluginM $ const $ pure Nothing

-- | Return `Nothing` if the computation fails
try :: CorePluginM a -> CorePluginM (Maybe a)
try m = CorePluginM $ fmap Just . runCorePluginM m

-- | Plugin environment
--
--   Its components are supposed to be computed at most once, when they are needed.
data CorePluginEnv = CorePluginEnv
  { modConstraint         :: CorePluginM Module
  , modConstraintBare     :: CorePluginM Module
  , modConstraintDeriving :: CorePluginM Module
  , modDataTypeEquality   :: CorePluginM Module
  , tyConDict             :: CorePluginM TyCon
  , tyConBareConstraint   :: CorePluginM TyCon
  , tyConDeriveContext    :: CorePluginM TyCon
  , funDictToBare         :: CorePluginM Id
  , tyEmptyConstraint     :: CorePluginM Type
  , classTypeEq           :: CorePluginM Class
  }

-- | Ask a field of the CorePluginEnv environment.
ask :: (CorePluginEnv -> CorePluginM a) -> CorePluginM a
ask f = join $ CorePluginM $ liftIO . fmap (Just . f) . readIORef

-- | Init the `CorePluginM` environment and save it to IORef
initCorePluginEnv :: CoreM (IORef CorePluginEnv)
initCorePluginEnv = liftIO $ newIORef defCorePluginEnv

-- | Lookup necessary environment components on demand.
defCorePluginEnv :: CorePluginEnv
defCorePluginEnv = CorePluginEnv
    { modConstraint = do
        mm <- try $ lookupModule mnConstraint [pnConstraintsDeriving, pnConstraints]
        saveAndReturn mm $ \a e -> e { modConstraint = a }

    , modConstraintBare = do
        mm <- try $ lookupModule mnConstraintBare [pnConstraintsDeriving]
        saveAndReturn mm $ \a e -> e { modConstraintBare = a }

    , modConstraintDeriving = do
        mm <- try $ lookupModule mnConstraintDeriving [pnConstraintsDeriving]
        saveAndReturn mm $ \a e -> e { modConstraintDeriving = a }

    , modDataTypeEquality = do
        mm <- try $ lookupModule mnDataTypeEquality [pnBase]
        saveAndReturn mm $ \a e -> e { modDataTypeEquality = a }

    , tyConDict = do
        m <- ask modConstraint
        mtc <- try $ lookupName m tnDict >>= lookupTyCon
        saveAndReturn mtc $ \a e -> e { tyConDict = a }

    , tyConBareConstraint = do
        m <- ask modConstraintBare
        mtc <- try $ lookupName m tnBareConstraint >>= lookupTyCon
        saveAndReturn mtc $ \a e -> e { tyConBareConstraint = a }

    , tyConDeriveContext = do
        m <- ask modConstraintDeriving
        mtc <- try $ lookupName m tnDeriveContext >>= lookupTyCon
        saveAndReturn mtc $ \a e -> e { tyConDeriveContext = a }

    , funDictToBare = do
        m <- ask modConstraintBare
        mf <- try $ lookupName m vnDictToBare >>= lookupId
        saveAndReturn mf $ \a e -> e { funDictToBare = a }

    , tyEmptyConstraint = do
        ec <- flip mkTyConApp [] <$> lookupTyCon (cTupleTyConName 0)
        saveAndReturn (Just ec) $ \a e -> e { tyEmptyConstraint = a }

    , classTypeEq = do
        m <- ask modDataTypeEquality
        mc <- try $ lookupName m cnTypeEq >>= lookupThing >>= \case
          ATyCon tc | Just cls <- tyConClass_maybe tc
            -> return cls
          _ -> exception
        saveAndReturn mc $ \a e -> e { classTypeEq = a }
    }
  where
    saveAndReturn Nothing  f = CorePluginM $ \eref ->
      Nothing <$ liftIO (modifyIORef' eref $ f exception)
    saveAndReturn (Just x) f = CorePluginM $ \eref ->
      Just x  <$ liftIO (modifyIORef' eref $ f (pure x))



lookupName :: Module -> OccName -> CorePluginM Name
lookupName m occn = do
    hscEnv <- liftCoreM getHscEnv
    liftIO
#if __GLASGOW_HASKELL__ < 806
        $ TcRnMonad.initTcForLookup hscEnv
        $ IfaceEnv.lookupOrig m occn
#else
        $ IfaceEnv.lookupOrigIO hscEnv m occn
#endif

lookupModule :: ModuleName
             -> [FastString]
             -> CorePluginM Module
lookupModule mdName pkgs = do
    hscEnv <- liftCoreM getHscEnv
    go hscEnv $ map Just pkgs ++ [Just (fsLit "this"), Nothing]
  where
    go _ [] = pluginError $ hsep [ text "Could not find module", ppr mdName]
    go he (x:xs) = findIt he x >>= \case
      Nothing -> go he xs
      Just md -> return md

    findIt he = fmap getIt . liftIO . Finder.findImportedModule he mdName
    getIt (Found _ md)                = Just md
    getIt (FoundMultiple ((md, _):_)) = Just md
    getIt _                           = Nothing


pluginError :: SDoc -> CorePluginM a
pluginError msg
  = pluginProblemMsg Nothing ErrUtils.SevError msg >> exception

pluginLocatedError :: SrcSpan -> SDoc -> CorePluginM a
pluginLocatedError loc msg
  = pluginProblemMsg (Just loc) ErrUtils.SevError msg >> exception

pluginWarning :: SDoc -> CorePluginM ()
pluginWarning = pluginProblemMsg Nothing ErrUtils.SevWarning

pluginLocatedWarning :: SrcSpan -> SDoc -> CorePluginM ()
pluginLocatedWarning loc = pluginProblemMsg (Just loc) ErrUtils.SevWarning



pluginProblemMsg :: Maybe SrcSpan
                 -> ErrUtils.Severity
                 -> SDoc
                 -> CorePluginM ()
pluginProblemMsg mspan sev msg = do
  dflags <- liftCoreM getDynFlags
  loc    <- case mspan of
    Just sp -> pure sp
    Nothing -> liftCoreM getSrcSpanM
  unqual <- liftCoreM getPrintUnqualified
  liftIO $ putLogMsg
    dflags NoReason sev loc (mkErrStyle dflags unqual) msg

#if __GLASGOW_HASKELL__ < 802
putLogMsg :: DynFlags -> WarnReason -> ErrUtils.Severity
          -> SrcSpan -> PprStyle -> SDoc -> IO ()
putLogMsg dflags = log_action dflags dflags
#endif


pnConstraintsDeriving :: FastString
pnConstraintsDeriving = mkFastString "constraints-deriving"

pnConstraints :: FastString
pnConstraints = mkFastString "constraints"

pnBase :: FastString
pnBase = mkFastString "base"

mnConstraint :: ModuleName
mnConstraint = mkModuleName "Data.Constraint"

mnConstraintBare :: ModuleName
mnConstraintBare = mkModuleName "Data.Constraint.Bare"

mnConstraintDeriving :: ModuleName
mnConstraintDeriving = mkModuleName "Data.Constraint.Deriving"

mnDataTypeEquality :: ModuleName
mnDataTypeEquality = mkModuleName "Data.Type.Equality"

tnDict :: OccName
tnDict = mkTcOcc "Dict"

tnBareConstraint :: OccName
tnBareConstraint = mkTcOcc "BareConstraint"

tnDeriveContext :: OccName
tnDeriveContext = mkTcOcc "DeriveContext"

vnDictToBare :: OccName
vnDictToBare = mkVarOcc "dictToBare"

cnTypeEq :: OccName
cnTypeEq = mkTcOcc "~"
