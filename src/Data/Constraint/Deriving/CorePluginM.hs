{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
#if __GLASGOW_HASKELL__ < 802
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
#endif
module Data.Constraint.Deriving.CorePluginM
  ( CorePluginM (), runCorePluginM
  , CorePluginEnv (), CorePluginEnvRef, initCorePluginEnv
  , liftCoreM, runTcM, liftIO, lookupName
    -- * Error handling
  , try, exception
    -- * Accessing read-only on-demand variables
  , ask
  , tyConDict, tyConBareConstraint, tyConDeriveContext
  , funDictToBare, tyEmptyConstraint, classTypeEq
    -- * Reporting
  , pluginWarning, pluginLocatedWarning
  , pluginError, pluginLocatedError
    -- * Debugging
  , pluginDebug, pluginTrace
    -- * Tools
  , newName, newTyVar, freshenTyVar, newLocalVar, getInstEnvs, getModuleAnns
  ) where

#if PLUGIN_DEBUG
import GHC.Stack (withFrozenCallStack)
#endif

import Control.Applicative (Alternative (..))
import Control.Monad       (join, (>=>))
import Data.Data           (Data, typeRep)
import Data.IORef          (IORef, modifyIORef', newIORef, readIORef)
import Data.Maybe          (catMaybes)
import Data.Proxy          (Proxy (..))

import Data.Constraint.Deriving.Import

-- | Since I do not have access to the guts of CoreM monad,
--   I implement a wrapper on top of it here.
--
--   It provides two pieces of functionality:
--
--     * Possibility to fail a computation with IO error action
--       (to show a nice error to a user and continue the work if possible);
--
--     * An environment with things that computed on demand, once at most.
--
newtype CorePluginM a = CorePluginM
  { _runCorePluginM :: IORef CorePluginEnv -> CoreM (Either (IO ()) a) }

runCorePluginM :: CorePluginM a -> IORef CorePluginEnv -> CoreM (Maybe a)
runCorePluginM m e = _runCorePluginM m e >>= \case
  Left er -> Nothing <$ liftIO er
  Right a -> pure $ Just a

instance Functor CorePluginM where
  fmap f m = CorePluginM $ fmap (fmap f) . _runCorePluginM m

instance Applicative CorePluginM where
  pure = CorePluginM . const . pure . Right
  mf <*> ma = CorePluginM $ \e -> (<*>) <$> _runCorePluginM mf e <*> _runCorePluginM ma e

instance Alternative CorePluginM where
  empty = CorePluginM . const $ pure $ Left $ pure ()
  ma <|> mb = CorePluginM $ \e -> f <$> _runCorePluginM ma e <*> _runCorePluginM mb e
    where
      f (Left _) = id
      f rx       = const rx

instance Monad CorePluginM where
  return = pure
  ma >>= k = CorePluginM $ \e -> _runCorePluginM ma e >>= \case
    Left  a -> pure (Left a)
    Right a -> _runCorePluginM (k a) e

instance MonadIO CorePluginM where
  liftIO = liftCoreM . liftIO

instance MonadThings CorePluginM where
  lookupThing = liftCoreM . lookupThing

instance MonadUnique CorePluginM where
  getUniqueSupplyM = CorePluginM $ const $ Right <$> getUniqueSupplyM


-- | Wrap CoreM action
liftCoreM :: CoreM a -> CorePluginM a
liftCoreM = CorePluginM . const . fmap Right

-- | Synonym for `fail`
exception :: CorePluginM a
exception = empty

-- | Return `Nothing` if the computation fails
try :: CorePluginM a -> CorePluginM (Maybe a)
try m = CorePluginM $ _runCorePluginM m >=> f
  where
    f (Left e)  = Right Nothing <$ liftIO e
    f (Right a) = pure . Right $ Just a

-- | Try and ignore the result
try' :: CorePluginM a -> CorePluginM ()
try' m = () <$ try m

-- | Reference to the plugin environment variables.
type CorePluginEnvRef = IORef CorePluginEnv

-- | Plugin environment
--
--   Its components are supposed to be computed at most once, when they are needed.
data CorePluginEnv = CorePluginEnv
  { modConstraint       :: CorePluginM Module
  , modConstraintBare   :: CorePluginM Module
  , modDeriveAll        :: CorePluginM Module
  , modToInstance       :: CorePluginM Module
  , modDataTypeEquality :: CorePluginM Module
  , tyConDict           :: CorePluginM TyCon
  , tyConBareConstraint :: CorePluginM TyCon
  , tyConDeriveContext  :: CorePluginM TyCon
  , funDictToBare       :: CorePluginM Id
  , tyEmptyConstraint   :: CorePluginM Type
  , classTypeEq         :: CorePluginM Class
  , globalInstEnv       :: CorePluginM InstEnv
  }

-- | Ask a field of the CorePluginEnv environment.
ask :: (CorePluginEnv -> CorePluginM a) -> CorePluginM a
ask f = join $ CorePluginM $ liftIO . fmap (Right . f) . readIORef

-- | Init the `CorePluginM` environment and save it to IORef.
initCorePluginEnv :: CoreM (IORef CorePluginEnv)
initCorePluginEnv = do
  env <- liftIO $ newIORef defCorePluginEnv
  -- need to force globalInstEnv as early as possible to make sure
  -- that ExternalPackageState var is not yet contaminated with
  -- many unrelated modules.
  gie <- _runCorePluginM (ask globalInstEnv) env
  seq gie $ return env


-- | Lookup necessary environment components on demand.
defCorePluginEnv :: CorePluginEnv
defCorePluginEnv = CorePluginEnv
    { modConstraint = do
        mm <- try $ lookupModule mnConstraint [pnConstraintsDeriving, pnConstraints]
        saveAndReturn mm $ \a e -> e { modConstraint = a }

    , modConstraintBare = do
        mm <- try $ lookupModule mnConstraintBare [pnConstraintsDeriving]
        saveAndReturn mm $ \a e -> e { modConstraintBare = a }

    , modDeriveAll = do
        mm <- try $ lookupModule mnDeriveAll [pnConstraintsDeriving]
        saveAndReturn mm $ \a e -> e { modDeriveAll = a }

    , modToInstance = do
        mm <- try $ lookupModule mnToInstance [pnConstraintsDeriving]
        saveAndReturn mm $ \a e -> e { modToInstance = a }

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
        m <- ask modDeriveAll
        mtc <- try $ lookupName m tnDeriveContext >>= lookupTyCon
        saveAndReturn mtc $ \a e -> e { tyConDeriveContext = a }

    , funDictToBare = do
        m <- ask modConstraintBare
        mf <- try $ lookupName m vnDictToBare >>= lookupId
        saveAndReturn mf $ \a e -> e { funDictToBare = a }

    , tyEmptyConstraint = do
        ec <- flip mkTyConApp [] <$> lookupTyCon (cTupleTyConName 0)
        saveAndReturn (Just ec) $ \a e -> e { tyEmptyConstraint = a }

#if __GLASGOW_HASKELL__ >= 808
    , classTypeEq = pure eqClass
#else
    , classTypeEq = do
        m <- ask modDataTypeEquality
        mc <- try $ lookupName m (mkTcOcc "~") >>= lookupThing >>= \case
          ATyCon tc | Just cls <- tyConClass_maybe tc
            -> return cls
          _ -> exception
        saveAndReturn mc $ \a e -> e { classTypeEq = a }
#endif

    , globalInstEnv = do
        hscEnv <- liftCoreM getHscEnv
        mn <- moduleName <$> liftCoreM getModule

        mdesc
          <- case [ m | m <- mgModSummaries $ hsc_mod_graph hscEnv
                      , ms_mod_name m == mn
                      , isNotBootFile m ] of
          []   -> pluginError $ hsep
                  [ text "Could not find"
                  , ppr mn
                  , text "in the module graph."
                  ]
          [md] -> return md
          _    -> pluginError $ hsep
                  [ text "Found multiple modules"
                  , ppr mn
                  , text "in the module graph."
                  ]
        -- direct module dependencies
        modsDirect <- fmap catMaybes
          . traverse (lookupDep hscEnv)
          $ ms_srcimps mdesc ++ ms_textual_imps mdesc
        let -- direct dependencies; must be in the explicit depenencies anyway
            mSetDirect = mkUniqSet $ filter notMyOwn modsDirect
            -- Modules that we definitely need to look through,
            -- even if they are from other, hidden packages
            reexportedDeps i = mkUniqSet $ do
              a@AvailTC{} <- mi_exports i
              let m = nameModule $ availName a
              [ m | m /= mi_module i, notMyOwn m]
            -- Load reexportedDeps recursively.
            -- This enumerate all modules that export some type constructors
            -- visible from the current module;
            -- this includes our base types and also all classes in scope.
            loadRec ms = do
              ifs <- traverse (loadModuleInterface reason)
                      $ backToList ms
              let ms' = foldr (unionUniqSets . reexportedDeps) ms ifs
              if isEmptyUniqSet $ ms' `minusUniqSet` ms
              then return ms
              else loadRec ms'
        gie <- runTcM $ do
          mods <- backToList <$> loadRec mSetDirect
          loadModuleInterfaces reason mods
          eps_inst_env <$> getEps
        saveAndReturn (Just gie) $ \a e -> e { globalInstEnv = a }

    }
  where
    saveAndReturn Nothing  f = CorePluginM $ \eref ->
      Left (pure ()) <$ liftIO (modifyIORef' eref $ f exception)
    saveAndReturn (Just x) f = CorePluginM $ \eref ->
      Right x  <$ liftIO (modifyIORef' eref $ f (pure x))
    maybeFound (Found _ m) = Just m
    maybeFound _           = Nothing
    lookupDep :: HscEnv
              -> (Maybe FastString, GenLocated SrcSpan ModuleName)
              -> CorePluginM (Maybe Module)
    lookupDep hsce (mpn, mn)
      = maybeFound <$>
        liftIO (findImportedModule hsce (unLoc mn) mpn)
    reason = text $ "Constraints.Deriving.CorePluginM "
                               ++ "itinialization of global InstEnv"
    -- Ignore my own modules: they do not contain any classes.
    notMyOwn m = moduleNameString (moduleName m) `notElem`
      [ "Data.Constraint.Deriving"
      , "Data.Constraint.Deriving.Import"
      , "Data.Constraint.Deriving.Compat"
      , "Data.Constraint.Deriving.DeriveAll"
      , "Data.Constraint.Deriving.ToInstance"
      , "Data.Constraint.Deriving.CorePluginM"
      ]
#if __GLASGOW_HASKELL__ < 804
    mgModSummaries = id
#endif
#if __GLASGOW_HASKELL__ >= 802
    backToList = nonDetEltsUniqSet
#else
    backToList = uniqSetToList
#endif


lookupName :: Module -> OccName -> CorePluginM Name
lookupName m occn = do
    hscEnv <- liftCoreM getHscEnv
    liftIO $ lookupOrigIO hscEnv m occn

runTcM :: TcM a -> CorePluginM a
runTcM mx = do
  hsce <- liftCoreM getHscEnv
  modu <- liftCoreM getModule
  let sp = realSrcLocSpan $ mkRealSrcLoc (fsLit "<CorePluginM.runTcM>") 1 1
  ((warns, errs), my) <- liftIO $ initTc hsce HsSrcFile False modu sp mx
  mapM_ pluginWarning $ pprErrMsgBagWithLoc warns
  case my of
    Nothing ->
      let f []     = pluginError $ text "runTcM failed"
          f [x]    = pluginError x
          f (x:xs) = pluginWarning x >> f xs
      in f $ pprErrMsgBagWithLoc errs
    Just y  -> do
      mapM_ pluginWarning $ pprErrMsgBagWithLoc errs
      return y

getInstEnvs :: ModGuts
            -> CorePluginM InstEnvs
getInstEnvs guts = do
  globalInsts <- ask globalInstEnv
  return $ InstEnvs
    { ie_global  = globalInsts
    , ie_local   = mg_inst_env guts
    , ie_visible = mkModuleSet . dep_orphs $ mg_deps guts
    }

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

    findIt he = fmap getIt . liftIO . findImportedModule he mdName
    getIt (Found _ md)                = Just md
    getIt (FoundMultiple ((md, _):_)) = Just md
    getIt _                           = Nothing


-- | Generate new unique type variable
newTyVar :: Kind -> CorePluginM TyVar
newTyVar k = flip mkTyVar k <$> newName tvName "gen"

-- | Assign a new unique to a type variable;
--   also assign a whole new name if the input is a wildcard.
freshenTyVar :: TyVar -> CorePluginM TyVar
freshenTyVar tv = do
    u <- getUniqueM
    nn <-
      if isInternalName n
      then return $ mkDerivedInternalName (repOccN (show u)) u n
      else do
        md <- liftCoreM getModule
        loc <- liftCoreM getSrcSpanM
        return $ mkExternalName u md (repOccN (show u) on) loc
    return $ mkTyVar nn k
  where
    n = tyVarName tv
    k = tyVarKind tv
    on = nameOccName n
    repOccN s oc = case occNameString oc of
      "_" -> mkOccName (occNameSpace oc) ("fresh_" ++ s)
      _   -> on

-- | Generate a new unique local var (not be exported!)
newLocalVar :: Type -> String -> CorePluginM Var
newLocalVar ty nameStr = do
    loc <- liftCoreM getSrcSpanM
    u <- getUniqueM
    return $
      mkLocalIdCompat (mkInternalName u (mkOccName varName nameStr) loc) Many ty

-- | Generate new unique name
newName :: NameSpace -> String -> CorePluginM Name
newName nspace nameStr = do
    md <- liftCoreM getModule
    loc <- liftCoreM getSrcSpanM
    u <- getUniqueM
    return $ mkExternalName u md occname loc
  where
    occname = mkOccName nspace nameStr


pluginError :: SDoc -> CorePluginM a
pluginError = pluginProblemMsg Nothing SevError

pluginLocatedError :: SrcSpan -> SDoc -> CorePluginM a
pluginLocatedError loc = pluginProblemMsg (Just loc) SevError

pluginWarning :: SDoc -> CorePluginM ()
pluginWarning = try' . pluginProblemMsg Nothing SevWarning

pluginLocatedWarning :: SrcSpan -> SDoc -> CorePluginM ()
pluginLocatedWarning loc = try' . pluginProblemMsg (Just loc) SevWarning

pluginDebug :: SDoc -> CorePluginM ()
#if PLUGIN_DEBUG
pluginDebug = try' . pluginProblemMsg Nothing SevDump
#else
pluginDebug = const (pure ())
#endif
{-# INLINE pluginDebug #-}



pluginTrace :: HasCallStack => SDoc -> a -> a
#if PLUGIN_DEBUG
pluginTrace = withFrozenCallStack pprSTrace
#else
pluginTrace = const id
#endif
{-# INLINE pluginTrace #-}

pluginProblemMsg :: Maybe SrcSpan
                 -> Severity
                 -> SDoc
                 -> CorePluginM a
pluginProblemMsg mspan sev msg = do
  dflags <- liftCoreM getDynFlags
  loc    <- case mspan of
    Just sp -> pure sp
    Nothing -> liftCoreM getSrcSpanM
  unqual <- liftCoreM getPrintUnqualified
  CorePluginM $ const $ pure $ Left $
    putLogMsgCompat dflags NoReason sev loc unqual msg


-- | Similar to `getAnnotations`, but keeps the annotation target.
--   Also, it is hardcoded to `deserializeWithData`.
--   Looks only for annotations defined in this module.
--   Ignores module annotations.
getModuleAnns :: forall a . Data a => ModGuts -> UniqMap [(Name, a)]
getModuleAnns = go . mg_anns
  where
    valTRep = typeRep (Proxy :: Proxy a)
    go :: [Annotation] -> UniqMap [(Name, a)]
    go [] = emptyUFM
    go (Annotation
         (NamedTarget n) -- ignore module targets
         (Serialized trep bytes)
        : as)
      | trep == valTRep -- match type representations
      = addToUFM_Acc (:) (:[]) (go as) (getUnique n) (n, deserializeWithData bytes)
    -- ignore non-matching annotations
    go (_:as) = go as


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

mnDeriveAll :: ModuleName
mnDeriveAll = mkModuleName "Data.Constraint.Deriving.DeriveAll"

mnToInstance :: ModuleName
mnToInstance = mkModuleName "Data.Constraint.Deriving.ToInstance"

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
