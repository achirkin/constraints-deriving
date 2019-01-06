{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Constraint.Deriving.CorePluginM
  ( CorePluginM (), runCorePluginM
  , CorePluginEnv (), CorePluginEnvRef, initCorePluginEnv
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
    -- * Tools
  , newName, newTyVar
  , bullet, isConstraintKind, getModuleAnns
  , filterAvails
  , maybeReplaceTypeOccurrences, replaceTypeOccurrences
  , OverlapMode (..), toOverlapFlag
  ) where


import qualified Avail
import           Class         (Class)
import           Control.Monad (join)
import           Data.Data     (Data, typeRep)
import           Data.IORef    (IORef, modifyIORef', newIORef, readIORef)
import           Data.Monoid   (Any (..))
import           Data.Proxy    (Proxy (..))
import qualified ErrUtils
import qualified Finder
import           GhcPlugins    hiding (OverlapMode (..), overlapMode, (<>))
import qualified GhcPlugins
import qualified IfaceEnv
import           MonadUtils    (MonadIO (..))
#if __GLASGOW_HASKELL__ < 806
import qualified Kind      (isConstraintKind)
import qualified TcRnMonad (initTcForLookup)
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


-- | Generate new unique type variable
newTyVar :: Kind -> CorePluginM TyVar
newTyVar k = flip mkTyVar k <$> newName tvName "gen"

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

filterAvails :: (Name -> Bool) -> [Avail.AvailInfo] -> [Avail.AvailInfo]
#if __GLASGOW_HASKELL__ < 802
filterAvails _    [] = []
filterAvails keep (a:as) = case go a of
    Nothing -> filterAvails keep as
    Just fa -> fa : filterAvails keep as
  where
    go x@(Avail.Avail _ n)
      | keep n    = Just x
      | otherwise = Nothing
    go (Avail.AvailTC n ns fs) =
      let ns' = filter keep ns
          fs' = filter (keep . flSelector) fs
      in if null ns' && null fs'
         then Nothing
         else Just $ Avail.AvailTC n ns' fs'
#else
filterAvails = Avail.filterAvails
#endif

#if __GLASGOW_HASKELL__ < 802
bullet :: SDoc
bullet = unicodeSyntax (char '•') (char '*')
#endif


-- This function was moved and renamed in GHC 8.6
-- | Check if this kind is Constraint, as seen to the typechecker.
isConstraintKind :: Kind -> Bool
#if __GLASGOW_HASKELL__ < 806
isConstraintKind = Kind.isConstraintKind
#else
isConstraintKind = tcIsConstraintKind
#endif

-- | Similar to `getAnnotations`, but keeps the annotation target.
--   Also, it is hardcoded to `deserializeWithData`.
--   Looks only for annotations defined in this module.
--   Ignores module annotations.
getModuleAnns :: forall a . Data a => ModGuts -> UniqFM [(Name, a)]
getModuleAnns = go . mg_anns
  where
    valTRep = typeRep (Proxy :: Proxy a)
    go :: [Annotation] -> UniqFM [(Name, a)]
    go [] = emptyUFM
    go (Annotation
         (NamedTarget n) -- ignore module targets
         (Serialized trep bytes)
        : as)
      | trep == valTRep -- match type representations
      = addToUFM_Acc (:) (:[]) (go as) n (n, deserializeWithData bytes)
    -- ignore non-matching annotations
    go (_:as) = go as



-- | Look through the type recursively;
--   If the type occurrence found, replace it with the new type.
--   While the type is checked, the function also tracks how type variables
--   are renamed.
--   So the result is the changed type and an indication if it has been changed.
maybeReplaceTypeOccurrences :: [TyVar] -> Type -> Type -> Type -> (Any, Type)
maybeReplaceTypeOccurrences tv told tnew = replace
  where
    mkSubsts xs = mkSubsts' tv $ map mkTyVarTy xs
    mkSubsts' [] [] = Just emptyTCvSubst
    mkSubsts' (x:xs) (t:ts) = (\s -> extendTCvSubst s x t)
                           <$> mkSubsts' xs ts
    mkSubsts' _ _ = Nothing
    replace :: Type -> (Any, Type)
    replace t
      | tvars <- tyCoVarsOfTypeWellScoped t
      , Just sub <- mkSubsts tvars
      , told' <- substTyAddInScope sub told
      , eqType t told'
        = (Any True, substTyAddInScope sub tnew)
        -- split type constructors
      | Just (tyCon, tys) <- splitTyConApp_maybe t
        = mkTyConApp tyCon <$> mapM replace tys
        -- split foralls
      | (bndrs@(_:_), t') <- splitForAllTys t
        = mkSpecForAllTys bndrs <$> replace t'
        -- split arrow types
      | Just (at, rt) <- splitFunTy_maybe t
        = mkFunTy <$> replace at <*> replace rt
      | otherwise
        = (Any False, t)


-- | Replace all occurrences of one type in another.
replaceTypeOccurrences :: Type -> Type -> Type -> Type
replaceTypeOccurrences told tnew = replace
  where
    replace :: Type -> Type
    replace t
        -- found occurrence
      | eqType t told
        = tnew
        -- split type constructors
      | Just (tyCon, tys) <- splitTyConApp_maybe t
        = mkTyConApp tyCon $ map replace tys
        -- split foralls
      | (bndrs@(_:_), t') <- splitForAllTys t
        = mkSpecForAllTys bndrs $ replace t'
        -- split arrow types
      | Just (at, rt) <- splitFunTy_maybe t
        = mkFunTy (replace at) (replace rt)
        -- could not find anything
      | otherwise
        = t



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


toOverlapFlag :: OverlapMode -> OverlapFlag
toOverlapFlag m = OverlapFlag (getOMode m) False
  where
    getOMode NoOverlap    = GhcPlugins.NoOverlap noSourceText
    getOMode Overlapping  = GhcPlugins.Overlapping noSourceText
    getOMode Overlappable = GhcPlugins.Overlappable noSourceText
    getOMode Overlaps     = GhcPlugins.Overlaps noSourceText
    getOMode Incoherent   = GhcPlugins.Incoherent noSourceText

#if __GLASGOW_HASKELL__ >= 802
    noSourceText = GhcPlugins.NoSourceText
#else
    noSourceText = "[plugin-generated code]"
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

cnTypeEq :: OccName
cnTypeEq = mkTcOcc "~"
