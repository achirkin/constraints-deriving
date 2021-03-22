{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
    -- * Tools
  , newName, newTyVar, freshenTyVar, newLocalVar
  , bullet, isConstraintKind, getModuleAnns
  , filterAvails, mapResultType
  , recMatchTyKi, replaceTypeOccurrences
  , OverlapMode (..), toOverlapFlag, instanceOverlapMode
  , lookupClsInsts, getInstEnvs, replaceInstance
  , mkTyArg
    -- * Debugging
  , pluginDebug, pluginTrace
  , HasCallStack
    -- * Reexport common things
  , CoreToDo (..), ModGuts (..), UniqFM, Name, CoreBind, Bind (..)
  , CoreBndr, CoreExpr, Type, TyCon, ThetaType, TyVar, TCvSubst
  , DataCon, PredType, FamTyConFlav (..), Coercion, Id
  , Outputable(..), Role (..), Expr (..), IdDetails (..)
  , EqRel (..), Pred(..), Uniquable (..), classifyPredType
  , isNullUFM, ($+$), ($$), (<+>), vcat, hsep, sep, hcat, hang, text, speakN
  , pprQuotedList, getOccString
  , occName, nameSrcSpan, lookupUFM, eltsUFM, delFromUFM
  , tyConSingleDataCon, splitTyConApp_maybe, tyConClass_maybe
  , classDataCon, mkTyConApp, idType, dataConWorkId, typeKind
  , mkCoreLams, mkCoreConApps, varsToCoreExprs
  , splitForAllTys, splitAppTy_maybe, getName
  , mkSpecForAllTys, mkFunTy, splitFunTyArg_maybe
  , mkVisFunTy, mkInvisFunTy, mkVisFunTys, mkInvisFunTys
  , isNewTyCon, isClassTyCon, tyConDataCons, isEmptyTCvSubst
  , tyConName, tyConTyVars, mkTyVarTys, tyConAppArgs_maybe, tyConAppTyCon_maybe
  , getPackageFamInstEnv, substTyAddInScope
  , extendTCvSubst, emptyTCvSubst, eqType, heqClass
  , getTyVar_maybe, tyCoVarsOfTypesWellScoped, isCTupleTyConName, dataConInstSig
  , famTyConFlav_maybe, splitFunTy_maybe
  , mkTyVarTy, mkAppTy, substTys, zipTvSubst, mkTvSubstPrs
  , mkReflCo, mkWildValBinder, tyCoVarsOfTypeWellScoped
  , mkCast, mkUnsafeCo, mkCoreApps, mkTyApps
  , getSrcSpanM, getUniqueM, mkInternalName, mkOccName, mkLocalIdOrCoVar
  , occNameSpace, occNameString, mkExportedLocalId
  , uniqSetAny, orphNamesOfType, idName, nameModule, moduleNameString, getOccName
  , moduleName, constraintKind, substTyVar, exprType
  , Unify.typesCantMatch, Unify.tcMatchTys, Unify.tcMatchTy
  , splitFunTysUnscaled
  , OccName.varName
  , module GHC.Core.Coercion.Axiom
  , module GHC.Core.Class
  , module GHC.Core.FamInstEnv
  , module GHC.Core.InstEnv
  , module GHC.Utils.Panic
  , module GHC.Tc.Utils.TcType
  , mkWildcardValBinder, getFunTyPair, mkLocalIdOrCoVarCompat
  ) where

import           GHC.Core.Class      (Class, classTyCon)
import           GHC.Core.Coercion.Axiom             (CoAxBranch, coAxBranchIncomps,
                                      coAxBranchLHS, coAxBranchRHS,
                                      coAxiomBranches, coAxiomSingleBranch,
                                      fromBranches)
import           GHC.Core.FamInstEnv          (FamInst, fi_tys, fi_tvs, fi_rhs, lookupFamInstEnvByTyCon, famInstAxiom)
import qualified GHC.Types.Avail     as Avail
import           GHC.Utils.Error     as ErrUtils
import           GHC.Driver.Finder   as Finder
import           GHC.Plugins         hiding (UniqFM, OverlapMode (..), empty,overlapMode, (<>))
import qualified GHC.Plugins         as GhcPlugins
import qualified GHC.Iface.Env       as IfaceEnv
import           GHC.Core.InstEnv    ( InstEnv, InstEnvs, ClsInst, DFunInstType, mkLocalInstance
                                     , identicalClsInstHead, instanceSig, lookupInstEnv, instanceDFunId)
import qualified GHC.Core.InstEnv    as InstEnv
import qualified GHC.Iface.Load      as LoadIface
import           GHC.Utils.Monad     (MonadIO (..))
import           GHC.Utils.Panic     (panicDoc)
import           GHC.Tc.Utils.TcType (tcSplitDFunTy)
import qualified GHC.Types.Name.Occurrence as OccName (varName)
import           GHC.Tc.Utils.Monad  (TcM, getEps, initTc)
import qualified GHC.Core.Unify      as Unify
import qualified GHC.Core.TyCo.Rep   as TyCoRep
import           GHC.Core.Predicate
import           Control.Applicative (Alternative (..))
import           Control.Monad       (join, (>=>))
import           Data.Data           (Data, typeRep)
import           Data.IORef          (IORef, modifyIORef', newIORef, readIORef)
import           Data.Maybe          (catMaybes)
import           Data.Monoid         as Mon (First (..), Monoid (..))
import           Data.Proxy          (Proxy (..))
import           Data.Semigroup      as Sem (Semigroup (..))

#if PLUGIN_DEBUG
import GHC.Stack (withFrozenCallStack)
#endif

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

    , classTypeEq = pure eqClass

    , globalInstEnv = do
        hscEnv <- liftCoreM getHscEnv
        mn <- moduleName <$> liftCoreM getModule

        mdesc
          <- case [ m | m <- mgModSummaries $ hsc_mod_graph hscEnv
                      , ms_mod_name m == mn
                      , isBootSummary m == NotBoot ] of
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
              a@Avail.AvailTC{} <- mi_exports i
              let m = nameModule $ Avail.availName a
              [ m | m /= mi_module i, notMyOwn m]
            -- Load reexportedDeps recursively.
            -- This enumerate all modules that export some type constructors
            -- visible from the current module;
            -- this includes our base types and also all classes in scope.
            loadRec ms = do
              ifs <- traverse (LoadIface.loadModuleInterface reason)
                      $ backToList ms
              let ms' = foldr (unionUniqSets . reexportedDeps) ms ifs
              if isEmptyUniqSet $ ms' `minusUniqSet` ms
              then return ms
              else loadRec ms'
        gie <- runTcM $ do
          mods <- backToList <$> loadRec mSetDirect
          LoadIface.loadModuleInterfaces reason mods
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
        liftIO (Finder.findImportedModule hsce (unLoc mn) mpn)
    reason = text $ "Constraints.Deriving.CorePluginM "
                               ++ "itinialization of global InstEnv"
    -- Ignore my own modules: they do not contain any classes.
    notMyOwn m = moduleNameString (moduleName m) `notElem`
      [ "Data.Constraint.Deriving"
      , "Data.Constraint.Deriving.DeriveAll"
      , "Data.Constraint.Deriving.ToInstance"
      , "Data.Constraint.Deriving.ToInstance"
      , "Data.Constraint.Deriving.CorePluginM"
      ]

    backToList = nonDetEltsUniqSet



lookupName :: Module -> OccName -> CorePluginM Name
lookupName m occn = do
    hscEnv <- liftCoreM getHscEnv
    liftIO $ IfaceEnv.lookupOrigIO hscEnv m occn


runTcM :: TcM a -> CorePluginM a
runTcM mx = do
  hsce <- liftCoreM getHscEnv
  modu <- liftCoreM getModule
  let sp = realSrcLocSpan $ mkRealSrcLoc (fsLit "<CorePluginM.runTcM>") 1 1
  ((warns, errs), my) <- liftIO $ initTc hsce HsSrcFile False modu sp mx
  mapM_ pluginWarning $ ErrUtils.pprErrMsgBagWithLoc warns
  case my of
    Nothing ->
      let f []     = pluginError $ text "runTcM failed"
          f [x]    = pluginError x
          f (x:xs) = pluginWarning x >> f xs
      in f $ ErrUtils.pprErrMsgBagWithLoc errs
    Just y  -> do
      mapM_ pluginWarning $ ErrUtils.pprErrMsgBagWithLoc errs
      return y

-- Made this similar to tcRnGetInfo
--   and a hidden function lookupInsts used there
lookupClsInsts :: InstEnvs -> TyCon -> [InstEnv.ClsInst]
lookupClsInsts ie tc =
  [ ispec        -- Search all
  | ispec <- InstEnv.instEnvElts (InstEnv.ie_local  ie)
          ++ InstEnv.instEnvElts (InstEnv.ie_global ie)
  , InstEnv.instIsVisible (InstEnv.ie_visible ie) ispec
  , tyConName tc `elemNameSet` InstEnv.orphNamesOfClsInst ispec
  ]

getInstEnvs :: ModGuts
            -> CorePluginM InstEnv.InstEnvs
getInstEnvs guts = do
  globalInsts <- ask globalInstEnv
  return $ InstEnv.InstEnvs
    { InstEnv.ie_global  = globalInsts
    , InstEnv.ie_local   = mg_inst_env guts
    , InstEnv.ie_visible = mkModuleSet . dep_orphs $ mg_deps guts
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

    findIt he = fmap getIt . liftIO . Finder.findImportedModule he mdName
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
      mkLocalId (mkInternalName u (mkOccName OccName.varName nameStr) loc) Many ty

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
pluginError = pluginProblemMsg Nothing ErrUtils.SevError

pluginLocatedError :: SrcSpan -> SDoc -> CorePluginM a
pluginLocatedError loc = pluginProblemMsg (Just loc) ErrUtils.SevError

pluginWarning :: SDoc -> CorePluginM ()
pluginWarning = try' . pluginProblemMsg Nothing ErrUtils.SevWarning

pluginLocatedWarning :: SrcSpan -> SDoc -> CorePluginM ()
pluginLocatedWarning loc = try' . pluginProblemMsg (Just loc) ErrUtils.SevWarning

pluginDebug :: SDoc -> CorePluginM ()
#if PLUGIN_DEBUG
pluginDebug = try' . pluginProblemMsg Nothing ErrUtils.SevDump
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
                 -> ErrUtils.Severity
                 -> SDoc
                 -> CorePluginM a
pluginProblemMsg mspan sev msg = do
  dflags <- liftCoreM getDynFlags
  loc    <- case mspan of
    Just sp -> pure sp
    Nothing -> liftCoreM getSrcSpanM
  CorePluginM $ const $ pure $ Left $
    putLogMsg dflags NoReason sev loc msg


filterAvails :: (Name -> Bool) -> [Avail.AvailInfo] -> [Avail.AvailInfo]
filterAvails = Avail.filterAvails


-- This function was moved and renamed in GHC 8.6
-- | Check if this kind is Constraint, as seen to the typechecker.
isConstraintKind :: Kind -> Bool
isConstraintKind = tcIsConstraintKind


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
      = addToUFM_Acc (:) (:[]) (go as) (getUnique n) (n, deserializeWithData bytes)
    -- ignore non-matching annotations
    go (_:as) = go as



-- | Similar to Unify.tcMatchTyKis, but looks if there is a non-trivial subtype
--   in the first type that matches the second.
--   Non-trivial means not a TyVar.
recMatchTyKi :: Bool -- ^ Whether to do inverse match (instance is more conrete)
             -> Type -> Type -> Maybe TCvSubst
recMatchTyKi inverse tsearched ttemp = go tsearched
  where
    go :: Type -> Maybe TCvSubst
    go t
        -- ignore plain TyVars
      | isTyVarTy t
        = Nothing
        -- found a good substitution
      | Just sub <- if inverse
                    then matchIt ttemp t
                    else matchIt t ttemp
        = Just sub
        -- split type constructors
      | Just (_, tys) <- splitTyConApp_maybe t
        = getFirst $ foldMap (First . go) tys
        -- split foralls
      | (_:_, t') <- splitForAllTys t
        = go t'
        -- split arrow types
      | Just (_, at, rt) <- splitFunTy_maybe t
        = go at <|> go rt
      | otherwise
        = Nothing
    matchIt = Unify.tcMatchTyKi


-- | Replace all occurrences of one type in another.
replaceTypeOccurrences :: Type -> Type -> Type -> Type
replaceTypeOccurrences told tnew = replace
  where
    replace :: Type -> Type
    replace t
        -- found occurrence
      | eqType t told
        = tnew
        -- split arrow types
      | Just (vis, mult, at, rt) <- splitFunTyArg_maybe t
        = mkFunTy vis mult (replace at) (replace rt)
        -- split type constructors
      | Just (tyCon, tys) <- splitTyConApp_maybe t
        = mkTyConApp tyCon $ map replace tys
        -- split foralls
      | (bndrs@(_:_), t') <- splitForAllTys t
        = mkSpecForAllTys bndrs $ replace t'
        -- could not find anything
      | otherwise
        = t


-- | Replace instance in ModGuts if its duplicate already exists there;
--   otherwise just add this instance.
replaceInstance :: InstEnv.ClsInst -> CoreBind -> ModGuts -> ModGuts
replaceInstance newI newB guts
  | NonRec _ newE <- newB
  , First (Just oldI) <- foldMap sameInst $ mg_insts guts
  , newDFunId <- InstEnv.instanceDFunId newI
  , origDFunId <- InstEnv.instanceDFunId oldI
  , dFunId <- newDFunId `setVarName`   idName origDFunId
                        `setVarUnique` varUnique origDFunId
  , bind   <- NonRec dFunId newE
  , inst   <- newI { InstEnv.is_dfun = dFunId
                   , InstEnv.is_dfun_name = idName dFunId
                   }
    = guts
      { mg_insts    = replInst origDFunId inst $ mg_insts guts
      , mg_inst_env = mg_inst_env guts
           `InstEnv.deleteFromInstEnv` oldI
           `InstEnv.extendInstEnv` inst
      , mg_binds    = bind : remBind origDFunId (mg_binds guts)
      }
  | otherwise
    = guts
      { mg_insts    = newI : mg_insts guts
      , mg_inst_env = InstEnv.extendInstEnv (mg_inst_env guts) newI
      , mg_binds    = newB : mg_binds guts
      }
  where
    remBind _ [] = []
    remBind i' (b@(NonRec i _):bs)
      | i == i'   = remBind i' bs
      | otherwise = b  : remBind i' bs
    remBind i' (Rec rb :bs) = Rec (filter ((i' /=) . fst) rb) : remBind i' bs
    replInst _ _ [] = []
    replInst d' i' (i:is)
      | InstEnv.instanceDFunId i == d'   = i' : is
      | otherwise = i : replInst d' i' is
    sameInst i
      = First $ if InstEnv.identicalClsInstHead newI i then Just i else Nothing




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
    mappend = (<>)


toOverlapFlag :: OverlapMode -> OverlapFlag
toOverlapFlag m = OverlapFlag (getOMode m) False
  where
    getOMode NoOverlap    = GhcPlugins.NoOverlap noSourceText
    getOMode Overlapping  = GhcPlugins.Overlapping noSourceText
    getOMode Overlappable = GhcPlugins.Overlappable noSourceText
    getOMode Overlaps     = GhcPlugins.Overlaps noSourceText
    getOMode Incoherent   = GhcPlugins.Incoherent noSourceText

    noSourceText = GhcPlugins.NoSourceText


instanceOverlapMode :: InstEnv.ClsInst -> OverlapMode
instanceOverlapMode i = case InstEnv.overlapMode (InstEnv.is_flag i) of
    GhcPlugins.NoOverlap {}    -> NoOverlap
    GhcPlugins.Overlapping {}  -> Overlapping
    GhcPlugins.Overlappable {} -> Overlappable
    GhcPlugins.Overlaps {}     -> Overlaps
    GhcPlugins.Incoherent {}   -> Incoherent



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


mkFunTy :: AnonArgFlag -> Mult -> Type -> Type -> Type
mkFunTy = TyCoRep.mkFunTy

splitFunTyArg_maybe :: Type -> Maybe (AnonArgFlag, Mult, Type, Type)
splitFunTyArg_maybe ty | Just ty' <- tcView ty = splitFunTyArg_maybe ty'
splitFunTyArg_maybe (TyCoRep.FunTy vis mult arg res)  = Just (vis, mult, arg, res)
splitFunTyArg_maybe _                            = Nothing

type UniqFM = GhcPlugins.UniqFM Unique

mkInvisFunTys :: [Type] -> Type -> Type
mkInvisFunTys = mkInvisFunTysMany

splitFunTysUnscaled :: Type -> ([Type], Type)
splitFunTysUnscaled t = (map TyCoRep.scaledThing ts, r)
  where
    (ts, r) = splitFunTys t


mkUnsafeCo :: Role -> Type -> Type -> Coercion
mkUnsafeCo = mkUnivCo (TyCoRep.PluginProv "constraints-deriving: trust me!")

-- | Transform the result type in a more complex fun type.
mapResultType :: (Type -> Type) -> Type -> Type
mapResultType f (TyCoRep.FunTy vis mult at rt)
  -- Looks like `idType (dataConWorkId klassDataCon)` has constraints as visible arguments.
  -- I guess usually that does not change anything for the user, because they don't ever observe
  -- type signatures of class data constructors.
  -- This only pops up since 8.10 with the introduction of visibility arguments.
  -- The check below workarounds this.
    = if isConstraintKind (typeKind at)
      then mkInvisFunTy mult at (mapResultType f rt)
      else mkFunTy vis mult at (mapResultType f rt)
mapResultType f t
  | (bndrs@(_:_), t') <- splitForAllTys t
    = mkSpecForAllTys bndrs $ mapResultType f t'
  | otherwise
    = f t

mkWildcardValBinder :: Type -> Id
mkWildcardValBinder = mkWildValBinder Many

getFunTyPair :: Type -> Maybe (Type, Type)
getFunTyPair = fmap (\(_, a, b) -> (a, b)) . splitFunTy_maybe

mkLocalIdOrCoVarCompat :: Name -> Type -> Id
mkLocalIdOrCoVarCompat = (`mkLocalIdOrCoVar` Many)
