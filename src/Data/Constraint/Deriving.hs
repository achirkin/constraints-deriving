{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TypeFamilies       #-}
module Data.Constraint.Deriving
  ( plugin
  , ToInstance (..)
  , OverlapMode (..)
  , DeriveAll (..)
  , DeriveContext
  ) where

import           Class
import           CoAxiom
import           Control.Monad (join)
import           Data.Data     (Data)
import           Data.IORef    (IORef, modifyIORef', newIORef, readIORef)
import qualified Data.Kind     as Kind
import           Data.Maybe    (catMaybes, fromMaybe, mapMaybe, maybeToList)
import           Data.Monoid   (Any (..), First (..))
import qualified Finder
import           GhcPlugins    (AnnTarget (..), Bind (..), CommandLineOption,
                                CoreBind, CoreM, CoreToDo (..), DFunId,
                                Expr (..), FastString, Id, IdDetails (..),
                                ModGuts (..), Module, ModuleName, Name, OccName,
                                Plugin (..), SDoc, SourceText (..), TyCon,
                                TyVar, Type, UniqFM, Unique, binderVar,
                                caseBinder, defaultPlugin, deserializeWithData,
                                emptyTCvSubst, eps_PTE, eqType, errorMsg,
                                extendTCvSubst, findAnns, fsLit, getAnnotations,
                                getHscEnv, getUniqueSupplyM, getUniquesM,
                                hm_details, hsep, idName, idType, isNewTyCon,
                                lookupHpt, lookupId, lookupThing, lookupTyCon,
                                md_types, mkAnnEnv, mkExportedLocalId,
                                mkExternalName, mkFunTy, mkModuleName,
                                mkOccName, mkPiTys, mkSpecForAllTys, mkTcOcc,
                                mkTyConApp, mkTyVarTy, mkUnsafeCo, mkVarOcc,
                                moduleName, occName, occNameSpace,
                                occNameString, ppr, setIdDetails, setIdType,
                                splitFunTy_maybe, splitPiTys,
                                splitTyConApp_maybe, substTyAddInScope,
                                tyCoVarsOfTypeWellScoped, tyConClass_maybe,
                                tyConName, typeEnvCoAxioms, varName, warnMsg,
                                ($$))
import qualified GhcPlugins
import qualified IfaceEnv
import qualified InstEnv
import           MonadUtils    (MonadIO (..))
import           Panic         (panicDoc)
import qualified TcRnMonad

-- | A marker to tell the core plugin to convert BareConstraint top-level binding into
--   an instance declaration.
newtype ToInstance = ToInstance { overlapMode :: OverlapMode }
  deriving (Eq, Show, Read, Data)

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


-- | A marker to tell the core plugin to derive all visible class instances for a given newtype.
--
--   The deriving logic is to simply re-use existing instance dictionaries by casting them.
data DeriveAll = DeriveAll
  deriving (Eq, Show, Data)

-- | This type family is used to impose constraints on type parameters when looking up type instances
--   for the `DeriveAll` core plugin.
--
--   `DeriveAll` uses only those instances that satisfy the specified constraint.
--   If the constraint is not specified, it is assumed to be `()`.
type family DeriveContext (t :: Kind.Type) :: Kind.Constraint

-- | To use the plugin, add
--
-- @
-- {\-\# OPTIONS_GHC -fplugin Data.Constraint.Deriving \#-\}
-- @
--
-- To the header of your file.
plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
#if MIN_VERSION_ghc(8,6,0)
  , pluginRecompile = purePlugin
#endif
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  eref <- liftIO $ newIORef defCorePluginEnv
  -- if a plugin pass totally  fails to do anything useful,
  -- copy original ModGuts as its output, so that next passes can do their jobs.
  return ( CoreDoPluginPass "Data.Constraint.Deriving.deriveAllInstances"
             (\x -> fromMaybe x <$> runCorePluginM (deriveAllInstances x) eref)
         : CoreDoPluginPass "Data.Constraint.Deriving.toInstance"
             (\x -> fromMaybe x <$> runCorePluginM (toInstance x) eref)
         : todo)



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

instance GhcPlugins.MonadThings CorePluginM where
  lookupThing = liftCoreM . lookupThing

instance GhcPlugins.MonadUnique CorePluginM where
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
  , tyConDict             :: CorePluginM TyCon
  , tyConBareConstraint   :: CorePluginM TyCon
  , tyConDeriveContext    :: CorePluginM TyCon
  , funDictToBare         :: CorePluginM Id
  }

-- | Ask a field of the CorePluginEnv environment.
ask :: (CorePluginEnv -> CorePluginM a) -> CorePluginM a
ask f = join $ CorePluginM $ liftIO . fmap (Just . f) . readIORef


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
    }
  where
    saveAndReturn Nothing  f = CorePluginM $ \eref ->
      Nothing <$ liftIO (modifyIORef' eref $ f exception)
    saveAndReturn (Just x) f = CorePluginM $ \eref ->
      Just x  <$ liftIO (modifyIORef' eref $ f (pure x))



{-
  Derive all specific instances of a type for its newtype wrapper.

  Steps:

  1. Lookup a type or type family instances (branches of CoAxiom) of referenced by the newtype decl

  2. For every type instance:

     2.1 Lookup all class instances

     2.2 For every class instance:

         * Use mkLocalInstance with parameters of found instance and replaced RHS types
         * Create a corresponding top-level binding (DFunId), add it to mg_binds of ModGuts.
         * Add new instance to (mg_insts :: [ClsInst]) of ModGuts
         * Update mg_inst_env of ModGuts accordingly.

 -}
deriveAllPass :: ModGuts -> CorePluginM ModGuts
deriveAllPass guts = do
    annotateds <-
      liftCoreM $ getAnnotations deserializeWithData guts :: CorePluginM (UniqFM [DeriveAll])
    go (reverse $ mg_binds guts) annotateds guts { mg_binds = []}
  where
    go :: [CoreBind] -> UniqFM [DeriveAll] -> ModGuts -> CorePluginM ModGuts
    -- All exports are processed, just return ModGuts
    go [] anns guts = undefined



deriveAll :: CoreBind -> CorePluginM (InstEnv.ClsInst, CoreBind)
deriveAll = undefined


deriveAllInstances :: ModGuts -> CorePluginM ModGuts
deriveAllInstances guts = do
  bf <- lookupBackendFamily
  deriveAllInstances' bf guts

deriveAllInstances'  :: CoAxiom Branched -> ModGuts -> CorePluginM ModGuts
deriveAllInstances' backendFamily  guts = do

    matchedInstances <- matchInstances <$> getUniquesM
    -- mapM_ (putMsg . ppr) typeMaps
    -- mapM_ (putMsg . ppr) matchedInstances
    --
    -- mapM_ (\b -> putMsg (ppr b) >> putMsg "------") $ mg_binds guts

    return guts
      { mg_insts = map snd matchedInstances ++ mg_insts guts
      , mg_inst_env = InstEnv.extendInstEnvList (mg_inst_env guts)
                    $ map snd matchedInstances
      , mg_binds = map fst matchedInstances ++ mg_binds guts
      }
  where

    -- backends for which I derive class instances
    backendInstances = fromBranches $ coAxiomBranches backendFamily

    -- list of backends with overlapping mods:
    --  just substitute class instances and we are done.
    typeMaps :: [(OverlapMode, [TyVar], Type, Type)]
    typeMaps = map mapBackend backendInstances
      where
        mapBackend coaxb = ( overlap coaxb
                           , coAxBranchTyVars coaxb
                           , coAxBranchRHS coaxb
                           , mkTyConApp dfBackendTyCon
                               $ coAxBranchLHS coaxb ++ [coAxBranchRHS coaxb]
                           )
        overlap coaxb = if null $ coAxBranchIncomps coaxb
                        then Overlapping
                        else Incoherent

    -- lookup class instances here
    instances = InstEnv.instEnvElts $ mg_inst_env guts

    -- DFbackend type constructor is supposed to be defined in this module
    dfBackendTyCon
      = let checkDfBackendTyCon tc
                = if occName (tyConName tc) == mkTcOcc "VecBackend"
                  then First $ Just tc
                  else First Nothing
         in fromMaybe (
               panicDoc "Data.Constraint.Deriving"
                        "Could not find VecBackend type constructor"
            ) . getFirst $ foldMap checkDfBackendTyCon $ mg_tcs guts

    matchInstances uniques = catMaybes $ zipWith ($)
      [ \u -> let refId = InstEnv.instanceDFunId ci
                  f i = (mkBind refId i, i)
               in f <$> matchInstance u tm refId (InstEnv.instanceHead ci)
      | tm <- typeMaps
      , ci <- instances
      ] uniques

    matchInstance :: Unique
                  -> (OverlapMode, [TyVar], Type, Type)
                  -> DFunId
                  -> ([TyVar], Class, [Type])
                  -> Maybe InstEnv.ClsInst
    matchInstance uniq
                  (overlapMode, bTyVars, bOrigT, bNewT)
                  iDFunId
                  (iTyVars, iclass, iTyPams)
      | (Any True, newTyPams) <- matchTys iTyPams
      , (_, newDFunTy) <- matchTy (idType iDFunId)
      , newDFunId <- mkExportedLocalId
          (DFunId isNewType) newName newDFunTy
        = Just $ InstEnv.mkLocalInstance
                    newDFunId
                    (toOverlapFlag overlapMode)
                    iTyVars iclass newTyPams
      | otherwise
        = Nothing
      where
        matchTy = maybeReplaceTypeOccurrences bTyVars bOrigT bNewT
        matchTys = mapM matchTy
        isNewType = isNewTyCon (classTyCon iclass)
        newName = mkExternalName uniq (mg_module guts)
                   newOccName
                   (mg_loc guts)
        newOccName
          = let oname = occName (idName $ iDFunId)
             in mkOccName (occNameSpace oname)
                          (occNameString oname ++ "VecBackend")

    -- Create a new DFunId by casting
    -- the original DFunId to a required type
    mkBind :: DFunId -> InstEnv.ClsInst -> CoreBind
    mkBind oldId newInst
        = NonRec newId
        $ Cast (Var oldId)
        $ mkUnsafeCo Representational (idType oldId) (idType newId)
      where
        newId = InstEnv.instanceDFunId newInst


toInstance :: ModGuts -> CorePluginM ModGuts
toInstance guts = do
  bc <- ask tyConBareConstraint
  toInstance' bc guts

toInstance' :: TyCon -> ModGuts -> CorePluginM ModGuts
toInstance' bareConstraintTc guts = do

    -- mapM_ (putMsg . ppr) $ mg_anns guts

    let (newInsts, parsedBinds) = mapM toInst $ mg_binds guts

    return guts
      { mg_insts = newInsts ++ mg_insts guts
      , mg_inst_env = InstEnv.extendInstEnvList (mg_inst_env guts)
                    $ newInsts
      , mg_binds = parsedBinds
      }
  where
    aenv = mkAnnEnv $ mg_anns guts

    getToInstanceAnns :: CoreBind -> [ToInstance]
    getToInstanceAnns (NonRec b _)
      = findAnns deserializeWithData aenv . NamedTarget $ varName b
    getToInstanceAnns (Rec _)      = []

    -- Possibly transform a function into an instance,
    -- Keep an instance declaration if succeeded.
    toInst :: CoreBind -> ([InstEnv.ClsInst], CoreBind)
    toInst cb@(NonRec cbVar  cbE)
      | [omode] <- toOverlapFlag . overlapMode <$> getToInstanceAnns cb
      , otype <- idType cbVar
      , (First (Just (cls, tys)), ntype') <- replace otype
      , (tvs, ntype) <- extractTyVars ntype'
      , isNewType <- isNewTyCon (classTyCon cls)
      , ncbVar <- flip setIdDetails (DFunId isNewType)
                $ setIdType cbVar ntype
       -- TODO: hmm, maybe I need to remove this id from mg_exports at least...
       -- mkLocalInstance :: DFunId -> OverlapFlag -> [TyVar] -> Class -> [Type] -> ClsInst
      = ([InstEnv.mkLocalInstance ncbVar omode tvs cls tys]
        , NonRec ncbVar
          $ Cast cbE $ mkUnsafeCo Representational otype ntype
        )
    toInst cb = ([], cb)

    extractTyVars :: Type -> ([TyVar], Type)
    extractTyVars t
      | tvs <- tyCoVarsOfTypeWellScoped t
      , bndrs <- catMaybes
               . map (\b -> caseBinder b (Just . binderVar) (const Nothing))
               . fst $ splitPiTys t
      = ( tvs ++ bndrs , mkSpecForAllTys tvs t)

    -- tyCoVarsOfTypeWellScoped
    replace :: Type -> (First (Class, [Type]), Type)
    replace t
        -- split type constructors
      | Just (tyCon, tys) <- splitTyConApp_maybe t
        = case (tyCon == bareConstraintTc, tys) of
            (True, [ty]) -> (First $ extractClass ty, ty)
            _            -> mkTyConApp tyCon <$> mapM replace tys
        -- split foralls
      | (bndrs@(_:_), t') <- splitPiTys t
        = mkPiTys bndrs <$> replace t'
        -- split arrow types
      | Just (at, rt) <- splitFunTy_maybe t
        = mkFunTy <$> replace at <*> replace rt
      | otherwise
        = (First Nothing, t)

    extractClass t = splitTyConApp_maybe t
                 >>= \(tc, ts) -> flip (,) ts <$> tyConClass_maybe tc


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
      | (bndrs@(_:_), t') <- splitPiTys t
        = mkPiTys bndrs <$> replace t'
        -- split arrow types
      | Just (at, rt) <- splitFunTy_maybe t
        = mkFunTy <$> replace at <*> replace rt
      | otherwise
        = (Any False, t)



-- TODO: remove this completely!
lookupBackendFamily :: CorePluginM (CoAxiom Branched)
lookupBackendFamily = do
    hscEnv <- liftCoreM getHscEnv
    md <- lookupModule mdName [fsLit "this"]
    backendName <- liftIO
        $ TcRnMonad.initTcForLookup hscEnv
        $ IfaceEnv.lookupOrig md (mkTcOcc "Backend")
    (eps, hpt) <- liftIO $
        TcRnMonad.initTcForLookup hscEnv TcRnMonad.getEpsAndHpt
    backendTyCon <- lookupTyCon backendName

    let getArrayAxiom ca@CoAxiom {..}
          | co_ax_tc == backendTyCon = Just ca
          | otherwise                = Nothing
        cas =  mapMaybe getArrayAxiom $ (do
          hmi <- maybeToList $ lookupHpt hpt (moduleName md)
          typeEnvCoAxioms . md_types $ hm_details hmi
          ) ++ typeEnvCoAxioms (eps_PTE eps)

    return $ case cas of
      []   -> panicDoc "Data.Constraint.Deriving" $ hsep
        [ "Could not find instances of the closed type family", ppr backendTyCon ]
      ca:_ -> ca
  where
    mdName = mkModuleName "Lib.BackendFamily"


lookupName :: Module -> OccName -> CorePluginM Name
lookupName m occn = do
    hscEnv <- liftCoreM getHscEnv
    liftIO
        $ TcRnMonad.initTcForLookup hscEnv
        $ IfaceEnv.lookupOrig m occn


lookupModule :: ModuleName
             -> [FastString]
             -> CorePluginM Module
lookupModule mdName pkgs = do
    hscEnv <- liftCoreM getHscEnv
    go hscEnv $ map Just pkgs ++ [Just (fsLit "this"), Nothing]
  where
    go _ [] = pluginError $ hsep [ "Could not find module", ppr mdName]
    go he (x:xs) = findIt he x >>= \case
      Nothing -> go he xs
      Just md -> return md

    findIt he = fmap getIt . liftIO . Finder.findImportedModule he mdName
    getIt (GhcPlugins.Found _ md)                = Just md
    getIt (GhcPlugins.FoundMultiple ((md, _):_)) = Just md
    getIt _                                      = Nothing


pluginError :: SDoc -> CorePluginM a
pluginError msg = do
  liftCoreM . errorMsg $ hsep
    [ "Error occurred while running"
    , ppr pnConstraintsDeriving
    , "core plugin:"]
    $$ msg
  exception


pluginWarning :: SDoc -> CorePluginM ()
pluginWarning msg = liftCoreM . warnMsg $ hsep
   [ppr pnConstraintsDeriving, "core plugin:"] $$ msg


pnConstraintsDeriving :: FastString
pnConstraintsDeriving = "constraints-deriving"

pnConstraints :: FastString
pnConstraints = "constraints"

mnConstraint :: ModuleName
mnConstraint = mkModuleName "Data.Constraint"

mnConstraintBare :: ModuleName
mnConstraintBare = mkModuleName "Data.Constraint.Bare"

mnConstraintDeriving :: ModuleName
mnConstraintDeriving = mkModuleName "Data.Constraint.Deriving"

tnDict :: OccName
tnDict = mkTcOcc "Dict"

tnBareConstraint :: OccName
tnBareConstraint = mkTcOcc "BareConstraint"

tnDeriveContext :: OccName
tnDeriveContext = mkTcOcc "DeriveContext"

vnDictToBare :: OccName
vnDictToBare = mkVarOcc "dictToBare"

-- -- | Replace all occurrences of one type in another.
-- replaceTypeOccurrences :: Type -> Type -> Type -> Type
-- replaceTypeOccurrences told tnew = replace
--   where
--     replace :: Type -> Type
--     replace t
--         -- found occurrence
--       | eqType t told
--         = tnew
--         -- split type constructors
--       | Just (tyCon, tys) <- splitTyConApp_maybe t
--         = mkTyConApp tyCon $ map replace tys
--         -- split foralls
--       | (bndrs@(_:_), t') <- splitPiTys t
--         = mkPiTys bndrs $ replace t'
--         -- split arrow types
--       | Just (at, rt) <- splitFunTy_maybe t
--         = mkFunTy (replace at) (replace rt)
--         -- could not find anything
--       | otherwise
--         = t

toOverlapFlag :: OverlapMode -> GhcPlugins.OverlapFlag
toOverlapFlag m = GhcPlugins.OverlapFlag (getOMode m) False
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

#if __GLASGOW_HASKELL__ < 802
mkPiTys :: [Var] -> Type -> Type
mkPiTys = mkPiTypes
#endif
