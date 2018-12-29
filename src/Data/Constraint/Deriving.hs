{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
module Data.Constraint.Deriving
  ( plugin
  , ToInstance (..)
  , OverlapMode (..)
  , DeriveAll (..)
  , DeriveContext
  ) where

import           Class         (Class, classTyCon)
import           CoAxiom       (coAxiomSingleBranch, CoAxBranch, Branched, CoAxiom (..), coAxBranchIncomps,
                                coAxBranchLHS, coAxBranchRHS, coAxBranchTyVars,
                                coAxiomBranches, fromBranches)
import           Control.Monad (join, unless)
import           Data.Data     (Data, typeRep)
import           Data.IORef    (IORef, modifyIORef', newIORef, readIORef)
import qualified Data.Kind     as Kind
import           Data.Maybe    (catMaybes, fromMaybe, mapMaybe, maybeToList)
import           Data.Monoid   (Any (..), First (..))
import           Data.Proxy    (Proxy (..))
import qualified ErrUtils
import qualified FamInstEnv
import qualified Finder
import           GhcPlugins    hiding (OverlapMode (..), overlapMode, (<>))
import qualified GhcPlugins
import qualified IfaceEnv
import           InstEnv       (ClsInst, extendInstEnvList, instEnvElts,
                                instanceDFunId, instanceHead, mkLocalInstance)
import           MonadUtils    (MonadIO (..))
import           Panic         (panicDoc)
import qualified TcRnMonad
import qualified Unify

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
  return ( CoreDoPluginPass "Data.Constraint.Deriving.DeriveAll"
             (\x -> fromMaybe x <$> runCorePluginM (deriveAllPass x) eref)
         : CoreDoPluginPass "Data.Constraint.Deriving.ToInstance"
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
  , tyConDict             :: CorePluginM TyCon
  , tyConBareConstraint   :: CorePluginM TyCon
  , tyConDeriveContext    :: CorePluginM TyCon
  , funDictToBare         :: CorePluginM Id
  , tyEmptyConstraint     :: CorePluginM Type
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

    , tyEmptyConstraint = do
        ec <- flip mkTyConApp [] <$> lookupTyCon (cTupleTyConName 0)
        saveAndReturn (Just ec) $ \a e -> e { tyEmptyConstraint = a }
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
deriveAllPass gs = go (mg_tcs gs) annotateds gs
  where
    annotateds :: UniqFM [(Name, DeriveAll)]
    annotateds = getModuleAnns gs

    go :: [TyCon] -> UniqFM [(Name, DeriveAll)] -> ModGuts -> CorePluginM ModGuts
    -- All exports are processed, just return ModGuts
    go [] anns guts = do
      unless (isNullUFM anns) $
        pluginWarning $ "One or more DeriveAll annotations are ignored:"
          $+$ vcat
            (map (pprBulletNameLoc . fst) . join $ eltsUFM anns)
          $+$ "Note, DeriveAll is meant to be used only on type declarations."
      return guts

    -- process type definitions present in the set of annotations
    go (x:xs) anns guts
      | Just ((xn,_):ds) <- lookupUFM anns x = do
      unless (null ds) $
        pluginLocatedWarning (nameSrcSpan xn) $
          "Ignoring redundant DeriveAll annotions" $$
          hcat
          [ "(the plugin needs only one annotation per type declaration, but got "
          , speakN (length ds + 1)
          , ")"
          ]
      (newInstances, newBinds) <- unzip . fromMaybe [] <$> try (deriveAll x guts)
      -- add new definitions and continue
      go xs (delFromUFM anns x) guts
        { mg_insts    = newInstances ++ mg_insts guts
        , mg_inst_env = extendInstEnvList (mg_inst_env guts) newInstances
        , mg_binds    = newBinds ++ mg_binds guts
        }

    -- ignore the rest of type definitions
    go (_:xs) anns guts = go xs anns guts

    pprBulletNameLoc n = hsep
      [bullet, ppr $ occName n, ppr $ nameSrcSpan n]



{- |
  At this point, the plugin has found a candidate type.
  The first thing I do here is to make sure this is indeed a proper newtype declaration.
  Then, lookup the DeriveContext-specified constraints.
  Then, enumerate specific type instances (based on constraints and type families in the newtype def.)
  Then, lookup all class instances for the found type instances.
 -}
deriveAll :: TyCon -> ModGuts -> CorePluginM [(ClsInst, CoreBind)]
deriveAll tyCon guts
-- match good newtypes only
  | True <- isNewTyCon tyCon
  , False <- isClassTyCon tyCon
  , [dataCon] <- tyConDataCons tyCon
    = do
      dcInsts <- lookupDeriveContextInstances guts tyCon
      unpackedInsts <-
        if null dcInsts
        then (:[]) <$> mockInstance tyCon
        else return $ map unpackInstance dcInsts
      allMatchingTypes <- join <$>
        traverse (lookupMatchingBaseTypes guts tyCon dataCon) unpackedInsts
      join <$> traverse (lookupMatchingInstances guts) allMatchingTypes

-- not a good newtype declaration
  | otherwise
    = pluginLocatedError
       (nameSrcSpan $ tyConName tyCon)
       "DeriveAll works only on plain newtype declarations"

  where
    mockInstance tc = do
      let tvs = tyConTyVars tc
          tys = mkTyVarTys tvs
      rhs <- ask tyEmptyConstraint
      return (tvs, tys, rhs)
    unpackInstance i
      = let tvs = FamInstEnv.fi_tvs i
            tys  = case tyConAppArgs_maybe <$> FamInstEnv.fi_tys i of
              [Just ts] -> ts
              _ -> panicDoc "DeriveAll" $
                hsep
                  [ "I faced an impossible type when matching an instance of type family DeriveContext:"
                  , ppr i, "at"
                  , ppr $ nameSrcSpan $ getName i]
            rhs = FamInstEnv.fi_rhs i
        in (tvs, tys, rhs)


-- | Find all instance of a type family in scope by its TyCon.
lookupTyFamInstances :: ModGuts -> TyCon -> CorePluginM [FamInstEnv.FamInst]
lookupTyFamInstances guts fTyCon = do
    pkgFamInstEnv <- liftCoreM getPackageFamInstEnv
    return $ FamInstEnv.lookupFamInstEnvByTyCon (pkgFamInstEnv, mg_fam_inst_env guts) fTyCon
  
-- | Find all possible instances of DeriveContext type family for a given TyCon
lookupDeriveContextInstances :: ModGuts -> TyCon -> CorePluginM [FamInstEnv.FamInst]
lookupDeriveContextInstances guts tyCon = do
    allInsts <- ask tyConDeriveContext >>= lookupTyFamInstances guts
    return $ filter check allInsts
  where
    check fi = case tyConAppTyCon_maybe <$> FamInstEnv.fi_tys fi of
      Just tc : _ -> tc == tyCon
      _           -> False


-- | For a given type and constraints, enumerate all possible concrete types;
--   specify overlapping mode if encountered with conflicting instances of closed type families.
--
--   returns: (overlap mode, basetype, newtype);
--            the TyVars of the newtype are a superset of the TyVars of the basetype.
lookupMatchingBaseTypes :: ModGuts
                        -> TyCon
                        -> DataCon
                        -> ([TyVar], [Type], Type)
                        -> CorePluginM [(OverlapMode, Type, Type)]
lookupMatchingBaseTypes guts tyCon dataCon (tvs, tys, constraints) = do
    pluginWarning $
      "lookupMatchingBasetypes:" $$
      hsep
      [ ppr theta, "=>", ppr (baseType, newType) ]
    return []
  where
    newType = mkTyConApp tyCon tys
              -- mkFunTys theta $ mkTyConApp tyCon tys
    theta = splitCts constraints ++ dataConstraints

    splitCts c = case splitTyConApp_maybe c of
      Nothing       -> [c]
      Just (tc, ts) ->
        if isCTupleTyConName $ getName tc
        then foldMap splitCts ts
        else [c]

    (dataConstraints, baseType) = case dataConInstSig dataCon tys of
      ([], cts, [bt]) -> (cts, bt)
      _ -> panicDoc "DeriveAll" $ hsep
        [ "Impossible happened:"
        , "expected a newtype constructor"
        , "with no existential tyvars and a single type argument,"
        , "but got", ppr dataCon
        , "at", ppr $ nameSrcSpan $ getName dataCon ]




{-
  Try to use equality pred types to reduce the number of type variables.
  Ignore non-equality constraints.
  If lhs and rhs are both type variables, then replace lhs with rhs.
  Otherwise, replace bare type vars with more complicated types (i.e. "expand" vars)
 -}
trySimplifyType :: PredType -> Type -> (Any, Type)
trySimplifyType pt t = case classifyPredType pt of
    EqPred _ t1 t2 -> go t1 t2
    _ -> (Any False, t)
  where
    go t1 t2
      | Just tv <- getTyVar_maybe t1
      , subst <- extendTCvSubst emptyTCvSubst tv t2
      , t' <- substTyAddInScope subst t
        = (Any (eqType t t'), t')
      | isTyVarTy t2
        = go t2 t1
      | otherwise
        = (Any False, t)

      

-- -- TODO: Not sure if I need it at all; most of the API functions look through synonyms
-- -- | Try to remove all occurrences of type synonyms.
-- clearSynonyms :: Type -> Type
-- clearSynonyms t'
--       -- split type constructors
--     | Just (tyCon, tys) <- splitTyConApp_maybe t
--       = mkTyConApp tyCon $ map clearSynonyms tys
--       -- split foralls
--     | (bndrs@(_:_), t1) <- splitPiTys t
--       = mkPiTys bndrs $ clearSynonyms t1
--       -- split arrow types
--     | Just (at, rt) <- splitFunTy_maybe t
--       = mkFunTy (clearSynonyms at) (clearSynonyms rt)
--     | otherwise
--       = t
--   where
--     stripOuter x = case tcView x of
--       Nothing -> x
--       Just y  -> stripOuter y
--     t = stripOuter t'

-- | Find all occurrences of type or data families in the type signature;
--   group them by TyCons.
--
--   Prerequisite: the type must be free of type synonyms (output of clearSynonyms).
lookupFamilies :: Type -> FoundFamilies
lookupFamilies t
      -- split type constructors
    | Just (tyCon, tys) <- splitTyConApp_maybe t
      = case famTyConFlav_maybe tyCon of
          Nothing -> foldr mergeFFams emptyUFM $ map lookupFamilies tys
          Just ff -> unitUFM tyCon (ff, [t])
      -- split foralls
    | ((_:_), t') <- splitPiTys t
      = lookupFamilies t'
      -- split arrow types
    | Just (at, rt) <- splitFunTy_maybe t
      = lookupFamilies at `mergeFFams` lookupFamilies rt
    | otherwise
      = emptyUFM
    

type FoundFamilies = UniqFM (FamTyConFlav, [Type])

mergeFFams :: FoundFamilies -> FoundFamilies -> FoundFamilies
mergeFFams = plusUFM_C (\(ff,  x) (_,  y) -> (ff, combineLists x y))
  where
    combineLists []     ys = ys
    combineLists (x:xs) ys = combineLists xs (addToList x ys)
    addToList x [] = [x]
    addToList x (y:ys)
      | eqType x y = y:ys
      | otherwise             = y:addToList x ys



-- | Enumerate available family instances and substitute type arguments,
--   such that original type family can be replaced with any of the types in the output list.
--   It passes a TCvSubst alongside with the substituted Type.
--   The substituted Type may have TyVars from the result set of the substitution,
--   thus I must be careful with using it:
--     either somehow substitute back these tyvars from the result,
--     or substitute the whole type that contains this family occurrence. 
--
--   return Nothing   means cannot expand family (shall use it as-is);
--   return (Just []) means all instances contradict family arguments.
expandFamily :: ModGuts
             -> FamTyConFlav
             -> Type
             -> CorePluginM (Maybe [(OverlapMode, Type, TCvSubst)])
-- cannot help here
expandFamily _ AbstractClosedSynFamilyTyCon{} _ = pure Nothing
-- .. and here
expandFamily _ BuiltInSynFamTyCon{}           _ = pure Nothing
-- .. closed type families with no equations cannot be helped either
expandFamily _ (ClosedSynFamilyTyCon Nothing) _ = pure Nothing
-- For a closed type family, equations are accessible right there
expandFamily _ (ClosedSynFamilyTyCon (Just coax)) ft
  = pure $ withFamily ft Nothing $ const $ expandClosedFamily (fromBranches $ coAxiomBranches coax)
-- For a data family or an open type family, I need to lookup instances
-- in the family instance environment.
expandFamily guts DataFamilyTyCon{} ft
  = withFamily ft (pure Nothing) $ expandOpenFamily guts
expandFamily guts OpenSynFamilyTyCon ft
  = withFamily ft (pure Nothing) $ expandOpenFamily guts

withFamily :: Type -> a -> (TyCon -> [Type] -> a) -> a
withFamily ft def f = case splitTyConApp_maybe ft of
  Nothing -> def
  Just (tc, ts) -> f tc ts


-- | The same as `expandFamily`, but I know already that the family is closed.
expandClosedFamily :: [CoAxBranch] -> [Type] -> Maybe [(OverlapMode, Type, TCvSubst)]
-- empty type family -- leave it as-is
expandClosedFamily [] _ = Nothing
expandClosedFamily bs fTyArgs = Just $ mapMaybe go bs
  where
    -- I've decided to use tcMatchTyKis, which means matching Kinds too,
    -- though I may discover later should I change it to tcMatchTys.
    go cb = (,,) (overlap cb) (coAxBranchRHS cb) <$> Unify.tcMatchTyKis fTyArgs (coAxBranchLHS cb) 

    overlap cb = if null $ coAxBranchIncomps cb
                 then Overlapping
                 else Incoherent


-- | The same as `expandFamily`, but I know already that the family is open.
expandOpenFamily :: ModGuts
                 -> TyCon  -- ^ Type family construtor
                 -> [Type] -- ^ Type family arguments
                 -> CorePluginM (Maybe [(OverlapMode, Type, TCvSubst)])
expandOpenFamily guts fTyCon fTyArgs = do
  tfInsts <- lookupTyFamInstances guts fTyCon
  return $
    if null tfInsts
    then Just [] -- No mercy
    else expandClosedFamily (coAxiomSingleBranch . FamInstEnv.famInstAxiom <$> tfInsts)  fTyArgs


-- TODO: simplify this further, unmess tyvar situation.
-- | For a given most concrete type, find all possible class instances.
--   Derive them all by creating a new CoreBind with a casted type.
--
--   Prerequisite: in the tripple (overlapmode, baseType, newType),
--   TyVars of the newType must be a superset of TyVars of the baseType.
lookupMatchingInstances :: ModGuts
                        -> (OverlapMode, Type, Type)
                        -> CorePluginM [(InstEnv.ClsInst, CoreBind)]
lookupMatchingInstances guts (overlapMode, baseType, newType) =
    matchInstances <$> getUniquesM
  where
    -- lookup class instances here
    instances = instEnvElts $ mg_inst_env guts

    matchInstances :: [Unique] -> [(InstEnv.ClsInst, CoreBind)]
    matchInstances uniques = catMaybes $ zipWith ($)
      [ \u -> let refId = instanceDFunId ci
                  f i = (i, mkBind refId i)
               in f <$> matchInstance u refId (instanceHead ci)
      | ci <- instances
      ] uniques

    matchInstance :: Unique
                  -> DFunId
                  -> ([TyVar], Class, [Type])
                  -> Maybe InstEnv.ClsInst
    matchInstance uniq
                  -- (overlapMode, bTyVars, bOrigT, bNewT)
                  iDFunId
                  (iTyVars, iclass, iTyPams)
      | (Any True, newTyPams) <- matchTys iTyPams
      , (_, newDFunTy) <- matchTy (idType iDFunId)
      , newDFunId <- mkExportedLocalId
          (DFunId isNewType) newName newDFunTy
        = Just $ mkLocalInstance
                    newDFunId
                    (toOverlapFlag overlapMode)
                    iTyVars iclass newTyPams
      | otherwise
        = Nothing
      where
        matchTy = maybeReplaceTypeOccurrences (tyCoVarsOfTypeWellScoped newType) baseType newType
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
        newId = instanceDFunId newInst



deriveAllInstances'  :: CoAxiom Branched -> ModGuts -> CorePluginM ModGuts
deriveAllInstances' backendFamily  guts = do

    matchedInstances <- matchInstances <$> getUniquesM
    -- mapM_ (putMsg . ppr) typeMaps
    -- mapM_ (putMsg . ppr) matchedInstances
    --
    -- mapM_ (\b -> putMsg (ppr b) >> putMsg "------") $ mg_binds guts

    return guts
      { mg_insts = map snd matchedInstances ++ mg_insts guts
      , mg_inst_env = extendInstEnvList (mg_inst_env guts)
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
    instances = instEnvElts $ mg_inst_env guts

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
      [ \u -> let refId = instanceDFunId ci
                  f i = (mkBind refId i, i)
               in f <$> matchInstance u tm refId (instanceHead ci)
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
        = Just $ mkLocalInstance
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
        newId = instanceDFunId newInst


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
      , mg_inst_env = extendInstEnvList (mg_inst_env guts)
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
      = ([mkLocalInstance ncbVar omode tvs cls tys]
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

#if __GLASGOW_HASKELL__ < 802
mkPiTys :: [Var] -> Type -> Type
mkPiTys = mkPiTypes
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
