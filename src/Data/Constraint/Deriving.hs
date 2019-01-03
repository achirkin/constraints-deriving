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

import qualified Avail
import           Class               (Class, classTyCon)
import           CoAxiom             (CoAxBranch, coAxBranchIncomps,
                                      coAxBranchLHS, coAxBranchRHS,
                                      coAxiomBranches, coAxiomSingleBranch,
                                      fromBranches)
import           Control.Applicative (Alternative (..))
import           Control.Arrow       (second)
import           Control.Monad       (join, unless)
import           Data.Data           (Data, typeRep)
import           Data.IORef          (IORef, modifyIORef', newIORef, readIORef)
import qualified Data.Kind           as Kind
import           Data.List           (groupBy, sortOn)
import           Data.Maybe          (fromMaybe, isJust, mapMaybe)
import           Data.Monoid         (Any (..), First (..))
import           Data.Proxy          (Proxy (..))
import qualified ErrUtils
import qualified FamInstEnv
import qualified Finder
import           GhcPlugins          hiding (OverlapMode (..), overlapMode,
                                      (<>))
import qualified GhcPlugins
import qualified IfaceEnv
import qualified InstEnv
import qualified Kind
import           MonadUtils          (MonadIO (..))
import           Panic               (panicDoc)
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
             (\x -> fromMaybe x <$> runCorePluginM (toInstancePass x) eref)
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
        , mg_inst_env = InstEnv.extendInstEnvList (mg_inst_env guts) newInstances
        , mg_binds    = newBinds ++ mg_binds guts
        }

    -- ignore the rest of type definitions
    go (_:xs) anns guts = go xs anns guts

    pprBulletNameLoc n = hsep
      [" ", bullet, ppr $ occName n, ppr $ nameSrcSpan n]



{- |
  At this point, the plugin has found a candidate type.
  The first thing I do here is to make sure this is indeed a proper newtype declaration.
  Then, lookup the DeriveContext-specified constraints.
  Then, enumerate specific type instances (based on constraints and type families in the newtype def.)
  Then, lookup all class instances for the found type instances.
 -}
deriveAll :: TyCon -> ModGuts -> CorePluginM [(InstEnv.ClsInst, CoreBind)]
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
      return (tys, rhs)
    unpackInstance i
      = let tys  = case tyConAppArgs_maybe <$> FamInstEnv.fi_tys i of
              [Just ts] -> ts
              _ -> panicDoc "DeriveAll" $
                hsep
                  [ "I faced an impossible type when matching an instance of type family DeriveContext:"
                  , ppr i, "at"
                  , ppr $ nameSrcSpan $ getName i]
            rhs = FamInstEnv.fi_rhs i
        in (tys, rhs)


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


-- | Result of base type lookup, matching, and expanding
data MatchingType
  = MatchingType
  { mtCtxEqs      :: [(TyVar, Type)]
    -- ^ Current list of constraints that I may want to process
    --   during type expansion or substitution
  , mtTheta       :: ThetaType
    -- ^ Irreducible constraints (I can prepend them in the class instance declarations)
  , mtOverlapMode :: OverlapMode
    -- ^ How to declare a class instance
  , mtBaseType    :: Type
    -- ^ The type behind the newtype wrapper
  , mtNewType     :: Type
    -- ^ The newtype with instantiated type arguments
  , mtIgnoreList  :: [Type]
    -- ^ A list of type families I have already attempted to expand, but failed
    --   (e.g. wired-in type families or closed families with no equations).
  }

instance Outputable MatchingType where
  ppr MatchingType {..} = vcat
    [ "MatchingType"
    , "{ mtCtxEqs      = " GhcPlugins.<> ppr mtCtxEqs
    , ", mtTheta       = " GhcPlugins.<> ppr mtTheta
    , ", mtOverlapMode = " GhcPlugins.<> text (show mtOverlapMode)
    , ", mtBaseType    = " GhcPlugins.<> ppr mtBaseType
    , ", mtNewType     = " GhcPlugins.<> ppr mtNewType
    , ", mtIgnorelist  = " GhcPlugins.<> ppr mtIgnoreList
    , "}"
    ]


-- | Replace TyVar in all components of a MatchingType
substMatchingType :: TCvSubst -> MatchingType -> MatchingType
substMatchingType sub MatchingType {..} = MatchingType
  { mtCtxEqs      = map (second $ substTyAddInScope sub) mtCtxEqs
  , mtTheta       = map (substTyAddInScope sub) mtTheta
  , mtOverlapMode = mtOverlapMode
  , mtBaseType    = substTyAddInScope sub mtBaseType
  , mtNewType     = substTyAddInScope sub mtNewType
  , mtIgnoreList  = map (substTyAddInScope sub) mtIgnoreList
  }

replaceTyMatchingType :: Type -> Type -> MatchingType -> MatchingType
replaceTyMatchingType oldt newt MatchingType {..} = MatchingType
  { mtCtxEqs      = map (second rep) mtCtxEqs
  , mtTheta       = map rep mtTheta
  , mtOverlapMode = mtOverlapMode
  , mtBaseType    = rep mtBaseType
  , mtNewType     = rep mtNewType
  , mtIgnoreList  = map rep mtIgnoreList
  }
  where
    rep = replaceTypeOccurrences oldt newt

-- | try to get rid of mtCtxEqs by replacing tyvars by rhs in all components of the MatchingType
cleanupMatchingType :: MatchingType -> MatchingType
cleanupMatchingType mt0 = go (groupLists $ mtCtxEqs mt0) mt0 { mtCtxEqs = []}
  where
    groupOn f = groupBy (\x y -> f x == f y)
    flattenSnd []                   = []
    flattenSnd ([]:xs)              = flattenSnd xs
    flattenSnd ((ts@((tv,_):_)):xs) = (tv, map snd ts): flattenSnd xs
    groupLists = flattenSnd . groupOn fst . sortOn fst


    go :: [(TyVar, [Type])] -> MatchingType -> MatchingType
    go [] mt = mt
    go ((_, []):xs) mt = go xs mt
    -- TyVar occurs once in mtCtxEqs: I can safely replace it in the type.
    go ((tv,[ty]):xs) mt
      = let sub = extendTCvSubst emptyTCvSubst tv ty
        in go (map (second (map $ substTyAddInScope sub)) xs) $ substMatchingType sub mt
    -- TyVar occurs more than once: it may indicate a trivial substition or contradiction
    go ((tv, tys):xs) mt
      = case removeEqualTypes tys of
          []  -> go xs mt -- redundant, but compiler is happy
          [t] -> go ((tv, [t]):xs) mt
          ts  -> go xs mt { mtCtxEqs = mtCtxEqs mt ++ map ((,) tv) ts }

    removeEqualTypes [] = []
    removeEqualTypes [t] = [t]
    removeEqualTypes (t:ts)
      | any (eqType t) ts = removeEqualTypes ts
      | otherwise         = t : removeEqualTypes ts


-- | For a given type and constraints, enumerate all possible concrete types;
--   specify overlapping mode if encountered with conflicting instances of closed type families.
--
lookupMatchingBaseTypes :: ModGuts
                        -> TyCon
                        -> DataCon
                        -> ([Type], Type)
                        -> CorePluginM [MatchingType]
lookupMatchingBaseTypes guts tyCon dataCon (tys, constraints) = do
    ftheta <- filterTheta theta
    let initMt = MatchingType
          { mtCtxEqs      = fst ftheta
          , mtTheta       = snd ftheta
          , mtOverlapMode = NoOverlap
          , mtBaseType    = baseType
          , mtNewType     = newType
          , mtIgnoreList  = []
          }
    mts <- map cleanupMatchingType . take 1000 -- TODO: improve the logic and the termination rule
        <$> go (cleanupMatchingType initMt)
    return mts
  where
    go :: MatchingType -> CorePluginM [MatchingType]
    go mt = expandOneFamily guts mt >>= \case
      Nothing  -> pure [mt]
      Just mts -> join <$> traverse go mts

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
  New plan for generating matching types


  Split ThetaType into two lists:

  [(TyVar, Type)] and the rest of ThetaType

  The rest of ThetaType is considered not useful;
  it will be just appended to a list of constraints in the result types.
  [(TyVar, Type)] is a list of equality constraints that might help the algorithm.

  I want to perform three operations related to this list:
  [1] Add new tyVar ~ TypeFamily, from type family occurrences in the base or newtypes
      (but also check this type family is not present in the eqs?)
  [2] Remove an item (TypeFamily) from the list by substituting all possible type family instances
      into the the base type, the newtype, and the list of constraints.
  [3] Remove a non-TypeFamily item (i.e. a proper data/newtype TyCon) by substituting TyVar with
      this type in the base type, the newtype, and the list of constraints.

  Actions [1,2] may lead to an infinite expansion (recursive families), so I need to bound the number of
  iterations. An approximate implementation plan:
  1. Apply [1] until no type families present in the basetype or the newtype
  2. Apply [2] or [3] until no esq left???

 -}


-- | Split constraints into two groups:
--   1. The ones used as substitutions
--   2. Irreducible ones w.r.t. the type expansion algorithm
filterTheta :: ThetaType -> CorePluginM ([(TyVar, Type)], ThetaType)
filterTheta = fmap (splitEithers . join) . traverse
  (\t -> do
    teqClass <- ask classTypeEq
    filterTheta' teqClass t
  )

-- "worker" part of filterTheta (with a provided reference to "~")
filterTheta' :: Class -> Type -> CorePluginM [Either (TyVar, Type) PredType]
filterTheta' teqClass t = go (classifyPredType t)
  where
    go (EqPred _ t1 t2)
      | Just tv <- getTyVar_maybe t1
        = return [Left (tv, t2)]
      | Just tv <- getTyVar_maybe t2
        = return [Left (tv, t1)]
      | otherwise
        = do
        tv <- newTyVar (typeKind t1)
        return [Left (tv, t1), Left (tv, t2)]
    go (ClassPred c ts)
      | c == heqClass
      , [_, _, t1, t2] <- ts
        = go (EqPred ReprEq t1 t2)
      | c == teqClass
      , [_, t1, t2] <- ts
        = go (EqPred ReprEq t1 t2)
      | otherwise
        = return [Right t]
    go _ = return [Right t]

expandOneFamily :: ModGuts -> MatchingType -> CorePluginM (Maybe [MatchingType])
expandOneFamily guts mt@MatchingType{..} = case mfam of
    Nothing      -> return Nothing
    Just (ff, t) ->
      expandFamily guts ff t >>= \case
        Nothing -> return $ Just [mt { mtIgnoreList = t : mtIgnoreList }]
        Just es -> return $ Just $ map (toMT t) es
  where
    -- first, substitute all type variables,
    -- then substitute family occurrence with RHS of the axiom (rezt)
    toMT ft (omode, rezt, subst)
      = let famOcc = substTyAddInScope subst ft
            newMt  = substMatchingType subst mt
        in replaceTyMatchingType famOcc rezt newMt
            { mtOverlapMode = omode
            }


    -- Lookup through all components
    look = First . lookupFamily mtIgnoreList
    First mfam = mconcat
      [ foldMap (look . snd) mtCtxEqs
      , foldMap look mtTheta
      , look mtBaseType
      , look mtNewType
      ]


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


-- | Depth-first lookup of the first occurrence of any type family.
--   First argument is a list of types to ignore.
lookupFamily :: [Type] -> Type -> Maybe (FamTyConFlav, Type)
lookupFamily ignoreLst t
      -- split type constructors
    | Just (tyCon, tys) <- splitTyConApp_maybe t
      = case foldMap (First . lookupFamily ignoreLst) tys of
          First (Just r) -> Just r
          First Nothing  -> famTyConFlav_maybe tyCon >>= \ff ->
            if any (eqType t) ignoreLst
            then Nothing
            else Just (ff, t)
      -- split foralls
    | ((_:_), t') <- splitPiTys t
      = lookupFamily ignoreLst t'
      -- split arrow types
    | Just (at, rt) <- splitFunTy_maybe t
      = lookupFamily ignoreLst at <|> lookupFamily ignoreLst rt
    | otherwise
      = Nothing


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
    = pure $ withFamily ft Nothing $ const $ expandClosedFamily os bcs
  where
    bcs = fromBranches $ coAxiomBranches coax
    os  = if any (not . null . coAxBranchIncomps) bcs
          then map overlap bcs else repeat NoOverlap
    overlap cb = if null $ coAxBranchIncomps cb
          then Overlapping
          else Incoherent
-- For a data family or an open type family, I need to lookup instances
-- in the family instance environment.
expandFamily guts DataFamilyTyCon{} ft
  = withFamily ft (pure Nothing) $ expandOpenFamily guts
expandFamily guts OpenSynFamilyTyCon ft
  = withFamily ft (pure Nothing) $ expandOpenFamily guts

withFamily :: Type -> a -> (TyCon -> [Type] -> a) -> a
withFamily ft def f = case splitTyConApp_maybe ft of
  Nothing       -> def
  Just (tc, ts) -> f tc ts


-- | The same as `expandFamily`, but I know already that the family is closed.
expandClosedFamily :: [OverlapMode]
                   -> [CoAxBranch]
                   -> [Type] -> Maybe [(OverlapMode, Type, TCvSubst)]
-- empty type family -- leave it as-is
expandClosedFamily _ [] _ = Nothing
expandClosedFamily os bs fTyArgs = Just $ mapMaybe go $ zip os bs
  where
    -- I've decided to use tcMatchTyKis, which means matching Kinds too,
    -- though I may discover later should I change it to tcMatchTys.
    go (om, cb) = (,,) om (coAxBranchRHS cb) <$> Unify.tcMatchTyKis fTyArgs (coAxBranchLHS cb)


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
    else expandClosedFamily
           (repeat NoOverlap)
           (coAxiomSingleBranch . FamInstEnv.famInstAxiom <$> tfInsts)
           fTyArgs


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


-- | For a given most concrete type, find all possible class instances.
--   Derive them all by creating a new CoreBind with a casted type.
--
--   Prerequisite: in the tripple (overlapmode, baseType, newType),
--   TyVars of the newType must be a superset of TyVars of the baseType.
lookupMatchingInstances :: ModGuts
                        -> MatchingType
                        -> CorePluginM [(InstEnv.ClsInst, CoreBind)]
lookupMatchingInstances guts mt = go . InstEnv.instEnvElts $ mg_inst_env guts
  where
    go [] = return []
    go (i:is) = matchInstance mt i >>= \case
      Nothing -> go is
      Just ni -> ((ni, mkBind (InstEnv.instanceDFunId i) ni):) <$> go is

    -- Create a new DFunId by casting
    -- the original DFunId to a required type
    mkBind :: DFunId -> InstEnv.ClsInst -> CoreBind
    mkBind oldId newInst
        = NonRec newId
        $ mkCast (Var oldId)
        $ mkUnsafeCo Representational (idType oldId) (idType newId)
      where
        newId = InstEnv.instanceDFunId newInst

-- | TODO: shall I add theta types? Would need to modify the core expression
matchInstance :: MatchingType
              -> InstEnv.ClsInst
              -> CorePluginM (Maybe InstEnv.ClsInst)
matchInstance MatchingType {..} baseInst
    | (Any True, newTyPams) <- matchTys iTyPams
    , (_, newDFunTy) <- matchTy (idType baseDFunId)
      = do
      newN <- newName (occNameSpace baseDFunName)
        $ occNameString baseDFunName ++ newtypeNameS
      let newDFunId = mkExportedLocalId
            (DFunId isNewType) newN newDFunTy
      return . Just $ InstEnv.mkLocalInstance
                        newDFunId
                        (toOverlapFlag mtOverlapMode)
                        iTyVars iClass newTyPams
    | otherwise
      = pure Nothing
  where
    baseDFunId = InstEnv.instanceDFunId baseInst
    (iTyVars, iClass, iTyPams) = InstEnv.instanceHead baseInst
    matchTy = maybeReplaceTypeOccurrences
          (tyCoVarsOfTypeWellScoped mtNewType) mtBaseType mtNewType
    matchTys = mapM matchTy
    isNewType = isNewTyCon (classTyCon iClass)
    baseDFunName = occName . idName $ baseDFunId
    newtypeNameS = case tyConAppTyCon_maybe mtNewType of
      Nothing -> "DeriveAll-generated"
      Just tc -> occNameString $ occName $ tyConName tc


toInstancePass :: ModGuts -> CorePluginM ModGuts
toInstancePass gs = go (reverse $ mg_binds gs) annotateds gs { mg_binds = []}
  where
    annotateds :: UniqFM [(Name, ToInstance)]
    annotateds = getModuleAnns gs

    go :: [CoreBind] -> UniqFM [(Name, ToInstance)] -> ModGuts -> CorePluginM ModGuts
    -- All exports are processed, just return ModGuts
    go [] anns guts = do
      unless (isNullUFM anns) $
        pluginWarning $ "One or more ToInstance annotations are ignored:"
          $+$ vcat
            (map (pprBulletNameLoc . fst) . join $ eltsUFM anns)
          $$ "Note possible issues:"
          $$ pprNotes
           [ "ToInstance is meant to be used only on bindings of type Ctx => Dict (Class t1 .. tn)."
           , "Currently, I process non-recursive bindings only."
           , sep
             [ "Non-exported bindings may vanish before the plugin pass:"
             , "make sure you export annotated definitions!"
             ]
           ]
      return guts

    -- process type definitions present in the set of annotations
    go (cbx@(NonRec x _):xs) anns guts
      | Just ((xn, ti):ds) <- lookupUFM anns x = do
      unless (null ds) $
        pluginLocatedWarning (nameSrcSpan xn) $
          "Ignoring redundant ToInstance annotions" $$
          hcat
          [ "(the plugin needs only one annotation per binding, but got "
          , speakN (length ds + 1)
          , ")"
          ]
      -- add new definitions and continue
      try (toInstance ti cbx) >>= \case
        Nothing
          -> go xs (delFromUFM anns x) guts { mg_binds = cbx : mg_binds guts}
        Just (newInstance, newBind)
          -> go xs (delFromUFM anns x) guts
            { mg_insts    = newInstance : mg_insts guts
            , mg_inst_env = InstEnv.extendInstEnv (mg_inst_env guts) newInstance
            , mg_binds    = newBind : mg_binds guts
            , mg_exports  = Avail.filterAvails (xn /=) $ mg_exports guts
            }

    -- ignore the rest of bindings
    go (x:xs) anns guts = go xs anns guts { mg_binds = x : mg_binds guts}

    pprBulletNameLoc n = hsep
      [" " , bullet, ppr $ occName n, ppr $ nameSrcSpan n]
    pprNotes = vcat . map (\x -> hsep [" ", bullet, x])

-- | Transform a given CoreBind into an instance.
--
--   The input core bind must have type `Ctx => Dict (Class t1 .. tn)`
--
--   The output is `instance {-# overlapMode #-} Ctx => Class t1 ... tn`
toInstance :: ToInstance -> CoreBind -> CorePluginM (InstEnv.ClsInst, CoreBind)

toInstance _ (Rec xs) = do
    loc <- liftCoreM getSrcSpanM
    pluginLocatedError
        (fromMaybe loc $ getFirst $ foldMap (First . Just . nameSrcSpan . getName . fst) xs)
      $ "ToInstance plugin pass does not support recursive bindings"
      $$ hsep ["(group:", pprQuotedList (map (getName . fst) xs), ")"]

toInstance (ToInstance overlapMode) (NonRec bindVar bindExpr) = do
    -- check if all type arguments are constraint arguments
    unless (all (Kind.isConstraintKind . typeKind) theta) $
      pluginLocatedError loc notGoodMsg

    -- get necessary definitions
    tcBareConstraint <- ask tyConBareConstraint
    tcDict <- ask tyConDict
    fDictToBare <- ask funDictToBare
    varCls <- newTyVar constraintKind
    let tyMatcher = mkTyConApp tcDict [mkTyVarTy varCls]

    -- Get instance definition
    match <- case Unify.tcMatchTy tyMatcher dictTy of
      Nothing -> pluginLocatedError loc notGoodMsg
      Just ma -> pure ma
    let matchedTy = substTyVar match varCls
        instSig = mkForAllTys bndrs $ mkFunTys theta matchedTy
        bindBareTy = mkForAllTys bndrs $ mkFunTys theta $ mkTyConApp tcBareConstraint [matchedTy]

    -- check if constraint is indeed a class and get it
    matchedClass <- case tyConAppTyCon_maybe matchedTy >>= tyConClass_maybe of
      Nothing -> pluginLocatedError loc notGoodMsg
      Just cl -> pure cl

    -- try to apply dictToBare to the expression of the found binding
    newExpr <- case unwrapDictExpr dictTy fDictToBare bindExpr of
      Nothing -> pluginLocatedError loc notGoodMsg
      Just ex -> pure $ mkCast ex
                      $ mkUnsafeCo Representational bindBareTy instSig


    return $ mkNewInstance overlapMode matchedClass bindVar newExpr

  where
    origBindTy = idType bindVar
    (bndrs, bindTy) = splitForAllTyVarBndrs origBindTy
    (theta, dictTy) = splitFunTys bindTy
    loc = nameSrcSpan $ getName bindVar
    notGoodMsg =
         "ToInstance plugin pass failed to process a Dict declaraion."
      $$ "The declaration must have form `forall a1..an . Ctx => Dict (Cls t1..tn)'"
      $$ "Declaration:"
      $$ hcat
         [ "  "
         , ppr bindVar, " :: "
         , ppr origBindTy
         ]
      $$ ""
      $$ "Please check:"
      $$ vcat
       ( map (\s -> hsep  [" ", bullet, s])
         [ "It must not have arguments (i.e. is it not a fuction, but a value);"
         , "It must have type Dict;"
         , "The argument of Dict must be a single class (e.g. no constraint tuples or equalities);"
         , "It must not have implicit arguments or any other complicated things."
         ]
       )

-- This fails if the CoreExpr type is not valid instance signature.
mkNewInstance :: OverlapMode
              -> Class
              -> Id -- ^ Original core binding (with old type)
              -> CoreExpr -- ^ implementation, with a proper new type (instance signature)
              -> (InstEnv.ClsInst, CoreBind)
mkNewInstance omode cls bindVar bindExpr
    = ( InstEnv.mkLocalInstance iDFunId ioflag tvs cls tys
      , NonRec iDFunId bindExpr)
  where
    ioflag  = toOverlapFlag omode
    itype   = exprType bindExpr
    iDFunId = flip setIdDetails (DFunId $ isNewTyCon (classTyCon cls))
            $ setIdType bindVar itype
    (tvs, itype') = splitForAllTys itype
    (_, typeBody) = splitFunTys itype'
    tys = case tyConAppArgs_maybe typeBody of
      Nothing -> panicDoc "ToInstance" $ hsep
        [ "Impossible happened:"
        , "expected a class constructor in mkNewInstance, but got"
        , ppr typeBody
        , "at", ppr $ nameSrcSpan $ getName bindVar
        ]
      Just ts -> ts


-- | Go through type applications and apply dictToBare function on `Dict c` type
unwrapDictExpr :: Type
                  -- ^ Dict c
                  --
                  --   Serves as stop test (if rhs expression matches the type)
               -> Id
                  -- ^ dictToBare :: forall (c :: Constraint) . Dict c -> BareConstraint c
               -> CoreExpr
                  -- ^ forall a1..an . (Ctx1,.. Ctxn) => Dict c
               -> Maybe CoreExpr
                  -- ^ forall a1..an . (Ctx1,.. Ctxn) => BareConstraint c
unwrapDictExpr dictT unwrapFun ex = case ex of
    Var _ -> testNWrap Nothing
    Lit _ -> testNWrap Nothing
    App e a -> testNWrap $       (App e <$> proceed a)
                        <|> (flip App a <$> proceed e)
    Lam b e -> testNWrap $ Lam b <$> proceed e
    Let b e -> testNWrap $ Let b <$> proceed e
    Case {} -> testNWrap Nothing
    Cast {} -> testNWrap Nothing
    Tick t e -> testNWrap $ Tick t <$> proceed e
    Type {}  -> Nothing
    Coercion {} -> Nothing
  where
    proceed = unwrapDictExpr dictT unwrapFun
    testNWrap go = if testType ex then wrap ex else go
    wrap e = flip fmap (getClsT e) $ \t -> Var unwrapFun `App` t `App` e
    -- type variables may differ, so I need to use tcMatchTy.
    -- I do not check if resulting substition is not trivial. Shall I?
    testType = isJust . Unify.tcMatchTy dictT . exprType
    getClsT e = case tyConAppArgs_maybe $ exprType e of
      Just [t] -> Just $ Type t
      _        -> Nothing



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

pnBase :: FastString
pnBase = "base"

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
      | (bndrs@(_:_), t') <- splitPiTys t
        = mkPiTys bndrs $ replace t'
        -- split arrow types
      | Just (at, rt) <- splitFunTy_maybe t
        = mkFunTy (replace at) (replace rt)
        -- could not find anything
      | otherwise
        = t

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
