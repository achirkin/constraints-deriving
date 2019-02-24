{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TypeFamilies       #-}
module Data.Constraint.Deriving.DeriveAll
  ( DeriveAll (..), DeriveContext
  , deriveAllPass
  , CorePluginEnvRef, initCorePluginEnv
  ) where


import           Class               (Class, classTyCon)
import           CoAxiom             (CoAxBranch, coAxBranchIncomps,
                                      coAxBranchLHS, coAxBranchRHS,
                                      coAxiomBranches, coAxiomSingleBranch,
                                      fromBranches)
import           Control.Applicative (Alternative (..))
import           Control.Arrow       (second)
import           Control.Monad       (join, unless)
import           Data.Data           (Data)
import           Data.Either         (partitionEithers)
import qualified Data.Kind           (Constraint, Type)
import           Data.List           (groupBy, sortOn)
import           Data.Maybe          (fromMaybe, mapMaybe)
import           Data.Monoid         (First (..))
import qualified FamInstEnv
import           GhcPlugins          hiding (OverlapMode (..), overlapMode,
                                      (<>))
import qualified GhcPlugins
import qualified InstEnv
import           Panic               (panicDoc)
import qualified Unify

import Data.Constraint.Deriving.CorePluginM

-- | A marker to tell the core plugin to derive all visible class instances for a given newtype.
--
--   The deriving logic is to simply re-use existing instance dictionaries by casting them.
data DeriveAll = DeriveAll
  deriving (Eq, Show, Read, Data)


-- | This type family is used to impose constraints on type parameters when looking up type instances
--   for the `DeriveAll` core plugin.
--
--   `DeriveAll` uses only those instances that satisfy the specified constraint.
--   If the constraint is not specified, it is assumed to be `()`.
type family DeriveContext (t :: Data.Kind.Type) :: Data.Kind.Constraint

-- | Run `DeriveAll` plugin pass
deriveAllPass :: CorePluginEnvRef -> CoreToDo
deriveAllPass eref = CoreDoPluginPass "Data.Constraint.Deriving.DeriveAll"
  -- if a plugin pass totally  fails to do anything useful,
  -- copy original ModGuts as its output, so that next passes can do their jobs.
  (\x -> fromMaybe x <$> runCorePluginM (deriveAllPass' x) eref)

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
deriveAllPass' :: ModGuts -> CorePluginM ModGuts
deriveAllPass' gs = go (mg_tcs gs) annotateds gs
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
      pluginDebug $ "DeriveAll invoked on TyCon" <+> ppr x
      (newInstances, newBinds) <- unzip . fromMaybe [] <$> try (deriveAll x guts)
      -- add new definitions and continue
      go xs (delFromUFM anns x) guts
        { mg_insts    = newInstances ++ mg_insts guts
        --   I decided to not modify mg_inst_env so that DeriveAll-derived instances
        --   do not refer to each other.
        --   Overwise, the result of the plugin would depend on the order of
        --   type declaration, which would be not good at all.
        -- , mg_inst_env = InstEnv.extendInstEnvList (mg_inst_env guts) newInstances
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
      pluginDebug
        . hang "DeriveAll (1): DeriveContext instances:" 2
        . vcat $ map ppr dcInsts
      unpackedInsts <-
        if null dcInsts
        then (:[]) <$> mockInstance tyCon
        else return $ map unpackInstance dcInsts
      pluginDebug
        . hang "DeriveAll (1): DeriveContext instance parameters and RHSs:" 2
        . vcat $ map ppr unpackedInsts
      allMatchingTypes <- join <$>
        traverse (lookupMatchingBaseTypes guts tyCon dataCon) unpackedInsts
      pluginDebug
        . hang "DeriveAll (2): matching base types:" 2
        . vcat $ map ppr allMatchingTypes
      r <- join <$> traverse (lookupMatchingInstances guts) allMatchingTypes
      pluginDebug
        . hang "DeriveAll (3): matching class instances:" 2
        . vcat $ map (ppr . fst) r
      return r

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
    -- ^ A list of type families I have already attempted to expand once
    --   (e.g. wired-in type families or closed families with no equations
    --         or something recursive).
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
    flattenSnd []                 = []
    flattenSnd ([]:xs)            = flattenSnd xs
    flattenSnd (ts@((tv,_):_):xs) = (tv, map snd ts): flattenSnd xs
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
    map cleanupMatchingType . take 1000 -- TODO: improve the logic and the termination rule
        <$> go (cleanupMatchingType initMt)
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
filterTheta = fmap (partitionEithers . join) . traverse
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
          -- nominal or rep-al equality does not matter here, because
          -- I don't distinguish between those a few lines above.
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
    Just (ff, t) -> expandFamily guts ff t >>= \case
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
--     | (bndrs@(_:_), t1) <- splitForAllTys t
--       = mkSpecForAllTys bndrs $ clearSynonyms t1
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
    | (_:_, t') <- splitForAllTys t
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
  = withFamily ft (pure Nothing) $ expandDataFamily guts
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
    go (om, cb) = (,,) om (coAxBranchRHS cb) <$> Unify.tcMatchTys fTyArgs (coAxBranchLHS cb)


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


-- | The same as `expandFamily`, but I know already that this is a data family.
expandDataFamily :: ModGuts
                 -> TyCon  -- ^ Type family construtor
                 -> [Type] -- ^ Type family arguments
                 -> CorePluginM (Maybe [(OverlapMode, Type, TCvSubst)])
expandDataFamily guts fTyCon fTyArgs = do
  tfInsts <- lookupTyFamInstances guts fTyCon
  return $
    if null tfInsts
    then Just [] -- No mercy
    else traverse expandDInstance tfInsts
  where
    expandDInstance inst
      | instTyArgs <- align fTyArgs (FamInstEnv.fi_tys inst)
      = (,,) NoOverlap (mkTyConApp fTyCon instTyArgs)
      <$> Unify.tcMatchTys fTyArgs instTyArgs
    align [] _          = []
    align xs []         = xs
    align (_:xs) (y:ys) = y : align xs ys



-- | For a given most concrete type, find all possible class instances.
--   Derive them all by creating a new CoreBind with a casted type.
--
--   Prerequisite: in the tripple (overlapmode, baseType, newType),
--   TyVars of the newType must be a superset of TyVars of the baseType.
lookupMatchingInstances :: ModGuts
                        -> MatchingType
                        -> CorePluginM [(InstEnv.ClsInst, CoreBind)]
lookupMatchingInstances guts mt
    | Just bTyCon <- tyConAppTyCon_maybe $ mtBaseType mt = do
      clsInsts <- flip lookupClsInsts bTyCon <$> getInstEnvs guts
      pluginDebug $ hang "lookupMatchingInstances candidate instances:" 2 $
        vcat $ map ppr clsInsts
      go clsInsts
    | otherwise = fmap (const []) . pluginDebug $ hcat
        [ text "DeriveAll.lookupMatchingInstances found no class instances for "
        , ppr (mtBaseType mt)
        , text ", because it could not get the type constructor."
        ]
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

-- TODO: shall I add theta types from MatchingType derive context?
--            Would need to modify the core expression
--
-- TODO: Filter out redundant or unsatisfiable PredTypes
--       e.g. Ord Char => Ord String
--       e.g. Ord (IO ()) => Ord [IO ()]
--
-- TODO: blacklist some types, e.g. parts of Generics, such as URec
--
-- TODO: add an interface to blacklist some classes
matchInstance :: MatchingType
              -> InstEnv.ClsInst
              -> CorePluginM (Maybe InstEnv.ClsInst)
matchInstance MatchingType {..} baseInst
    | Just baseSub
        <- getFirst $ foldMap (First . flip recMatchTyKi mtBaseType) iTyPams
    , substBaseTy
        <- replaceTypeOccurrences mtBaseType mtNewType . substTyAddInScope baseSub
    , newTyPams
        <- map substBaseTy iTyPams
    , newTheta
        <- map (replaceTypeOccurrences mtBaseType mtNewType)
         $ substTheta baseSub iTheta
    , newDFunTyNoTyVars
        <- mkFunTys newTheta
         $ mkTyConApp (classTyCon iClass) newTyPams
    , newTyVars
        <- toposortTyVars $ tyCoVarsOfTypeWellScoped newDFunTyNoTyVars
    , newDFunTy
        <- mkSpecForAllTys newTyVars newDFunTyNoTyVars
      = do
      newN <- newName (occNameSpace baseDFunName)
        $ occNameString baseDFunName
          ++ show (getUnique baseDFunId) -- unique per baseDFunId
          ++ newtypeNameS                -- unique per newType
      let newDFunId = mkExportedLocalId
            (DFunId isNewType) newN newDFunTy
      return . Just $ InstEnv.mkLocalInstance
                        newDFunId
                        (toOverlapFlag mtOverlapMode)
                        iTyVars iClass newTyPams
    | otherwise
      = do
      pluginDebug $ hang "Ignored instance" 2
        (ppr mtBaseType <+> ppr baseInst
        )
      pure Nothing
  where
    baseDFunId = InstEnv.instanceDFunId baseInst
    (iTyVars, iTheta, iClass, iTyPams) = InstEnv.instanceSig baseInst
    isNewType = isNewTyCon (classTyCon iClass)
    baseDFunName = occName . idName $ baseDFunId
    newtypeNameS = case tyConAppTyCon_maybe mtNewType of
      Nothing -> "DeriveAll-generated"
      Just tc -> occNameString $ occName $ tyConName tc
